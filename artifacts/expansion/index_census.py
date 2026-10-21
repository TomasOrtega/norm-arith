#!/usr/bin/env python3
"""Index retained latest-attempt census observations without changing the census."""

from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
RUN = ROOT / ".lake/census-full-v3"
OUT = ROOT / "artifacts/expansion"


def main():
    attempts = []
    excluded = []
    observation_counts = Counter()
    multi = Counter()
    term_syntax = Counter()
    errors = Counter()
    all_syntax = Counter()
    statuses = Counter()
    source_cache = {}

    def enrich(row, path, events, number):
        if path not in source_cache:
            source_cache[path] = (ROOT / ".lake/packages/mathlib" / path).read_bytes()
        source = source_cache[path]
        block = source[row["start_byte"]:row["end_byte"]].decode()
        physical = block.splitlines()
        return dict(row, path=path, raw_event_path=str(events.relative_to(ROOT)), raw_event_line=number,
                    source=block, source_sha256=hashlib.sha256(block.encode()).hexdigest(),
                    source_physical_lines=len(physical),
                    nonblank_source_lines=sum(bool(line.strip()) for line in physical))

    for result_path in sorted((RUN / "files").glob("*/result.json")):
        result = json.loads(result_path.read_text())
        events = RUN / result["directory"] / "events.jsonl"
        if not events.exists():
            continue
        path = result["path"]
        with events.open() as stream:
            for number, line in enumerate(stream, 1):
                row = json.loads(line)
                if row.get("type") == "attempt":
                    statuses[row["status"]] += 1
                    if row["status"] != "no_line_saving_untried":
                        attempts.append(enrich(row, path, events, number))
                        if row["status"] == "failed":
                            errors[row.get("error", "")] += 1
                elif row.get("type") == "observation" and row.get("phase") == "original":
                    reason = row["eligibility_reason"]
                    observation_counts[reason] += 1
                    all_syntax[row["syntax_kind"]] += 1
                    if row["kind"] == "term":
                        term_syntax[row["syntax_kind"]] += 1
                    if row["goal_eligible"] and row["end_line"] > row["start_line"]:
                        multi[reason] += 1
                        if reason != "eligible":
                            excluded.append(enrich(row, path, events, number))

    attempts.sort(key=lambda row: (-row["nonblank_source_lines"], row["path"], row["start_byte"]))
    excluded.sort(key=lambda row: (-row["nonblank_source_lines"], row["path"], row["start_byte"]))
    for name, rows in [("attempts.jsonl", attempts), ("excluded-multiline-eligible-goals.jsonl", excluded)]:
        (OUT / name).write_text("".join(json.dumps(row, ensure_ascii=False) + "\n" for row in rows))
    summary = {
        "status": "read_only_diagnosis_index", "source_run": str(RUN.relative_to(ROOT)),
        "attempt_status_counts": dict(statuses),
        "original_observation_eligibility_reason_counts": dict(observation_counts),
        "multiline_original_goal_eligible_reason_counts": dict(multi),
        "failure_exact_messages": [{"count": n, "message": e} for e, n in errors.most_common()],
        "observed_tactic_sequence_syntax": {k: n for k, n in all_syntax.items() if "Seq" in k or "calc" in k},
        "term_syntax_counts": dict(term_syntax.most_common()),
        "largest_failed_spans": [{k: row[k] for k in ["path", "start_line", "end_line", "nonblank_source_lines", "syntax_kind", "goal", "error"]}
                                  for row in attempts if row["status"] == "failed"][:40],
        "largest_excluded_multiline_spans": [{k: row[k] for k in ["path", "start_line", "end_line", "nonblank_source_lines", "eligibility_reason", "syntax_kind", "goal"]}
                                             for row in excluded[:40]],
        "limitations": "Span line counts are ranking aids, not verified replaceable savings; overlapping spans are retained."
    }
    (OUT / "census-index.json").write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({k: summary[k] for k in ["attempt_status_counts", "original_observation_eligibility_reason_counts", "multiline_original_goal_eligible_reason_counts"]}, indent=2))


if __name__ == "__main__":
    main()
