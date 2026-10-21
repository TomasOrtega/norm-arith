#!/usr/bin/env python3
"""Rank unobserved tactic-sequence tails; these are not replay-verified proposals."""

from collections import Counter
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
RUN = ROOT / ".lake/census-full-v3"
OUT = ROOT / "artifacts/expansion"


def main():
    candidates = []
    statuses = Counter()
    for result_path in sorted((RUN / "files").glob("*/result.json")):
        result = json.loads(result_path.read_text())
        events = RUN / result["directory"] / "events.jsonl"
        if not events.exists():
            continue
        observations = []
        for number, line in enumerate(events.read_text().splitlines(), 1):
            row = json.loads(line)
            if row.get("type") == "observation" and row.get("phase") == "original":
                observations.append(dict(row, raw_event_line=number))
        seqs = [row for row in observations if row["syntax_kind"] in {
            "Lean.Parser.Tactic.tacticSeq1Indented", "Lean.Parser.Tactic.tacticSeqBracketed"}]
        if not seqs:
            continue
        existing = {(row["start_byte"], row["end_byte"], row["goal"]) for row in observations}
        source = (ROOT / ".lake/packages/mathlib" / result["path"]).read_bytes()
        seen = set()
        for row in observations:
            if row["kind"] != "tactic" or not row["goal_eligible"]:
                continue
            if row["eligibility_reason"] != "multi_goal_tactic":
                continue
            if row["syntax_kind"] in {"Lean.cdotTk", "null", "Lean.cdot"}:
                continue
            parents = [seq for seq in seqs if seq["parent_declaration"] == row["parent_declaration"]
                       and seq["start_byte"] < row["start_byte"]
                       and row["end_byte"] <= seq["end_byte"]]
            if not parents:
                continue
            seq = min(parents, key=lambda parent: parent["end_byte"] - parent["start_byte"])
            key = row["start_byte"], seq["end_byte"], row["goal"]
            if key in existing or key in seen:
                continue
            seen.add(key)
            block = source[row["start_byte"]:seq["end_byte"]].decode()
            lines = block.splitlines()
            nonblank = sum(bool(line.strip()) for line in lines)
            if nonblank <= 1:
                continue
            statuses[row["syntax_kind"]] += 1
            candidates.append({**row, "path": result["path"], "source": block,
                               "proposed_end_byte": seq["end_byte"], "proposed_end_line": seq["end_line"],
                               "candidate_nonblank_lines": nonblank,
                               "prefix_context_declarations_added": row["context_declarations"] - seq["context_declarations"],
                               "original_sequence_start_line": seq["start_line"],
                               "original_sequence_goal": seq["goal"],
                               "raw_event_path": str(events.relative_to(ROOT)),
                               "status": "heuristic_unobserved_suffix_not_replayed"})
    candidates.sort(key=lambda row: (-row["candidate_nonblank_lines"], row["path"], row["start_byte"]))
    (OUT / "candidate-suffixes.jsonl").write_text("".join(json.dumps(row, ensure_ascii=False) + "\n" for row in candidates))
    summary = {"candidate_records": len(candidates), "files": len({row["path"] for row in candidates}),
               "start_syntax_counts": dict(statuses),
               "limitations": "Source-containment heuristic only: no Lean syntax parent relation, goal replay, source compilation, overlap selection, or line-saving claim.",
               "largest": [{k: row[k] for k in ["path", "start_line", "proposed_end_line", "candidate_nonblank_lines", "syntax_kind", "goal"]}
                           for row in candidates[:30]]}
    (OUT / "suffix-index.json").write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({k: summary[k] for k in ["candidate_records", "files", "start_syntax_counts"]}, indent=2))


if __name__ == "__main__":
    main()
