#!/usr/bin/env python3
"""Select a deterministic line-saving patch from isolated census proposals."""

import argparse
from bisect import bisect_left, bisect_right
from collections import Counter
import json
from pathlib import Path
import subprocess

from benchmark import BenchmarkError, code_line_count, prepare_sources, safe_source_path, sha256, without_comments


class SelectionError(Exception):
    pass


def render_replacement(prefix, token, suffix):
    if token not in {"norm_arith", "by norm_arith"}:
        raise SelectionError("replacement is outside the fixed rule set")
    before, after = prefix.decode("utf-8"), suffix.decode("utf-8")
    edited = before + token + after
    if any(len(line) > 100 for line in edited.splitlines()) and token == "by norm_arith":
        indent = before[:len(before) - len(before.lstrip())]
        edited = before + "by\n" + indent + "  norm_arith" + after
    if any(len(line) > 100 for line in edited.splitlines()):
        raise SelectionError("fixed proof formatting exceeds Mathlib's 100-character line limit")
    return edited if edited.endswith("\n") else edited + "\n"


def candidate_from_proposal(proposal, source):
    if proposal.get("status") != "success" or proposal.get("kernel_checked") is not True:
        raise SelectionError("proposal has no checked successful replay")
    if proposal.get("replacement_eligible") is not True:
        raise SelectionError("observation is not source-replaceable")
    path = proposal["path"]
    safe_source_path(path)
    if not path.startswith("Mathlib/") or sha256(source) != proposal.get("source_sha256"):
        raise SelectionError("source path or hash mismatch")
    start, end = proposal["start_byte"], proposal["end_byte"]
    if not isinstance(start, int) or not isinstance(end, int) or not 0 <= start < end <= len(source):
        raise SelectionError("invalid source byte range")
    body_start, body_end = proposal.get("body_start_byte"), proposal.get("body_end_byte")
    if not isinstance(body_start, int) or not isinstance(body_end, int) or not (
            0 <= body_start <= start < end <= body_end <= len(source)):
        raise SelectionError("proposal is outside the declaration proof body")
    if sha256(source[start:end]) != proposal.get("original_sha256"):
        raise SelectionError("proposal span hash mismatch")
    replacement = proposal["replacement"]
    if replacement not in {"norm_arith", "by norm_arith"}:
        raise SelectionError("replacement is outside the fixed rule set")
    try:
        source[start:end].decode("utf-8")
        starts = [0, *(index + 1 for index, char in enumerate(source) if char == 10)]
        first = bisect_right(starts, start) - 1
        last = bisect_right(starts, end - 1) - 1
        stop = starts[last + 1] if last + 1 < len(starts) else len(source)
        original = source[starts[first]:stop].decode("utf-8")
        edited = render_replacement(source[starts[first]:start], replacement, source[end:stop])
    except UnicodeDecodeError as error:
        raise SelectionError("span splits a UTF-8 character") from error
    code = without_comments(source.decode()).splitlines()
    before = sum(bool(line.strip()) for line in code[first:last + 1])
    after = code_line_count(edited)
    identifier = sha256(json.dumps([path, start, end, proposal.get("key")], separators=(",", ":")))[:20]
    return {
        "id": f"census-{identifier}", "path": path,
        "declaration": proposal.get("parent_declaration", ""),
        "status": "unchanged", "reason": "pending deterministic selection",
        "start_line": first + 1, "end_line": last + 1,
        "original_sha256": sha256(original), "replacement": edited,
        "proof_lines_saved": before - after, "original_proof_lines": before,
        "replacement_proof_lines": after, "observation_key": proposal.get("key"),
        "fragment": proposal.get("fragment", "unspecified"),
        "source_start_byte": start, "source_end_byte": end,
        "body_start_byte": body_start, "body_end_byte": body_end,
    }


def choose_intervals(candidates):
    ordered = sorted((item for item in candidates if item["proof_lines_saved"] > 0),
                     key=lambda item: (item["end_line"], item["start_line"], item["id"]))
    ends = [item["end_line"] for item in ordered]
    best = [(0, ())]
    for index, item in enumerate(ordered):
        previous = bisect_left(ends, item["start_line"], 0, index)
        weight, chosen = best[previous]
        take = (weight + item["proof_lines_saved"], (*chosen, index))
        skip = best[-1]

        def rank(option):
            return (-option[0], len(option[1]), tuple(
                (ordered[i]["start_line"], ordered[i]["end_line"], ordered[i]["id"])
                for i in option[1]))

        best.append(min((take, skip), key=rank))
    return sorted((ordered[index] for index in best[-1][1]),
                  key=lambda item: (item["start_line"], item["end_line"], item["id"]))


def select_file(candidates, import_lines=1):
    ledger, distinct, seen = {}, [], set()
    for item in sorted(candidates, key=lambda item: item["id"]):
        signature = (item["start_line"], item["end_line"], item["replacement"])
        if signature in seen:
            ledger[item["id"]] = "duplicate_replacement"
        elif item["proof_lines_saved"] <= 0:
            ledger[item["id"]] = "no_line_saving"
            seen.add(signature)
        else:
            distinct.append(item)
            seen.add(signature)
    selected = choose_intervals(distinct)
    if sum(item["proof_lines_saved"] for item in selected) <= import_lines:
        for item in distinct:
            ledger[item["id"]] = "import_cost_offsets_savings"
        return [], ledger
    selected_ids = {item["id"] for item in selected}
    for item in distinct:
        ledger[item["id"]] = "selected" if item["id"] in selected_ids else "overlap"
    return selected, ledger


def select_run(census, mathlib, excluded=None):
    excluded = excluded or {}
    census_manifest = json.loads((census / "manifest.json").read_text())
    revision = subprocess.check_output(["git", "-C", str(mathlib), "rev-parse", "HEAD"], text=True).strip()
    if revision != census_manifest["mathlib_revision"]:
        raise SelectionError("census and source revision differ")
    candidates, specifications, ledger = [], [], []
    for path in census_manifest["selected_files"]:
        directory = census / "files" / path[:-5].replace("/", ".")
        result_path = directory / "result.json"
        if not result_path.exists():
            ledger.append({"path": path, "outcome": "unprocessed_file"})
            continue
        result = json.loads(result_path.read_text())
        if not result.get("complete"):
            ledger.append({"path": path, "outcome": "extraction_incomplete", "status": result.get("status")})
            continue
        source = (mathlib / safe_source_path(path)).read_bytes()
        file_candidates = []
        for line in (census / result["proposal_file"]).read_text().splitlines():
            proposal = json.loads(line)
            try:
                item = candidate_from_proposal(proposal, source)
            except (SelectionError, BenchmarkError) as error:
                ledger.append({"path": path, "key": proposal.get("key"),
                               "outcome": "uneditable_proposal", "reason": str(error)})
                continue
            if item["id"] in excluded:
                item.update(status="failed", reason=excluded[item["id"]])
            file_candidates.append(item)
        if not file_candidates:
            continue
        selected, reasons = select_file([item for item in file_candidates if item["id"] not in excluded])
        selected_ids = {item["id"] for item in selected}
        for item in file_candidates:
            if item["id"] not in excluded:
                item.update(status="replace" if item["id"] in selected_ids else "unchanged",
                            reason=reasons[item["id"]])
            ledger.append({"id": item["id"], "path": path, "key": item["observation_key"],
                           "outcome": item["reason"], "proof_lines_saved": item["proof_lines_saved"]})
        candidates.extend(file_candidates)
        specifications.append({"path": path, "source_sha256": sha256(source),
                               "imports": ["NormArith"] if selected else [], "helpers": []})
    manifest = {
        "schema_version": 1, "mathlib_revision": revision, "selection_status": "integration-trial",
        "census_protocol_hash": census_manifest["protocol_hash"],
        "selection_rule": "format fixed proofs to at most 100 Unicode characters per line, wrapping by blocks with two-space continuation indentation; maximize saved code lines over disjoint whole-line spans; ties prefer fewer edits, then source order and stable id; charge one import per affected file; require positive net saving",
        "candidates": candidates, "files": specifications,
    }
    _, accounting = prepare_sources(manifest, mathlib)
    return manifest, ledger, accounting


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("census", type=Path)
    parser.add_argument("--mathlib", type=Path, default=Path(__file__).resolve().parents[1] / ".lake/packages/mathlib")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--exclude", type=Path, help="JSON mapping of source-compile-rejected ids to reasons")
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    if any(args.output.iterdir()):
        parser.error("output directory must be empty")
    manifest, ledger, accounting = select_run(args.census, args.mathlib,
                                            json.loads(args.exclude.read_text()) if args.exclude else None)
    (args.output / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    (args.output / "selection.jsonl").write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in ledger))
    summary = {"evidence_stage": "selected_isolated_proposals_not_source_compiled",
               "accounting": accounting, "outcome_counts": dict(Counter(row["outcome"] for row in ledger))}
    (args.output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(args.output / "manifest.json")


if __name__ == "__main__":
    try:
        main()
    except (SelectionError, BenchmarkError, OSError, ValueError) as error:
        raise SystemExit(f"selection: {error}")
