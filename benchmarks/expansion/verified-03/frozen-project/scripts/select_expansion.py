#!/usr/bin/env python3
"""Combine checked census proposals and reviewed preparations without double counting."""

import argparse
from collections import Counter, defaultdict
import copy
import json
from pathlib import Path
import subprocess

from benchmark import BenchmarkError, code_line_count, prepare_sources, safe_source_path, sha256, without_comments
from select_census import select_file


def merge_manifests(manifests, mathlib, excluded=None):
    excluded = excluded or {}
    revisions = {manifest["mathlib_revision"] for manifest in manifests}
    if len(revisions) != 1:
        raise BenchmarkError("input manifests must share one Mathlib revision")
    specifications, candidates, sources = {}, {}, {}
    for manifest in manifests:
        for item in manifest["files"]:
            path = item["path"]
            safe_source_path(path)
            if item.get("helpers") or item.get("imports", []) not in ([], ["NormArith"]):
                raise BenchmarkError("expansion supports one tactic import and no helpers")
            if path in specifications and item["source_sha256"] != specifications[path]["source_sha256"]:
                raise BenchmarkError(f"conflicting source hashes: {path}")
            specifications[path] = dict(item, imports=[], helpers=[])
        for original in manifest["candidates"]:
            if original["status"] not in {"replace", "unchanged"}:
                continue
            candidate = copy.deepcopy(original)
            path = candidate["path"]
            if path not in sources:
                sources[path] = (mathlib / safe_source_path(path)).read_bytes()
            source = sources[path]
            if sha256(source) != specifications[path]["source_sha256"]:
                raise BenchmarkError(f"source hash mismatch: {path}")
            lines = source.splitlines(keepends=True)
            first, last = candidate["start_line"], candidate["end_line"]
            if not isinstance(first, int) or not isinstance(last, int) or not 1 <= first <= last <= len(lines):
                raise BenchmarkError(f"invalid line span: {candidate['id']}")
            left, right = sum(map(len, lines[:first - 1])), sum(map(len, lines[:last]))
            if sha256(source[left:right]) != candidate["original_sha256"]:
                raise BenchmarkError(f"span hash mismatch: {candidate['id']}")
            start, end = candidate["source_start_byte"], candidate["source_end_byte"]
            body_start, body_end = candidate["body_start_byte"], candidate["body_end_byte"]
            if not (left <= start < end <= right and 0 <= body_start <= start < end <= body_end <= len(source)):
                raise BenchmarkError(f"invalid proof span: {candidate['id']}")
            prefix, suffix = source[left:start].decode(), source[end:right].decode()
            replacement = candidate["replacement"]
            if not replacement.startswith(prefix) or not replacement.endswith(suffix):
                raise BenchmarkError(f"replacement changes source outside the proof: {candidate['id']}")
            stop = len(replacement) - len(suffix) if suffix else len(replacement)
            proof = replacement[len(prefix):stop]
            if candidate.get("proof_replacement", proof) != proof:
                raise BenchmarkError(f"inconsistent proof replacement: {candidate['id']}")
            if any(len(line) > 100 for line in replacement.splitlines()):
                raise BenchmarkError(f"replacement exceeds 100 characters: {candidate['id']}")
            code = without_comments(source.decode()).splitlines()
            before = sum(bool(line.strip()) for line in code[first - 1:last])
            after = code_line_count(replacement)
            candidate.update(proof_replacement=proof, manual_review=True,
                             original_proof_lines=before, replacement_proof_lines=after,
                             proof_lines_saved=before - after)
            candidate.setdefault("proof_kind", "reviewed_checked_census")
            previous = candidates.get(candidate["id"])
            if previous:
                fields = ["path", "start_line", "end_line", "original_sha256", "replacement",
                          "source_start_byte", "source_end_byte", "body_start_byte", "body_end_byte"]
                if any(previous[field] != candidate[field] for field in fields):
                    raise BenchmarkError(f"conflicting candidate id: {candidate['id']}")
            else:
                candidates[candidate["id"]] = candidate
    by_path = defaultdict(list)
    for candidate in candidates.values():
        by_path[candidate["path"]].append(candidate)
    ledger = []
    for path, items in sorted(by_path.items()):
        selected, reasons = select_file([item for item in items if item["id"] not in excluded])
        selected_ids = {item["id"] for item in selected}
        specifications[path]["imports"] = ["NormArith"] if selected else []
        for item in items:
            if item["id"] in excluded:
                item.update(status="failed", reason=excluded[item["id"]])
            else:
                item.update(status="replace" if item["id"] in selected_ids else "unchanged",
                            reason=reasons[item["id"]])
            ledger.append({"id": item["id"], "path": path, "outcome": item["reason"],
                           "proof_lines_saved": item["proof_lines_saved"]})
    merged = {"schema_version": 1, "mathlib_revision": next(iter(revisions)),
              "selection_status": "integration-trial",
              "selection_rule": "maximize saved code lines over disjoint whole-line spans; charge every preparation and one import per file; require positive net file saving; ties prefer fewer edits then source order and stable id; timing never selects edits",
              "files": [specifications[path] for path in sorted(by_path)],
              "candidates": sorted(candidates.values(), key=lambda item: (item["path"], item["start_line"], item["id"]))}
    _, accounting = prepare_sources(merged, mathlib)
    return merged, ledger, accounting


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifests", type=Path, nargs="+")
    parser.add_argument("--mathlib", type=Path, default=Path(__file__).resolve().parents[1] / ".lake/packages/mathlib")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--exclude", type=Path)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    if any(args.output.iterdir()):
        parser.error("output directory must be empty")
    raw = [path.read_bytes() for path in args.manifests]
    merged, ledger, accounting = merge_manifests([json.loads(data) for data in raw], args.mathlib,
        json.loads(args.exclude.read_text()) if args.exclude else None)
    revision = subprocess.check_output(["git", "-C", str(args.mathlib), "rev-parse", "HEAD"], text=True).strip()
    if revision != merged["mathlib_revision"]:
        raise BenchmarkError("manifest revision differs from the Mathlib checkout")
    (args.output / "inputs").mkdir()
    inputs = []
    for index, (path, data) in enumerate(zip(args.manifests, raw)):
        name = f"inputs/{index:02d}.json"
        (args.output / name).write_bytes(data)
        inputs.append({"source": str(path.resolve()), "snapshot": name, "sha256": sha256(data)})
    merged["input_manifests"] = inputs
    (args.output / "manifest.json").write_text(json.dumps(merged, indent=2, ensure_ascii=False) + "\n")
    (args.output / "selection.jsonl").write_text("".join(json.dumps(row) + "\n" for row in ledger))
    summary = {"evidence_stage": "selected_proposals_not_combined_source_compiled", "accounting": accounting,
               "outcome_counts": dict(Counter(row["outcome"] for row in ledger))}
    (args.output / "summary.json").write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n")
    print(args.output / "manifest.json")


if __name__ == "__main__":
    try:
        main()
    except (BenchmarkError, OSError, ValueError, KeyError) as error:
        raise SystemExit(f"expansion selection: {error}")
