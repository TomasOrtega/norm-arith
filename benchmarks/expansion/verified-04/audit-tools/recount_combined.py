#!/usr/bin/env python3
"""Independently recount a compiled composed patch, including preparation."""

import argparse
from collections import defaultdict
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[2]
LEXER_PATH = ROOT / "artifacts/independent-line-count.py"
SPEC = importlib.util.spec_from_file_location("independent_lean_line_audit", LEXER_PATH)
COUNTER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(COUNTER)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("verification", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    directory = args.verification.resolve()
    report_path, manifest_path = directory / "verification.json", directory / "manifest.json"
    report_bytes, manifest_bytes = report_path.read_bytes(), manifest_path.read_bytes()
    report, manifest = json.loads(report_bytes), json.loads(manifest_bytes)
    assert report["status"] == "complete"
    assert sha(manifest_bytes) == report["final_manifest_sha256"]
    assert sha((directory / "input-manifest.json").read_bytes()) == report["input_manifest_sha256"]
    patch = (directory / "mathlib.patch").read_bytes()
    assert sha(patch) == report["patch_sha256"] == manifest["source_verification"]["patch_sha256"]
    specifications = {row["path"]: row for row in manifest["files"]}
    selected = defaultdict(list)
    for candidate in manifest["candidates"]:
        if candidate["status"] == "replace":
            selected[candidate["path"]].append(candidate)
    originals, replacements, files, spans = {}, {}, [], []
    original_total = replacement_total = imports_total = artifacts_total = 0
    for row in report["files"]:
        path = row["path"]
        assert row["status"] == "verified" and not row["style_diagnostics"]
        before = (ROOT / ".lake/packages/mathlib" / path).read_bytes()
        after = (directory / "sources" / path).read_bytes()
        assert sha(before) == row["original_source_sha256"] == specifications[path]["source_sha256"]
        assert sha(after) == row["replacement_source_sha256"]
        assert not specifications[path].get("helpers")
        assert specifications[path].get("imports") == ["NormArith"]
        for name, digest in row["artifact_sha256"].items():
            assert sha(Path(name).read_bytes()) == digest, name
            artifacts_total += 1
        lines = before.decode().splitlines(keepends=True)
        whole_line_code = COUNTER.code_lines(before.decode())
        proof_only = list(lines)
        before_lines = after_lines = 0
        ordered = sorted(selected[path], key=lambda candidate: candidate["start_line"])
        assert all(a["end_line"] < b["start_line"] for a, b in zip(ordered, ordered[1:]))
        for candidate in reversed(ordered):
            first, last = candidate["start_line"], candidate["end_line"]
            original = "".join(lines[first - 1:last])
            replacement = candidate["replacement"]
            assert sha(original.encode()) == candidate["original_sha256"]
            left = sum(len(line.encode()) for line in lines[:first - 1])
            right = sum(len(line.encode()) for line in lines[:last])
            start, end = candidate["source_start_byte"], candidate["source_end_byte"]
            assert left <= start < end <= right
            assert (before[left:start] + candidate["proof_replacement"].encode() + before[end:right]).decode() == replacement
            assert candidate["manual_review"] is True
            assert all(len(line) <= 100 for line in replacement.splitlines())
            count_before = sum(whole_line_code[first - 1:last])
            count_after = sum(COUNTER.code_lines(replacement))
            before_lines += count_before
            after_lines += count_after
            proof_only[first - 1:last] = replacement.splitlines(keepends=True)
            spans.append({"id": candidate["id"], "path": path, "start_line": first, "end_line": last,
                          "original_sha256": sha(original.encode()), "original": original,
                          "replacement": replacement, "original_code_lines": count_before,
                          "replacement_code_lines_including_preparation": count_after,
                          "saved_code_lines": count_before - count_after})
        assert after.count(b"import NormArith\n") == 1
        assert after.replace(b"import NormArith\n", b"", 1) == "".join(proof_only).encode()
        file_before, file_after = sum(whole_line_code), sum(COUNTER.code_lines(after.decode()))
        assert file_before - file_after == before_lines - after_lines - 1
        original_total += before_lines
        replacement_total += after_lines
        imports_total += 1
        files.append({"path": path, "original_sha256": sha(before), "replacement_sha256": sha(after),
                      "original_file_code_lines": file_before, "replacement_file_code_lines": file_after,
                      "net_file_code_lines_saved": file_before - file_after,
                      "original_proof_code_lines": before_lines,
                      "replacement_proof_code_lines_including_preparation": after_lines,
                      "added_import_code_lines": 1})
        originals[path], replacements[path] = before, after
    assert set(originals) == set(selected)
    assert COUNTER.apply_patch_independently(patch.decode(), originals) == replacements
    account = report["accounting"]
    assert (original_total, replacement_total, imports_total) == (
        account["original_proof_lines"], account["replacement_proof_lines"], account["added_import_lines"])
    assert original_total - replacement_total - imports_total == account["net_lines_saved_including_imports"]
    result = {
        "schema_version": 1, "status": "independently_verified_composed_patch",
        "evidence_stage": "intermediate_source_verified_patch_discovery_ongoing_not_a_timing_result",
        "created_at_utc": datetime.now(timezone.utc).isoformat(), "python": sys.version,
        "verification_directory": str(directory), "helper_sha256": sha(Path(__file__).read_bytes()),
        "independent_lexer_sha256": sha(LEXER_PATH.read_bytes()),
        "verification_report_sha256": sha(report_bytes), "verified_manifest_sha256": sha(manifest_bytes),
        "patch_sha256": sha(patch), "selected_replacements": len(spans), "affected_files": len(files),
        "original_proof_code_lines": original_total,
        "replacement_proof_code_lines_including_preparation": replacement_total,
        "proof_code_lines_saved": original_total - replacement_total, "added_helper_code_lines": 0,
        "added_import_code_lines": imports_total,
        "net_file_code_lines_saved": sum(row["net_file_code_lines_saved"] for row in files),
        "maximum_replacement_line_characters": max(len(line) for row in spans for line in row["replacement"].splitlines()),
        "fresh_compilation_artifacts_rehashed": artifacts_total,
        "checks": ["independent comment/string lexer", "exact original proof-span hashes",
                   "literal prepared-proof reconstruction", "whole-file accounting",
                   "independent unified-diff application", "source and fresh compilation output hashes"],
        "files": files, "proof_spans": spans,
    }
    args.output.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({key: result[key] for key in ["status", "selected_replacements", "affected_files",
          "original_proof_code_lines", "replacement_proof_code_lines_including_preparation",
          "added_import_code_lines", "net_file_code_lines_saved", "fresh_compilation_artifacts_rehashed"]}, indent=2))


if __name__ == "__main__":
    main()
