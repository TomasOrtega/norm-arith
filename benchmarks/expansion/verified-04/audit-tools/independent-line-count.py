#!/usr/bin/env python3
"""Recount literal Lean source changes without the benchmark's counting code."""

import argparse
from collections import defaultdict
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import sys


def sha(data):
    return hashlib.sha256(data).hexdigest()


def code_lines(text):
    present = [False] * (text.count("\n") + 1)
    line, index, depth, mode, raw_end = 0, 0, 0, "code", ""
    while index < len(text):
        char = text[index]
        if char == "\n":
            line += 1
            if mode == "line":
                mode = "code"
            index += 1
            continue
        if mode == "line":
            index += 1
            continue
        if depth:
            if text.startswith("/-", index):
                depth += 1
                index += 2
            elif text.startswith("-/", index):
                depth -= 1
                index += 2
            else:
                index += 1
            continue
        if mode == "raw":
            if text.startswith(raw_end, index):
                present[line] = True
                index += len(raw_end)
                mode = "code"
            else:
                present[line] |= not char.isspace()
                index += 1
            continue
        if mode == "string":
            present[line] |= not char.isspace()
            if char == "\\" and index + 1 < len(text) and text[index + 1] != "\n":
                index += 2
            else:
                if char == '"':
                    mode = "code"
                index += 1
            continue
        if mode == "identifier":
            present[line] |= not char.isspace()
            if char == "»":
                mode = "code"
            index += 1
            continue
        if text.startswith("--", index):
            mode = "line"
            index += 2
        elif text.startswith("/-", index):
            depth = 1
            index += 2
        elif char == "«":
            present[line] = True
            mode = "identifier"
            index += 1
        else:
            raw = re.match(r'r(#+)?"', text[index:]) if char == "r" else None
            character = re.match(r"'(?:[^'\\\n]|\\[^\n])'", text[index:]) if char == "'" else None
            if raw:
                present[line] = True
                raw_end = '"' + (raw.group(1) or "")
                index += len(raw.group())
                mode = "raw"
            elif character:
                present[line] = True
                index += len(character.group())
            elif char == '"':
                present[line] = True
                mode = "string"
                index += 1
            else:
                present[line] |= not char.isspace()
                index += 1
    if depth or mode not in {"code", "line"}:
        raise ValueError(f"unterminated lexical construct: {mode}, block depth {depth}")
    return present


def lexical_checks():
    cases = [
        ('/- comment\n /- nested -/ -/\nexample := "-- /- literal" -- trailing\n', 1),
        ('def a := r#"/- raw --"#\n/- hidden\n hidden -/\ndef b := \'"\'\n', 2),
        ('def «-- /-» := 1\n-- comment only\n', 1),
        ('def x := "quoted \\" -- literal"\n', 1),
    ]
    for text, count in cases:
        assert sum(code_lines(text)) == count, repr(text)


def apply_patch_independently(patch, originals):
    lines = patch.splitlines(keepends=True)
    index, result = 0, {}
    while index < len(lines):
        assert lines[index].startswith("--- a/")
        name = lines[index][6:].rstrip("\n")
        index += 1
        assert lines[index] == f"+++ b/{name}\n"
        index += 1
        before = originals[name].decode().splitlines(keepends=True)
        after, cursor = [], 0
        while index < len(lines) and lines[index].startswith("@@ "):
            header = re.fullmatch(r"@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@.*\n", lines[index])
            assert header, lines[index]
            start, old_count, new_start, new_count = map(int, [header[1], header[2] or 1,
                                                             header[3], header[4] or 1])
            after.extend(before[cursor:start - 1])
            cursor = start - 1
            assert len(after) == new_start - 1
            index += 1
            removed, added = 0, 0
            while index < len(lines) and not lines[index].startswith(("@@ ", "--- a/")):
                token, content = lines[index][0], lines[index][1:]
                assert token in " +-", lines[index]
                if token in " -":
                    assert before[cursor] == content
                    cursor += 1
                    removed += 1
                if token in " +":
                    after.append(content)
                    added += 1
                index += 1
            assert (removed, added) == (old_count, new_count)
        after.extend(before[cursor:])
        assert name not in result
        result[name] = "".join(after).encode()
    return result


def audit(project):
    lexical_checks()
    directory = project / ".lake/source-verification-style-v4"
    report_path = directory / "verification.json"
    report = json.loads(report_path.read_bytes())
    manifest_path = directory / "manifest.json"
    manifest = json.loads(manifest_path.read_bytes())
    frozen_path = project / ".lake/frozen-style-v4/manifest.json"
    frozen = json.loads(frozen_path.read_bytes())
    selected_path = project / ".lake/selection-style-v4/manifest.json"
    patch_path = directory / "mathlib.patch"
    patch = patch_path.read_bytes()
    assert report["status"] == "complete"
    assert sha(patch) == report["patch_sha256"] == frozen["source_verification"]["patch_sha256"]
    assert sha(manifest_path.read_bytes()) == report["final_manifest_sha256"]
    assert sha(selected_path.read_bytes()) == report["input_manifest_sha256"]
    assert frozen["candidates"] == manifest["candidates"] and frozen["files"] == manifest["files"]
    candidates = defaultdict(list)
    for row in manifest["candidates"]:
        if row["status"] == "replace":
            candidates[row["path"]].append(row)
    originals, files, proof_rows = {}, [], []
    for entry in report["files"]:
        name = entry["path"]
        before = (project / ".lake/packages/mathlib" / name).read_bytes()
        after = (directory / "sources" / name).read_bytes()
        originals[name] = before
        assert sha(before) == entry["original_source_sha256"]
        assert sha(after) == entry["replacement_source_sha256"]
        specification = next(row for row in manifest["files"] if row["path"] == name)
        assert sha(before) == specification["source_sha256"]
        assert specification["helpers"] == [] and specification["imports"] == ["NormArith"]
        source_lines = before.decode().splitlines(keepends=True)
        source_presence = code_lines(before.decode())
        expected, previous = source_lines[:], 0
        for row in sorted(candidates[name], key=lambda row: row["start_line"]):
            first, last = row["start_line"], row["end_line"]
            assert first > previous
            previous = last
            text = "".join(source_lines[first - 1:last])
            assert sha(text.encode()) == row["original_sha256"]
            old, new = sum(source_presence[first - 1:last]), sum(code_lines(row["replacement"]))
            assert old == row["original_proof_lines"] and new == row["replacement_proof_lines"]
            assert old - new == row["proof_lines_saved"]
            proof_rows.append({"id": row["id"], "path": name, "start_line": first, "end_line": last,
                               "original_sha256": sha(text.encode()), "original": text,
                               "replacement": row["replacement"], "before_code_lines": old,
                               "after_code_lines": new, "saved_code_lines": old - new})
        for row in sorted(candidates[name], key=lambda row: row["start_line"], reverse=True):
            expected[row["start_line"] - 1:row["end_line"]] = row["replacement"].splitlines(keepends=True)
        patched = after.decode().splitlines(keepends=True)
        import_positions = [i for i, line in enumerate(patched) if line == "import NormArith\n"]
        assert len(import_positions) == 1 and import_positions[0] < 20
        del patched[import_positions[0]]
        assert "".join(patched) == "".join(expected), name
        files.append({"path": name, "original_sha256": sha(before), "patched_sha256": sha(after),
                      "before_file_code_lines": sum(source_presence),
                      "after_file_code_lines": sum(code_lines(after.decode())), "added_import_code_lines": 1})
        for artifact, expected_hash in entry["artifact_sha256"].items():
            assert sha(Path(artifact).read_bytes()) == expected_hash
    applied = apply_patch_independently(patch.decode(), originals)
    assert set(applied) == set(candidates)
    for name, data in applied.items():
        assert data == (directory / "sources" / name).read_bytes()
    old = sum(row["before_code_lines"] for row in proof_rows)
    new = sum(row["after_code_lines"] for row in proof_rows)
    imports = sum(row["added_import_code_lines"] for row in files)
    net = sum(row["before_file_code_lines"] - row["after_file_code_lines"] for row in files)
    assert net == old - new - imports
    assert (len(proof_rows), len(files), old, new, imports, net) == (16, 10, 67, 16, 10, 41)
    return {"schema_version": 1, "status": "independently_verified", "created_at_utc": datetime.now(timezone.utc).isoformat(),
            "method": "Independent nested-comment/string lexer, literal proof-line spans, whole-file code counts, independent unified-diff application; no project counting imports",
            "python": sys.version, "helper_sha256": sha(Path(__file__).read_bytes()),
            "input_sha256": {str(path.relative_to(project)): sha(path.read_bytes()) for path in
                             [selected_path, manifest_path, frozen_path, report_path, patch_path]},
            "patch_sha256": sha(patch), "replacements": len(proof_rows), "affected_files": len(files),
            "original_proof_code_lines": old, "replacement_proof_code_lines": new,
            "proof_code_lines_saved": old - new, "added_helper_code_lines": 0,
            "added_import_code_lines": imports, "net_file_code_lines_saved": net,
            "maximum_replacement_line_characters": max(len(line) for row in proof_rows for line in row["replacement"].splitlines()),
            "compiled_artifacts_hash_checked": sum(len(entry["artifact_sha256"]) for entry in report["files"]),
            "files": files, "proof_spans": proof_rows}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--output", type=Path, default=Path("artifacts/independent-line-count.json"))
    arguments = parser.parse_args()
    result = audit(arguments.project.resolve())
    output = arguments.output if arguments.output.is_absolute() else arguments.project / arguments.output
    output.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({key: result[key] for key in ["status", "replacements", "affected_files", "original_proof_code_lines",
                                                 "replacement_proof_code_lines", "added_import_code_lines", "net_file_code_lines_saved"]}))
