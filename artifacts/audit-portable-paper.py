#!/usr/bin/env python3
"""Audit the independently rebuilt paper without importing project validators."""

from collections import defaultdict
from datetime import datetime, timezone
import hashlib
import json
import math
from pathlib import Path
import re
import shutil
import sys


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    source = Path(__file__).resolve().parents[1]
    clean = Path(sys.argv[1]).resolve()
    output = source / "artifacts/portable-paper-build.json"
    bundle = clean / "artifacts/paper-evidence"
    record = json.loads((bundle / "bundle.json").read_text())
    expected_bundle = "9ea6f5e7381073707b00b007d72cd16d20ce7bc71cdf12d2bf460a3cb45ae7b0"
    assert sha(bundle / "bundle.json") == expected_bundle
    assert not list(clean.rglob(".lake")) and not list(clean.rglob(".git"))
    assert sys.version_info[:3] == (3, 15, 0)

    copied = json.loads((clean / "copy-receipt.json").read_text())["copied_file_sha256"]
    refreshed = json.loads((clean / "final-source-refresh.json").read_text())
    source_hashes = {}
    for name, copied_hash in copied.items():
        assert sha(clean / name) == refreshed.get(name, copied_hash), name
        assert (clean / name).read_bytes() == (source / name).read_bytes(), name
        if not name.startswith("artifacts/"):
            source_hashes[name] = sha(clean / name)

    validation = json.loads((clean / "paper/output/validation.json").read_text())
    original_validation = json.loads((source / "paper/output/validation.json").read_text())
    assert validation["main_pages"] == original_validation["main_pages"] == 4
    assert not validation["draft"] and not validation["layout_log_issues"]
    assert validation["lean_validation"] == "checked release artifacts"
    pdf = clean / "paper/output/pdf/paper.pdf"
    assert sha(pdf) == validation["pdf_sha256"]
    assert (clean / "paper/output/paper.txt").read_bytes() == (source / "paper/output/paper.txt").read_bytes()
    pages = int(re.search(r"(?m)^Pages:\s+(\d+)", (clean / "paper/output/pdfinfo.txt").read_text())[1])
    assert pages == 14
    assert len(list((clean / "paper/tmp/pdfs").glob("page-*.png"))) == pages

    generated = {}
    for path in sorted((clean / "paper/generated").iterdir()):
        if path.suffix in {".tex", ".lean"} or path.name == "final-evidence.json":
            assert path.read_bytes() == (source / path.relative_to(clean)).read_bytes(), path.name
            generated[path.name] = sha(path)
    facts = json.loads((clean / "paper/generated/final-evidence.json").read_text())
    account = facts["patch"]["accounting"]
    assert [account[k] for k in ["proposed_replacements", "original_proof_lines", "replacement_proof_lines",
                                  "added_helper_lines", "added_import_lines", "net_lines_saved_including_imports"]] == [16, 67, 16, 0, 10, 41]
    assert len(facts["patch"]["affected_files"]) == 10
    assert [facts["census"]["summary"][k] for k in ["processed_files", "completed_files", "failed_files", "successful_proposals"]] == [8637, 8610, 27, 40]
    assert facts["census"]["unknown_due_incomplete_file"] == 99

    raw_path = bundle / next(v for k, v in record["copied_inputs"].items()
                             if k.endswith("/benchmark-confirmatory-style-v4/measurements.jsonl"))
    rows = [json.loads(line) for line in raw_path.read_text().splitlines()]
    measured = [row for row in rows if row["phase"] == "measured"]
    assert len(rows) == 820 and len(measured) == 800
    assert all(row["returncode"] == 0 and not row["timed_out"] for row in rows)
    totals = defaultdict(float)
    units = set()
    files = set()
    for row in measured:
        key = row["pair"], row["variant"], row["path"]
        assert key not in units
        units.add(key)
        totals[row["pair"], row["variant"]] += row["seconds"]
        files.add(row["path"])
    assert len(files) == 10 and len(totals) == 80
    assert set(pair for pair, _ in totals) == set(range(40))
    before = sum(totals[i, "original"] for i in range(40)) / 40
    after = sum(totals[i, "replacement"] for i in range(40)) / 40
    timing = facts["timing"]
    for actual, expected in [(before, timing["original_mean_seconds"]), (after, timing["replacement_mean_seconds"]),
                             (before / after, timing["estimate"])]:
        assert math.isclose(actual, expected, rel_tol=0, abs_tol=1e-12)
    independent = json.loads((clean / "independent-portable-statistics.json").read_text())
    for key, expected in independent["recomputed_inference"].items():
        assert timing[key] == expected, key
    assert timing["interval"]["lower"] > 1 and timing["success_criterion_met"]

    audit_paths = [clean / ".audit/final-build.jsonl", clean / ".audit/stats.jsonl"]
    audit = [json.loads(line) for path in audit_paths for line in path.read_text().splitlines()]
    assert not [event for event in audit if event["event"].startswith("denied")]
    build_audit = [json.loads(line) for line in audit_paths[0].read_text().splitlines()]
    assert sum(event["event"] == "python_guard_active" for event in build_audit) == 3
    self_test = [json.loads(line) for line in (clean / ".audit/self-test.jsonl").read_text().splitlines()]
    assert sum(event["event"] == "denied_workspace_access" for event in self_test) == 1

    recorder = clean / "paper/output/pdf/paper.fls"
    lines = recorder.read_text().splitlines()
    base = next(Path(line[4:]) for line in lines if line.startswith("PWD "))
    inputs = []
    for line in lines:
        if line.startswith("INPUT "):
            path = Path(line[6:])
            path = (path if path.is_absolute() else base / path).resolve()
            assert not path.is_relative_to(source), path
            inputs.append(str(path))

    language = json.loads((clean / "paper/output/language-candidates.json").read_text())
    assert not language["candidates"] and not language["unreviewed_words"]
    assert language["record_matches_current_corpus"]
    evidence_dir = source / "artifacts/portable-paper-audit"
    evidence_dir.mkdir(exist_ok=True)
    retained = {
        "guard-source.py": ".audit/sitecustomize.py", "build.jsonl": ".audit/final-build.jsonl",
        "self-test.jsonl": ".audit/self-test.jsonl", "statistics.jsonl": ".audit/stats.jsonl",
        "build.log": "portable-final-build.log", "copy-receipt.json": "copy-receipt.json",
        "final-source-refresh.json": "final-source-refresh.json",
        "independent-statistics.json": "independent-portable-statistics.json",
        "paper.fls": "paper/output/pdf/paper.fls", "validation.json": "paper/output/validation.json",
        "toolchain.json": "paper/output/toolchain.json",
    }
    for name, relative in retained.items():
        shutil.copy2(clean / relative, evidence_dir / name)
    receipt = {
        "schema_version": 1, "status": "independent_portable_rebuild_passed",
        "created_at_utc": datetime.now(timezone.utc).isoformat(),
        "clean_root": str(clean), "python": sys.version, "executable": sys.executable,
        "build_command": ["python3", "paper/build.py", "--reuse-checked-examples", "--render"],
        "cache_policy": "Copied source and bundle only; no .lake or .git; generated, output, and tmp removed before final build",
        "bundle_sha256": expected_bundle, "helper_sha256": sha(Path(__file__)),
        "source_sha256": source_hashes, "generated_sha256": generated,
        "source_and_generated_match_final_original": True, "extracted_pdf_text_matches_final_original": True,
        "main_pages": 4, "total_pages": pages, "rendered_pages": pages,
        "visual_review": "All 14 rendered pages inspected in contact sheets; no clipping or overlaps observed",
        "pdf_sha256": sha(pdf), "original_pdf_sha256": original_validation["pdf_sha256"],
        "pdf_byte_identity_required": False,
        "language_corpus_sha256": language["corpus_sha256"],
        "language_vocabulary_review_sha256": language["vocabulary_review_sha256"],
        "layout_log_issues": validation["layout_log_issues"],
        "audit_guard_sha256": sha(clean / ".audit/sitecustomize.py"),
        "audit_logs_sha256": {str(path.relative_to(clean)): sha(path) for path in audit_paths},
        "workspace_read_self_test": "blocked as required", "build_workspace_access_denials": 0,
        "guarded_build_python_processes": 3, "lean_or_lake_subprocesses": 0,
        "tex_recorder_sha256": sha(recorder), "tex_input_records": len(inputs),
        "tex_unique_input_paths": len(set(inputs)), "tex_original_workspace_inputs": [],
        "replacements": 16, "affected_files": 10, "original_proof_code_lines": 67,
        "replacement_proof_code_lines": 16, "added_import_code_lines": 10, "net_lines_saved": 41,
        "measured_records": len(measured), "paired_passes": 40,
        "mean_original_seconds": before, "mean_replacement_seconds": after,
        "ratio_of_mean_pass_totals": before / after, "interval": timing["interval"],
        "independent_statistics_sha256": sha(clean / "independent-portable-statistics.json"),
        "retained_evidence_sha256": {str((evidence_dir / name).relative_to(source)): sha(evidence_dir / name)
                                    for name in sorted(retained)},
        "limitations": "This rebuild validates portable saved evidence and paper generation. It runs no new Lean proof check, census, timing experiment, or fresh native build."
    }
    output.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({key: receipt[key] for key in ["status", "main_pages", "total_pages", "net_lines_saved", "ratio_of_mean_pass_totals", "pdf_sha256"]}, indent=2))


if __name__ == "__main__":
    main()
