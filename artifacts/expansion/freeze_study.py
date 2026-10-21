#!/usr/bin/env python3
"""Validate a compiled expanded patch and change only its selection status."""

import argparse
from datetime import datetime, timezone
import difflib
import importlib.util
import json
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("freeze_benchmark", ROOT / "scripts/benchmark.py")
BENCHMARK = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BENCHMARK)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def validate(project, verification, audit_path):
    project, verification = Path(project).resolve(), Path(verification).resolve()
    report_bytes = (verification / "verification.json").read_bytes()
    report = json.loads(report_bytes)
    manifest_bytes = (verification / "manifest.json").read_bytes()
    manifest = json.loads(manifest_bytes)
    audit = json.loads(Path(audit_path).read_bytes())
    require(report.get("status") == "complete" and
            report.get("evidence_stage") == "combined_source_patch_kernel_checked_with_fresh_outputs",
            "source verification is not complete")
    require(manifest.get("selection_status") == "source-verified-trial" and
            BENCHMARK.sha256(manifest_bytes) == report["final_manifest_sha256"],
            "source-verified manifest differs from its receipt")
    require(audit.get("status") == "independently_verified_composed_patch" and
            audit.get("verification_report_sha256") == BENCHMARK.sha256(report_bytes) and
            audit.get("verified_manifest_sha256") == BENCHMARK.sha256(manifest_bytes),
            "independent audit differs from source verification")
    accounting = report["accounting"]
    count_pairs = (
        ("original_proof_code_lines", "original_proof_lines"),
        ("replacement_proof_code_lines_including_preparation", "replacement_proof_lines"),
        ("added_import_code_lines", "added_import_lines"),
        ("added_helper_code_lines", "added_helper_lines"),
        ("net_file_code_lines_saved", "net_lines_saved_including_imports"),
        ("selected_replacements", "proposed_replacements"),
    )
    require(all(audit.get(left) == accounting[right] for left, right in count_pairs) and
            audit.get("affected_files") == len(report["files"]),
            "independent audit count differs from source verification")
    BENCHMARK.verify_frozen_inputs(report["input_sha256"])
    current_sources = {str(path.relative_to(project)): BENCHMARK.sha256(path.read_bytes())
                       for path in BENCHMARK.project_lean_sources(project)}
    require(current_sources == report["project_lean_sources"], "project Lean source inventory changed")
    mathlib = project / ".lake/packages/mathlib"
    revision = BENCHMARK.capture(["git", "rev-parse", "HEAD"], mathlib)
    require(revision == manifest["mathlib_revision"] == report["mathlib_revision"], "Mathlib revision differs")
    require(not BENCHMARK.capture(["git", "status", "--porcelain", "--untracked-files=no"], mathlib),
            "Mathlib tracked sources changed")
    prepared, accounting = BENCHMARK.prepare_sources(manifest, mathlib)
    patch = "".join(line for source in prepared for line in difflib.unified_diff(
        source["original"].splitlines(keepends=True), source["replacement"].splitlines(keepends=True),
        fromfile="a/" + source["path"], tofile="b/" + source["path"])).encode()
    require(patch == (verification / "mathlib.patch").read_bytes() and
            BENCHMARK.sha256(patch) == report["patch_sha256"] == audit["patch_sha256"],
            "rendered patch differs from source verification or audit")
    require(accounting == report["accounting"] and accounting["net_lines_saved_including_imports"] > 232,
            "accounting differs or the new patch does not exceed 232 net lines")
    require(len(report["files"]) == len(prepared) and
            {row["path"] for row in report["files"]} == {source["path"] for source in prepared},
            "source verification file set differs")
    artifacts = 0
    for row in report["files"]:
        require(row.get("status") == "verified" and row["process"]["returncode"] == 0 and
                not row["process"].get("timed_out") and not row.get("style_diagnostics"),
                "failed source verification file")
        BENCHMARK.verify_frozen_inputs(row["artifact_sha256"])
        artifacts += len(row["artifact_sha256"])
    require(artifacts == audit["fresh_compilation_artifacts_rehashed"], "artifact count differs from audit")
    return manifest, patch, {
        "schema_version": 1, "status": "verified_and_frozen",
        "frozen_at_utc": datetime.now(timezone.utc).isoformat(), "only_changed_field": "selection_status",
        "verified_manifest_sha256": BENCHMARK.sha256(manifest_bytes),
        "verification_report_sha256": BENCHMARK.sha256(report_bytes),
        "independent_audit_sha256": BENCHMARK.sha256(Path(audit_path).read_bytes()),
        "patch_sha256": BENCHMARK.sha256(patch), "files": len(prepared),
        "compiled_artifacts": artifacts, "input_count": len(report["input_sha256"]),
        "accounting": {key: value for key, value in accounting.items() if key != "candidates"},
        "implementation_costs": BENCHMARK.implementation_line_costs(project),
        "timing_status": "not_started_waiting_for_owner_QUIET_START",
        "benchmark_sha256": BENCHMARK.sha256(Path(BENCHMARK.__file__).read_bytes()),
        "freeze_helper_sha256": BENCHMARK.sha256(Path(__file__).read_bytes()),
        "supplemental_metadata_sha256": {
            relative: BENCHMARK.sha256((project / relative).read_bytes())
            for relative in (
                "artifacts/expansion/machine-profile-before-study.json",
                "artifacts/expansion/expanded-study-protocol.md",
                "artifacts/expansion/calibration_review.py",
                "artifacts/expansion/verify_expanded_statistics.py",
            )
        },
    }


def freeze(project, verification, audit_path, output):
    manifest, patch, receipt = validate(project, verification, audit_path)
    output = Path(output)
    require(not output.exists() and not output.is_symlink(), "freeze output must be new")
    frozen = dict(manifest, selection_status="frozen")
    output.mkdir(parents=True)
    data = (json.dumps(frozen, indent=2, ensure_ascii=False) + "\n").encode()
    (output / "manifest.json").write_bytes(data)
    (output / "mathlib.patch").write_bytes(patch)
    receipt["frozen_manifest_sha256"] = BENCHMARK.sha256(data)
    (output / "freeze.json").write_text(json.dumps(receipt, indent=2) + "\n")
    return receipt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("verification", type=Path)
    parser.add_argument("audit", type=Path)
    parser.add_argument("--project", type=Path, default=ROOT)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    if args.check_only == (args.output is not None):
        parser.error("choose exactly one of --check-only and --output")
    try:
        if args.check_only:
            _, _, receipt = validate(args.project, args.verification, args.audit)
            receipt.update(status="nonmeasurement_checks_passed_not_frozen", frozen_at_utc=None)
        else:
            receipt = freeze(args.project, args.verification, args.audit, args.output)
        print(json.dumps(receipt, indent=2))
        return 0
    except (BENCHMARK.BenchmarkError, OSError, ValueError, KeyError, TypeError) as error:
        print("study freeze failed: " + str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
