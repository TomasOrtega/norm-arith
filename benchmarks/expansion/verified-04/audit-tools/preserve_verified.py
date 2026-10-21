#!/usr/bin/env python3
"""Preserve an independently recounted expanded patch and its source evidence."""

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import sys

import archive_targeted


ROOT = Path(__file__).resolve().parents[2]
archive = archive_targeted.archive


def sha(path):
    return archive.file_hash(path)


def save(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("verification", type=Path)
    parser.add_argument("selection", type=Path)
    parser.add_argument("audit", type=Path)
    parser.add_argument("--implementation-costs", type=Path,
                        default=ROOT / "artifacts/expansion/implementation-costs-v4.json")
    parser.add_argument("--stage", choices=["intermediate", "final"], default="final")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    run, selection, output = args.verification.resolve(), args.selection.resolve(), args.output.resolve()
    report = json.loads((run / "verification.json").read_text())
    audit = json.loads(args.audit.read_text())
    assert report["status"] == "complete"
    assert audit["verification_report_sha256"] == sha(run / "verification.json")
    assert audit["patch_sha256"] == report["patch_sha256"]
    assert not output.exists()
    output.mkdir(parents=True)
    copied = {}

    def copy(source, relative, expected=None):
        source = Path(source)
        expected = expected or sha(source)
        assert sha(source) == expected, source
        target = output / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        if target.exists():
            assert sha(target) == expected, target
        else:
            shutil.copyfile(source, target)
        assert sha(target) == expected, target
        copied[str(source)] = {"snapshot": str(relative), "sha256": expected}

    for source, target in [("manifest.json", "manifest.json"), ("input-manifest.json", "input-manifest.json"),
                           ("mathlib.patch", "mathlib.patch"), ("verification.json", "verification-receipt.json")]:
        copy(run / source, Path(target))
    copy(args.audit, Path("independent-audit.json"))
    copy(selection / "summary.json", Path("selection-summary.json"))
    copy(selection / "selection.jsonl", Path("selection.jsonl"))
    manifest = json.loads((run / "input-manifest.json").read_text())
    for item in manifest["input_manifests"]:
        copy(selection / item["snapshot"], Path(item["snapshot"]), item["sha256"])
    for source, expected in report["project_lean_sources"].items():
        copy(ROOT / source, Path("frozen-project") / source, expected)
    for source in ["lean-toolchain", "lakefile.toml", "lake-manifest.json", "scripts/verify_selection.py",
                   "scripts/benchmark.py", "scripts/census.py", "scripts/select_census.py"]:
        copy(ROOT / source, Path("frozen-project") / source, report["input_sha256"][str(ROOT / source)])
    copy(ROOT / "scripts/select_expansion.py", Path("frozen-project/scripts/select_expansion.py"))
    for row in report["files"]:
        source = row["path"]
        copy(ROOT / ".lake/packages/mathlib" / source, Path("mathlib-original") / source,
             row["original_source_sha256"])
        copy(run / "sources" / source, Path("mathlib-patched") / source,
             row["replacement_source_sha256"])
    body_records = {}
    for item in report["body_census_evidence"]:
        census_root = Path(item["census"])
        prefix = Path("body-census") / census_root.name
        event = Path(item["events_path"])
        copy(event, prefix / event.relative_to(census_root), item["events_sha256"])
        result_path = census_root / "files" / item["path"][:-5].replace("/", ".") / "result.json"
        copy(result_path, prefix / result_path.relative_to(census_root), item["result_sha256"])
        copy(census_root / "manifest.json", prefix / "manifest.json", item["manifest_sha256"])
        body_records[item["candidate_id"]] = item
    save(output / "body-evidence.json", body_records)
    copy(args.implementation_costs, Path("implementation-costs.json"))
    for source in [Path(__file__), ROOT / "artifacts/expansion/recount_combined.py",
                   ROOT / "artifacts/independent-line-count.py", ROOT / "artifacts/expansion/archive_targeted.py",
                   ROOT / "scripts/archive_census.py"]:
        copy(source, Path("audit-tools") / source.name)
    names = archive.regular_files(run)
    signatures = {name: archive.signature(run / name) for name in names}
    inventory = {name: {"sha256": sha(run / name), "bytes": (run / name).stat().st_size} for name in names}
    archive.make_tar(output / "raw-verification.tar.gz", run, names, "run", inventory)
    tar_index = archive_targeted.verify_tar(output / "raw-verification.tar.gz", inventory)
    archive.verify_unchanged(run, {"inventory": inventory, "signatures": signatures})
    save(output / "raw-verification-index.json", {"schema_version": 1, "files": tar_index})
    save(output / "evidence-map.json", copied)
    receipt = {"schema_version": 1, "status": "independently_verified_expanded_patch",
               "evidence_stage": args.stage + "_source_verified_expanded_patch_untimed",
               "independent_audit_stage_override": (
                   "The preserved generic audit labels discovery ongoing; this final receipt supersedes that stage label after the targeted run terminated. Its numerical and byte checks are unchanged."
                   if args.stage == "final" else "No override: another targeted discovery pass is still running."),
               "discovery_scope": "targeted_followup_885_selected_875_complete_10_incomplete_not_full_coverage",
               "timing_status": "untimed_expansion_preserved_baseline_speed_not_transferable",
               "patch_sha256": report["patch_sha256"],
               "selected_replacements": audit["selected_replacements"], "affected_files": audit["affected_files"],
               "net_code_lines_saved": audit["net_file_code_lines_saved"],
               "fresh_artifacts_rehashed": audit["fresh_compilation_artifacts_rehashed"],
               "raw_verification_archive_sha256": sha(output / "raw-verification.tar.gz"),
               "raw_verification_archive_bytes": (output / "raw-verification.tar.gz").stat().st_size,
               "raw_verification_members": len(tar_index),
               "every_raw_archive_member_reopened_and_rehashed": True,
               "targeted_discovery_archive": "artifacts/expansion/discovery-v3-archive/archive.json"}
    save(output / "milestone.json", receipt)
    save(output / "inventory.json", {name: {"sha256": sha(output / name), "bytes": (output / name).stat().st_size}
                                    for name in archive.regular_files(output)})
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
