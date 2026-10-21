#!/usr/bin/env python3
"""Preserve a finished targeted discovery without claiming full coverage."""

import argparse
from datetime import datetime, timezone
import gzip
import hashlib
import json
from pathlib import Path
import shutil
import sys
import tarfile
import tempfile


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
import archive_census as archive
import census


def require(condition, message):
    if not condition:
        raise ValueError(message)


def save(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def jsonl(path, rows):
    path.write_text("".join(census.canonical_json(row) + "\n" for row in rows))


def validate(root):
    manifest = archive.read_json(root / "manifest.json")
    summary = archive.read_json(root / "summary.json")
    integrity = archive.read_json(root / "integrity.json")
    universe = {item["path"]: item["sha256"] for item in manifest["files"]}
    selected = manifest["selected_files"]
    require(manifest["scope"] == "calibration", "expected explicitly targeted/calibration scope")
    require(selected == sorted(set(selected)) and 0 < len(selected) < len(universe),
            "targeted selection must be a strict, unique source-universe subset")
    require(all(path in universe for path in selected), "selected file outside source universe")
    protocol = {field: manifest[field] for field in (
        "config", "implementation_sha256", "mathlib_revision", "environment_sha256",
        "selected_files", "extractor_binary_sha256")}
    require(census.digest(census.canonical_json(protocol)) == manifest["protocol_hash"],
            "protocol hash mismatch")
    require(integrity == {"protocol_hash": manifest["protocol_hash"], "status": "valid"},
            "run integrity invalid or pending")
    require(summary["frozen_inputs_verified"] and summary["processed_files"] == len(selected)
            and summary["unprocessed_files"] == 0 and not summary["full_universe_processed"]
            and not summary["full_universe_completed"], "targeted run not terminal")
    inventory, signatures = {}, {}
    for name in archive.regular_files(root):
        path = root / name
        signatures[name] = archive.signature(path)
        inventory[name] = {"sha256": archive.file_hash(path), "bytes": signatures[name][0]}
        require(archive.signature(path) == signatures[name], f"changed while hashing: {name}")
    for name, expected in {**manifest["implementation_sha256"],
                           **manifest["environment_sha256"]}.items():
        archive.check_hash(root, "frozen-implementation/" + archive.relative_name(name),
                           expected, inventory)
    origin = archive.read_json(root / "setup-cache-origin.json")
    for name, expected in origin["copied_files_sha256"].items():
        require(name.startswith("setups/"), "invalid setup-origin path")
        archive.check_hash(root, name, expected, inventory)
    outcomes, attempts, proposals = [], [], []
    attributed = set()
    for name in selected:
        module = name[:-5].replace("/", ".")
        result_name = f"files/{module}/result.json"
        result = archive.read_json(root / result_name)
        archive.verify_result(root, result, (name, universe[name]), inventory)
        directory = result.get("directory")
        require(directory and archive.read_json(root / directory / "result.json") == result,
                f"latest attempt mismatch: {name}")
        outcomes.append({"result_file": result_name, "result": result})
        for path in sorted((root / "files" / module).glob("attempt-*/result.json")):
            attempt_name = str(path.relative_to(root))
            attempt = archive.read_json(path)
            current = attempt == result and str(path.parent.relative_to(root)) == directory
            archive.verify_result(root, attempt, (name, universe[name]), inventory)
            require(attempt["directory"] == str(path.parent.relative_to(root)),
                    f"attempt directory mismatch: {attempt_name}")
            attempts.append({"result_file": attempt_name, "current_attempt": current, "result": attempt})
            records = archive.proposal_records(root, attempt, attempt_name, current, inventory)
            proposals.extend(records)
            if attempt.get("proposal_file"):
                attributed.add(attempt["proposal_file"])
            if not attempt["complete"]:
                continue
            event_name = str((path.parent / "events.jsonl").relative_to(root))
            require(event_name in attempt["evidence_sha256"], "unhashed complete events")
            events, error = census.parse_events(root / event_name)
            extraction = attempt["extraction"]
            checked = census.validate_events(events, extraction["returncode"], error,
                                              extraction.get("timed_out", False))
            require(all(attempt.get(key) == value for key, value in checked.items()),
                    f"event summary mismatch: {attempt_name}")
            successes = {event["key"]: event for event in events
                         if event.get("type") == "attempt" and event.get("status") == "success"}
            require(sorted(row["proposal"]["key"] for row in records) == sorted(successes),
                    f"proposal/event key mismatch: {attempt_name}")
            for row in records:
                proposal = row["proposal"]
                require(all(proposal.get(key) == value for key, value in successes[proposal["key"]].items()),
                        f"proposal/event content mismatch: {attempt_name}")
    for name in inventory:
        if name.endswith("/proposals.jsonl") and name not in attributed:
            require(not (root / name).read_text().strip(), f"unattributed proposal ledger: {name}")
    with tempfile.TemporaryDirectory(prefix="norm-arith-targeted-summary-") as temporary:
        temporary = Path(temporary)
        save(temporary / "integrity.json", integrity)
        recomputed = census.summarize(manifest, [row["result"] for row in outcomes], temporary)
    require(summary == recomputed, "summary differs from complete per-file ledger")
    require(sum(row["current_attempt"] for row in proposals) == summary["successful_proposals"],
            "latest proposal total mismatch")
    return {"manifest": manifest, "summary": summary, "inventory": inventory, "signatures": signatures,
            "outcomes": outcomes, "attempts": attempts, "proposals": proposals}


def verify_tar(path, expected):
    index = {}
    with tarfile.open(path, "r:gz") as handle:
        for member in handle:
            require(member.isfile() and member.name.startswith("run/"), "unexpected tar member")
            name = member.name[4:]
            require(name in expected and name not in index, f"unexpected or duplicate member: {name}")
            value = hashlib.sha256()
            with handle.extractfile(member) as content:
                while block := content.read(1024 * 1024):
                    value.update(block)
            require(member.size == expected[name]["bytes"] and value.hexdigest() == expected[name]["sha256"],
                    f"archive byte mismatch: {name}")
            index[name] = {**expected[name], "tar_member": member.name,
                           "uncompressed_tar_data_offset": member.offset_data}
    require(set(index) == set(expected), "raw archive missing files")
    return index


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    root, output = args.source.resolve(), args.output.absolute()
    require(root.is_dir() and not output.exists() and not output.resolve().is_relative_to(root),
            "output must be a new directory outside the source run")
    output.parent.mkdir(parents=True, exist_ok=True)
    with archive.finished_run_lock(root), tempfile.TemporaryDirectory(
            prefix=".targeted-archive-", dir=output.parent) as temporary:
        stage = Path(temporary)
        data = validate(root)
        print("Validated targeted ledgers; compressing raw records", flush=True)
        archive.make_tar(stage / "raw.tar.gz", root, sorted(data["inventory"]), "run", data["inventory"])
        index = verify_tar(stage / "raw.tar.gz", data["inventory"])
        save(stage / "raw-index.json", {"schema_version": 1, "files": index})
        for name in ["manifest.json", "summary.json", "integrity.json", "setup-cache-origin.json"]:
            archive.copy_verified(root, name, stage / name, data["inventory"])
        jsonl(stage / "file-outcomes.jsonl", data["outcomes"])
        jsonl(stage / "attempt-outcomes.jsonl", data["attempts"])
        jsonl(stage / "proposals.jsonl", data["proposals"])
        tools = stage / "archive-tools"
        tools.mkdir()
        for source in [Path(__file__), Path(archive.__file__), Path(census.__file__)]:
            shutil.copyfile(source, tools / source.name)
        summary = data["summary"]
        receipt = {"schema_version": 1, "created_at_utc": datetime.now(timezone.utc).isoformat(),
                   "status": "validated_targeted_discovery_archive", "scope": "targeted_followup",
                   "recorded_scope": data["manifest"]["scope"], "source": str(root),
                   "protocol_hash": data["manifest"]["protocol_hash"],
                   "mathlib_revision": data["manifest"]["mathlib_revision"],
                   "full_universe_coverage_claim": False,
                   "coverage": "Every selected file has an outcome; ten incomplete files remain failures. This targeted follow-up does not establish full Mathlib coverage or a compiled patch.",
                   **{key: summary[key] for key in ["universe_files", "selected_files", "processed_files",
                       "completed_files", "failed_files", "unprocessed_files", "successful_proposals",
                       "frozen_inputs_verified", "file_status_counts", "evidence_stage"]},
                   "raw_files": len(index), "raw_bytes": sum(row["bytes"] for row in index.values()),
                   "archived_attempts": len(data["attempts"]), "archived_proposal_records": len(data["proposals"]),
                   "raw_archive_sha256": archive.file_hash(stage / "raw.tar.gz"),
                   "raw_archive_bytes": (stage / "raw.tar.gz").stat().st_size,
                   "raw_index_sha256": archive.file_hash(stage / "raw-index.json"),
                   "archive_reopened_and_every_member_rehashed": True}
        save(stage / "archive.json", receipt)
        save(stage / "inventory.json", {name: {"bytes": (stage / name).stat().st_size,
             "sha256": archive.file_hash(stage / name)} for name in archive.regular_files(stage)})
        (stage / "raw.tar.gz.sha256").write_text(receipt["raw_archive_sha256"] + "  raw.tar.gz\n")
        archive.verify_unchanged(root, data)
        require(not output.exists(), "output appeared during archival")
        stage.rename(output)
        print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
