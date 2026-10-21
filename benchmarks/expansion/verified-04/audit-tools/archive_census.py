#!/usr/bin/env python3
"""Validate and archive a finished full-universe semantic census."""

import argparse
from contextlib import contextmanager
from datetime import datetime, timezone
import fcntl
import gzip
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import stat
import sys
import tarfile
import tempfile

import census


class ArchiveError(Exception):
    pass


def file_hash(path):
    value = hashlib.sha256()
    with path.open("rb") as handle:
        while chunk := handle.read(1024 * 1024):
            value.update(chunk)
    return value.hexdigest()


def relative_name(value):
    if not isinstance(value, str) or not value or "\\" in value:
        raise ArchiveError(f"invalid relative evidence path: {value!r}")
    path = PurePosixPath(value)
    if path.is_absolute() or str(path) != value or any(part in (".", "..") for part in path.parts):
        raise ArchiveError(f"invalid relative evidence path: {value!r}")
    return value


def read_json(path):
    try:
        value = json.loads(path.read_text())
    except (OSError, ValueError) as error:
        raise ArchiveError(f"cannot read JSON evidence {path}: {error}") from error
    if not isinstance(value, dict):
        raise ArchiveError(f"expected JSON object: {path}")
    return value


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def write_jsonl(path, values):
    with path.open("w") as handle:
        for value in values:
            handle.write(census.canonical_json(value) + "\n")


def signature(path):
    info = path.stat(follow_symlinks=False)
    return info.st_size, info.st_mtime_ns, info.st_ctime_ns, info.st_ino, info.st_mode


def regular_files(root):
    names = []
    for directory, subdirectories, files in os.walk(root, followlinks=False):
        for name in subdirectories + files:
            path = Path(directory) / name
            mode = path.lstat().st_mode
            if stat.S_ISLNK(mode) or not (stat.S_ISDIR(mode) or stat.S_ISREG(mode)):
                raise ArchiveError(f"symlink or special file in census: {path.relative_to(root)}")
        names.extend(str((Path(directory) / name).relative_to(root)) for name in files)
    return sorted(names)


@contextmanager
def finished_run_lock(root):
    path = root / ".run.lock"
    if not path.is_file() or path.is_symlink():
        raise ArchiveError("census has no regular .run.lock")
    with path.open("rb") as handle:
        try:
            fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise ArchiveError("census is running; its output lock is held") from error
        try:
            yield
        finally:
            fcntl.flock(handle, fcntl.LOCK_UN)


def manifest_universe(manifest):
    if manifest.get("schema_version") != 1 or manifest.get("scope") != "full":
        raise ArchiveError("archive requires a schema-1 full-universe census manifest")
    files = manifest.get("files", [])
    specifications = {}
    for item in files:
        name = relative_name(item["path"])
        if not name.startswith("Mathlib/") or not name.endswith(".lean") or name in specifications:
            raise ArchiveError("invalid or duplicate file in manifest universe")
        if not re.fullmatch(r"[0-9a-f]{64}", item.get("sha256", "")):
            raise ArchiveError(f"invalid source hash in manifest: {name}")
        specifications[name] = item["sha256"]
    selected = manifest.get("selected_files", [])
    if not files or selected != sorted(specifications):
        raise ArchiveError("selected files do not equal the complete manifest universe")
    fields = ("config", "implementation_sha256", "mathlib_revision", "environment_sha256",
              "selected_files", "extractor_binary_sha256")
    try:
        protocol = {field: manifest[field] for field in fields}
    except KeyError as error:
        raise ArchiveError(f"manifest lacks protocol field: {error}") from error
    if census.digest(census.canonical_json(protocol)) != manifest.get("protocol_hash"):
        raise ArchiveError("manifest protocol hash does not match its frozen inputs")
    return specifications


def permitted_file(name, modules, frozen):
    if name in {"manifest.json", "summary.json", "integrity.json", ".run.lock", "launch.json",
                "setup-cache-origin.json", "setup-cache-origin.manifest.json"}:
        return True
    if re.fullmatch(r"startup-\d+\.(?:json|stdout\.log|stderr\.log)", name):
        return True
    if re.fullmatch(r"interruption-\d+\.json", name):
        return True
    parts = PurePosixPath(name).parts
    if parts[0] == "frozen-implementation":
        return "/".join(parts[1:]) in frozen
    if parts[0] == "files" and len(parts) >= 3 and parts[1] in modules:
        if len(parts) == 3:
            return parts[2] in {"result.json", "orchestrator_error.json"}
        return (len(parts) == 4 and re.fullmatch(r"attempt-\d+", parts[2]) is not None
                and parts[3] in {"events.jsonl", "proposals.jsonl", "request.json", "stdout.log", "stderr.log",
                                  "setup.stderr.log", "setup.json.gz", "result.json"})
    if parts[0] == "setups" and len(parts) == 2:
        return (any(parts[1].endswith(suffix) and parts[1][:-len(suffix)] in modules
                    for suffix in (".json.gz", ".metadata.json"))
                or re.fullmatch(r"batch-[0-9a-f]{16}(?:-\d+)?\.(?:metadata\.json|stderr\.log|jsonl\.gz)", parts[1]) is not None)
    return False


def check_hash(root, name, expected, inventory):
    name = relative_name(name)
    if name not in inventory or inventory[name]["sha256"] != expected:
        raise ArchiveError(f"evidence changed or missing: {name}")


def validate_origin(root, manifest, inventory):
    name = "setup-cache-origin.json"
    if name not in inventory:
        if "setup-cache-origin.manifest.json" in inventory:
            raise ArchiveError("setup-cache origin manifest has no origin ledger")
        return
    origin = read_json(root / name)
    source_name = "setup-cache-origin.manifest.json"
    check_hash(root, source_name, origin.get("source_manifest_sha256"), inventory)
    source = read_json(root / source_name)
    if origin.get("source_protocol_hash") != source.get("protocol_hash"):
        raise ArchiveError("setup-cache origin protocol mismatch")
    for field in ("mathlib_revision", "environment_sha256"):
        if origin.get(field) != manifest.get(field) or source.get(field) != manifest.get(field):
            raise ArchiveError(f"setup-cache origin changed {field}")
    if source.get("files") != manifest.get("files"):
        raise ArchiveError("setup-cache origin has a different source universe")
    cached = origin.get("cached_file_sha256")
    if not isinstance(cached, dict) or not cached:
        raise ArchiveError("setup-cache origin lacks its copied-file hashes")
    for cached_name, expected in cached.items():
        if not relative_name(cached_name).startswith("setups/"):
            raise ArchiveError("setup-cache origin points outside the run's setup cache")
        check_hash(root, cached_name, expected, inventory)


def verify_result(root, result, specification, inventory):
    name = result.get("path")
    if name != specification[0] or not isinstance(result.get("complete"), bool) or not result.get("status"):
        raise ArchiveError(f"invalid per-file outcome: {specification[0]}")
    if result.get("complete") != (result["status"] == "complete"):
        raise ArchiveError(f"contradictory completion status: {name}")
    if result.get("status") in {"pending", "running", "unprocessed"}:
        raise ArchiveError(f"unfinished per-file outcome: {name}")
    if result.get("source_sha256") != specification[1]:
        if result.get("status") != "orchestrator_exception":
            raise ArchiveError(f"per-file source hash disagrees with manifest: {name}")
    evidence = result.get("evidence_sha256")
    if evidence:
        for evidence_name, expected in evidence.items():
            check_hash(root, evidence_name, expected, inventory)
        try:
            census.verify_evidence(root, result)
        except census.CensusError as error:
            raise ArchiveError(str(error)) from error
        return True
    module = name[:-5].replace("/", ".")
    error_path = root / "files" / module / "orchestrator_error.json"
    if (result.get("status") != "orchestrator_exception" or result.get("complete")
            or result.get("successful_proposals", 0) != 0 or read_json(error_path) != result):
        raise ArchiveError(f"file has no hashed extractor evidence or matching orchestrator failure: {name}")
    return False


def proposal_records(root, result, result_name, current, inventory):
    name = result.get("proposal_file")
    count = result.get("successful_proposals", 0)
    if not name:
        if count:
            raise ArchiveError(f"successful result has no proposal file: {result_name}")
        return []
    relative_name(name)
    if name not in result.get("evidence_sha256", {}) or name not in inventory:
        raise ArchiveError(f"proposal file lacks a verified evidence hash: {name}")
    records = []
    for number, line in enumerate((root / name).read_text().splitlines(), 1):
        try:
            proposal = json.loads(line)
        except ValueError as error:
            raise ArchiveError(f"invalid proposal JSONL: {name}:{number}") from error
        if (not isinstance(proposal, dict) or proposal.get("status") != "success"
                or proposal.get("kernel_checked") is not True or proposal.get("path") != result["path"]
                or proposal.get("source_sha256") != result.get("source_sha256")):
            raise ArchiveError(f"unchecked or mismatched proposal: {name}:{number}")
        if census.digest(proposal.get("original", "")) != proposal.get("original_sha256"):
            raise ArchiveError(f"proposal source span hash mismatch: {name}:{number}")
        records.append({"result_file": result_name, "proposal_file": name,
                        "current_attempt": current, "proposal": proposal})
    if len(records) != count or (not result["complete"] and records):
        raise ArchiveError(f"proposal count disagrees with per-file outcome: {name}")
    return records


def validate_run(root):
    manifest = read_json(root / "manifest.json")
    specifications = manifest_universe(manifest)
    integrity = read_json(root / "integrity.json")
    if integrity.get("status") != "valid" or integrity.get("protocol_hash") != manifest["protocol_hash"]:
        raise ArchiveError("census integrity is pending or invalid")
    summary = read_json(root / "summary.json")
    if summary.get("frozen_inputs_verified") is not True or summary.get("full_universe_processed") is not True:
        raise ArchiveError("census has not processed the full frozen universe")
    frozen = {**manifest["implementation_sha256"], **manifest["environment_sha256"]}
    modules = {name[:-5].replace("/", ".") for name in specifications}
    inventory, signatures = {}, {}
    for name in regular_files(root):
        if not permitted_file(name, modules, frozen):
            raise ArchiveError(f"unexpected run file; build outputs and environment dumps cannot be archived: {name}")
        path = root / name
        signatures[name] = signature(path)
        inventory[name] = {"sha256": file_hash(path), "bytes": signatures[name][0]}
        if signature(path) != signatures[name]:
            raise ArchiveError(f"census input changed while hashing: {name}")
    for name, expected in frozen.items():
        check_hash(root, "frozen-implementation/" + relative_name(name), expected, inventory)
    validate_origin(root, manifest, inventory)
    for name in inventory:
        if not re.fullmatch(r"interruption-\d+\.json", name):
            continue
        interruption = read_json(root / name)
        processed, unprocessed = interruption.get("processed_files"), interruption.get("unprocessed_files")
        if (interruption.get("status") != "interrupted" or interruption.get("reason") != "STOP_REQUESTED"
                or interruption.get("protocol_hash") != manifest["protocol_hash"]
                or type(processed) is not int or type(unprocessed) is not int
                or min(processed, unprocessed) < 0 or processed + unprocessed != len(specifications)):
            raise ArchiveError(f"invalid interruption ledger: {name}")
    outcomes, attempts, proposals, no_extractor = [], [], [], []
    attributed_proposal_files = set()
    for name, expected in specifications.items():
        module = name[:-5].replace("/", ".")
        result_name = f"files/{module}/result.json"
        result = read_json(root / result_name)
        if not verify_result(root, result, (name, expected), inventory):
            no_extractor.append(name)
        outcomes.append({"result_file": result_name, "result": result})
        directory = result.get("directory")
        if directory:
            if not re.fullmatch(re.escape(f"files/{module}/") + r"attempt-\d+", relative_name(directory)):
                raise ArchiveError(f"per-file attempt directory mismatch: {name}")
            if read_json(root / directory / "result.json") != result:
                raise ArchiveError(f"latest result disagrees with attempt ledger: {name}")
        elif result.get("status") != "orchestrator_exception":
            raise ArchiveError(f"file outcome has no attempt ledger: {name}")
        for path in sorted((root / "files" / module).glob("attempt-*/result.json")):
            attempt_name = str(path.relative_to(root))
            attempt = read_json(path)
            current = attempt == result and str(path.parent.relative_to(root)) == directory
            if not current:
                verify_result(root, attempt, (name, expected), inventory)
            if attempt.get("directory") != str(path.parent.relative_to(root)):
                raise ArchiveError(f"historical attempt directory mismatch: {attempt_name}")
            attempts.append({"result_file": attempt_name, "current_attempt": current, "result": attempt})
            records = proposal_records(root, attempt, attempt_name, current, inventory)
            proposals.extend(records)
            if attempt.get("proposal_file"):
                attributed_proposal_files.add(attempt["proposal_file"])
            if attempt.get("complete"):
                event_name = str((path.parent / "events.jsonl").relative_to(root))
                if event_name not in attempt.get("evidence_sha256", {}):
                    raise ArchiveError(f"complete file lacks a hashed event ledger: {attempt_name}")
                events, parse_error = census.parse_events(root / event_name)
                if any(not isinstance(event, dict) for event in events):
                    raise ArchiveError(f"invalid event object: {event_name}")
                extraction = attempt.get("extraction", {})
                checked = census.validate_events(events, extraction.get("returncode"), parse_error,
                                                 extraction.get("timed_out", False))
                if any(attempt.get(key) != value for key, value in checked.items()):
                    raise ArchiveError(f"complete outcome disagrees with raw event ledger: {attempt_name}")
                successes = {event["key"]: event for event in events
                             if event.get("type") == "attempt" and event.get("status") == "success"}
                if sorted(record["proposal"].get("key", "") for record in records) != sorted(successes):
                    raise ArchiveError(f"proposal keys disagree with checked events: {attempt_name}")
                for record in records:
                    proposal = record["proposal"]
                    event = successes.get(proposal.get("key"))
                    if event is None or any(proposal.get(key) != value for key, value in event.items()):
                        raise ArchiveError(f"proposal disagrees with checked event: {attempt_name}")
    orphan_proposals = 0
    for name in inventory:
        if not name.endswith("/proposals.jsonl") or name in attributed_proposal_files:
            continue
        for number, line in enumerate((root / name).read_text().splitlines(), 1):
            try:
                proposal = json.loads(line)
            except ValueError as error:
                raise ArchiveError(f"invalid orphan proposal JSONL: {name}:{number}") from error
            if not isinstance(proposal, dict):
                raise ArchiveError(f"invalid orphan proposal object: {name}:{number}")
            proposals.append({"result_file": None, "proposal_file": name, "current_attempt": False,
                              "verification": "archive_time_hash_only_no_matching_attempt_ledger", "proposal": proposal})
            orphan_proposals += 1
    with tempfile.TemporaryDirectory(prefix="census-summary-") as temporary:
        temporary = Path(temporary)
        write_json(temporary / "integrity.json", integrity)
        recomputed = census.summarize(manifest, [entry["result"] for entry in outcomes], temporary)
    if summary != recomputed:
        changed = sorted(key for key in set(summary) | set(recomputed) if summary.get(key) != recomputed.get(key))
        raise ArchiveError(f"summary disagrees with per-file ledger: {', '.join(changed)}")
    if (summary["processed_files"] != len(specifications) or summary["unprocessed_files"] != 0
            or sum(record["current_attempt"] for record in proposals) != summary["successful_proposals"]):
        raise ArchiveError("full-universe file/proposal accounting is incomplete")
    return {"manifest": manifest, "summary": summary, "inventory": inventory, "signatures": signatures,
            "outcomes": outcomes, "attempts": attempts, "proposals": proposals,
            "files_without_extractor_evidence": no_extractor, "unattributed_proposals": orphan_proposals}


def copy_verified(root, name, target, inventory):
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(root / name, target)
    if file_hash(target) != inventory[name]["sha256"]:
        raise ArchiveError(f"census input changed while copying: {name}")


def write_compact(root, output, validated, full_raw):
    inventory = validated["inventory"]
    for name in inventory:
        if name in {"manifest.json", "summary.json", "integrity.json", "launch.json", "setup-cache-origin.json",
                    "setup-cache-origin.manifest.json"} or name.startswith("frozen-implementation/") or re.fullmatch(r"interruption-\d+\.json", name):
            copy_verified(root, name, output / name, inventory)
    write_jsonl(output / "file-outcomes.jsonl", validated["outcomes"])
    write_jsonl(output / "attempt-outcomes.jsonl", validated["attempts"])
    write_jsonl(output / "proposals.jsonl", validated["proposals"])
    write_json(output / "source-inventory.json", {"schema_version": 1, "files": inventory})
    tools = output / "archive-tools"
    tools.mkdir()
    shutil.copyfile(Path(__file__), tools / "archive_census.py")
    shutil.copyfile(Path(census.__file__), tools / "census.py")
    summary = validated["summary"]
    report = {"schema_version": 1, "created_at_utc": datetime.now(timezone.utc).isoformat(),
              "status": "validated_full_universe_archive", "protocol_hash": validated["manifest"]["protocol_hash"],
              "mathlib_revision": validated["manifest"]["mathlib_revision"],
              **{key: summary[key] for key in ("processed_files", "completed_files", "failed_files",
                                              "full_universe_processed", "full_universe_completed",
                                              "frozen_inputs_verified", "successful_proposals", "file_status_counts")},
              "archived_attempts": len(validated["attempts"]), "archived_proposals": len(validated["proposals"]),
              "unattributed_proposals": validated["unattributed_proposals"],
              "files_without_extractor_evidence": validated["files_without_extractor_evidence"],
              "raw_files": len(inventory), "raw_bytes": sum(entry["bytes"] for entry in inventory.values()),
              "raw_archive_requested": full_raw,
              "evidence_stage": summary["evidence_stage"],
              "coverage": "All manifest files have a recorded outcome; failed files remain failures.",
              "compact_contents": "All file outcomes, attempt outcomes, proposals, input hashes, and frozen source/configuration; raw events and setups are indexed but not copied.",
              "archiver_sha256": file_hash(tools / "archive_census.py"),
              "validation_helper_sha256": file_hash(tools / "census.py")}
    write_json(output / "archive.json", report)
    write_json(output / "inventory.json", {"schema_version": 1, "files": {
        name: {"sha256": file_hash(output / name), "bytes": (output / name).stat().st_size}
        for name in regular_files(output)}})
    return report


def make_tar(path, root, names, prefix, expected=None):
    with path.open("wb") as raw, gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0) as compressed:
        with tarfile.open(fileobj=compressed, mode="w", format=tarfile.PAX_FORMAT) as archive:
            for name in names:
                source = root / name
                if expected is not None and file_hash(source) != expected[name]["sha256"]:
                    raise ArchiveError(f"census input changed before raw archive: {name}")
                info = tarfile.TarInfo(str(PurePosixPath(prefix) / name))
                info.size = source.stat().st_size
                info.mode, info.mtime = 0o644, 0
                with source.open("rb") as handle:
                    archive.addfile(info, handle)


def verify_unchanged(root, validated):
    if regular_files(root) != sorted(validated["inventory"]):
        raise ArchiveError("census file inventory changed during archival")
    for name, old in validated["signatures"].items():
        if signature(root / name) != old:
            raise ArchiveError(f"census input changed during archival: {name}")


def archive_run(source, output, *, full_raw=False):
    source = Path(source).absolute()
    output = Path(output).absolute()
    if source.is_symlink() or not source.is_dir():
        raise ArchiveError("source must be a regular census run directory")
    source = source.resolve()
    if output.exists() or output.is_symlink() or output.resolve().is_relative_to(source):
        raise ArchiveError("output must be a new directory outside the census run")
    stage = None
    try:
        with finished_run_lock(source):
            validated = validate_run(source)
            output.parent.mkdir(parents=True, exist_ok=True)
            stage = Path(tempfile.mkdtemp(prefix=".archive-", dir=output.parent))
            report = write_compact(source, stage, validated, full_raw)
            names = regular_files(stage)
            make_tar(stage / "compact.tar.gz", stage, names, "census-evidence")
            archive_names = ["compact.tar.gz"]
            if full_raw:
                make_tar(stage / "raw.tar.gz", source, sorted(validated["inventory"]), "run", validated["inventory"])
                archive_names.append("raw.tar.gz")
            archives = {name: {"sha256": file_hash(stage / name), "bytes": (stage / name).stat().st_size}
                        for name in archive_names}
            write_json(stage / "archives.json", archives)
            for name, metadata in archives.items():
                (stage / f"{name}.sha256").write_text(f"{metadata['sha256']}  {name}\n")
            verify_unchanged(source, validated)
            if output.exists():
                raise ArchiveError("output directory appeared during archival")
            stage.rename(output)
            stage = None
            return report
    except (census.CensusError, OSError, ValueError, KeyError, TypeError) as error:
        raise ArchiveError(str(error)) from error
    finally:
        if stage is not None:
            shutil.rmtree(stage)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path, help="Finished census run directory")
    parser.add_argument("--output", type=Path, required=True, help="New evidence bundle directory")
    parser.add_argument("--full-raw", action="store_true", help="Also compress every regular run file; may be large")
    args = parser.parse_args(argv)
    report = archive_run(args.source, args.output, full_raw=args.full_raw)
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except ArchiveError as error:
        print(f"archive census: {error}", file=sys.stderr)
        raise SystemExit(2)
