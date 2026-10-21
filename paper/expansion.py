"""Validate targeted discovery and a composed patch without claiming a new census."""

from collections import Counter
import importlib.util
from pathlib import Path
import sys


def script(name):
    directory = Path(__file__).resolve().parents[1] / "scripts"
    spec = importlib.util.spec_from_file_location("paper_expansion_" + name, directory / (name + ".py"))
    module = importlib.util.module_from_spec(spec)
    sys.path.insert(0, str(directory))
    try:
        spec.loader.exec_module(module)
    finally:
        sys.path.pop(0)
    return module


MERGER = script("select_expansion")
VERIFIER = script("verify_selection")


def recorded_name(path):
    name = str(Path(path).absolute())
    return "/private" + name if name.startswith("/var/") else name


def safe_relative(name, check):
    path = Path(name)
    check(isinstance(name, str) and name and not path.is_absolute() and
          ".." not in path.parts and "\\" not in name, "unsafe expansion evidence path")
    return path


def outcome_summary(manifest, rows, check):
    selected = manifest["selected_files"]
    check(len(rows) == len(selected) and sorted(row.get("path", "") for row in rows) == selected,
          "targeted discovery has missing or duplicate file outcomes")
    universe = {item["path"]: item["sha256"] for item in manifest["files"]}
    unknown = 0
    for row in rows:
        complete = row.get("complete")
        check(type(complete) is bool and complete == (row.get("status") == "complete") and
              row.get("status") not in {None, "pending", "running", "unprocessed"},
              "targeted discovery has unfinished or contradictory outcomes")
        check(row.get("source_sha256") == universe[row["path"]] or row["status"] == "orchestrator_exception",
              "targeted outcome source differs from pinned inventory")
        eligible, counts = row.get("eligible_observations", 0), row.get("attempt_status_counts", {})
        check(type(eligible) is int and eligible >= 0 and
              all(type(value) is int and value >= 0 for value in counts.values()),
              "invalid targeted observation counts")
        residual = eligible - sum(counts.values())
        check(residual >= 0 and (not complete or residual == 0), "targeted observations do not partition")
        unknown += residual
    complete = sum(row["complete"] for row in rows)
    result = {"universe_files": len(universe), "selected_files": len(selected),
              "processed_files": len(selected), "completed_files": complete,
              "failed_files": len(selected) - complete, "unprocessed_files": 0,
              "full_universe_processed": False, "full_universe_completed": False,
              "file_status_counts": dict(Counter(row["status"] for row in rows)),
              "resource_tier_counts": dict(Counter(str(row.get("resource_tier", "unknown")) for row in rows))}
    for key in ["counts", "attempt_status_counts", "original_observation_fragment_counts", "original_eligible_fragment_counts"]:
        counts = Counter()
        for row in rows:
            counts.update(row.get(key, {}))
        result[key] = dict(counts)
    fragments = {}
    for row in rows:
        for fragment, counts in row.get("attempt_status_counts_by_original_fragment", {}).items():
            fragments.setdefault(fragment, Counter()).update(counts)
    result["attempt_status_counts_by_original_fragment"] = {key: dict(value) for key, value in fragments.items()}
    for key in ["successful_proposals", "eligible_observations"]:
        result[key] = sum(row.get(key, 0) for row in rows)
    return result, unknown


def targeted_discovery(model, check, canonical_sha):
    check(model.result["census"] is not None, "targeted discovery needs validated full-census background")
    archive_path = model.path("targeted_archive")
    directory = archive_path.parent
    archive = model.read(archive_path)
    inventory = model.read(directory / "inventory.json")
    required = {"archive.json", "manifest.json", "summary.json", "integrity.json", "file-outcomes.jsonl",
                "attempt-outcomes.jsonl", "proposals.jsonl", "raw-index.json", "raw.tar.gz",
                "setup-cache-origin.json", "archive-tools/archive_targeted.py", "archive-tools/census.py"}
    check(archive.get("schema_version") == 1 and archive.get("status") == "validated_targeted_discovery_archive" and
          archive.get("scope") == "targeted_followup" and archive.get("recorded_scope") == "calibration" and
          archive.get("full_universe_coverage_claim") is False and required <= inventory.keys(),
          "targeted discovery lacks a validated, explicitly limited archive")
    for name, item in inventory.items():
        path = directory / safe_relative(name, check)
        check(type(item.get("bytes")) is int and item["bytes"] >= 0, "invalid targeted payload size")
        model.fingerprints({str(path): item["sha256"]})
    manifest, summary = model.read(directory / "manifest.json"), model.read(directory / "summary.json")
    integrity = model.read(directory / "integrity.json")
    background = model.result["census"]["manifest"]
    check(manifest.get("files") == background["files"] and
          manifest.get("mathlib_revision") == archive.get("mathlib_revision") == background["mathlib_revision"],
          "targeted discovery source universe differs from full-census background")
    selected = manifest.get("selected_files", [])
    universe = {item["path"]: item["sha256"] for item in manifest["files"]}
    check(selected == sorted(set(selected)) and 0 < len(selected) < len(universe) and
          all(name in universe for name in selected), "targeted discovery is not a strict frozen source subset")
    protocol = {key: manifest[key] for key in ("config", "implementation_sha256", "mathlib_revision",
                "environment_sha256", "selected_files", "extractor_binary_sha256")}
    check(manifest.get("scope") == summary.get("scope") == "calibration" and
          canonical_sha(protocol) == manifest.get("protocol_hash") == summary.get("protocol_hash") == archive.get("protocol_hash") and
          integrity == {"status": "valid", "protocol_hash": manifest["protocol_hash"]},
          "targeted discovery protocol or integrity differs")
    outcomes = model.read(directory / "file-outcomes.jsonl", lines=True)
    rows = [record["result"] for record in outcomes]
    derived, unknown = outcome_summary(manifest, rows, check)
    check(all(summary.get(key) == value for key, value in derived.items()) and
          summary.get("frozen_inputs_verified") is True and archive.get("frozen_inputs_verified") is True,
          "targeted discovery summary differs from file outcomes")
    for key in ["universe_files", "selected_files", "processed_files", "completed_files", "failed_files",
                "unprocessed_files", "successful_proposals", "file_status_counts", "evidence_stage"]:
        check(archive.get(key) == summary[key], "targeted archive summary differs: " + key)
    check(summary.get("evidence_stage") == "isolated_kernel_checked_proposals_not_compiled_patches" and
          archive.get("archive_reopened_and_every_member_rehashed") is True,
          "targeted archive lacks its raw validation record")
    raw_index = model.read(directory / "raw-index.json")
    check(archive.get("raw_index_sha256") == inventory["raw-index.json"]["sha256"] and
          archive.get("raw_archive_sha256") == inventory["raw.tar.gz"]["sha256"] and
          archive.get("raw_archive_bytes") == inventory["raw.tar.gz"]["bytes"],
          "targeted raw archive binding differs")
    for name, expected in {**manifest["implementation_sha256"], **manifest["environment_sha256"]}.items():
        check(raw_index.get("files", {}).get("frozen-implementation/" + name, {}).get("sha256") == expected,
              "targeted archive lacks a frozen implementation snapshot")
    attempts = model.read(directory / "attempt-outcomes.jsonl", lines=True)
    proposals = model.read(directory / "proposals.jsonl", lines=True)
    current = [record["result"] for record in attempts if record.get("current_attempt")]
    check(sorted(current, key=lambda row: row["path"]) == sorted(rows, key=lambda row: row["path"]),
          "targeted current-attempt ledger differs from file outcomes")
    current_proposals = [record for record in proposals if record.get("current_attempt")]
    check(len(current_proposals) == summary["successful_proposals"] and
          len(proposals) == archive.get("archived_proposal_records") and len(attempts) == archive.get("archived_attempts"),
          "targeted proposal or attempt count differs")
    keys = set()
    for record in proposals:
        proposal = record["proposal"]
        check(proposal.get("status") == "success" and proposal.get("kernel_checked") is True,
              "targeted proposal is not kernel-checked success evidence")
        key = (record.get("result_file"), proposal.get("key"))
        check(key not in keys and proposal.get("path") in selected and
              proposal.get("source_sha256") == universe[proposal["path"]],
              "targeted proposal source or identity differs")
        keys.add(key)
    model.result["targeted"] = {"manifest": manifest, "summary": summary, "archive": archive,
                                "unknown_due_incomplete_file": unknown}
    model.result["stages"].append("targeted-discovery")


def composed_selection(model, manifest, summary, ledger, check):
    check(model.result.get("targeted") is not None, "composed selection has no targeted discovery")
    inputs = manifest.get("input_manifests", [])
    check(inputs and isinstance(inputs, list), "composed selection lacks input snapshots")
    snapshots = []
    directory = model.path("selector_manifest").parent
    for item in inputs:
        path = directory / safe_relative(item["snapshot"], check)
        check(model.hash(path) == item["sha256"], "composed input snapshot hash differs")
        snapshots.append(model.read(path))
    excluded = {row["id"]: row["reason"] for row in manifest["candidates"] if row["status"] == "failed"}
    expected, expected_ledger, accounting = MERGER.merge_manifests(snapshots, model.source_root, excluded)
    expected["input_manifests"] = inputs
    check(expected == manifest and expected_ledger == ledger,
          "composed selection differs from deterministic source-backed reselection")
    check(summary.get("evidence_stage") == "selected_proposals_not_combined_source_compiled" and
          summary.get("accounting") == accounting and
          summary.get("outcome_counts") == dict(Counter(row["outcome"] for row in ledger)),
          "composed selection accounting or ledger differs")


def body_evidence(model, report, manifest, check):
    VERIFIER.validate_proof_spans(manifest, model.source_root, allow_preparation=True)
    check(report.get("proof_span_policy") == "manually_reviewed_exact_proof_replacement_with_source_bound_original_body_evidence",
          "composed patch lacks its original-body proof guard")
    selected = {row["id"]: row for row in manifest["candidates"] if row["status"] == "replace"}
    records = report.get("body_census_evidence", [])
    check(len(records) == len(selected) and {row.get("candidate_id") for row in records} == selected.keys(),
          "composed patch lacks unique body evidence for every selected edit")
    specifications = {row["path"]: row["source_sha256"] for row in manifest["files"]}
    cached = {}
    for record in records:
        candidate = selected[record["candidate_id"]]
        fields = {"path": candidate["path"], "parent_declaration": candidate.get("parent_declaration", candidate["declaration"]),
                  "body_start_byte": candidate["body_start_byte"], "body_end_byte": candidate["body_end_byte"],
                  "source_sha256": specifications[candidate["path"]]}
        check(all(record.get(key) == value for key, value in fields.items()) and
              record.get("role") == "original_source_body_evidence_only_not_a_checked_replacement_proposal",
              "composed body evidence differs from selected source span")
        census = Path(record["census"])
        manifest_path = census / "manifest.json"
        result_path = census / "files" / candidate["path"][:-5].replace("/", ".") / "result.json"
        events_path = Path(record["events_path"])
        for path, key in [(manifest_path, "manifest_sha256"), (result_path, "result_sha256"), (events_path, "events_sha256")]:
            check(model.hash(path) == record[key] and report["input_sha256"].get(recorded_name(path)) == record[key],
                  "composed body provenance lacks a frozen source record")
        if str(events_path) not in cached:
            original_manifest, original_result = model.read(manifest_path), model.read(result_path)
            events = model.read(events_path, lines=True)
            check(original_manifest.get("mathlib_revision") == manifest["mathlib_revision"] and
                  original_manifest.get("protocol_hash") == record["census_protocol_hash"] and
                  original_result.get("complete") is True and original_result.get("status") == "complete" and
                  original_result.get("source_sha256") == specifications[candidate["path"]],
                  "composed body source observation is incomplete or mismatched")
            relative = str(events_path.relative_to(census))
            check(original_result.get("evidence_sha256", {}).get(relative) == record["events_sha256"],
                  "composed body event hash differs from its file result")
            cached[str(events_path)] = events
        matches = [row for row in cached[str(events_path)] if row.get("type") == "observation" and
                   row.get("phase") == "original" and row.get("key") == record["original_observation_key"] and
                   all(row.get(key) == fields[key] for key in ["parent_declaration", "body_start_byte", "body_end_byte"])]
        check(bool(matches), "selected proof body has no original source observation")
