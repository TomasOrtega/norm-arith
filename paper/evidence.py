"""Validate the evidence chain before the paper prints final library results."""

import argparse
from collections import Counter
from datetime import datetime, timezone
import difflib
import hashlib
import importlib.util
import json
import os
import re
from pathlib import Path
import subprocess
import shutil
import tempfile

from evidence_transport import TransportError, restore_configured_bundle

ROOT = Path(__file__).resolve().parents[1]
PATH_KEYS = (
    "census_summary", "census_manifest", "census_integrity", "census_outcomes", "census_archive",
    "selector_summary", "selector_manifest", "selector_ledger",
    "source_verification_report", "source_verified_manifest", "frozen_manifest",
    "confirmatory_report", "confirmatory_analysis_plan", "confirmatory_measurements",
    "targeted_archive",
)
SPEC = importlib.util.spec_from_file_location("paper_evidence_benchmark", ROOT / "scripts/benchmark.py")
BENCHMARK = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BENCHMARK)


class EvidenceError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise EvidenceError(message)


def file_sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def canonical_sha(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def implementation_sha(root=ROOT):
    digest = hashlib.sha256()
    pending = [root / "NormArith.lean"]
    paths = set()
    while pending:
        path = pending.pop()
        if path in paths:
            continue
        paths.add(path)
        imports = re.findall(r"(?m)^\s*(?:(?:public|meta)\s+)*import\s+(NormArith(?:\.[\w']+)*)\s*$", path.read_text())
        pending.extend(root / (name.replace(".", "/") + ".lean") for name in imports)
    for path in sorted(paths):
        digest.update(str(path.relative_to(root)).encode() + b"\0" + path.read_bytes())
    return digest.hexdigest()


def recorded_name(path):
    name = str(Path(path).absolute())
    return "/private" + name if name.startswith("/var/") else name


def patch_bytes(prepared):
    return "".join(line for source in prepared for line in difflib.unified_diff(
        source["original"].splitlines(keepends=True), source["replacement"].splitlines(keepends=True),
        fromfile="a/" + source["path"], tofile="b/" + source["path"])).encode()


class Evidence:
    def __init__(self, config, root, *, bundle=None, receipt=None):
        self.config = config
        self.study_mode = config.get("study_mode", "full_census")
        require(self.study_mode in {"full_census", "composed_expansion"}, "unknown study mode")
        if self.study_mode == "composed_expansion":
            require(config.get("targeted_archive") is not None,
                    "composed expansion requires targeted discovery evidence")
        else:
            require(config.get("targeted_archive") is None,
                    "targeted discovery requires composed_expansion study mode")
        self.bundle, self.receipt = bundle, receipt
        self.root = Path(receipt["original_project"]) if receipt else root.resolve()
        self.mathlib = self.root / ".lake/packages/mathlib"
        self.source_root = bundle / "mathlib" if bundle else self.mathlib
        self.project_source_root = bundle / "project" if bundle else self.root
        self.inputs, self.verified_hashes = {}, {}
        self.result = {"stages": [], "inputs": self.inputs, "census": None, "selection": None,
                       "patch": None, "timing": None}

    def path(self, key, fallback=None):
        name = self.config.get(key) or fallback
        require(isinstance(name, (str, Path)) and bool(str(name)), f"missing evidence path: {key}")
        path = Path(name)
        return path if path.is_absolute() else self.root / path

    def actual(self, path):
        if self.bundle is None:
            return path.resolve()
        name = recorded_name(path)
        require(name in self.receipt["copied_inputs"], "portable evidence has no copied input: " + name)
        return self.bundle / self.receipt["copied_inputs"][name]

    def hash(self, path):
        return file_sha(self.actual(path))

    def read(self, path, *, lines=False):
        name = recorded_name(path.resolve()) if self.bundle is None else recorded_name(path)
        data = self.actual(path).read_bytes()
        self.inputs[name] = hashlib.sha256(data).hexdigest()
        value = [json.loads(line) for line in data.decode().splitlines() if line.strip()] if lines else json.loads(data)
        require(isinstance(value, list if lines else dict), f"invalid JSON evidence: {path}")
        return value

    def group(self, keys):
        present = [self.config.get(key) is not None for key in keys]
        require(not any(present) or all(present), "incomplete evidence group: " + ", ".join(keys))
        return any(present)

    def fingerprints(self, values):
        require(isinstance(values, dict), "missing evidence input fingerprints")
        for name, expected in values.items():
            path = Path(name)
            path = path if path.is_absolute() else self.root / path
            canonical = recorded_name(path.resolve()) if self.bundle is None else recorded_name(path)
            if self.bundle is not None:
                require(self.receipt["verified_input_sha256"].get(canonical) == expected, "input lacks strict export-time validation: " + name)
                if canonical in self.receipt["copied_inputs"]:
                    require(self.hash(path) == expected, "copied evidence input changed: " + name)
            else:
                require(path.is_file() and file_sha(path) == expected, f"evidence input changed or is absent: {name}")
            require(canonical not in self.verified_hashes or self.verified_hashes[canonical] == expected, "inconsistent evidence fingerprints: " + name)
            self.verified_hashes[canonical] = expected

    def census(self):
        if not self.group(["census_summary", "census_manifest", "census_integrity"]):
            require(self.config.get("census_outcomes") is None and self.config.get("census_archive") is None, "census outcomes or archive have no manifest")
            return
        manifest = self.read(self.path("census_manifest"))
        summary = self.read(self.path("census_summary"))
        integrity = self.read(self.path("census_integrity"))
        require(manifest.get("schema_version") == summary.get("schema_version") == 1, "unsupported census schema")
        require(manifest.get("scope") == summary.get("scope") == "full", "calibration or partial scope is not final census evidence")
        protocol = {key: manifest[key] for key in ("config", "implementation_sha256", "mathlib_revision",
                    "environment_sha256", "selected_files", "extractor_binary_sha256")}
        require(canonical_sha(protocol) == manifest.get("protocol_hash"), "census protocol hash mismatch")
        require(integrity.get("status") == "valid" and integrity.get("protocol_hash") == summary.get("protocol_hash") == manifest["protocol_hash"], "census integrity is pending, invalid, or mismatched")
        require(summary.get("full_universe_processed") is True and summary.get("frozen_inputs_verified") is True,
                "census has not processed all frozen files")
        require(manifest.get("files") and all(isinstance(item, dict) for item in manifest["files"]), "empty census source universe")
        specifications = {item["path"]: item["sha256"] for item in manifest["files"]}
        paths = sorted(specifications)
        if self.bundle is None:
            tracked = subprocess.check_output(["git", "-C", str(self.mathlib), "ls-files", "-z", "--", "Mathlib"])
            tracked = sorted(name.decode() for name in tracked.split(b"\0") if name.startswith(b"Mathlib/") and name.endswith(b".lean"))
            revision = subprocess.check_output(["git", "-C", str(self.mathlib), "rev-parse", "HEAD"], text=True).strip()
            require(revision == manifest["mathlib_revision"], "census revision differs from the pinned checkout")
            require(not subprocess.check_output(["git", "-C", str(self.mathlib), "status", "--porcelain", "--untracked-files=no"]), "pinned mathlib checkout has tracked changes")
        else:
            require(self.receipt["verified_mathlib_revision"] == manifest["mathlib_revision"] and self.receipt["verified_source_universe_sha256"] == canonical_sha(manifest["files"]), "portable source-universe validation differs from the census")
            tracked = paths
        require(len(specifications) == len(manifest["files"]) and paths == tracked == manifest["selected_files"], "census does not cover the exact tracked source universe")
        self.fingerprints({str(self.mathlib / name): digest for name, digest in specifications.items()})
        directory = self.path("census_manifest").parent
        snapshots = {**manifest["implementation_sha256"], **manifest["environment_sha256"]}
        self.fingerprints({str(directory / "frozen-implementation" / name): digest for name, digest in snapshots.items()})
        outcomes = self.config.get("census_outcomes")
        bundled_outcomes = self.bundle is not None and recorded_name(directory / "file-outcomes.jsonl") in self.receipt["copied_inputs"]
        if outcomes or bundled_outcomes or (self.bundle is None and (directory / "file-outcomes.jsonl").exists()):
            records = self.read(self.path("census_outcomes", directory / "file-outcomes.jsonl"), lines=True)
            results = [record["result"] for record in records]
        else:
            results = [self.read(directory / "files" / name[:-5].replace("/", ".") / "result.json") for name in paths]
        require(len(results) == len(paths) and sorted(row.get("path", "") for row in results) == paths, "missing or duplicate census file outcomes")
        for row in results:
            require(isinstance(row.get("complete"), bool) and row.get("complete") == (row.get("status") == "complete"), "contradictory census file completion")
            require(row.get("status") not in {None, "pending", "running", "unprocessed"}, "unfinished census file outcome")
            require(row.get("source_sha256") == specifications[row["path"]] or row["status"] == "orchestrator_exception", "census file source mismatch")
        residual = 0
        for row in results:
            eligible = row.get("eligible_observations", 0)
            statuses = row.get("attempt_status_counts", {})
            require(type(eligible) is int and eligible >= 0 and all(type(value) is int and value >= 0 for value in statuses.values()), "invalid eligible-observation or attempt counts")
            unknown = eligible - sum(statuses.values())
            require(unknown >= 0 and (not row["complete"] or unknown == 0), "eligible observations do not partition into unique attempt outcomes")
            residual += unknown
        complete = sum(row["complete"] for row in results)
        derived = {"universe_files": len(paths), "selected_files": len(paths), "processed_files": len(paths),
                   "completed_files": complete, "failed_files": len(paths) - complete, "unprocessed_files": 0,
                   "full_universe_completed": complete == len(paths),
                   "file_status_counts": dict(Counter(row["status"] for row in results)),
                   "resource_tier_counts": dict(Counter(str(row.get("resource_tier", "unknown")) for row in results))}
        for key in ["counts", "attempt_status_counts", "original_observation_fragment_counts", "original_eligible_fragment_counts"]:
            counts = Counter()
            for row in results:
                counts.update(row.get(key, {}))
            derived[key] = dict(counts)
        fragments = {}
        for row in results:
            for fragment, counts in row.get("attempt_status_counts_by_original_fragment", {}).items():
                fragments.setdefault(fragment, Counter()).update(counts)
        derived["attempt_status_counts_by_original_fragment"] = {key: dict(value) for key, value in fragments.items()}
        for key in ["successful_proposals", "eligible_observations"]:
            derived[key] = sum(row.get(key, 0) for row in results)
        require(all(summary.get(key) == value for key, value in derived.items()), "census summary disagrees with final per-file outcomes")
        require(summary.get("evidence_stage") == "isolated_kernel_checked_proposals_not_compiled_patches", "unknown census evidence stage")
        archive_path = self.path("census_archive", directory / "archive.json")
        archive = self.read(archive_path)
        archived = self.read(archive_path.parent / "inventory.json")
        require(archive.get("schema_version") == archived.get("schema_version") == 1 and archive.get("status") == "validated_full_universe_archive", "census has no validated compact archive")
        require(archive.get("protocol_hash") == manifest["protocol_hash"] and archive.get("mathlib_revision") == manifest["mathlib_revision"], "census archive lineage differs")
        for key in ["processed_files", "completed_files", "failed_files", "full_universe_processed", "full_universe_completed", "frozen_inputs_verified", "successful_proposals", "file_status_counts"]:
            require(archive.get(key) == summary[key], "census archive coverage differs: " + key)
        payload = archived.get("files", {})
        require(all(name in payload for name in ["archive.json", "manifest.json", "summary.json", "integrity.json", "file-outcomes.jsonl", "attempt-outcomes.jsonl", "proposals.jsonl", "source-inventory.json", "archive-tools/archive_census.py", "archive-tools/census.py"]), "census archive lacks required payload records")
        for name, item in payload.items():
            require(not Path(name).is_absolute() and ".." not in Path(name).parts, "unsafe census archive payload path")
            self.fingerprints({str(archive_path.parent / name): item["sha256"]})
        require(archive.get("archiver_sha256") == payload["archive-tools/archive_census.py"]["sha256"] and archive.get("validation_helper_sha256") == payload["archive-tools/census.py"]["sha256"], "census archive validation-tool hashes differ")
        for key, name in [("census_manifest", "manifest.json"), ("census_summary", "summary.json"), ("census_integrity", "integrity.json")]:
            require(self.hash(self.path(key)) == payload[name]["sha256"], "census data differs from validated archive: " + name)
        archived_outcomes = self.read(archive_path.parent / "file-outcomes.jsonl", lines=True)
        require([item["result"] for item in archived_outcomes] == results, "census outcomes differ from validated compact archive")
        self.read(archive_path.parent / "source-inventory.json")
        self.result.update(census={"summary": summary, "manifest": manifest, "complete_files": [row["path"] for row in results if row["complete"]], "unknown_due_incomplete_file": residual})
        self.result["stages"].append("census")

    def selection(self):
        if not self.group(["selector_summary", "selector_manifest", "selector_ledger"]):
            return
        require(self.result["census"] is not None, "selection has no validated full census")
        manifest = self.read(self.path("selector_manifest"))
        summary = self.read(self.path("selector_summary"))
        ledger = self.read(self.path("selector_ledger"), lines=True)
        census = self.result["census"]["manifest"]
        if self.study_mode == "composed_expansion":
            from expansion import composed_selection
            composed_selection(self, manifest, summary, ledger, require)
            require(manifest.get("mathlib_revision") == census["mathlib_revision"], "composed selection revision differs")
        else:
            require(manifest.get("census_protocol_hash") == census["protocol_hash"] and manifest.get("mathlib_revision") == census["mathlib_revision"], "selection and census lineage differ")
            require(summary.get("evidence_stage") == "selected_isolated_proposals_not_source_compiled", "unknown selector evidence stage")
        specifications = {item["path"]: item["sha256"] for item in census["files"]}
        require(all(item["path"] in specifications and item["source_sha256"] == specifications[item["path"]] for item in manifest.get("files", [])), "selector source inventory differs from the census")
        if self.study_mode != "composed_expansion":
            require(all(item["path"] in self.result["census"]["complete_files"] for item in manifest["candidates"] if item["status"] == "replace"), "selector used an incomplete census file")
        prepared, account = BENCHMARK.prepare_sources(manifest, self.source_root)
        require(account == summary.get("accounting"), "selector accounting differs from source patch")
        require(dict(Counter(row["outcome"] for row in ledger)) == summary.get("outcome_counts"), "selector ledger and outcome counts differ")
        selected = [row for row in manifest["candidates"] if row["status"] == "replace"]
        require({row["id"] for row in selected} == {row["id"] for row in ledger if row.get("outcome") == "selected"}, "selected candidates differ from selection ledger")
        require(len({row["id"] for row in ledger if "id" in row}) == sum("id" in row for row in ledger), "duplicate selector ledger candidate")
        self.result["selection"] = {"manifest": manifest, "summary": summary, "prepared": prepared, "ledger": ledger}
        self.result["stages"].append("selection")

    def verification(self):
        if not self.group(["source_verification_report", "frozen_manifest"]):
            require(self.config.get("source_verified_manifest") is None, "source-verified manifest has no verification report")
            return
        selection = self.result["selection"]
        require(selection is not None, "source verification has no validated deterministic selection")
        report = self.read(self.path("source_verification_report"))
        verified_path = self.path("source_verified_manifest", self.path("source_verification_report").parent / "manifest.json")
        verified = self.read(verified_path)
        frozen = self.read(self.path("frozen_manifest"))
        require(report.get("schema_version") == 1 and report.get("status") == "complete" and report.get("evidence_stage") == "combined_source_patch_kernel_checked_with_fresh_outputs", "combined patch has no complete source verification")
        require(report.get("input_manifest_sha256") == self.hash(self.path("selector_manifest")), "source verification used a different selection")
        require(report.get("final_manifest_sha256") == self.hash(verified_path), "source-verified manifest hash mismatch")
        require(verified.get("selection_status") == "source-verified-trial" and frozen.get("selection_status") == "frozen", "patch selection has not passed verification and freeze")
        require(all(verified.get(key) == value for key, value in selection["manifest"].items() if key != "selection_status"), "verification changed the selected patch")
        require(all(frozen.get(key) == value for key, value in verified.items() if key != "selection_status"), "frozen patch differs from source-verified patch")
        prepared, account = BENCHMARK.prepare_sources(frozen, self.source_root)
        patch_sha = hashlib.sha256(patch_bytes(prepared)).hexdigest()
        require(report.get("patch_sha256") == patch_sha and report.get("accounting") == account, "compiled patch or accounting mismatch")
        require(report.get("mathlib_revision") == frozen["mathlib_revision"] == self.result["census"]["manifest"]["mathlib_revision"], "source verification revision mismatch")
        evidence = verified.get("source_verification", {})
        require(evidence.get("patch_sha256") == patch_sha and evidence.get("input_manifest_sha256") == report["input_manifest_sha256"], "manifest source-verification link mismatch")
        require(report.get("input_sha256", {}).get(recorded_name(self.path("selector_manifest"))) == report["input_manifest_sha256"], "verification does not freeze its selected input manifest")
        self.fingerprints(report.get("input_sha256"))
        if self.study_mode == "composed_expansion":
            from expansion import body_evidence
            body_evidence(self, report, frozen, require)
            implementation = report.get("project_lean_sources", {})
            require(implementation and all(name.endswith(".lean") for name in implementation),
                    "composed source verification has no implementation inventory")
            for name, digest in implementation.items():
                require(report["input_sha256"].get(recorded_name(self.root / name)) == digest,
                        "composed implementation is not frozen in source verification")
            targeted = self.result["targeted"]["manifest"]
            require(all(implementation.get(name) == digest for name, digest in targeted["implementation_sha256"].items()
                        if name.endswith(".lean")), "targeted discovery used a different final implementation")
            require(all(report["input_sha256"].get(recorded_name(self.root / name)) == digest
                        for name, digest in targeted["environment_sha256"].items()),
                    "targeted discovery used a different final configuration")
        else:
            implementation = self.result["census"]["manifest"]["implementation_sha256"]
        require(all(report.get("project_lean_sources", {}).get(name) == digest for name, digest in implementation.items() if name.endswith(".lean")), "source verification used a different tactic implementation")
        rows = report.get("files", [])
        paths = [source["path"] for source in prepared]
        require(rows and len(rows) == len(paths) and {row["path"] for row in rows} == set(paths), "source verification omitted affected files")
        for row in rows:
            source = next(source for source in prepared if source["path"] == row["path"])
            ids = sorted(item["id"] for item in frozen["candidates"] if item["status"] == "replace" and item["path"] == row["path"])
            require(row.get("status") == "verified" and row.get("candidate_ids") == ids, "selected edits are not all source-verified")
            require(row.get("original_source_sha256") == hashlib.sha256(source["original"].encode()).hexdigest() and row.get("replacement_source_sha256") == hashlib.sha256(source["replacement"].encode()).hexdigest(), "verified source bytes differ from the patch")
            process = row.get("process", {})
            require(process.get("returncode") == 0 and process.get("timed_out") is False, "failed source-verification compiler process")
            artifacts = row.get("artifact_sha256", {})
            require(all(any(name.endswith(suffix) for name in artifacts) for suffix in [".olean", ".ilean", ".c"]), "verification lacks fresh compiler artifacts")
            for name in artifacts:
                path = Path(name)
                path = path if path.is_absolute() else self.root / path
                require(self.actual(path).is_file() and self.actual(path).stat().st_size > 0,
                        "empty compiler artifact: " + name)
            self.fingerprints(artifacts)
        self.result["patch"] = {"accounting": account, "affected_files": paths, "manifest": frozen,
                                "patch_sha256": patch_sha, "verification": report,
                                "implementation_costs": BENCHMARK.implementation_line_costs(self.project_source_root)}
        self.result["stages"].append("source-verification")

    def timing(self):
        if not self.group(["confirmatory_report", "confirmatory_analysis_plan", "confirmatory_measurements"]):
            return
        patch = self.result["patch"]
        require(patch is not None, "timing has no validated compiled frozen patch")
        report = self.read(self.path("confirmatory_report"))
        plan = self.read(self.path("confirmatory_analysis_plan"))
        rows = self.read(self.path("confirmatory_measurements"), lines=True)
        inference, provenance = report.get("inference", {}), report.get("provenance", {})
        require(report.get("schema_version") == 1 and report.get("status") == "complete" and report.get("selection_status") == "frozen", "benchmark is incomplete or selection is not frozen")
        require(inference.get("mode") == plan.get("mode") == "confirmatory" and inference.get("calibration_validated") is True and inference.get("inputs_unchanged") is True, "timing is not validated confirmatory evidence")
        require(report.get("manifest") == patch["manifest"] and provenance.get("manifest_sha256") == self.hash(self.path("frozen_manifest")), "timing used a different frozen manifest")
        require(provenance.get("proposed_patch_sha256") == patch["patch_sha256"] and report.get("accounting") == patch["accounting"], "timing used a different source patch")
        require(report.get("analysis_plan", {}).get("sha256") == self.hash(self.path("confirmatory_analysis_plan")), "analysis-plan hash mismatch")
        require(plan.get("selection_status") == "frozen" and plan.get("all_affected_files_and_pairs_retained") is True and plan.get("affected_files") == patch["affected_files"], "analysis plan omits affected files or samples")
        require(all(provenance.get(key) == value for key, value in plan.get("provenance", {}).items()), "benchmark provenance changed after plan freeze")
        require(plan.get("input_sha256", {}).get(recorded_name(self.path("frozen_manifest"))) == provenance["manifest_sha256"], "analysis plan does not freeze the measured manifest")
        self.fingerprints(plan.get("input_sha256"))
        self.fingerprints(report.get("resolved_setup_sha256"))
        require(report.get("resolved_calibration_match") is True and report.get("resolved_runtime") == plan.get("calibration", {}).get("resolved_runtime") and bool(report.get("resolved_runtime", {}).get("variants")), "resolved runtime differs from calibrated pilot")
        calibration = plan.get("calibration", {})
        if self.bundle is None:
            current_runtime = BENCHMARK.resolved_runtime_provenance(
                report, self.root, self.path("confirmatory_report").parent, report["resolved_setup_sha256"])
            require(current_runtime == report["resolved_runtime"], "resolved runtime provenance differs from the saved setup files")
            calibrated = BENCHMARK.validate_calibration(Path(calibration["path"]), provenance, patch["affected_files"])
            require(calibrated == calibration, "confirmatory calibration lineage differs from the frozen plan")
        artifact = self.read(Path(calibration["path"]))
        require(self.hash(Path(calibration["path"])) == calibration["sha256"] and artifact.get("block_pairs") == calibration.get("block_pairs"), "calibration artifact differs from its frozen reference")
        pilot = self.read(Path(calibration["pilot_report"]["path"]))
        pilot_rows = self.read(Path(calibration["pilot_measurements"]["path"]), lines=True)
        for key in ["pilot_report", "pilot_measurements"]:
            require(self.hash(Path(calibration[key]["path"])) == calibration[key]["sha256"], "pilot reference hash mismatch")
        require(pilot.get("status") == "complete" and pilot.get("selection_status") == "frozen" and pilot_rows == pilot.get("measurements"), "portable pilot evidence is incomplete or inconsistent")
        require(all(pilot.get("provenance", {}).get(key) == provenance.get(key) for key in BENCHMARK.CALIBRATION_MATCH_KEYS), "pilot workload differs from confirmatory workload")
        require(pilot.get("resolved_runtime") == report["resolved_runtime"], "pilot and confirmatory runtime provenance differ")
        require([row["path"] for row in pilot.get("summary", {}).get("files", [])] == patch["affected_files"], "pilot affected-file set differs")
        BENCHMARK.paired_blocks(pilot_rows, patch["affected_files"], pilot["provenance"]["repetitions"], calibration["block_pairs"])
        require(rows == report.get("measurements"), "benchmark report differs from raw samples")
        count = provenance.get("repetitions")
        require(type(count) is int and count == plan.get("measured_pairs"), "measured sample count differs from frozen plan")
        require(provenance.get("warmups") == plan.get("warmup_pairs") and provenance.get("warmups", 0) >= 1, "warmup count differs from frozen plan")
        require(all(row.get("phase") in {"warmup", "measured"} for row in rows), "unexpected benchmark phase")
        warmups = [dict(row, phase="measured") for row in rows if row["phase"] == "warmup"]
        BENCHMARK.paired_totals(warmups, patch["affected_files"], provenance["warmups"])
        expected_order = [(pair, variant) for pair in range(provenance["warmups"])
                          for variant in (["original", "replacement"] if pair % 2 == 0 else ["replacement", "original"])
                          for _ in patch["affected_files"]]
        require([(row["pair"], row["variant"]) for row in warmups] == expected_order, "warmup variant order differs from the fixed protocol")
        interval = plan.get("interval", {})
        require(interval.get("method") == "paired_nonoverlapping_equal_block_BCa" and interval.get("confidence_level") == 0.95 and interval.get("resamples", 0) >= 10000, "unexpected confirmatory interval protocol")
        require(interval.get("block_pairs") == calibration["block_pairs"], "confirmatory interval differs from the calibrated block size")
        require(plan.get("primary_statistic") == "ratio_of_mean_pass_totals" and
                plan.get("pair_order") == "even: original then replacement; odd: replacement then original",
                "frozen analysis contract differs from the benchmark protocol")
        fixed_interval = {"bias_ties": "half_weight", "quantile": "linear_interpolation_at_p_times_n_minus_one",
                          "acceleration": "delete_one_whole_block_jackknife",
                          "success": "valid calibrated interval with lower endpoint strictly greater than one"}
        require(all(interval.get(key) == value for key, value in fixed_interval.items()),
                "frozen interval analysis contract differs from the benchmark protocol")
        paths = patch["affected_files"]
        require(report.get("summary") == BENCHMARK.summarize(rows, paths, count), "benchmark summary differs from raw samples")
        expected = BENCHMARK.confirmatory_statistics(rows, paths, count, interval["block_pairs"], interval["resamples"], interval["seed"])
        require(all(inference.get(key) == value for key, value in expected.items()), "confirmatory estimate, interval, or gate differs from raw samples")
        require(provenance.get("mathlib_revision") == patch["manifest"]["mathlib_revision"], "benchmark revision mismatch")
        census = self.result["census"]["manifest"]
        implementation = patch["verification"]["project_lean_sources"] if self.study_mode == "composed_expansion" else census["implementation_sha256"]
        require(all(provenance.get("project_lean_sources", {}).get(name) == digest for name, digest in implementation.items() if name.endswith(".lean")), "benchmark used a different tactic implementation")
        for name, key in [("lakefile.toml", "project_lakefile_sha256"), ("lake-manifest.json", "project_lake_manifest_sha256"), ("lean-toolchain", "project_toolchain_sha256")]:
            environment_expected = patch["verification"]["input_sha256"].get(recorded_name(self.root / name)) if self.study_mode == "composed_expansion" else census["environment_sha256"].get(name)
            require(provenance.get(key) == environment_expected, "benchmark and verified environments differ: " + name)
        if self.study_mode == "composed_expansion":
            executables = provenance.get("compiler_executables", {})
            require(executables and executables == report["resolved_runtime"].get("compiler_executables") and
                    provenance.get("python_version") == report["resolved_runtime"].get("python_version"),
                    "expanded timing lacks compiler or Python runtime lineage")
            for name, digest in executables.items():
                require(report["resolved_setup_sha256"].get(name) == digest,
                        "expanded compiler executable is not frozen")
            for row in rows:
                artifacts = row.get("artifact_sha256", {})
                require(row.get("compilation_status") == "verified" and
                        all(any(name.endswith(suffix) for name in artifacts) for suffix in [".olean", ".ilean", ".c"]) and
                        all(isinstance(digest, str) and re.fullmatch(r"[0-9a-f]{64}", digest) for digest in artifacts.values()),
                        "expanded timing row lacks fresh compilation evidence")
        for key in ["tactic_implementation_code_lines", "census_implementation_code_lines"]:
            require(type(provenance.get(key)) is int and provenance[key] == patch["implementation_costs"][key], "missing or mismatched separate implementation code cost: " + key)
        per_file = []
        for path in paths:
            values = {variant: [row["seconds"] for row in rows if row["phase"] == "measured" and row["path"] == path and row["variant"] == variant] for variant in ["original", "replacement"]}
            original, replacement = (sum(values[key]) / count for key in ["original", "replacement"])
            per_file.append({"path": path, "original_mean_seconds": original, "replacement_mean_seconds": replacement, "ratio": original / replacement})
        self.result["timing"] = {**expected, "files": per_file, "report": report,
                                 "tactic_implementation_code_lines": provenance["tactic_implementation_code_lines"],
                                 "census_implementation_code_lines": provenance["census_implementation_code_lines"]}
        self.result["stages"].append("confirmatory-timing")

    def load(self):
        self.census()
        if self.study_mode == "composed_expansion":
            from expansion import targeted_discovery
            targeted_discovery(self, require, canonical_sha)
        self.selection()
        self.verification()
        self.timing()
        if self.config.get("claim_speedup"):
            require(self.result["timing"] is not None and self.result["timing"]["success_criterion_met"] is True, "speed claim requested without a passing confirmatory gate")
        return self.result


def evidence_facts(result):
    facts = {"stages": result["stages"], "census": {"summary": result["census"]["summary"], "unknown_due_incomplete_file": result["census"]["unknown_due_incomplete_file"]} if result["census"] else None,
            "selection": result["selection"]["summary"] if result["selection"] else None,
            "patch": {key: result["patch"][key] for key in ["accounting", "affected_files", "patch_sha256", "implementation_costs"]} if result["patch"] else None,
            "timing": {key: value for key, value in result["timing"].items() if key != "report"} if result["timing"] else None}
    if result.get("targeted") is not None:
        facts["targeted"] = {key: result["targeted"][key] for key in ["summary", "unknown_due_incomplete_file"]}
    return facts


def validate_bundle(directory, expected):
    directory = directory.resolve()
    receipt_path = directory / "bundle.json"
    require(file_sha(receipt_path) == expected, "portable evidence receipt hash mismatch")
    receipt = json.loads(receipt_path.read_bytes())
    require(receipt.get("schema_version") == 1 and receipt.get("validation_mode") == "strict-live-export", "unsupported or unvalidated evidence bundle")
    for name, item in receipt["inventory"].items():
        path = directory / name
        require(not Path(name).is_absolute() and ".." not in Path(name).parts and path.resolve().is_relative_to(directory), "unsafe evidence bundle path")
        require(path.is_file() and not path.is_symlink() and path.stat().st_size == item["bytes"] and file_sha(path) == item["sha256"], "portable payload changed or missing: " + name)
    require(all(name in receipt["inventory"] for name in receipt["copied_inputs"].values()), "portable input is absent from the byte inventory")
    example = receipt["paper_inputs"]["examples_object"]
    require(example in receipt["inventory"] and receipt["inventory"][example]["bytes"] > 0 and
            (directory / example).stat().st_size > 0, "empty checked-example object in portable evidence")
    return receipt


def load_evidence(config, root=ROOT):
    try:
        if config.get("evidence_bundle") is not None:
            require(not any(config.get(key) is not None for key in PATH_KEYS), "portable mode cannot mix live evidence paths")
            restore_configured_bundle(config, root)
            name = Path(config["evidence_bundle"])
            directory = name if name.is_absolute() else root / name
            receipt = validate_bundle(directory, config.get("evidence_bundle_sha256"))
            model = Evidence(receipt["configuration"], root, bundle=directory.resolve(), receipt=receipt)
            result = model.load()
            require(canonical_sha(evidence_facts(result)) == receipt["validated_facts_sha256"], "portable evidence recomputation differs from export-time validation")
            result["validation_context"] = "Portable bundle: runtime/import input bytes were checked at export; copied evidence and proof outputs were checked again."
            result["bundle_sha256"] = config["evidence_bundle_sha256"]
            result["paper_inputs"] = {key: directory.resolve() / name if key != "implementation_sha256" else name
                                      for key, name in receipt["paper_inputs"].items()}
            result["paper_metadata"] = receipt["configuration"].get("paper_metadata", {})
            if config.get("claim_speedup"):
                require(result["timing"] and result["timing"]["success_criterion_met"], "speed claim requested without a passing confirmatory gate")
            return result
        require(config.get("evidence_bundle_sha256") is None, "bundle receipt hash has no bundle path")
        result = Evidence(config, root).load()
        result["validation_context"] = "Live evidence: the listed stages were checked in this workspace; no absent stage is inferred."
        return result
    except (OSError, KeyError, TypeError, subprocess.SubprocessError, BENCHMARK.BenchmarkError, TransportError) as error:
        raise EvidenceError(f"invalid paper evidence: {error}") from error


def export_bundle(config, destination, root=ROOT):
    require(config.get("evidence_bundle") is None, "bundle export requires strict live evidence")
    model = Evidence(config, root)
    result = model.load()
    expected_stages = ["census", "selection", "source-verification", "confirmatory-timing"]
    if model.study_mode == "composed_expansion":
        expected_stages.insert(1, "targeted-discovery")
    require(result["stages"] == expected_stages, "final bundle needs every validated evidence stage")
    require(not destination.exists(), "evidence bundle destination must not exist")
    destination.parent.mkdir(parents=True, exist_ok=True)
    temporary = Path(tempfile.mkdtemp(prefix=".paper-evidence-", dir=destination.parent))
    copied, inventory = {}, {}

    def copy(path, relative=None):
        path = path.resolve()
        name = recorded_name(path)
        if name in copied:
            return
        relative = relative or "records/" + hashlib.sha256(name.encode()).hexdigest() + path.suffix
        target = temporary / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, target)
        digest = file_sha(target)
        require(file_sha(path) == digest, "evidence changed while copying: " + name)
        if name in model.inputs:
            require(model.inputs[name] == digest, "evidence changed after validation: " + name)
        if name in model.verified_hashes:
            require(model.verified_hashes[name] == digest, "verified artifact changed after validation: " + name)
        copied[name] = relative
        inventory[relative] = {"sha256": digest, "bytes": target.stat().st_size}

    try:
        for name in model.inputs:
            copy(Path(name))
        manifest = result["census"]["manifest"]
        snapshots = {**manifest["implementation_sha256"], **manifest["environment_sha256"]}
        census_directory = model.path("census_manifest").parent
        for name in snapshots:
            copy(census_directory / "frozen-implementation" / name)
            if model.study_mode != "composed_expansion" and (name.startswith("NormArith") or name in manifest["environment_sha256"]):
                path = temporary / "project" / name
                path.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(census_directory / "frozen-implementation" / name, path)
                inventory[str(path.relative_to(temporary))] = {"sha256": file_sha(path), "bytes": path.stat().st_size}
        if model.study_mode == "composed_expansion":
            current_sources = result["patch"]["verification"]["project_lean_sources"]
            for name in [*current_sources, "lakefile.toml", "lake-manifest.json", "lean-toolchain"]:
                copy(model.root / name, "project/" + name)
            targeted_directory = model.path("targeted_archive").parent
            targeted_inventory = model.read(targeted_directory / "inventory.json")
            for name in targeted_inventory:
                if name != "raw.tar.gz":
                    copy(targeted_directory / name, "targeted-archive/" + name)
        archive_path = model.path("census_archive", census_directory / "archive.json")
        archive_inventory = model.read(archive_path.parent / "inventory.json")
        for name in archive_inventory["files"]:
            copy(archive_path.parent / name, "census-archive/" + name)
        source_paths = {item["path"] for item in result["selection"]["manifest"]["files"]}
        proposal_rows = model.read(archive_path.parent / "proposals.jsonl", lines=True)
        source_hashes = {item["path"]: item["sha256"] for item in manifest["files"]}
        for record in proposal_rows:
            proposal = record.get("proposal", {})
            if proposal.get("path") in source_hashes and proposal.get("source_sha256") == source_hashes[proposal["path"]]:
                source_paths.add(proposal["path"])
        for name in sorted(source_paths):
            copy(model.mathlib / name, "mathlib/" + name)
        for row in result["patch"]["verification"]["files"]:
            for index, name in enumerate(row["artifact_sha256"]):
                relative = "verification-artifacts/" + row["path"][:-5] + "/" + str(index) + Path(name).suffix
                copy(Path(name), relative)
        for key in ["source_verification_report", "confirmatory_report"]:
            patch_path = model.path(key).parent / "mathlib.patch"
            require(file_sha(patch_path) == result["patch"]["patch_sha256"], "saved source patch differs from verified patch")
            copy(patch_path)
        reports = [result["patch"]["verification"], result["timing"]["report"]]
        calibration = model.read(model.path("confirmatory_analysis_plan"))["calibration"]
        reports.append(model.read(Path(calibration["pilot_report"]["path"])))
        for report in reports:
            for records in report.get("source_header_setups", {}).values():
                for record in records.values():
                    for key in ["header_file", "raw_setup_file", "setup_file"]:
                        if key in record:
                            copy(Path(record[key]))
        pilot_report_path = model.root / "benchmarks/results/report.json"
        pilot_manifest_path = model.root / "benchmarks/results/manifest.json"
        pilot_report, pilot_manifest = model.read(pilot_report_path), model.read(pilot_manifest_path)
        require(pilot_report.get("status") == "complete" and pilot_manifest.get("mathlib_revision") == manifest["mathlib_revision"], "archived pilot is incomplete or has a different pinned revision")
        pilot_candidate = next(item for item in pilot_manifest["candidates"] if item["id"] == "fderiv-telescope")
        pilot_source = model.mathlib / pilot_candidate["path"]
        original = "".join(pilot_source.read_text().splitlines(keepends=True)[pilot_candidate["start_line"] - 1:pilot_candidate["end_line"]])
        require(hashlib.sha256(original.encode()).hexdigest() == pilot_candidate["original_sha256"], "archived pilot source block differs")
        source = model.root / "NormArithTest/Paper.lean"
        check_path, object_path = model.root / "paper/output/lean-check.json", model.root / "paper/tmp/lean/Paper.olean"
        check = model.read(check_path)
        program_hash = implementation_sha(model.root)
        require(check.get("returncode") == 0 and check.get("source_sha256") == file_sha(source) and check.get("implementation_sha256") == program_hash, "paper examples have no current successful Lean check")
        require(object_path.is_file() and object_path.stat().st_size > 0, "paper example check has no nonempty compiled object")
        paper_paths = {"pilot_report": pilot_report_path, "pilot_manifest": pilot_manifest_path, "pilot_source": pilot_source,
                       "examples_source": source, "examples_check": check_path, "examples_object": object_path}
        for key, spec in config.get("paper_metadata", {}).items():
            path = root / spec["path"]
            require(path.is_file() and file_sha(path) == spec["sha256"], "paper metadata changed: " + key)
            paper_paths["metadata_" + key] = path
        paper_paths["final_analysis_plan"] = model.path("confirmatory_analysis_plan")
        for key, path in paper_paths.items():
            copy(path, "paper-inputs/" + key + path.suffix)
        paper_inputs = {key: copied[recorded_name(path.resolve())] for key, path in paper_paths.items()}
        paper_inputs["implementation_sha256"] = program_hash
        tools = ["paper/evidence.py", "paper/generate.py", "paper/evidence_transport.py", "scripts/benchmark.py", "scripts/verify_selection.py", "scripts/select_census.py", "scripts/census.py"]
        if model.study_mode == "composed_expansion":
            tools += ["paper/expansion.py", "scripts/select_expansion.py"]
        for name in tools:
            path = ROOT / name
            copy(path, "tools/" + name)
        for name, digest in model.verified_hashes.items():
            require(Path(name).is_file() and file_sha(Path(name)) == digest, "verified input changed before bundle publication: " + name)
        configuration = dict(config)
        for key in PATH_KEYS:
            configuration[key] = str(model.path(key)) if config.get(key) is not None else None
        receipt = {"schema_version": 1, "validation_mode": "strict-live-export", "exported_at_utc": datetime.now(timezone.utc).isoformat(), "original_project": str(model.root),
                   "runtime_verification": "Runtime/import bytes checked at export; their complete hash inventory is retained. Dependency binaries need not be copied for paper rebuilding.",
                   "verified_mathlib_revision": manifest["mathlib_revision"], "verified_source_universe_sha256": canonical_sha(manifest["files"]),
                   "configuration": configuration, "copied_inputs": copied, "inventory": inventory, "paper_inputs": paper_inputs,
                   "verified_input_sha256": model.verified_hashes, "validated_facts_sha256": canonical_sha(evidence_facts(result))}
        (temporary / "bundle.json").write_text(json.dumps(receipt, indent=2) + "\n")
        expected = file_sha(temporary / "bundle.json")
        validate_bundle(temporary, expected)
        portable = {"evidence_bundle": str(temporary), "evidence_bundle_sha256": expected}
        load_evidence(portable, root)
        os.rename(temporary, destination)
        return {"evidence_bundle": str(destination), "evidence_bundle_sha256": expected}
    finally:
        if temporary.exists():
            shutil.rmtree(temporary)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--status", type=Path, default=ROOT / "paper/status.json")
    parser.add_argument("--export", type=Path, required=True, help="new portable bundle directory after strict live validation")
    args = parser.parse_args()
    config = json.loads(args.status.read_bytes())
    try:
        print(json.dumps(export_bundle(config, args.export.resolve()), indent=2))
    except (EvidenceError, OSError, KeyError, TypeError, BENCHMARK.BenchmarkError) as error:
        raise SystemExit("paper evidence: " + str(error)) from error


if __name__ == "__main__":
    main()
