"""Synthetic adapter fixtures; these files are never manuscript evidence."""

import copy
from datetime import datetime, timezone
import importlib.util
import json
from pathlib import Path
import subprocess
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

import generate

import evidence

SPEC = importlib.util.spec_from_file_location("paper_fixture_benchmark", Path(__file__).resolve().parents[1] / "scripts/benchmark.py")
BENCHMARK = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BENCHMARK)


def dump(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + "\n")
    return path


class EvidenceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.mathlib = self.root / ".lake/packages/mathlib"
        self.path = "Mathlib/SyntheticFixture.lean"
        source = "import Mathlib.Init\nexample : True := by\n  change True\n  trivial\n"
        target = self.mathlib / self.path
        target.parent.mkdir(parents=True)
        target.write_text(source)
        subprocess.run(["git", "init", "-q", str(self.mathlib)], check=True)
        subprocess.run(["git", "-C", str(self.mathlib), "add", "."], check=True)
        subprocess.run(["git", "-C", str(self.mathlib), "-c", "user.name=Fixture", "-c", "user.email=fixture@example.org", "commit", "-qm", "synthetic fixture"], check=True)
        self.revision = subprocess.check_output(["git", "-C", str(self.mathlib), "rev-parse", "HEAD"], text=True).strip()
        for name, text in {"NormArith.lean": "-- synthetic implementation\n", "lean-toolchain": "lean:synthetic\n", "lake-manifest.json": "{}\n", "lakefile.toml": 'name="synthetic"\n'}.items():
            (self.root / name).write_text(text)
        self.config = dict.fromkeys(evidence.PATH_KEYS)
        self.config.update(claim_speedup=False, description="Synthetic adapter fixture; not manuscript evidence.")
        self.census = self.root / "synthetic-census"
        implementation = {"NormArith.lean": evidence.file_sha(self.root / "NormArith.lean")}
        environment = {name: evidence.file_sha(self.root / name) for name in ["lean-toolchain", "lake-manifest.json", "lakefile.toml"]}
        protocol = {"config": {"synthetic_fixture": True}, "implementation_sha256": implementation,
                    "environment_sha256": environment, "mathlib_revision": self.revision,
                    "selected_files": [self.path], "extractor_binary_sha256": "a" * 64}
        self.census_manifest = dict(protocol, schema_version=1, scope="full", protocol_hash=evidence.canonical_sha(protocol),
                                    files=[{"path": self.path, "sha256": evidence.file_sha(target)}])
        self.result = {"path": self.path, "source_sha256": evidence.file_sha(target), "status": "complete", "complete": True,
                       "counts": {}, "attempt_status_counts": {"success": 1, "failed": 5}, "eligible_observations": 6,
                       "successful_proposals": 1, "original_observation_fragment_counts": {"core": 6},
                       "original_eligible_fragment_counts": {"core": 6},
                       "attempt_status_counts_by_original_fragment": {"core": {"success": 1, "failed": 5}}, "resource_tier": 1}
        self.summary = {"schema_version": 1, "scope": "full", "protocol_hash": self.census_manifest["protocol_hash"],
                        "frozen_inputs_verified": True, "full_universe_processed": True, "full_universe_completed": True,
                        "universe_files": 1, "selected_files": 1, "processed_files": 1, "completed_files": 1,
                        "failed_files": 0, "unprocessed_files": 0, "file_status_counts": {"complete": 1},
                        "resource_tier_counts": {"1": 1}, "evidence_stage": "isolated_kernel_checked_proposals_not_compiled_patches",
                        **{key: self.result[key] for key in ["counts", "attempt_status_counts", "eligible_observations", "successful_proposals", "original_observation_fragment_counts", "original_eligible_fragment_counts", "attempt_status_counts_by_original_fragment"]}}
        self.put("census_manifest", self.census / "manifest.json", self.census_manifest)
        self.put("census_summary", self.census / "summary.json", self.summary)
        self.put("census_integrity", self.census / "integrity.json", {"status": "valid", "protocol_hash": self.census_manifest["protocol_hash"]})
        dump(self.census / "files/Mathlib.SyntheticFixture/result.json", self.result)
        for name in [*implementation, *environment]:
            destination = self.census / "frozen-implementation" / name
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes((self.root / name).read_bytes())
        self.archive_census()
        original = "".join(source.splitlines(keepends=True)[1:])
        self.selection = {"schema_version": 1, "mathlib_revision": self.revision, "selection_status": "integration-trial",
                          "census_protocol_hash": self.census_manifest["protocol_hash"], "synthetic_fixture": True,
                          "files": [{"path": self.path, "source_sha256": evidence.file_sha(target), "imports": ["NormArith"], "helpers": []}],
                          "candidates": [{"id": "synthetic-only", "path": self.path, "declaration": "example", "status": "replace", "reason": "selected",
                                          "start_line": 2, "end_line": 4, "original_sha256": BENCHMARK.sha256(original),
                                          "replacement": "example : True := by norm_arith\n"}]}
        self.prepared, self.account = BENCHMARK.prepare_sources(self.selection, self.mathlib)
        self.put("selector_manifest", self.root / "synthetic-selection/manifest.json", self.selection)
        self.put("selector_summary", self.root / "synthetic-selection/summary.json", {"evidence_stage": "selected_isolated_proposals_not_source_compiled", "accounting": self.account, "outcome_counts": {"selected": 1}})
        ledger = self.root / "synthetic-selection/selection.jsonl"
        ledger.write_text(json.dumps({"id": "synthetic-only", "path": self.path, "outcome": "selected", "proof_lines_saved": 2}) + "\n")
        self.config["selector_ledger"] = str(ledger.relative_to(self.root))
        self.verification = self.root / "synthetic-verification"
        self.verification.mkdir()
        patch = evidence.patch_bytes(self.prepared)
        (self.verification / "mathlib.patch").write_bytes(patch)
        artifacts = []
        for suffix in [".olean", ".ilean", ".c"]:
            artifact = self.verification / ("synthetic" + suffix)
            artifact.write_text("SYNTHETIC UNIT-TEST ARTIFACT; NOT LEAN EVIDENCE")
            artifacts.append(artifact)
        self.verified = dict(self.selection, selection_status="source-verified-trial", source_verification={
            "path": str(self.verification / "verification.json"), "input_manifest_sha256": evidence.file_sha(self.root / self.config["selector_manifest"]), "patch_sha256": BENCHMARK.sha256(patch)})
        dump(self.verification / "manifest.json", self.verified)
        self.verification_report = {"schema_version": 1, "status": "complete", "evidence_stage": "combined_source_patch_kernel_checked_with_fresh_outputs",
                                    "mathlib_revision": self.revision, "input_manifest_sha256": evidence.file_sha(self.root / self.config["selector_manifest"]),
                                    "patch_sha256": BENCHMARK.sha256(patch), "final_manifest_sha256": evidence.file_sha(self.verification / "manifest.json"),
                                    "accounting": self.account, "project_lean_sources": implementation, "input_sha256": {str((self.root / self.config["selector_manifest"]).resolve()): evidence.file_sha(self.root / self.config["selector_manifest"])},
                                    "files": [{"path": self.path, "status": "verified", "candidate_ids": ["synthetic-only"],
                                               "original_source_sha256": evidence.file_sha(target), "replacement_source_sha256": BENCHMARK.sha256(self.prepared[0]["replacement"]),
                                               "process": {"returncode": 0, "timed_out": False}, "artifact_sha256": {str(path): evidence.file_sha(path) for path in artifacts}}]}
        self.put("source_verification_report", self.verification / "verification.json", self.verification_report)
        self.frozen = dict(self.verified, selection_status="frozen")
        self.put("frozen_manifest", self.root / "synthetic-frozen/manifest.json", self.frozen)

    def test_expansion_mode_requires_its_targeted_evidence(self):
        self.config["study_mode"] = "composed_expansion"
        with self.assertRaisesRegex(evidence.EvidenceError, "targeted discovery"):
            self.load()

    def test_unknown_study_mode_is_rejected(self):
        self.config["study_mode"] = "unknown-study"
        with self.assertRaisesRegex(evidence.EvidenceError, "study mode"):
            self.load()

    def test_undefined_interval_stays_reportable_in_generated_facts(self):
        result = {"census": None, "patch": None,
                  "timing": {"estimate": 1.0, "interval": {"status": "undefined", "lower": None, "upper": None},
                             "original_mean_seconds": 1.0, "replacement_mean_seconds": 1.0}}
        with tempfile.TemporaryDirectory() as directory, patch.object(generate, "GENERATED", Path(directory)):
            generate.study_data({"example_candidate_id": None}, result)
            self.assertIn("undefined", (Path(directory) / "study-facts.tex").read_text())

    def test_generated_net_savings_label_describes_saved_lines(self):
        result = self.load()
        with tempfile.TemporaryDirectory() as directory, patch.object(generate, "GENERATED", Path(directory)):
            generate.final_tables(result)
            self.assertIn("Net lines saved after helpers and imports",
                          (Path(directory) / "census-table.tex").read_text())

    def paper_inputs(self, expanded=False):
        pilot_manifest = copy.deepcopy(self.selection)
        pilot_manifest["candidates"][0]["id"] = "fderiv-telescope"
        dump(self.root / "benchmarks/results/manifest.json", pilot_manifest)
        dump(self.root / "benchmarks/results/report.json", dict(self.timing_report, synthetic_fixture=True))
        source = self.root / "NormArithTest/Paper.lean"
        source.parent.mkdir(exist_ok=True)
        source.write_text("-- Synthetic unit-test text; this fixture does not invoke Lean.\n" + "".join(
            f"-- paper:begin {name}\nexample : True := by trivial\n-- paper:end {name}\n"
            for name in (["hidden", "reverse", "mathlib", "boundary", "quantified", "metric"] if expanded else ["hidden", "reverse", "mathlib", "boundary"])))
        dump(self.root / "paper/output/lean-check.json", {"synthetic_fixture": True, "returncode": 0,
             "source_sha256": evidence.file_sha(source), "implementation_sha256": evidence.implementation_sha(self.root)})
        artifact = self.root / "paper/tmp/lean/Paper.olean"
        artifact.parent.mkdir(parents=True)
        artifact.write_text("SYNTHETIC UNIT-TEST ARTIFACT; NOT A LEAN PROOF")

    def archive_census(self):
        archive = self.root / "synthetic-census-archive"
        archive.mkdir(exist_ok=True)
        for name in ["manifest.json", "summary.json", "integrity.json"]:
            shutil.copyfile(self.census / name, archive / name)
        result = json.loads((self.census / "files/Mathlib.SyntheticFixture/result.json").read_bytes())
        shutil.copytree(self.census / "frozen-implementation", archive / "frozen-implementation", dirs_exist_ok=True)
        (archive / "file-outcomes.jsonl").write_text(json.dumps({"result_file": "files/Mathlib.SyntheticFixture/result.json", "result": result}) + "\n")
        (archive / "attempt-outcomes.jsonl").write_text("")
        (archive / "proposals.jsonl").write_text("")
        dump(archive / "source-inventory.json", {"schema_version": 1, "files": {"files/Mathlib.SyntheticFixture/result.json": {"sha256": evidence.file_sha(self.census / "files/Mathlib.SyntheticFixture/result.json")}}})
        for name in ["archive_census.py", "census.py"]:
            (archive / "archive-tools").mkdir(exist_ok=True)
            shutil.copyfile(Path(__file__).resolve().parents[1] / "scripts" / name, archive / "archive-tools" / name)
        summary = json.loads((self.census / "summary.json").read_bytes())
        report = {"schema_version": 1, "status": "validated_full_universe_archive", "synthetic_fixture": True,
                  "protocol_hash": self.census_manifest["protocol_hash"], "mathlib_revision": self.revision,
                  "archiver_sha256": evidence.file_sha(archive / "archive-tools/archive_census.py"),
                  "validation_helper_sha256": evidence.file_sha(archive / "archive-tools/census.py"),
                  **{key: summary[key] for key in ["processed_files", "completed_files", "failed_files", "full_universe_processed", "full_universe_completed", "frozen_inputs_verified", "successful_proposals", "file_status_counts"]}}
        dump(archive / "archive.json", report)
        dump(archive / "inventory.json", {"schema_version": 1, "files": {str(path.relative_to(archive)): {"sha256": evidence.file_sha(path), "bytes": path.stat().st_size} for path in archive.rglob("*") if path.is_file() and path.name != "inventory.json"}})
        self.config["census_archive"] = str((archive / "archive.json").relative_to(self.root))

    def put(self, key, path, value):
        dump(path, value)
        self.config[key] = str(path.relative_to(self.root))

    def load(self):
        return evidence.load_evidence(self.config, self.root)

    def add_timing(self, pairs=None, *, expanded=False, block_pairs=2, seed=42):
        pairs = pairs or [(2, 1), (2, 1), (4, 1), (4, 1), (9, 1), (9, 1)]
        output = self.root / "synthetic-timing"
        output.mkdir()
        (output / "mathlib.patch").write_bytes(evidence.patch_bytes(self.prepared))
        provenance = {key: "synthetic fixture" for key in BENCHMARK.CALIBRATION_MATCH_KEYS}
        provenance.update(mathlib_revision=self.revision, manifest_sha256=evidence.file_sha(self.root / self.config["frozen_manifest"]),
                          proposed_patch_sha256=self.verification_report["patch_sha256"],
                          project_lean_sources=copy.deepcopy(self.verification_report["project_lean_sources"]),
                          project_lake_manifest_sha256=evidence.file_sha(self.root / "lake-manifest.json"),
                          project_lakefile_sha256=evidence.file_sha(self.root / "lakefile.toml"),
                          project_toolchain_sha256=evidence.file_sha(self.root / "lean-toolchain"),
                          repetitions=len(pairs), warmups=1, threads=1,
                          tactic_implementation_code_lines=0, census_implementation_code_lines=0,
                          lean_environment={"LEAN_IMPORT_WORKERS": "1"}, lean_version="synthetic", lake_version="synthetic")
        self.rows = []
        for phase, values in [("warmup", [(1, 1)]), ("measured", pairs)]:
            for pair, times in enumerate(values):
                for variant in (["original", "replacement"] if pair % 2 == 0 else ["replacement", "original"]):
                    self.rows.append({"phase": phase, "pair": pair, "variant": variant, "path": self.path,
                                      "seconds": times[variant == "replacement"], "returncode": 0, "timed_out": False})
        self.timing_report = {"schema_version": 1, "status": "complete", "selection_status": "frozen", "provenance": provenance,
                              "manifest": self.frozen, "accounting": self.account, "measurements": self.rows,
                              "summary": BENCHMARK.summarize(self.rows, [self.path], len(pairs)),
                              "setup": [{"label": "tactic-rebuild", "seconds": 1, "returncode": 0, "timed_out": False}],
                              "source_header_setups": {}, "resolved_setup_sha256": {}, "resolved_calibration_match": True}
        for variant in ["original", "replacement"]:
            setup_path = dump(output / variant / "setup.json", {"name": "Mathlib.SyntheticFixture", "importArts": {}, "options": {}})
            header = {"imports": [{"module": "Mathlib.Init"} if variant == "original" else {"module": "NormArith"}]}
            self.timing_report["source_header_setups"][variant] = {self.path: {"setup_file": str(setup_path), "header": header}}
            self.timing_report["resolved_setup_sha256"][str(setup_path)] = evidence.file_sha(setup_path)
        if expanded:
            compiler = self.root / "synthetic-compiler"
            compiler.write_text("Synthetic test bytes; not an executable.\n")
            compilers = {str(compiler.resolve()): evidence.file_sha(compiler)}
            provenance.update(compiler_executables=compilers, python_version="synthetic")
            self.timing_report["resolved_setup_sha256"].update(compilers)
            for row in self.rows:
                row.update(compilation_status="verified", artifact_sha256=self.verification_report["files"][0]["artifact_sha256"])
        runtime = BENCHMARK.resolved_runtime_provenance(self.timing_report, self.root, output)
        self.timing_report["resolved_runtime"] = runtime
        pilot = self.root / "synthetic-pilot"
        dump(pilot / "report.json", dict(self.timing_report))
        raw = pilot / "measurements.jsonl"
        raw.write_text("".join(json.dumps(row) + "\n" for row in self.rows))
        calibration = dump(pilot / "calibration.json", {"schema_version": 1, "date": datetime.now(timezone.utc).date().isoformat(),
                           "rationale": "Synthetic unit-test block rationale; not measured calibration.", "block_pairs": block_pairs,
                           "pilot_report": {"path": "report.json", "sha256": evidence.file_sha(pilot / "report.json")},
                           "pilot_measurements": {"path": "measurements.jsonl", "sha256": evidence.file_sha(raw)}})
        calibrated = BENCHMARK.validate_calibration(calibration, provenance, [self.path])
        self.plan = {"mode": "confirmatory", "selection_status": "frozen", "all_affected_files_and_pairs_retained": True,
                     "affected_files": [self.path], "provenance": provenance, "input_sha256": {str((self.root / self.config["frozen_manifest"]).resolve()): evidence.file_sha(self.root / self.config["frozen_manifest"])},
                     "measured_pairs": len(pairs), "warmup_pairs": 1, "calibration": calibrated,
                     "primary_statistic": "ratio_of_mean_pass_totals",
                     "pair_order": "even: original then replacement; odd: replacement then original",
                     "interval": {"method": "paired_nonoverlapping_equal_block_BCa", "confidence_level": 0.95,
                                  "block_pairs": block_pairs, "resamples": 10000, "seed": seed, "bias_ties": "half_weight",
                                  "quantile": "linear_interpolation_at_p_times_n_minus_one",
                                  "acceleration": "delete_one_whole_block_jackknife",
                                  "success": "valid calibrated interval with lower endpoint strictly greater than one"}}
        self.timing_report["inference"] = {"mode": "confirmatory", "calibration_validated": True, "inputs_unchanged": True,
                                         **BENCHMARK.confirmatory_statistics(self.rows, [self.path], len(pairs), block_pairs, 10000, seed)}
        self.put("confirmatory_analysis_plan", output / "analysis-plan.json", self.plan)
        self.put("confirmatory_report", output / "report.json", self.timing_report)
        measurements = output / "measurements.jsonl"
        measurements.write_text("".join(json.dumps(row) + "\n" for row in self.rows))
        self.config["confirmatory_measurements"] = str(measurements.relative_to(self.root))
        self.save_timing()

    def save_timing(self):
        dump(self.root / self.config["confirmatory_analysis_plan"], self.plan)
        self.timing_report["analysis_plan"] = {"sha256": evidence.file_sha(self.root / self.config["confirmatory_analysis_plan"])}
        dump(self.root / self.config["confirmatory_report"], self.timing_report)

    def test_confirmatory_ratio_and_interval_are_recomputed_from_all_samples(self):
        self.add_timing()
        self.config["claim_speedup"] = True
        result = self.load()
        self.assertAlmostEqual(result["timing"]["estimate"], 5)
        self.assertGreater(result["timing"]["interval"]["lower"], 1)
        self.assertEqual(len(result["timing"]["files"]), 1)
        self.timing_report["inference"]["estimate"] = 99
        self.save_timing()
        with self.assertRaises(evidence.EvidenceError):
            self.load()

    def test_false_speed_gate_can_be_reported_but_cannot_be_claimed(self):
        self.add_timing([(1, 2), (1, 2), (1, 4), (1, 4), (1, 9), (1, 9)])
        self.assertFalse(self.load()["timing"]["success_criterion_met"])
        self.config["claim_speedup"] = True
        with self.assertRaises(evidence.EvidenceError):
            self.load()

    def test_confirmatory_block_size_must_equal_the_calibrated_block_size(self):
        self.add_timing([(value, 1) for value in [2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7]])
        self.plan["interval"]["block_pairs"] = 4
        self.timing_report["inference"].update(BENCHMARK.confirmatory_statistics(self.rows, [self.path], 12, 4, 10000, 42))
        self.save_timing()
        with self.assertRaisesRegex(evidence.EvidenceError, "calibrated block size"):
            self.load()

    def test_fixed_analysis_contract_cannot_be_changed_with_consistent_statistics(self):
        self.add_timing()
        cases = [("primary_statistic", "median_ratio"), ("pair_order", "original first for all pairs"),
                 ("bias_ties", "exclude"), ("quantile", "nearest_rank"),
                 ("acceleration", "delete_one_file"), ("success", "estimate greater than one")]
        for key, value in cases:
            with self.subTest(key=key):
                target = self.plan if key in {"primary_statistic", "pair_order"} else self.plan["interval"]
                original = target[key]
                target[key] = value
                self.save_timing()
                with self.assertRaisesRegex(evidence.EvidenceError, "analysis contract"):
                    self.load()
                target[key] = original

    def test_confirmatory_report_must_have_the_real_calibration_lineage(self):
        self.add_timing()
        self.plan["calibration"] = {"resolved_runtime": self.timing_report["resolved_runtime"]}
        self.save_timing()
        with self.assertRaises(evidence.EvidenceError):
            self.load()

    def test_runtime_evidence_cannot_be_changed(self):
        self.add_timing()
        self.timing_report["source_header_setups"]["replacement"][self.path]["header"]["imports"] = []
        self.save_timing()
        with self.assertRaises(evidence.EvidenceError):
            self.load()

    def test_portable_bundle_rebuilds_without_the_original_workspace(self):
        self.add_timing()
        self.paper_inputs()
        with tempfile.TemporaryDirectory() as exported:
            config = evidence.export_bundle(self.config, Path(exported) / "bundle", self.root)
            original = self.load()
            shutil.rmtree(self.root)
            result = evidence.load_evidence(config, Path(exported))
            self.assertEqual(evidence.evidence_facts(result), evidence.evidence_facts(original))
            self.assertEqual(result["project_source_root"], (Path(exported) / "bundle/project").resolve())
            self.assertIn("checked at export", result["validation_context"])
            self.assertEqual(result["timing"]["bootstrap_resamples"], 10000)
            new_root = Path(exported) / "new-workspace"
            paper = new_root / "paper"
            paper.mkdir(parents=True)
            (new_root / "scripts").mkdir()
            repository = Path(__file__).resolve().parents[1]
            for name in ["generate.py", "evidence.py", "evidence_transport.py", "plots.py"]:
                shutil.copyfile(repository / "paper" / name, paper / name)
            shutil.copyfile(repository / "scripts/benchmark.py", new_root / "scripts/benchmark.py")
            dump(paper / "status.json", dict(config, description="Synthetic fixture; not manuscript evidence."))
            subprocess.run([sys.executable, str(paper / "generate.py")], cwd=new_root, check=True, timeout=15)
            generated = paper / "generated"
            self.assertFalse((new_root / ".lake").exists())
            self.assertTrue((generated / "mathlib-original.lean").is_file())
            self.assertTrue((generated / "hidden.lean").is_file())
            self.assertTrue(json.loads((generated / "examples.json").read_text())["checked"])
            self.assertIn("saved hashes", (generated / "example-status.tex").read_text())
            implementation = json.loads((generated / "implementation.json").read_bytes())
            self.assertEqual(implementation["modules"][0]["relative_source"], "NormArith.lean")
            self.assertEqual((generated / "implementation/NormArith.lean").read_bytes(),
                             (Path(exported) / "bundle/project/NormArith.lean").read_bytes())
            self.assertEqual(json.loads((generated / "provenance.json").read_bytes())["implementation"], implementation)

    def test_portable_measured_source_drift_and_missing_source_are_rejected(self):
        self.add_timing()
        self.paper_inputs()
        with tempfile.TemporaryDirectory() as exported:
            bundle = Path(exported) / "bundle"
            config = evidence.export_bundle(self.config, bundle, self.root)
            shutil.rmtree(self.root)
            source = bundle / "project/NormArith.lean"
            original = source.read_bytes()
            source.write_bytes(b"-- changed measured source\n")
            with self.assertRaisesRegex(evidence.EvidenceError, "portable payload changed or missing"):
                evidence.load_evidence(config, Path(exported))
            source.unlink()
            with self.assertRaisesRegex(evidence.EvidenceError, "portable payload changed or missing"):
                evidence.load_evidence(config, Path(exported))
            source.write_bytes(original)
            self.assertEqual(evidence.load_evidence(config, Path(exported))["project_source_root"],
                             (bundle / "project").resolve())

    def test_compact_archive_paths_work_after_the_original_workspace_is_deleted(self):
        self.add_timing()
        self.paper_inputs()
        for key, name in [("census_manifest", "manifest.json"), ("census_summary", "summary.json"), ("census_integrity", "integrity.json")]:
            self.config[key] = "synthetic-census-archive/" + name
        self.config["census_archive"] = None
        with tempfile.TemporaryDirectory() as exported:
            config = evidence.export_bundle(self.config, Path(exported) / "bundle", self.root)
            shutil.rmtree(self.root)
            self.assertEqual(evidence.load_evidence(config, Path(exported))["census"]["summary"]["processed_files"], 1)

    def test_archive_receipt_or_payload_mismatch_prevents_final_claims(self):
        archive = self.root / "synthetic-census-archive"
        (archive / "file-outcomes.jsonl").write_text("CHANGED SYNTHETIC PAYLOAD")
        with self.assertRaises(evidence.EvidenceError):
            self.load()

    def test_portable_payload_change_and_mixed_live_mode_are_rejected(self):
        self.add_timing()
        self.paper_inputs()
        with tempfile.TemporaryDirectory() as exported:
            config = evidence.export_bundle(self.config, Path(exported) / "bundle", self.root)
            with self.assertRaises(evidence.EvidenceError):
                evidence.load_evidence(dict(config, census_summary=self.config["census_summary"]), self.root)
            receipt = json.loads((Path(config["evidence_bundle"]) / "bundle.json").read_bytes())
            artifact = next(name for name in receipt["inventory"] if name.startswith("verification-artifacts/"))
            (Path(config["evidence_bundle"]) / artifact).write_text("CHANGED SYNTHETIC ARTIFACT")
            with self.assertRaises(evidence.EvidenceError):
                evidence.load_evidence(config, self.root)

    def test_coherently_hashed_empty_verification_outputs_are_rejected(self):
        row = self.verification_report["files"][0]
        for name in row["artifact_sha256"]:
            with self.subTest(name=name):
                artifact = Path(name)
                original = artifact.read_bytes()
                artifact.write_bytes(b"")
                row["artifact_sha256"][name] = evidence.file_sha(artifact)
                dump(self.root / self.config["source_verification_report"], self.verification_report)
                with self.assertRaisesRegex(evidence.EvidenceError, "empty compiler artifact"):
                    self.load()
                artifact.write_bytes(original)
                row["artifact_sha256"][name] = evidence.file_sha(artifact)

    def test_empty_portable_proof_is_rejected_with_consistent_hashes(self):
        self.add_timing()
        self.paper_inputs()
        with tempfile.TemporaryDirectory() as exported:
            config = evidence.export_bundle(self.config, Path(exported) / "bundle", self.root)
            bundle = Path(config["evidence_bundle"])
            receipt = json.loads((bundle / "bundle.json").read_bytes())
            verification_name = evidence.recorded_name((self.root / self.config["source_verification_report"]).resolve())
            report_relative = receipt["copied_inputs"][verification_name]
            report_path = bundle / report_relative
            report = json.loads(report_path.read_bytes())
            original_name = next(name for name in report["files"][0]["artifact_sha256"] if name.endswith(".olean"))
            artifact_relative = receipt["copied_inputs"][evidence.recorded_name(Path(original_name).resolve())]
            artifact = bundle / artifact_relative
            artifact.write_bytes(b"")
            empty_hash = evidence.file_sha(artifact)
            receipt["inventory"][artifact_relative] = {"sha256": empty_hash, "bytes": 0}
            receipt["verified_input_sha256"][evidence.recorded_name(Path(original_name).resolve())] = empty_hash
            report["files"][0]["artifact_sha256"][original_name] = empty_hash
            dump(report_path, report)
            receipt["inventory"][report_relative] = {"sha256": evidence.file_sha(report_path), "bytes": report_path.stat().st_size}
            dump(bundle / "bundle.json", receipt)
            config["evidence_bundle_sha256"] = evidence.file_sha(bundle / "bundle.json")
            with self.assertRaisesRegex(evidence.EvidenceError, "empty compiler artifact"):
                evidence.load_evidence(config, self.root)
    def test_empty_portable_checked_example_is_rejected_with_consistent_hashes(self):
        self.add_timing()
        self.paper_inputs()
        with tempfile.TemporaryDirectory() as exported:
            config = evidence.export_bundle(self.config, Path(exported) / "bundle", self.root)
            bundle = Path(config["evidence_bundle"])
            receipt = json.loads((bundle / "bundle.json").read_bytes())
            relative = receipt["paper_inputs"]["examples_object"]
            artifact = bundle / relative
            artifact.write_bytes(b"")
            receipt["inventory"][relative] = {"sha256": evidence.file_sha(artifact), "bytes": 0}
            dump(bundle / "bundle.json", receipt)
            config["evidence_bundle_sha256"] = evidence.file_sha(bundle / "bundle.json")
            with self.assertRaisesRegex(evidence.EvidenceError, "empty checked-example object"):
                evidence.load_evidence(config, self.root)

    def test_table_generation_keeps_all_files_and_separate_costs(self):
        self.add_timing()
        result = self.load()
        result["timing"]["files"].append({"path": "Mathlib/SyntheticSecond.lean", "original_mean_seconds": 1,
                                           "replacement_mean_seconds": 2, "ratio": 0.5})
        with tempfile.TemporaryDirectory() as generated:
            with patch.object(generate, "GENERATED", Path(generated)):
                generate.final_tables(result)
            table = (Path(generated) / "timing-table.tex").read_text()
            self.assertIn(self.path, table)
            self.assertIn("Mathlib/SyntheticSecond.lean", table)
            self.assertIn("0.5000", table)
            self.assertIn("\\begin{longtable}", table)
            costs = (Path(generated) / "line-costs.tex").read_text()
            self.assertIn("Tactic implementation", costs)
            self.assertIn("Census infrastructure", costs)
            self.assertIn("total repository size", costs)

    def test_absent_evidence_stays_pending(self):
        result = evidence.load_evidence(dict.fromkeys(evidence.PATH_KEYS), self.root)
        self.assertEqual(result["stages"], [])

    def test_checked_line_savings_are_generated_from_the_combined_patch(self):
        result = self.load()
        self.assertEqual(result["stages"], ["census", "selection", "source-verification"])
        self.assertEqual(result["patch"]["accounting"]["net_lines_saved_including_imports"], 1)
        self.assertEqual(result["patch"]["affected_files"], [self.path])

    def test_partial_calibration_and_invalid_integrity_are_rejected(self):
        for field, value in [("scope", "calibration"), ("full_universe_processed", False), ("frozen_inputs_verified", False)]:
            changed = dict(self.summary, **{field: value})
            dump(self.root / self.config["census_summary"], changed)
            with self.subTest(field=field), self.assertRaises(evidence.EvidenceError):
                self.load()
        dump(self.root / self.config["census_summary"], self.summary)
        dump(self.root / self.config["census_integrity"], {"status": "pending", "protocol_hash": self.census_manifest["protocol_hash"]})
        with self.assertRaises(evidence.EvidenceError):
            self.load()

    def test_finished_census_retains_failed_files_in_its_denominator(self):
        for key in ["selector_manifest", "selector_summary", "selector_ledger", "source_verification_report", "frozen_manifest"]:
            self.config[key] = None
        result = dict(self.result, status="partial_extraction", complete=False, successful_proposals=0)
        dump(self.census / "files/Mathlib.SyntheticFixture/result.json", result)
        summary = dict(self.summary, completed_files=0, failed_files=1, full_universe_completed=False,
                       successful_proposals=0, file_status_counts={"partial_extraction": 1})
        dump(self.root / self.config["census_summary"], summary)
        self.archive_census()
        loaded = self.load()["census"]["summary"]
        self.assertEqual(loaded["universe_files"], 1)
        self.assertEqual(loaded["failed_files"], 1)
        self.assertFalse(loaded["full_universe_completed"])

    def test_incomplete_files_expose_known_unknowns_and_duplicate_outcomes_are_rejected(self):
        for key in ["selector_manifest", "selector_summary", "selector_ledger", "source_verification_report", "frozen_manifest"]:
            self.config[key] = None
        result = dict(self.result, status="partial_extraction", complete=False, eligible_observations=8,
                      successful_proposals=0, original_eligible_fragment_counts={"core": 8})
        summary = dict(self.summary, completed_files=0, failed_files=1, full_universe_completed=False,
                       eligible_observations=8, successful_proposals=0, original_eligible_fragment_counts={"core": 8}, file_status_counts={"partial_extraction": 1})
        dump(self.census / "files/Mathlib.SyntheticFixture/result.json", result)
        dump(self.root / self.config["census_summary"], summary)
        self.archive_census()
        loaded = self.load()
        self.assertEqual(loaded["census"]["unknown_due_incomplete_file"], 2)
        with tempfile.TemporaryDirectory() as generated:
            with patch.object(generate, "GENERATED", Path(generated)):
                generate.final_tables(loaded)
            self.assertIn("Unknown due to incomplete files & 2", (Path(generated) / "census-outcomes.tex").read_text())
        result["eligible_observations"] = 5
        dump(self.census / "files/Mathlib.SyntheticFixture/result.json", result)
        with self.assertRaises(evidence.EvidenceError):
            self.load()

    def test_missing_warmup_and_frozen_input_fingerprints_are_rejected(self):
        self.add_timing()
        for changes in ["warmup", "fingerprints"]:
            with self.subTest(changes=changes):
                saved_rows = self.timing_report["measurements"]
                saved_inputs = self.plan["input_sha256"]
                if changes == "warmup":
                    self.timing_report["measurements"] = [row for row in saved_rows if row["phase"] == "measured"]
                    (self.root / self.config["confirmatory_measurements"]).write_text("".join(json.dumps(row) + "\n" for row in self.timing_report["measurements"]))
                else:
                    self.plan["input_sha256"] = {}
                self.save_timing()
                with self.assertRaises(evidence.EvidenceError):
                    self.load()
                self.timing_report["measurements"] = saved_rows
                self.plan["input_sha256"] = saved_inputs
                (self.root / self.config["confirmatory_measurements"]).write_text("".join(json.dumps(row) + "\n" for row in saved_rows))

    def test_source_inventory_and_protocol_mismatches_are_rejected(self):
        changed = copy.deepcopy(self.census_manifest)
        changed["files"][0]["sha256"] = "0" * 64
        dump(self.root / self.config["census_manifest"], changed)
        with self.assertRaises(evidence.EvidenceError):
            self.load()
        dump(self.root / self.config["census_manifest"], dict(self.census_manifest, protocol_hash="0" * 64))
        with self.assertRaises(evidence.EvidenceError):
            self.load()

    def test_unchecked_or_different_frozen_patch_is_rejected(self):
        changed = copy.deepcopy(self.frozen)
        changed["candidates"][0]["replacement"] += "-- changed\n"
        dump(self.root / self.config["frozen_manifest"], changed)
        with self.assertRaises(evidence.EvidenceError):
            self.load()
        dump(self.root / self.config["frozen_manifest"], self.frozen)
        dump(self.root / self.config["source_verification_report"], dict(self.verification_report, status="failed"))
        with self.assertRaises(evidence.EvidenceError):
            self.load()

    def test_unrecorded_setup_is_not_zero_cost(self):
        self.add_timing()
        loaded = self.load()
        loaded["timing"]["report"]["setup"] = []
        with tempfile.TemporaryDirectory() as generated:
            with patch.object(generate, "GENERATED", Path(generated)):
                generate.final_tables(loaded)
            text = (Path(generated) / "timing-setup.tex").read_text()
            self.assertIn("Not measured", text)
            self.assertNotIn("0.000", text)

    def test_study_facts_and_example_use_only_the_verified_selected_patch(self):
        loaded = self.load()
        config = dict(self.config, example_candidate_id="synthetic-only")
        with tempfile.TemporaryDirectory() as generated:
            with patch.object(generate, "GENERATED", Path(generated)):
                generate.study_data(config, loaded)
                facts = (Path(generated) / "study-facts.tex").read_text()
                self.assertIn(r"\newcommand{\PatchNetSaved}{1}", facts)
                self.assertNotIn(r"\\newcommand", facts)
                record = json.loads((Path(generated) / "census-example.json").read_text())
                self.assertEqual(record["candidate_id"], "synthetic-only")
                self.assertEqual(record["combined_patch_sha256"], loaded["patch"]["patch_sha256"])
                self.assertEqual((Path(generated) / "census-example-original.lean").read_text(),
                                 "".join(self.prepared[0]["original"].splitlines(keepends=True)[1:]))
                self.assertEqual((Path(generated) / "census-example-replacement.lean").read_text(),
                                 self.selection["candidates"][0]["replacement"])
                with self.assertRaises(ValueError):
                    generate.study_data(dict(config, example_candidate_id="unselected"), loaded)
                loaded["patch"]["verification"]["files"][0]["candidate_ids"] = []
                with self.assertRaises(ValueError):
                    generate.study_data(config, loaded)

    def test_uncompiled_selection_does_not_become_patch_savings(self):
        self.config["source_verification_report"] = None
        self.config["frozen_manifest"] = None
        result = self.load()
        self.assertIsNone(result["patch"])
        self.assertEqual(result["stages"], ["census", "selection"])

    def test_missing_group_paths_and_unearned_speed_claim_are_rejected(self):
        self.config["census_integrity"] = None
        with self.assertRaises(evidence.EvidenceError):
            self.load()
        self.config["census_integrity"] = "synthetic-census/integrity.json"
        self.config["claim_speedup"] = True
        with self.assertRaises(evidence.EvidenceError):
            self.load()


if __name__ == "__main__":
    unittest.main()
