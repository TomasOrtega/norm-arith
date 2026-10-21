"""End-to-end synthetic expanded-release fixtures; never manuscript evidence."""

import copy
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

import evidence
import expansion
import generate
import test_evidence as baseline
import test_expansion as targeted
from test_calibration_metadata import add_export_metadata
from unittest.mock import patch


def dump(path, value, lines=False):
    targeted.dump(path, value, lines=lines)


class ComposedEvidenceTests(unittest.TestCase):
    def setUp(self):
        self.fixture = baseline.EvidenceTests()
        self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)
        f = self.fixture
        background = f.mathlib / "Mathlib/BackgroundFixture.lean"
        background.write_text("-- Synthetic background file.\n")
        subprocess.run(["git", "-C", str(f.mathlib), "add", "."], check=True)
        subprocess.run(["git", "-C", str(f.mathlib), "-c", "user.name=Fixture", "-c", "user.email=fixture@example.org", "commit", "-qm", "synthetic background"], check=True)
        f.revision = subprocess.check_output(["git", "-C", str(f.mathlib), "rev-parse", "HEAD"], text=True).strip()
        f.census_manifest.update(mathlib_revision=f.revision)
        f.census_manifest["files"].insert(0, {"path": "Mathlib/BackgroundFixture.lean", "sha256": evidence.file_sha(background)})
        f.census_manifest["selected_files"] = [row["path"] for row in f.census_manifest["files"]]
        protocol = {key: f.census_manifest[key] for key in ["config", "implementation_sha256", "mathlib_revision",
                    "environment_sha256", "selected_files", "extractor_binary_sha256"]}
        f.census_manifest["protocol_hash"] = evidence.canonical_sha(protocol)
        empty = dict(f.result, path="Mathlib/BackgroundFixture.lean", source_sha256=evidence.file_sha(background),
                     counts={}, eligible_observations=0, attempt_status_counts={}, successful_proposals=0,
                     original_observation_fragment_counts={}, original_eligible_fragment_counts={},
                     attempt_status_counts_by_original_fragment={})
        f.summary.update(protocol_hash=f.census_manifest["protocol_hash"], universe_files=2, selected_files=2,
                         processed_files=2, completed_files=2, file_status_counts={"complete": 2}, resource_tier_counts={"1": 2})
        dump(f.census / "manifest.json", f.census_manifest)
        dump(f.census / "summary.json", f.summary)
        dump(f.census / "integrity.json", {"status": "valid", "protocol_hash": f.census_manifest["protocol_hash"]})
        archive = f.root / "synthetic-census-archive"
        for name in ["manifest.json", "summary.json", "integrity.json"]:
            shutil.copyfile(f.census / name, archive / name)
        dump(archive / "file-outcomes.jsonl", [{"result": empty}, {"result": f.result}], lines=True)
        receipt = json.loads((archive / "archive.json").read_bytes())
        receipt.update(protocol_hash=f.census_manifest["protocol_hash"], mathlib_revision=f.revision,
                       processed_files=2, completed_files=2, file_status_counts={"complete": 2})
        dump(archive / "archive.json", receipt)
        dump(archive / "inventory.json", {"schema_version": 1, "files": {
            str(path.relative_to(archive)): {"sha256": evidence.file_sha(path), "bytes": path.stat().st_size}
            for path in archive.rglob("*") if path.is_file() and path.name != "inventory.json"}})
        f.config["census_outcomes"] = str((archive / "file-outcomes.jsonl").relative_to(f.root))
        x = targeted.ExpansionTests()
        x.setUp()
        self.addCleanup(x.doCleanups)
        source_hash = evidence.file_sha(f.mathlib / f.path)
        x.manifest.update(files=f.census_manifest["files"], mathlib_revision=f.revision, selected_files=[f.path])
        protocol = {key: x.manifest[key] for key in ["config", "implementation_sha256", "mathlib_revision",
                    "environment_sha256", "selected_files", "extractor_binary_sha256"]}
        x.protocol = evidence.canonical_sha(protocol)
        x.manifest["protocol_hash"] = x.protocol
        x.summary["protocol_hash"] = x.protocol
        x.archive.update(protocol_hash=x.protocol, mathlib_revision=f.revision)
        x.row.update(path=f.path, source_sha256=source_hash)
        dump(x.directory / "manifest.json", x.manifest)
        dump(x.directory / "summary.json", x.summary)
        dump(x.directory / "integrity.json", {"status": "valid", "protocol_hash": x.protocol})
        dump(x.directory / "file-outcomes.jsonl", [{"result": x.row}], lines=True)
        dump(x.directory / "attempt-outcomes.jsonl", [{"result": x.row, "current_attempt": True}], lines=True)
        dump(x.directory / "proposals.jsonl", [{"result_file": "synthetic/result.json", "current_attempt": True,
             "proposal": {"path": f.path, "source_sha256": source_hash, "key": "synthetic-key", "status": "success", "kernel_checked": True}}], lines=True)
        x.save_archive()
        shutil.copytree(x.directory, f.root / "targeted")
        f.config.update(study_mode="composed_expansion", targeted_archive="targeted/archive.json")
        source = (f.mathlib / f.path).read_bytes()
        start, end = source.index(b"by\n"), len(source) - 1
        candidate = dict(f.selection["candidates"][0], start_line=2, end_line=4,
                         original_sha256=evidence.BENCHMARK.sha256(b"example : True := by\n  change True\n  trivial\n"),
                         replacement="example : True := by norm_arith\n", proof_replacement="by norm_arith", source_start_byte=start,
                         source_end_byte=end, body_start_byte=start, body_end_byte=end,
                         parent_declaration="example", manual_review=True,
                         proof_kind="reviewed_tactic_sequence_or_calc_fragment")
        component = dict(f.selection, mathlib_revision=f.revision, candidates=[candidate])
        input_path = f.root / "synthetic-selection/inputs/00.json"
        dump(input_path, component)
        f.selection, ledger, f.account = expansion.MERGER.merge_manifests([component], f.mathlib)
        f.selection["input_manifests"] = [{"snapshot": "inputs/00.json", "source": "synthetic-original.json",
                                           "sha256": evidence.file_sha(input_path)}]
        f.prepared, _ = evidence.BENCHMARK.prepare_sources(f.selection, f.mathlib)
        dump(f.root / f.config["selector_manifest"], f.selection)
        dump(f.root / f.config["selector_summary"], {"evidence_stage": "selected_proposals_not_combined_source_compiled",
             "accounting": f.account, "outcome_counts": {"selected": 1}})
        dump(f.root / f.config["selector_ledger"], ledger, lines=True)
        patch = evidence.patch_bytes(f.prepared)
        (f.verification / "mathlib.patch").write_bytes(patch)
        manifest_hash = evidence.file_sha(f.root / f.config["selector_manifest"])
        f.verified = dict(f.selection, selection_status="source-verified-trial", source_verification={
            "path": str(f.verification / "verification.json"), "input_manifest_sha256": manifest_hash,
            "patch_sha256": evidence.BENCHMARK.sha256(patch)})
        dump(f.verification / "manifest.json", f.verified)
        (f.root / "NormArith.lean").write_text("-- Synthetic final implementation differs from background.\n")
        inputs = {evidence.recorded_name(f.root / f.config["selector_manifest"]): manifest_hash}
        for name in ["NormArith.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain"]:
            inputs[evidence.recorded_name(f.root / name)] = evidence.file_sha(f.root / name)
        body_root = f.root / "synthetic-body-census"
        body_events = body_root / "files/Mathlib.SyntheticFixture/attempt-01/events.jsonl"
        dump(body_events, [{"type": "observation", "phase": "original", "key": "body-key",
                           "parent_declaration": "example", "body_start_byte": start, "body_end_byte": end}], lines=True)
        dump(body_root / "manifest.json", f.census_manifest)
        body_result = {"path": f.path, "module": "Mathlib.SyntheticFixture", "source_sha256": source_hash,
                       "complete": True, "status": "complete", "directory": "files/Mathlib.SyntheticFixture/attempt-01",
                       "evidence_sha256": {str(body_events.relative_to(body_root)): evidence.file_sha(body_events)}}
        body_result_path = body_root / "files/Mathlib.SyntheticFixture/result.json"
        dump(body_result_path, body_result)
        for path in [body_events, body_result_path, body_root / "manifest.json"]:
            inputs[evidence.recorded_name(path)] = evidence.file_sha(path)
        f.verification_report.update(mathlib_revision=f.revision, input_manifest_sha256=manifest_hash,
             final_manifest_sha256=evidence.file_sha(f.verification / "manifest.json"), accounting=f.account,
             patch_sha256=evidence.BENCHMARK.sha256(patch), input_sha256=inputs,
             project_lean_sources={"NormArith.lean": evidence.file_sha(f.root / "NormArith.lean")},
             proof_span_policy="manually_reviewed_exact_proof_replacement_with_source_bound_original_body_evidence",
             body_census_evidence=[{"candidate_id": "synthetic-only", "path": f.path, "parent_declaration": "example",
                 "body_start_byte": start, "body_end_byte": end, "source_sha256": source_hash, "census": str(body_root),
                 "census_protocol_hash": f.census_manifest["protocol_hash"], "original_observation_key": "body-key",
                 "events_path": str(body_events), "events_sha256": evidence.file_sha(body_events),
                 "result_sha256": evidence.file_sha(body_result_path), "manifest_sha256": evidence.file_sha(body_root / "manifest.json"),
                 "role": "original_source_body_evidence_only_not_a_checked_replacement_proposal"}])
        f.verification_report["files"][0]["replacement_source_sha256"] = evidence.BENCHMARK.sha256(f.prepared[0]["replacement"])
        dump(f.root / f.config["source_verification_report"], f.verification_report)
        f.frozen = dict(f.verified, selection_status="frozen")
        dump(f.root / f.config["frozen_manifest"], f.frozen)
        self.set_targeted_implementation(evidence.file_sha(f.root / "NormArith.lean"))

    def set_targeted_implementation(self, digest):
        f = self.fixture
        directory = f.root / "targeted"
        manifest = json.loads((directory / "manifest.json").read_bytes())
        manifest["implementation_sha256"] = {"NormArith.lean": digest}
        manifest["environment_sha256"] = {name: evidence.file_sha(f.root / name)
                                             for name in ["lean-toolchain", "lakefile.toml", "lake-manifest.json"]}
        protocol = {key: manifest[key] for key in ["config", "implementation_sha256", "mathlib_revision",
                    "environment_sha256", "selected_files", "extractor_binary_sha256"]}
        manifest["protocol_hash"] = evidence.canonical_sha(protocol)
        dump(directory / "manifest.json", manifest)
        summary = json.loads((directory / "summary.json").read_bytes())
        summary["protocol_hash"] = manifest["protocol_hash"]
        dump(directory / "summary.json", summary)
        dump(directory / "integrity.json", {"status": "valid", "protocol_hash": manifest["protocol_hash"]})
        index = {"files": {"frozen-implementation/" + name: {"sha256": value}
                             for name, value in {**manifest["implementation_sha256"], **manifest["environment_sha256"]}.items()}}
        dump(directory / "raw-index.json", index)
        archive = json.loads((directory / "archive.json").read_bytes())
        archive.update(protocol_hash=manifest["protocol_hash"], raw_index_sha256=evidence.file_sha(directory / "raw-index.json"))
        dump(directory / "archive.json", archive)
        dump(directory / "inventory.json", {str(path.relative_to(directory)): {"sha256": evidence.file_sha(path), "bytes": path.stat().st_size}
                                              for path in directory.rglob("*") if path.is_file() and path.name != "inventory.json"})

    def test_targeted_counts_must_use_the_final_verified_implementation(self):
        self.set_targeted_implementation(self.fixture.census_manifest["implementation_sha256"]["NormArith.lean"])
        with self.assertRaisesRegex(evidence.EvidenceError, "targeted.*implementation"):
            self.fixture.load()

    def test_new_implementation_is_bound_to_verification_not_historical_census(self):
        result = self.fixture.load()
        self.assertEqual(result["stages"], ["census", "targeted-discovery", "selection", "source-verification"])
        self.assertEqual(result["census"]["summary"]["processed_files"], 2)
        self.assertEqual(result["targeted"]["summary"]["processed_files"], 1)
        self.assertNotEqual(result["patch"]["verification"]["project_lean_sources"], self.fixture.census_manifest["implementation_sha256"])

    def test_missing_body_evidence_is_rejected(self):
        self.fixture.verification_report["body_census_evidence"] = []
        dump(self.fixture.root / self.fixture.config["source_verification_report"], self.fixture.verification_report)
        with self.assertRaisesRegex(evidence.EvidenceError, "body evidence"):
            self.fixture.load()

    def test_coherent_body_hashes_cannot_move_the_original_observation(self):
        f = self.fixture
        record = f.verification_report["body_census_evidence"][0]
        events = Path(record["events_path"])
        rows = [json.loads(line) for line in events.read_text().splitlines()]
        rows[0]["body_end_byte"] -= 1
        dump(events, rows, lines=True)
        result_path = Path(record["census"]) / "files/Mathlib.SyntheticFixture/result.json"
        result = json.loads(result_path.read_bytes())
        result["evidence_sha256"][str(events.relative_to(Path(record["census"])))] = evidence.file_sha(events)
        dump(result_path, result)
        record.update(events_sha256=evidence.file_sha(events), result_sha256=evidence.file_sha(result_path))
        for path in [events, result_path]:
            f.verification_report["input_sha256"][evidence.recorded_name(path)] = evidence.file_sha(path)
        dump(f.root / f.config["source_verification_report"], f.verification_report)
        with self.assertRaisesRegex(evidence.EvidenceError, "original source observation"):
            f.load()

    def test_expanded_timing_requires_fresh_output_metadata(self):
        f = self.fixture
        f.add_timing([(2 + i // 4, 1) for i in range(40)], expanded=True, block_pairs=4, seed=20261020)
        f.rows[0]["artifact_sha256"] = {"fake.olean": "bad", "fake.ilean": "bad", "fake.c": "bad"}
        dump(f.root / f.config["confirmatory_measurements"], f.rows, lines=True)
        f.save_timing()
        with self.assertRaisesRegex(evidence.EvidenceError, "fresh compilation evidence"):
            f.load()

    def test_prominent_intervals_and_observed_drift_are_reported(self):
        f = self.fixture
        f.add_timing([(2 + i // 4, 1) for i in range(40)], expanded=True, block_pairs=4, seed=20261020)
        result = f.load()
        with tempfile.TemporaryDirectory() as directory:
            with patch.object(generate, 'GENERATED', Path(directory)):
                generate.future_status(dict(f.config, description='Synthetic fixture.'), result)
            detail = (Path(directory) / 'confirmatory-status.tex').read_text()
            main = (Path(directory) / 'timing-main.tex').read_text()
            self.assertIn('conditional paired 95', main)
            self.assertIn('conditional paired 95', detail)
            self.assertIn('+125.00\\%', detail)
            self.assertIn('+0.00\\%', detail)

    def test_portable_expansion_rebuild_without_original_workspace(self):
        f = self.fixture
        f.add_timing([(2 + i // 4, 1) for i in range(40)], expanded=True, block_pairs=4, seed=20261020)
        f.config["example_candidate_id"] = "synthetic-only"
        f.paper_inputs(expanded=True)
        add_export_metadata(f, 4)
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / "bundle"
            configuration = evidence.export_bundle(f.config, output, f.root)
            original = f.load()
            shutil.rmtree(f.root)
            restored = evidence.load_evidence(configuration, Path(temporary))
            self.assertEqual(evidence.evidence_facts(original), evidence.evidence_facts(restored))
            self.assertFalse((Path(temporary) / ".lake").exists())
            self.assertFalse(any(path.name == "raw.tar.gz" for path in output.rglob("*")))
            workspace = Path(temporary) / "fresh-workspace"
            paper = workspace / "paper"
            paper.mkdir(parents=True)
            scripts = workspace / "scripts"
            scripts.mkdir()
            repository = Path(__file__).resolve().parents[1]
            for name in ["evidence.py", "evidence_transport.py", "expansion.py", "generate.py"]:
                shutil.copyfile(repository / "paper" / name, paper / name)
            for name in ["benchmark.py", "verify_selection.py", "select_expansion.py", "select_census.py", "census.py"]:
                shutil.copyfile(repository / "scripts" / name, scripts / name)
            dump(paper / "status.json", dict(configuration, description="Synthetic fixture; not manuscript evidence."))
            subprocess.run([sys.executable, str(paper / "generate.py")], cwd=workspace, check=True, timeout=20)
            self.assertTrue((paper / "generated/quantified.lean").is_file())
            self.assertTrue((paper / "generated/metric.lean").is_file())
            self.assertIn('selected 4 pairs', (paper / 'generated/calibration-status.tex').read_text())
            self.assertFalse((workspace / ".lake").exists())


if __name__ == "__main__":
    unittest.main()
