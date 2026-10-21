"""Synthetic composed-study validation checks; no Lean proof or timing evidence."""

from collections import Counter
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

import evidence
import expansion


def digest(data):
    return hashlib.sha256(data).hexdigest()


def dump(path, value, lines=False):
    path.parent.mkdir(parents=True, exist_ok=True)
    text = "".join(json.dumps(row) + "\n" for row in value) if lines else json.dumps(value) + "\n"
    path.write_text(text)


class Model:
    def __init__(self, root, background):
        self.root = root
        self.source_root = root / "mathlib"
        self.config = {"targeted_archive": str(root / "targeted/archive.json"),
                       "selector_manifest": str(root / "selection/manifest.json")}
        self.result = {"census": {"manifest": background}, "stages": ["census"]}

    def path(self, key):
        return Path(self.config[key])

    def read(self, path, lines=False):
        data = Path(path).read_text()
        return [json.loads(line) for line in data.splitlines() if line] if lines else json.loads(data)

    def hash(self, path):
        return digest(Path(path).read_bytes())

    def fingerprints(self, values):
        for name, value in values.items():
            evidence.require(Path(name).is_file() and self.hash(name) == value, "fingerprint changed")


class ExpansionTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.path = "Mathlib/Synthetic.lean"
        self.source = "import Mathlib.Init\nexample : True := by\n  change True\n  trivial\n"
        source_path = self.root / "mathlib" / self.path
        source_path.parent.mkdir(parents=True)
        source_path.write_text(self.source)
        self.source_hash = digest(self.source.encode())
        self.universe = [{"path": "Mathlib/Background.lean", "sha256": "b" * 64},
                         {"path": self.path, "sha256": self.source_hash}]
        self.background = {"files": self.universe, "mathlib_revision": "c" * 40}
        self.model = Model(self.root, self.background)
        self.directory = self.root / "targeted"
        self.directory.mkdir()
        protocol = {"config": {"synthetic_fixture": True}, "implementation_sha256": {"NormArith.lean": "d" * 64},
                    "environment_sha256": {"lean-toolchain": "e" * 64}, "mathlib_revision": "c" * 40,
                    "selected_files": [self.path], "extractor_binary_sha256": "f" * 64}
        self.protocol = evidence.canonical_sha(protocol)
        self.manifest = dict(protocol, files=self.universe, schema_version=1, scope="calibration", protocol_hash=self.protocol)
        self.row = {"path": self.path, "source_sha256": self.source_hash, "status": "complete", "complete": True,
                    "eligible_observations": 3, "attempt_status_counts": {"success": 1, "failed": 2},
                    "counts": {}, "original_observation_fragment_counts": {"core": 3},
                    "original_eligible_fragment_counts": {"core": 3},
                    "attempt_status_counts_by_original_fragment": {"core": {"success": 1, "failed": 2}},
                    "successful_proposals": 1, "resource_tier": 1}
        self.summary = {"schema_version": 1, "scope": "calibration", "protocol_hash": self.protocol,
                        "universe_files": 2, "selected_files": 1, "processed_files": 1, "completed_files": 1,
                        "failed_files": 0, "unprocessed_files": 0, "full_universe_processed": False,
                        "full_universe_completed": False, "frozen_inputs_verified": True,
                        "file_status_counts": {"complete": 1}, "resource_tier_counts": {"1": 1},
                        "evidence_stage": "isolated_kernel_checked_proposals_not_compiled_patches",
                        **{key: self.row[key] for key in ["counts", "eligible_observations", "attempt_status_counts",
                           "successful_proposals", "original_observation_fragment_counts", "original_eligible_fragment_counts",
                           "attempt_status_counts_by_original_fragment"]}}
        self.archive = {"schema_version": 1, "scope": "targeted_followup", "recorded_scope": "calibration",
                        "status": "validated_targeted_discovery_archive", "full_universe_coverage_claim": False,
                        "mathlib_revision": "c" * 40, "protocol_hash": self.protocol, "frozen_inputs_verified": True,
                        "archive_reopened_and_every_member_rehashed": True, "archived_attempts": 1,
                        "archived_proposal_records": 1,
                        **{key: self.summary[key] for key in ["universe_files", "selected_files", "processed_files",
                           "completed_files", "failed_files", "unprocessed_files", "successful_proposals",
                           "file_status_counts", "evidence_stage"]}}
        dump(self.directory / "manifest.json", self.manifest)
        dump(self.directory / "summary.json", self.summary)
        dump(self.directory / "integrity.json", {"status": "valid", "protocol_hash": self.protocol})
        dump(self.directory / "file-outcomes.jsonl", [{"result": self.row}], lines=True)
        dump(self.directory / "attempt-outcomes.jsonl", [{"result": self.row, "current_attempt": True}], lines=True)
        dump(self.directory / "proposals.jsonl", [{"result_file": "synthetic/result.json", "current_attempt": True,
             "proposal": {"path": self.path, "source_sha256": self.source_hash, "key": "synthetic-key", "status": "success", "kernel_checked": True}}], lines=True)
        dump(self.directory / "raw-index.json", {"files": {
            "frozen-implementation/NormArith.lean": {"sha256": "d" * 64},
            "frozen-implementation/lean-toolchain": {"sha256": "e" * 64}}})
        dump(self.directory / "setup-cache-origin.json", {"synthetic_fixture": True})
        for name in ["archive_targeted.py", "census.py"]:
            path = self.directory / "archive-tools" / name
            path.parent.mkdir(exist_ok=True)
            path.write_text("# Synthetic fixture, not an archive validator.\n")
        (self.directory / "raw.tar.gz").write_bytes(b"SYNTHETIC RAW BYTES, NOT A CENSUS ARCHIVE")
        self.save_archive()

    def save_archive(self):
        self.archive.update(raw_archive_sha256=digest((self.directory / "raw.tar.gz").read_bytes()),
                            raw_archive_bytes=(self.directory / "raw.tar.gz").stat().st_size,
                            raw_index_sha256=digest((self.directory / "raw-index.json").read_bytes()))
        dump(self.directory / "archive.json", self.archive)
        dump(self.directory / "inventory.json", {str(path.relative_to(self.directory)): {
             "sha256": digest(path.read_bytes()), "bytes": path.stat().st_size}
             for path in self.directory.rglob("*") if path.is_file() and path.name != "inventory.json"})

    def targeted(self):
        expansion.targeted_discovery(self.model, evidence.require, evidence.canonical_sha)

    def selection(self):
        start = self.source.index("by\n")
        candidate = {"id": "synthetic-only", "path": self.path, "declaration": "example",
                     "parent_declaration": "example", "status": "replace", "reason": "selected",
                     "start_line": 2, "end_line": 4, "original_sha256": digest("".join(self.source.splitlines(keepends=True)[1:]).encode()),
                     "replacement": "example : True := by norm_arith\n", "proof_replacement": "by norm_arith",
                     "source_start_byte": start, "source_end_byte": len(self.source.encode()) - 1,
                     "body_start_byte": start, "body_end_byte": len(self.source.encode()) - 1,
                     "manual_review": True, "proof_kind": "reviewed_tactic_sequence_or_calc_fragment"}
        original = {"schema_version": 1, "mathlib_revision": "c" * 40,
                    "files": [{"path": self.path, "source_sha256": self.source_hash, "imports": ["NormArith"], "helpers": []}],
                    "candidates": [candidate]}
        self.input_path = self.root / "selection/inputs/00.json"
        dump(self.input_path, original)
        manifest, ledger, account = expansion.MERGER.merge_manifests([original], self.model.source_root)
        manifest["input_manifests"] = [{"snapshot": "inputs/00.json", "sha256": digest(self.input_path.read_bytes()),
                                        "source": "synthetic-original-manifest.json"}]
        summary = {"evidence_stage": "selected_proposals_not_combined_source_compiled", "accounting": account,
                   "outcome_counts": dict(Counter(row["outcome"] for row in ledger))}
        self.model.result["targeted"] = {}
        return manifest, summary, ledger

    def test_targeted_subset_stays_separate_from_full_background(self):
        self.targeted()
        self.assertEqual(self.model.result["targeted"]["summary"]["processed_files"], 1)
        self.assertEqual(len(self.model.result["census"]["manifest"]["files"]), 2)
        self.assertEqual(self.model.result["stages"], ["census", "targeted-discovery"])

    def test_targeted_archive_cannot_be_relabelled_full(self):
        self.archive["full_universe_coverage_claim"] = True
        self.save_archive()
        with self.assertRaisesRegex(evidence.EvidenceError, "limited archive"):
            self.targeted()

    def test_coherent_archive_hashes_do_not_hide_missing_outcomes(self):
        dump(self.directory / "file-outcomes.jsonl", [], lines=True)
        self.save_archive()
        with self.assertRaisesRegex(evidence.EvidenceError, "missing or duplicate"):
            self.targeted()

    def test_source_snapshot_and_raw_payload_binding(self):
        (self.directory / "raw.tar.gz").write_bytes(b"changed")
        with self.assertRaisesRegex(evidence.EvidenceError, "fingerprint"):
            self.targeted()
        self.save_archive()
        dump(self.directory / "raw-index.json", {"files": {}})
        self.save_archive()
        with self.assertRaisesRegex(evidence.EvidenceError, "frozen implementation"):
            self.targeted()

    def test_non_kernel_checked_proposal_cannot_count_as_success(self):
        path = self.directory / "proposals.jsonl"
        records = self.model.read(path, lines=True)
        records[0]["proposal"].update(status="failed", kernel_checked=False)
        dump(path, records, lines=True)
        self.save_archive()
        with self.assertRaisesRegex(evidence.EvidenceError, "kernel.checked"):
            self.targeted()

    def test_composed_selection_is_recomputed_from_snapshots(self):
        manifest, summary, ledger = self.selection()
        expansion.composed_selection(self.model, manifest, summary, ledger, evidence.require)
        manifest["candidates"][0]["status"] = "unchanged"
        ledger[0]["outcome"] = "no_line_saving"
        _, summary["accounting"] = evidence.BENCHMARK.prepare_sources(manifest, self.model.source_root)
        summary["outcome_counts"] = {"no_line_saving": 1}
        with self.assertRaisesRegex(evidence.EvidenceError, "reselection"):
            expansion.composed_selection(self.model, manifest, summary, ledger, evidence.require)

    def test_composition_snapshot_tamper_is_rejected(self):
        manifest, summary, ledger = self.selection()
        self.input_path.write_text("{}\n")
        with self.assertRaisesRegex(evidence.EvidenceError, "snapshot hash"):
            expansion.composed_selection(self.model, manifest, summary, ledger, evidence.require)


if __name__ == "__main__":
    unittest.main()
