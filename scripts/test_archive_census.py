import fcntl
import gzip
import json
from pathlib import Path
import tarfile
import tempfile
import unittest
from unittest.mock import patch

import archive_census
import census


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, sort_keys=True) + "\n")


def fixture(root):
    root.mkdir()
    (root / ".run.lock").touch()
    implementation = {"NormArith.lean": "import NormArith.Tactic\n",
                      "scripts/census.py": "# frozen extractor driver\n"}
    hashes = {}
    for name, text in implementation.items():
        path = root / "frozen-implementation" / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        hashes[name] = census.digest(text)
    specifications = [{"path": name, "sha256": census.digest(name)}
                      for name in ("Mathlib/A.lean", "Mathlib/B.lean")]
    protocol = {"config": {}, "implementation_sha256": hashes, "environment_sha256": {},
                "mathlib_revision": "a" * 40, "extractor_binary_sha256": "b" * 64,
                "selected_files": [item["path"] for item in specifications]}
    manifest = {"schema_version": 1, **protocol, "protocol_hash": census.digest(census.canonical_json(protocol)),
                "files": specifications, "scope": "full"}
    write_json(root / "manifest.json", manifest)
    write_json(root / "integrity.json", {"status": "valid", "protocol_hash": manifest["protocol_hash"]})
    results = []
    for index, specification in enumerate(specifications):
        module = specification["path"][:-5].replace("/", ".")
        directory = root / "files" / module / "attempt-01"
        directory.mkdir(parents=True)
        events = [{"type": "phase_end", "phase": "original", "errors": index == 1},
                  {"type": "file_end", "status": "complete", "counts": {"normGoals": 1}}]
        proposals = []
        if index == 0:
            attempt = {"type": "attempt", "key": "proof", "status": "success", "kernel_checked": True}
            events.insert(0, {"type": "observation", "phase": "original", "key": "proof",
                              "replacement_eligible": True, "fragment": "core"})
            events.insert(1, attempt)
            proposals = [{**attempt, "path": specification["path"], "source_sha256": specification["sha256"],
                          "original": "by\n  exact le_rfl", "original_sha256": census.digest("by\n  exact le_rfl"),
                          "replacement": "by norm_arith"}]
        (directory / "events.jsonl").write_text("".join(census.canonical_json(item) + "\n" for item in events))
        (directory / "proposals.jsonl").write_text("".join(census.canonical_json(item) + "\n" for item in proposals))
        (directory / "stdout.log").write_text("")
        (directory / "stderr.log").write_text("")
        result = {"path": specification["path"], "module": module, "source_sha256": specification["sha256"],
                  "attempt": 1, "resource_tier": 1, "directory": str(directory.relative_to(root)),
                  "proposal_file": str((directory / "proposals.jsonl").relative_to(root)),
                  "extraction": {"returncode": 0, "timed_out": False}, **census.validate_events(events, 0)}
        result["evidence_sha256"] = {str(path.relative_to(root)): census.digest(path.read_bytes())
                                     for path in directory.iterdir()}
        write_json(directory / "result.json", result)
        write_json(directory.parent / "result.json", result)
        results.append(result)
    census.summarize(manifest, results, root)
    return manifest, results


class ArchiveCensusTests(unittest.TestCase):
    def test_complete_processing_keeps_failed_file_and_all_proposals(self):
        with tempfile.TemporaryDirectory() as temporary:
            root, output = Path(temporary) / "run", Path(temporary) / "archive"
            _, results = fixture(root)
            report = archive_census.archive_run(root, output)
            self.assertEqual(report["failed_files"], 1)
            self.assertTrue(report["full_universe_processed"])
            self.assertFalse(report["full_universe_completed"])
            outcomes = [json.loads(line) for line in (output / "file-outcomes.jsonl").read_text().splitlines()]
            self.assertEqual([entry["result"] for entry in outcomes], results)
            proposals = [json.loads(line) for line in (output / "proposals.jsonl").read_text().splitlines()]
            self.assertEqual(len(proposals), 1)
            self.assertTrue(proposals[0]["current_attempt"])
            self.assertFalse((output / "files").exists())
            inventory = json.loads((output / "inventory.json").read_text())
            for name, value in inventory["files"].items():
                self.assertEqual(value["sha256"], census.digest((output / name).read_bytes()))
                self.assertEqual(value["bytes"], (output / name).stat().st_size)
            archives = json.loads((output / "archives.json").read_text())
            self.assertEqual(archives["compact.tar.gz"]["sha256"], census.digest((output / "compact.tar.gz").read_bytes()))

    def test_pending_invalid_and_calibration_runs_are_refused(self):
        for condition in ("pending", "invalid", "calibration"):
            with self.subTest(condition=condition), tempfile.TemporaryDirectory() as temporary:
                root, output = Path(temporary) / "run", Path(temporary) / "archive"
                manifest, _ = fixture(root)
                if condition == "calibration":
                    write_json(root / "manifest.json", {**manifest, "scope": condition})
                else:
                    write_json(root / "integrity.json", {"status": condition, "protocol_hash": manifest["protocol_hash"]})
                with self.assertRaises(archive_census.ArchiveError):
                    archive_census.archive_run(root, output)
                self.assertFalse(output.exists())

    def test_live_writer_lock_is_refused(self):
        with tempfile.TemporaryDirectory() as temporary:
            root, output = Path(temporary) / "run", Path(temporary) / "archive"
            fixture(root)
            with (root / ".run.lock").open("rb") as lock:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                with self.assertRaisesRegex(archive_census.ArchiveError, "running"):
                    archive_census.archive_run(root, output)
            self.assertFalse(output.exists())

    def test_complete_summary_cannot_hide_missing_universe_file(self):
        with tempfile.TemporaryDirectory() as temporary:
            root, output = Path(temporary) / "run", Path(temporary) / "archive"
            manifest, _ = fixture(root)
            manifest["selected_files"].pop()
            write_json(root / "manifest.json", manifest)
            with self.assertRaisesRegex(archive_census.ArchiveError, "universe"):
                archive_census.archive_run(root, output)

    def test_raw_evidence_hash_and_summary_disagreement_are_refused(self):
        for condition in ("hash", "failed_hash", "summary", "attempt"):
            with self.subTest(condition=condition), tempfile.TemporaryDirectory() as temporary:
                root, output = Path(temporary) / "run", Path(temporary) / "archive"
                _, results = fixture(root)
                if condition in ("hash", "failed_hash"):
                    index = 1 if condition == "failed_hash" else 0
                    (root / results[index]["directory"] / "events.jsonl").write_text("changed\n")
                elif condition == "summary":
                    summary = json.loads((root / "summary.json").read_text())
                    write_json(root / "summary.json", {**summary, "failed_files": 0})
                else:
                    write_json(root / results[0]["directory"] / "result.json", {**results[0], "status": "failed"})
                with self.assertRaises(archive_census.ArchiveError):
                    archive_census.archive_run(root, output)
                self.assertFalse(output.exists())

    def test_orchestrator_failure_has_explicit_missing_extractor_evidence(self):
        with tempfile.TemporaryDirectory() as temporary:
            root, output = Path(temporary) / "run", Path(temporary) / "archive"
            manifest, results = fixture(root)
            result = {"path": "Mathlib/B.lean", "complete": False, "status": "orchestrator_exception",
                      "error": "recorded failure", "successful_proposals": 0}
            directory = root / "files/Mathlib.B"
            write_json(directory / "result.json", result)
            write_json(directory / "orchestrator_error.json", result)
            census.summarize(manifest, [results[0], result], root)
            report = archive_census.archive_run(root, output)
            self.assertEqual(report["files_without_extractor_evidence"], ["Mathlib/B.lean"])
            self.assertEqual(report["failed_files"], 1)

    def test_historical_proposals_are_kept_but_not_counted_as_current_successes(self):
        with tempfile.TemporaryDirectory() as temporary:
            root, output = Path(temporary) / "run", Path(temporary) / "archive"
            manifest, results = fixture(root)
            old = results[0]
            new_directory = root / "files/Mathlib.A/attempt-02"
            new_directory.mkdir()
            for name in ("events.jsonl", "proposals.jsonl", "stdout.log", "stderr.log"):
                (new_directory / name).write_bytes((root / old["directory"] / name).read_bytes())
            new = {**old, "attempt": 2, "resource_tier": 2, "directory": str(new_directory.relative_to(root)),
                   "proposal_file": str((new_directory / "proposals.jsonl").relative_to(root)),
                   "evidence_sha256": {str(path.relative_to(root)): census.digest(path.read_bytes())
                                       for path in new_directory.iterdir()}}
            write_json(new_directory / "result.json", new)
            write_json(new_directory.parent / "result.json", new)
            census.summarize(manifest, [new, results[1]], root)
            report = archive_census.archive_run(root, output)
            self.assertEqual(report["archived_proposals"], 2)
            self.assertEqual(report["successful_proposals"], 1)
            records = [json.loads(line) for line in (output / "proposals.jsonl").read_text().splitlines()]
            self.assertEqual([record["current_attempt"] for record in records], [False, True])

    def test_proposal_must_match_checked_event_even_when_rehashed(self):
        with tempfile.TemporaryDirectory() as temporary:
            root, output = Path(temporary) / "run", Path(temporary) / "archive"
            _, results = fixture(root)
            result = results[0]
            path = root / result["proposal_file"]
            proposal = json.loads(path.read_text())
            proposal["key"] = "different-proof"
            path.write_text(census.canonical_json(proposal) + "\n")
            result["evidence_sha256"][result["proposal_file"]] = census.digest(path.read_bytes())
            write_json(root / result["directory"] / "result.json", result)
            write_json(root / "files/Mathlib.A/result.json", result)
            with self.assertRaisesRegex(archive_census.ArchiveError, "checked event"):
                archive_census.archive_run(root, output)

    def test_orphan_proposals_are_preserved_without_success_credit(self):
        with tempfile.TemporaryDirectory() as temporary:
            root, output = Path(temporary) / "run", Path(temporary) / "archive"
            manifest, results = fixture(root)
            result = {"path": "Mathlib/B.lean", "complete": False, "status": "orchestrator_exception",
                      "error": "recorded failure", "successful_proposals": 0}
            directory = root / "files/Mathlib.B"
            write_json(directory / "result.json", result)
            write_json(directory / "orchestrator_error.json", result)
            proposal = directory / "attempt-02/proposals.jsonl"
            proposal.parent.mkdir()
            proposal.write_text('{"key":"unattributed-proof"}\n')
            census.summarize(manifest, [results[0], result], root)
            report = archive_census.archive_run(root, output)
            self.assertEqual(report["successful_proposals"], 1)
            self.assertEqual(report["unattributed_proposals"], 1)
            self.assertEqual(report["archived_proposals"], 2)

    def test_full_raw_archive_contains_only_run_regular_files(self):
        with tempfile.TemporaryDirectory() as temporary:
            root, output = Path(temporary) / "run", Path(temporary) / "archive"
            fixture(root)
            (Path(temporary) / "outside-secret").write_text("not run evidence")
            archive_census.archive_run(root, output, full_raw=True)
            with tarfile.open(output / "raw.tar.gz", "r:gz") as archive:
                names = archive.getnames()
                self.assertIn("run/manifest.json", names)
                self.assertTrue(all(name.startswith("run/") for name in names))
                self.assertTrue(all(member.isfile() for member in archive.getmembers()))
                self.assertFalse(any("outside-secret" in name for name in names))

    def test_symlinks_unknown_environment_dumps_and_build_outputs_are_refused(self):
        for condition in ("symlink", "environment", "build"):
            with self.subTest(condition=condition), tempfile.TemporaryDirectory() as temporary:
                root, output = Path(temporary) / "run", Path(temporary) / "archive"
                fixture(root)
                if condition == "symlink":
                    (root / "setups").symlink_to(Path(temporary), target_is_directory=True)
                elif condition == "environment":
                    (root / "environment.json").write_text('{"TOKEN":"secret"}')
                else:
                    (root / "large.olean").write_bytes(b"build artifact")
                with self.assertRaises(archive_census.ArchiveError):
                    archive_census.archive_run(root, output, full_raw=True)
                self.assertFalse(output.exists())

    def test_origin_and_snapshot_hashes_are_checked(self):
        for condition in ("snapshot", "origin"):
            with self.subTest(condition=condition), tempfile.TemporaryDirectory() as temporary:
                root, output = Path(temporary) / "run", Path(temporary) / "archive"
                manifest, _ = fixture(root)
                if condition == "snapshot":
                    (root / "frozen-implementation/NormArith.lean").write_text("changed")
                else:
                    (root / "setups").mkdir()
                    setup = root / "setups/Mathlib.A.json.gz"
                    with gzip.open(setup, "wb") as stream:
                        stream.write(b"{}")
                    origin = {"source_manifest_sha256": census.digest((root / "manifest.json").read_bytes()),
                              "source_protocol_hash": manifest["protocol_hash"], "mathlib_revision": manifest["mathlib_revision"],
                              "environment_sha256": {}, "cached_file_sha256": {"setups/Mathlib.A.json.gz": "c" * 64}}
                    write_json(root / "setup-cache-origin.json", origin)
                    write_json(root / "setup-cache-origin.manifest.json", manifest)
                with self.assertRaises(archive_census.ArchiveError):
                    archive_census.archive_run(root, output)

    def test_input_mutation_during_publication_leaves_no_output(self):
        with tempfile.TemporaryDirectory() as temporary:
            root, output = Path(temporary) / "run", Path(temporary) / "archive"
            fixture(root)
            original = archive_census.write_compact

            def mutate(*args, **kwargs):
                value = original(*args, **kwargs)
                (root / "integrity.json").write_text("changed after validation")
                return value

            with patch.object(archive_census, "write_compact", side_effect=mutate):
                with self.assertRaisesRegex(archive_census.ArchiveError, "changed"):
                    archive_census.archive_run(root, output)
            self.assertFalse(output.exists())
            self.assertFalse(list(Path(temporary).glob(".archive-*")))

    def test_existing_output_is_not_replaced(self):
        with tempfile.TemporaryDirectory() as temporary:
            root, output = Path(temporary) / "run", Path(temporary) / "archive"
            fixture(root)
            output.mkdir()
            (output / "keep").write_text("existing")
            with self.assertRaises(archive_census.ArchiveError):
                archive_census.archive_run(root, output)
            self.assertEqual((output / "keep").read_text(), "existing")

    def test_completed_resumed_run_preserves_interruption_history(self):
        with tempfile.TemporaryDirectory() as temporary:
            root, output = Path(temporary) / "run", Path(temporary) / "archive"
            manifest, _ = fixture(root)
            interruption = {"status": "interrupted", "reason": "STOP_REQUESTED",
                            "protocol_hash": manifest["protocol_hash"], "processed_files": 1, "unprocessed_files": 1}
            write_json(root / "interruption-01.json", interruption)
            archive_census.archive_run(root, output)
            self.assertEqual(json.loads((output / "interruption-01.json").read_text()), interruption)

    def test_interruption_from_other_protocol_is_refused(self):
        with tempfile.TemporaryDirectory() as temporary:
            root, output = Path(temporary) / "run", Path(temporary) / "archive"
            fixture(root)
            write_json(root / "interruption-01.json", {"status": "interrupted", "reason": "STOP_REQUESTED",
                                                      "protocol_hash": "different", "processed_files": 1, "unprocessed_files": 1})
            with self.assertRaisesRegex(archive_census.ArchiveError, "interruption"):
                archive_census.archive_run(root, output)


if __name__ == "__main__":
    unittest.main()
