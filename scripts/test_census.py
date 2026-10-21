import hashlib
import gzip
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

import census


class CensusTests(unittest.TestCase):
    @unittest.skipUnless(os.environ.get("NORM_ARITH_CENSUS_INTEGRATION") == "1", "opt-in Lean replay integration")
    def test_tactic_suffix_preserves_preparation_and_nested_branch_boundary(self):
        project = Path(__file__).resolve().parents[1]
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "CensusSuffix.lean"
            source.write_text("""module
public import Mathlib.Analysis.Normed.Module.Basic
public section
theorem suffix {E : Type*} [NormedAddCommGroup E] (x y : E) (a b : ℝ)
    (h : True → ‖x‖ ≤ a) (hy : ‖y‖ ≤ b) : True → ‖x + y‖ ≤ a + b := by
  intro ht
  have hx := h ht
  have triangle := norm_add_le x y
  exact triangle.trans (add_le_add hx hy)
theorem nested {E : Type*} [NormedAddCommGroup E] (x y : E) (a b : ℝ)
    (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ b) : (‖x + y‖ ≤ a + b) ∧ True := by
  constructor
  · have triangle := norm_add_le x y
    exact triangle.trans (add_le_add hx hy)
  · trivial
def finalized {E : Type*} [NormedAddCommGroup E] (x y : E) (a b : ℝ)
    (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ b) : {v : E // ‖v‖ ≤ a + b} := ⟨x + y, ?bound⟩
where finally
  case bound =>
    have triangle := norm_add_le x y
    exact triangle.trans (add_le_add hx hy)
""")
            setup = json.loads((project / ".lake/build/ir/NormArith.setup.json").read_text())
            setup["name"] = "CensusSuffix"
            (root / "setup.json").write_text(json.dumps(setup))
            request = {"source": str(source), "setup": str(root / "setup.json"),
                       "output": str(root / "events.jsonl"), "relativePath": "CensusSuffix.lean",
                       "requireLineSaving": True, "goalHeartbeats": 200000,
                       "goalTimeoutMs": 2000, "memoryMb": 4096, "maxAttemptsPerFile": 10000,
                       "attempts": True, "importCycle": False}
            (root / "request.json").write_text(json.dumps(request))
            result = subprocess.run(["lake", "env", ".lake/build/bin/norm_arith_census",
                                     str(root / "request.json")], cwd=project, capture_output=True,
                                    text=True, timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)
            events, error = census.parse_events(root / "events.jsonl")
            self.assertIsNone(error)
            self.assertTrue(census.validate_events(events, result.returncode)["complete"])
            successes = [event for event in events if event.get("type") == "attempt"
                         and event.get("status") == "success" and event.get("kind") == "tactic_suffix"]
            data = source.read_bytes()
            selected = []
            for name in ("suffix", "nested", "finalized"):
                matches = [event for event in successes if event["parent_declaration"] == name
                           and data[event["start_byte"]:event["end_byte"]].startswith(b"have triangle")]
                self.assertTrue(matches, f"missing checked suffix in {name}")
                selected.append(matches[0])
                for event in matches:
                    span = data[event["start_byte"]:event["end_byte"]].decode()
                    self.assertIn("exact triangle.trans", span)
                    self.assertNotIn("have hx", span)
                    self.assertNotIn("trivial", span)
                    self.assertLessEqual(event["end_byte"], event["body_end_byte"])
            for event in sorted(selected, key=lambda event: event["start_byte"], reverse=True):
                data = data[:event["start_byte"]] + b"norm_arith" + data[event["end_byte"]:]
            data = data.replace(b"public section", b"public import NormArith\npublic section", 1)
            source.write_bytes(data)
            compiled = subprocess.run(["lake", "env", "lean", "--setup", str(root / "setup.json"),
                                       "-o", str(root / "CensusSuffix.olean"), str(source)],
                                      cwd=project, capture_output=True, text=True, timeout=120)
            self.assertEqual(compiled.returncode, 0, compiled.stdout + compiled.stderr)
            self.assertGreater((root / "CensusSuffix.olean").stat().st_size, 0)

    def test_stop_marker_drains_active_work_without_starting_queued_files(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            marker = root / "STOP_REQUESTED"
            started = []

            def work(item):
                started.append(item)
                marker.touch()
                return {"status": "complete", "complete": True}

            completed = [future.result() for _, future in
                         census.bounded_results(range(100), work, 1, marker.exists)]
            self.assertEqual(started, [0])
            manifest = {"selected_files": list(range(100)), "files": list(range(100)),
                        "scope": "full", "protocol_hash": "test"}
            summary = census.summarize(manifest, completed, root)
            self.assertEqual(summary["unprocessed_files"], 99)
            self.assertFalse(summary["full_universe_processed"])
            self.assertFalse(summary["full_universe_completed"])

    def test_existing_stop_marker_requires_explicit_removal_before_resume(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "STOP_REQUESTED").touch()
            args = census.parser().parse_args(["--output", directory, "--project", directory, "--resume"])
            with self.assertRaisesRegex(census.CensusError, "STOP_REQUESTED"):
                census.run(args)

    def test_inventory_counts_tracked_production_files_only(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            subprocess.run(["git", "init", "-q", directory], check=True)
            for name in ("Mathlib/A.lean", "Mathlib/Sub/B.lean", "Mathlib/Untracked.lean",
                         "MathlibTest/C.lean", "Archive/D.lean", "Mathlib/A.txt"):
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("example : True := trivial\n")
            subprocess.run(["git", "-C", directory, "add", "Mathlib/A.lean",
                            "Mathlib/Sub/B.lean", "MathlibTest", "Archive", "Mathlib/A.txt"],
                           check=True)
            self.assertEqual(census.tracked_files(root), ["Mathlib/A.lean", "Mathlib/Sub/B.lean"])

    def test_resume_refuses_changed_source_or_protocol(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "manifest.json"
            original = {"protocol_hash": "a", "files": [{"path": "Mathlib/A.lean", "sha256": "x"}]}
            census.freeze_manifest(path, original, resume=False)
            census.freeze_manifest(path, original, resume=True)
            for changed in ({**original, "protocol_hash": "b"},
                            {**original, "files": [{"path": "Mathlib/A.lean", "sha256": "y"}]}):
                with self.assertRaises(census.CensusError):
                    census.freeze_manifest(path, changed, resume=True)

    def test_exit_zero_without_terminal_ledger_is_incomplete(self):
        result = census.validate_events([
            {"type": "file_start", "path": "Mathlib/A.lean"},
            {"type": "phase_end", "phase": "original", "errors": False, "counts": {}},
        ], returncode=0)
        self.assertFalse(result["complete"])
        self.assertEqual(result["status"], "incomplete_ledger")

    def test_success_requires_kernel_check_matching_original_and_one_outcome(self):
        observation = {"type": "observation", "phase": "original", "key": "k",
                       "replacement_eligible": True}
        ending = [{"type": "phase_end", "phase": "original", "errors": False, "counts": {}},
                  {"type": "file_end", "status": "complete", "counts": {}}]
        for attempts in ([{"type": "attempt", "key": "k", "status": "success", "kernel_checked": False}],
                         [{"type": "attempt", "key": "elsewhere", "status": "success", "kernel_checked": True}],
                         [{"type": "attempt", "key": "k", "status": "success", "kernel_checked": True}] * 2,
                         []):
            result = census.validate_events([observation, *attempts, *ending], returncode=0)
            self.assertFalse(result["complete"])
            self.assertEqual(result["successful_proposals"], 0)

    def test_explicit_failures_count_in_denominator(self):
        events = [
            {"type": "observation", "phase": "original", "key": "k", "replacement_eligible": True},
            {"type": "attempt", "key": "k", "status": "import_cycle", "kernel_checked": False},
            {"type": "phase_end", "phase": "original", "errors": False, "counts": {}},
            {"type": "file_end", "status": "complete", "counts": {}},
        ]
        result = census.validate_events(events, returncode=0)
        self.assertTrue(result["complete"])
        self.assertEqual(result["eligible_observations"], 1)
        self.assertEqual(result["attempt_status_counts"], {"import_cycle": 1})
        self.assertEqual(result["successful_proposals"], 0)

    def test_elaboration_errors_never_become_success(self):
        events = [
            {"type": "phase_end", "phase": "original", "errors": True, "counts": {}},
            {"type": "file_end", "status": "complete", "counts": {}},
        ]
        self.assertFalse(census.validate_events(events, returncode=0)["complete"])
        self.assertFalse(census.validate_events(events, returncode=1)["complete"])

    def test_resource_failure_keeps_retry_reason_when_last_json_line_is_truncated(self):
        self.assertEqual(census.validate_events([], -9, parse_error="truncated", timed_out=True)["status"], "file_timeout")
        self.assertEqual(census.validate_events([], -9, parse_error="truncated")["status"], "process_failed")
        self.assertEqual(census.validate_events([], 0, parse_error="truncated")["status"], "invalid_jsonl")

    def test_proposal_offsets_are_utf8_bytes_and_exact_hashes(self):
        source = "-- ∀\nexample (x : ℝ) : ‖x‖ ≤ ‖x‖ := le_rfl\n".encode()
        start = source.index(b"le_rfl")
        attempt = {"key": "k", "status": "success", "kernel_checked": True,
                   "start_byte": start, "end_byte": start + 6, "replacement": "by norm_arith"}
        proposal = census.source_proposal("Mathlib/A.lean", source, attempt)
        self.assertEqual(proposal["original"], "le_rfl")
        self.assertEqual(proposal["original_sha256"], hashlib.sha256(b"le_rfl").hexdigest())
        with self.assertRaises(census.CensusError):
            census.source_proposal("Mathlib/A.lean", source, {**attempt, "start_byte": 4})

    def test_batch_setup_results_must_preserve_exact_module_order(self):
        names = ["Mathlib.A", "Mathlib.B"]
        text = '\n'.join(json.dumps({"name": name, "importArts": {}}) for name in names)
        self.assertEqual([item["name"] for item in census.parse_setup_batch(text, names)], names)
        for broken in (text.splitlines()[0], '\n'.join(reversed(text.splitlines())), text + '\nnull'):
            with self.assertRaises(census.CensusError):
                census.parse_setup_batch(broken, names)

    def test_process_timeout_preserves_logs_and_reaps_child(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            result = census.run_process(
                [os.sys.executable, "-u", "-c", "import time; print('started'); time.sleep(10)"],
                root, os.environ.copy(), 0.15, root / "stdout", root / "stderr")
            self.assertTrue(result["timed_out"])
            self.assertNotEqual(result["returncode"], 0)
            self.assertIn("started", (root / "stdout").read_text())
            self.assertGreater(result["peak_rss_bytes"], 0)

    def test_resume_rejects_changed_or_missing_raw_evidence(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "events.jsonl").write_text("{}\n")
            (root / "proposals.jsonl").write_text("")
            result = {"evidence_sha256": {name: census.digest((root / name).read_bytes())
                                           for name in ("events.jsonl", "proposals.jsonl")}}
            census.verify_evidence(root, result)
            (root / "events.jsonl").write_text('{"changed":true}\n')
            with self.assertRaises(census.CensusError):
                census.verify_evidence(root, result)
            (root / "events.jsonl").unlink()
            with self.assertRaises(census.CensusError):
                census.verify_evidence(root, result)

    def test_retry_requires_incomplete_resource_failure_and_stops_after_tier_two(self):
        for status in ("file_timeout", "process_failed"):
            self.assertTrue(census.retry_eligible({"status": status, "complete": False, "resource_tier": 1}))
            self.assertFalse(census.retry_eligible({"status": status, "complete": False, "resource_tier": 2}))
        for status in ("complete", "partial_extraction", "original_elaboration_failed", "setup_failed"):
            self.assertFalse(census.retry_eligible({"status": status, "complete": False, "resource_tier": 1}))
        self.assertFalse(census.retry_eligible({"status": "complete", "complete": True,
                                               "attempt_status_counts": {"goal_timeout": 5}, "resource_tier": 1}))

    def test_cached_setup_requires_recorded_uncompressed_hash(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            data = b'{"name":"Mathlib.A","importArts":{}}'
            with gzip.open(root / "Mathlib.A.json.gz", "wb") as handle:
                handle.write(data)
            (root / "Mathlib.A.metadata.json").write_text(json.dumps({"sha256": census.digest(data)}))
            self.assertEqual(census.read_cached_setup(root, "Mathlib.A")[0], data)
            with gzip.open(root / "Mathlib.A.json.gz", "wb") as handle:
                handle.write(b'{"name":"Mathlib.A","importArts":{"changed":[]}}')
            with self.assertRaises(census.CensusError):
                census.read_cached_setup(root, "Mathlib.A")

    def test_implementation_drift_cannot_complete_frozen_run(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "NormArith.lean").write_text("original")
            (root / "extractor").write_bytes(b"native")
            manifest = {"implementation_sha256": {"NormArith.lean": census.digest("original")},
                        "extractor_binary_sha256": census.digest(b"native"), "environment_sha256": {}}
            census.verify_implementation(root, manifest, root / "extractor")
            (root / "NormArith.lean").write_text("changed")
            with self.assertRaises(census.CensusError):
                census.verify_implementation(root, manifest, root / "extractor")

    @unittest.skipUnless(os.environ.get("NORM_ARITH_CENSUS_INTEGRATION") == "1", "opt-in Lean replay integration")
    def test_generated_declarations_are_observed_in_command_environment(self):
        project = Path(__file__).resolve().parents[1]
        relatives = ["Mathlib/Algebra/Algebra/Operations.lean",
                     "Mathlib/Algebra/BigOperators/Associated.lean",
                     "Mathlib/Algebra/Category/Grp/IsFinite.lean",
                     "Mathlib/Algebra/BigOperators/Finprod.lean",
                     "Mathlib/Algebra/Group/End.lean",
                     "Mathlib/Algebra/Homology/DerivedCategory/Ext/ExtClass.lean"]
        modules = [relative[:-5].replace("/", ".") for relative in relatives]
        query = subprocess.run(["lake", "--no-build", "-q", "-J", "query",
                                *[f"@mathlib/+{module}:setup" for module in modules]],
                               cwd=project, capture_output=True, text=True, timeout=120, check=True)
        for relative, setup in zip(relatives, census.parse_setup_batch(query.stdout, modules)):
            with self.subTest(path=relative), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                (root / "setup.json").write_text(json.dumps(setup))
                request = {"source": str(project / ".lake/packages/mathlib" / relative),
                           "setup": str(root / "setup.json"), "output": str(root / "events.jsonl"),
                           "relativePath": relative, "goalHeartbeats": 200000, "goalTimeoutMs": 2000,
                           "memoryMb": 4096, "maxAttemptsPerFile": 10000, "attempts": False,
                           "importCycle": False, "requireLineSaving": True}
                (root / "request.json").write_text(json.dumps(request))
                result = subprocess.run(["lake", "env", ".lake/build/bin/norm_arith_census",
                                         str(root / "request.json")], cwd=project, capture_output=True, text=True,
                                        timeout=120)
                events, error = census.parse_events(root / "events.jsonl")
                self.assertIsNone(error)
                errors = [event for event in events if event.get("type") == "node_error"]
                self.assertEqual(errors, [], json.dumps(errors, indent=2))
                self.assertTrue(census.validate_events(events, result.returncode)["complete"], result.stderr)

    @unittest.skipUnless(os.environ.get("NORM_ARITH_CENSUS_INTEGRATION") == "1", "opt-in Lean replay integration")
    def test_real_term_and_tactic_replay_uses_predeclaration_context(self):
        project = Path(__file__).resolve().parents[1]
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "CensusFixture.lean"
            source.write_text("""module
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public section
theorem term_style {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) (a b : ℝ) (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ b) : ‖x + y‖ ≤ a + b :=
  le_trans (norm_add_le x y) (add_le_add hx hy)
theorem tactic_style {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) (a b : ℝ) (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ b) : ‖x + y‖ ≤ a + b := by
  calc
    ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
    _ ≤ a + b := add_le_add hx hy
theorem rearrangement {E : Type*} [NormedAddCommGroup E] (x y x' y' : E) :
    ‖x + y‖ ≤ ‖x' + y'‖ + ‖x' - x‖ + ‖y' - y‖ := by
  have identity : ∀ x' y', x + y = x' + y' + (x - x') + (y - y') := fun _ _ => by abel
  rw [norm_sub_rev, norm_sub_rev y', identity]
  exact norm_add₃_le
theorem unsupported (x : ℝ) : ‖x * x‖ ≤ ‖x‖ * ‖x‖ := le_of_eq (norm_mul x x)
theorem statement_guard :
    (⟨(0 : ℝ), by simp⟩ : {x : ℝ // ‖x‖ ≤ 0}).1 = 0 := rfl
theorem equation_proof : ∀ x : ℝ, ‖x‖ ≤ ‖x‖
  | _ => le_rfl
theorem generated_match_context (x a : ℝ) (h : ‖x‖ ≤ a) (pair : True ∧ True) : ‖x‖ ≤ a :=
  (fun ⟨_, _⟩ => h) pair
theorem rational_module {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) (a b : ℝ) (hx : ‖(3 : ℝ) • x + y‖ ≤ a) (hy : ‖y‖ ≤ b) :
    ‖x‖ ≤ (1 / 3 : ℝ) * (a + b) := by
  have h : (3 : ℝ) * ‖x‖ ≤ a + b := calc
    _ = ‖(3 : ℝ) • x‖ := by rw [norm_smul]; norm_num
    _ ≤ ‖(3 : ℝ) • x + y‖ + ‖y‖ := by
      simpa only [add_sub_cancel_right] using norm_sub_le ((3 : ℝ) • x + y) y
    _ ≤ a + b := add_le_add hx hy
  linarith
""")
            setup = json.loads((project / ".lake/build/ir/NormArith.setup.json").read_text())
            setup["name"] = "CensusFixture"
            (root / "setup.json").write_text(json.dumps(setup))
            request = {"source": str(source), "setup": str(root / "setup.json"),
                       "output": str(root / "events.jsonl"), "relativePath": "CensusFixture.lean",
                       "goalHeartbeats": 200000, "goalTimeoutMs": 2000, "memoryMb": 4096,
                       "maxAttemptsPerFile": 10000, "attempts": True, "importCycle": False}
            request["requireLineSaving"] = False
            (root / "request.json").write_text(json.dumps(request))
            result = subprocess.run(["lake", "env", ".lake/build/bin/norm_arith_census",
                                     str(root / "request.json")], cwd=project, capture_output=True, text=True,
                                    timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)
            events, error = census.parse_events(root / "events.jsonl")
            self.assertIsNone(error)
            ledger = census.validate_events(events, result.returncode)
            self.assertTrue(ledger["complete"], json.dumps(events[-3:]))
            original = [event for event in events if event.get("phase") == "original"
                        and event.get("type") == "observation"]
            self.assertTrue(original)
            self.assertTrue(all(not event["parent_available"] for event in original),
                            json.dumps([event for event in original if event["parent_available"]], indent=2))
            successes = [event for event in events if event.get("type") == "attempt"
                         and event.get("status") == "success"]
            self.assertTrue(any(event["kind"] == "term" and event["parent_declaration"] == "term_style"
                                for event in successes))
            self.assertTrue(any(event["parent_declaration"] == "term_style" and event["fragment"] == "core"
                                for event in original), "explicit real normed-space context must classify as core")
            self.assertTrue(any(event["kind"] == "tactic" and event["parent_declaration"] == "tactic_style"
                                for event in successes))
            self.assertTrue(any(event["parent_declaration"] == "rearrangement" for event in successes),
                            json.dumps([event for event in events if event.get("type") == "attempt"
                                        and event.get("parent_declaration") == "rearrangement"], indent=2))
            self.assertTrue(any(event["parent_declaration"] == "rational_module" and event["start_line"] != event["end_line"]
                                for event in successes), "rational vector-identity replay must finalize module proof")
            self.assertFalse(any(event["parent_declaration"] == "unsupported" for event in successes))
            statement_nodes = [event for event in original if event["parent_declaration"] == "statement_guard"]
            self.assertTrue(statement_nodes)
            self.assertTrue(all(not event["replacement_eligible"] for event in statement_nodes))
            self.assertTrue(any(event.get("eligibility_reason") == "outside_decl_body" for event in statement_nodes))
            self.assertTrue(any(event["parent_declaration"] == "equation_proof" and event["replacement_eligible"]
                                for event in original))
            for success in successes:
                self.assertLessEqual(success["body_start_byte"], success["start_byte"])
                self.assertLessEqual(success["end_byte"], success["body_end_byte"])
                census.source_proposal("CensusFixture.lean", source.read_bytes(), success)


if __name__ == "__main__":
    unittest.main()
