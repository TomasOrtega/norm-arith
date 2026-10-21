import contextlib
from datetime import datetime, timezone
import importlib.util
import io
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
from types import SimpleNamespace
import unittest
from unittest import mock


SPEC = importlib.util.spec_from_file_location("benchmark", Path(__file__).with_name("benchmark.py"))
benchmark = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = benchmark
SPEC.loader.exec_module(benchmark)


class ManifestTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.source = "module\n\nimport Mathlib.Foo\n\nexample : True := by\n  trivial\n"
        path = self.root / "Mathlib/Example.lean"
        path.parent.mkdir()
        path.write_text(self.source)
        self.manifest = {
            "schema_version": 1,
            "mathlib_revision": "a" * 40,
            "files": [{
                "path": "Mathlib/Example.lean",
                "source_sha256": benchmark.sha256(self.source),
                "imports": ["NormArith"],
                "helpers": [],
            }],
            "candidates": [{
                "id": "example",
                "path": "Mathlib/Example.lean",
                "declaration": "example",
                "status": "replace",
                "start_line": 6,
                "end_line": 6,
                "original_sha256": benchmark.sha256("  trivial\n"),
                "replacement": "  have h : True := by trivial\n  exact h\n",
            }],
        }

    def test_counts_preparation_and_shared_helper_once(self):
        self.manifest["files"][0]["helpers"] = [{
            "id": "helper", "before_line": 5,
            "text": "private theorem helper : True := by\n  trivial\n\n",
        }]
        prepared, accounting = benchmark.prepare_sources(self.manifest, self.root)
        self.assertEqual(accounting["original_proof_lines"], 1)
        self.assertEqual(accounting["replacement_proof_lines"], 2)
        self.assertEqual(accounting["added_helper_lines"], 2)
        self.assertEqual(accounting["net_proof_lines_saved"], -3)
        self.assertIn("import NormArith\nimport Mathlib.Foo", prepared[0]["replacement"])
        self.assertEqual(prepared[0]["replacement"].count("private theorem helper"), 1)

    def test_stale_span_cannot_silently_rewrite_another_proof(self):
        self.manifest["candidates"][0]["start_line"] = 5
        with self.assertRaisesRegex(benchmark.BenchmarkError, "span hash"):
            benchmark.prepare_sources(self.manifest, self.root)

    def test_changed_file_rejected_even_when_target_span_still_matches(self):
        (self.root / "Mathlib/Example.lean").write_text(self.source + "-- changed elsewhere\n")
        with self.assertRaisesRegex(benchmark.BenchmarkError, "source hash"):
            benchmark.prepare_sources(self.manifest, self.root)

    def test_exclusions_are_not_counted_as_replacements(self):
        self.manifest["candidates"][0]["status"] = "unsupported"
        prepared, accounting = benchmark.prepare_sources(self.manifest, self.root)
        self.assertEqual(prepared, [])
        self.assertEqual(accounting["net_proof_lines_saved"], 0)
        self.assertEqual(accounting["proposed_replacements"], 0)

    def test_overlapping_proof_spans_rejected(self):
        duplicate = dict(self.manifest["candidates"][0], id="duplicate")
        self.manifest["candidates"].append(duplicate)
        with self.assertRaisesRegex(benchmark.BenchmarkError, "overlap"):
            benchmark.prepare_sources(self.manifest, self.root)


class MeasurementTests(unittest.TestCase):
    def test_interrupted_measurement_reaps_its_compiler_process_group(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            pidfile = root / "compiler.pid"
            child = f"import os,pathlib,time; pathlib.Path({str(pidfile)!r}).write_text(str(os.getpid())); time.sleep(60)"
            helper = (
                f"import sys; sys.path.insert(0, {str(Path(benchmark.__file__).parent)!r}); "
                "from pathlib import Path; import benchmark; "
                f"benchmark.run_process([{sys.executable!r}, '-c', {child!r}], "
                f"Path({str(root)!r}), Path({str(root / 'logs')!r}), 60)"
            )
            process = subprocess.Popen([sys.executable, "-c", helper], stdout=subprocess.PIPE,
                                       stderr=subprocess.PIPE, start_new_session=True)
            compiler_pid = None
            try:
                deadline = time.monotonic() + 5
                while not pidfile.exists() and time.monotonic() < deadline:
                    time.sleep(0.01)
                self.assertTrue(pidfile.exists(), "compiler did not start")
                compiler_pid = int(pidfile.read_text())
                os.kill(process.pid, signal.SIGINT)
                process.communicate(timeout=5)
                try:
                    os.kill(compiler_pid, 0)
                    alive = True
                except ProcessLookupError:
                    alive = False
                self.assertFalse(alive, "interrupted harness left its compiler alive")
            finally:
                if process.poll() is None:
                    process.kill()
                    process.communicate()
                if compiler_pid is not None:
                    try:
                        os.killpg(compiler_pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass

    def test_each_measured_compilation_records_its_fresh_output_hashes(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            lean = root / "lean"
            lean.write_text(f"#!{sys.executable}\nimport sys\nfrom pathlib import Path\n"
                            "for flag in ['-o', '-i', '-c']:\n"
                            "    Path(sys.argv[sys.argv.index(flag) + 1]).write_text(flag + ': fresh artifact')\n")
            lean.chmod(0o755)
            setup = root / "setup.json"
            setup.write_text("{}")
            args = SimpleNamespace(output=root / "run", project=root, timeout=5, threads=1)
            report = {"measurements": []}
            with contextlib.redirect_stdout(io.StringIO()):
                benchmark.compile_pass(args, report, [{"path": "Mathlib/Example.lean"}], str(lean),
                                       os.environ.copy(), {"original": {"Mathlib/Example.lean": setup}},
                                       "measured", 0, "original")
            row = report["measurements"][0]
            self.assertEqual(row["compilation_status"], "verified")
            expected = {str(path.resolve()): benchmark.sha256(path.read_bytes())
                        for path in (root / "run/runs/measured/000/original/artifacts").rglob("*") if path.is_file()}
            self.assertEqual(row["artifact_sha256"], expected)
            persisted = json.loads((root / "run/measurements.jsonl").read_text())
            self.assertEqual(persisted, row)

    def test_resolved_calibration_binds_actual_compiler_executable_bytes(self):
        report = {"source_header_setups": {}, "provenance": {
            "compiler_executables": {"/toolchain/bin/lean": "a" * 64}, "python_version": "3.15.0"}}
        current = benchmark.resolved_runtime_provenance(report, Path("/project"), Path("/run"))
        report["provenance"]["compiler_executables"]["/toolchain/bin/lean"] = "b" * 64
        changed = benchmark.resolved_runtime_provenance(report, Path("/project"), Path("/run"))
        with self.assertRaisesRegex(benchmark.BenchmarkError, "resolved runtime"):
            benchmark.validate_resolved_calibration({"resolved_runtime": current}, changed)

    def test_edited_header_setup_uses_original_module_config_and_real_variant_imports(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "replacement.lean"
            source.write_text("module\nimport NormArith\nimport Mathlib.Init\n")
            header = {"isModule": True, "imports": [
                {"module": "NormArith", "isExported": False, "isMeta": False, "importAll": False},
                {"module": "Mathlib.Init", "isExported": False, "isMeta": False, "importAll": False},
            ]}
            commands = []

            def command(label, argv):
                commands.append(argv)
                if "--deps-json" in argv:
                    return json.dumps({"imports": [{"result": header, "errors": []}]})
                self.assertEqual(argv[:3], ["lake", "setup-file", str(root / "mathlib/Mathlib/Example.lean")])
                self.assertEqual(json.loads(argv[3]), header)
                return json.dumps({"name": "Mathlib.Example", "package": "mathlib", "isModule": True,
                                   "options": {"autoImplicit": True, "serverOnly": True}, "importArts": {},
                                   "dynlibs": ["native/NormArith.dylib"], "plugins": []})

            setups, records = benchmark.edited_source_setups(
                {"Mathlib/Example.lean": source}, mathlib=root / "mathlib", lean="lean", lake="lake",
                command=command, output=root / "headers", label="replacement",
                build_setups={"Mathlib/Example.lean": {"name": "Mathlib.Example", "package": "mathlib",
                                                        "options": {"autoImplicit": False}}},
            )
            self.assertEqual(setups["Mathlib/Example.lean"]["dynlibs"], ["native/NormArith.dylib"])
            self.assertEqual(setups["Mathlib/Example.lean"]["options"], {"autoImplicit": False})
            self.assertEqual(records["Mathlib/Example.lean"]["header"], header)
            self.assertEqual(records["Mathlib/Example.lean"]["source_sha256"], benchmark.sha256(source.read_bytes()))
            self.assertEqual(len(commands), 2)

    def test_timing_environment_records_lean_import_workers(self):
        environment = {"PATH": "/usr/bin", "LEAN_IMPORT_WORKERS": "2", "LEAN_NUM_THREADS": "1",
                       "LEAN_CUSTOM_SETTING": "recorded", "UNRELATED_TOKEN": "omit"}
        actual = json.loads(subprocess.check_output([sys.executable, "-c", benchmark.lean_environment_probe()],
                                                    env=environment, text=True))
        self.assertEqual(actual, {"PATH": "/usr/bin", "LEAN_IMPORT_WORKERS": "2", "LEAN_NUM_THREADS": "1",
                                  "LEAN_CUSTOM_SETTING": "recorded"})
        expected = {"lean_environment": actual}
        changed = {"lean_environment": dict(actual, LEAN_IMPORT_WORKERS="4")}
        with self.assertRaisesRegex(benchmark.BenchmarkError, "resolved runtime"):
            benchmark.validate_resolved_calibration({"resolved_runtime": expected}, changed)

    def test_setup_inputs_preserve_plugin_records_and_hash_their_libraries(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            record = {"header_file": str(root / "header.json"), "raw_setup_file": str(root / "raw.json"),
                      "setup_file": str(root / "setup.json"), "dynlibs": ["lib/dynamic.dylib"],
                      "plugins": [{"path": "lib/plugin.dylib", "initFn": "initialize_fixture"}]}
            paths = benchmark.setup_record_inputs({"Mathlib.Example": record}, root)
            self.assertIn(root / "lib/dynamic.dylib", paths)
            self.assertIn(root / "lib/plugin.dylib", paths)
            self.assertEqual(record["plugins"], [{"path": "lib/plugin.dylib", "initFn": "initialize_fixture"}])

    def test_fresh_dependency_preserves_ordinary_and_private_import_parts(self):
        compiled = {"Mathlib.A": [
            ["fresh/A.olean", "fresh/A.olean.server", "fresh/A.olean.private"],
            ["fresh/A.ir.sig", "fresh/A.ir"],
        ]}
        for requested in [
            [["cached/A.olean"]],
            [["cached/A.olean", "cached/A.olean.server"], ["cached/A.ir.sig"]],
            [["cached/A.olean", "cached/A.olean.server", "cached/A.olean.private"],
             ["cached/A.ir.sig", "cached/A.ir"]],
        ]:
            with self.subTest(requested=requested):
                setup = {"importArts": {"Mathlib.A": requested}}
                actual = benchmark.source_setup(setup, compiled)
                expected = [[path.replace("cached/", "fresh/") for path in part] for part in requested]
                self.assertEqual(actual["importArts"]["Mathlib.A"], expected)

    def test_affected_dependencies_compile_before_their_importers(self):
        order = benchmark.dependency_order({
            "Mathlib/Z.lean": {"importArts": {"Mathlib.A": []}},
            "Mathlib/A.lean": {"importArts": {}},
        })
        self.assertEqual(order, ["Mathlib/A.lean", "Mathlib/Z.lean"])
        with self.assertRaisesRegex(benchmark.BenchmarkError, "import cycle"):
            benchmark.dependency_order({"Mathlib/A.lean": {"importArts": {"Mathlib.A": []}}})

    def test_tactic_rebuild_leaves_sources_tests_and_dependency_artifacts_alone(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            preserve = [
                root / "NormArith/Tactic.lean",
                root / ".lake/build/lib/lean/NormArithTest.olean",
                root / ".lake/build/lib/libnorm_x2darith_NormArithTest.dylib",
                root / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Init.olean",
            ]
            remove = [
                root / ".lake/build/lib/lean/NormArith/Tactic.olean",
                root / ".lake/build/ir/NormArith.c",
                root / ".lake/build/lib/libnorm_x2darith_NormArith.dylib",
                root / ".lake/build/lib/libnorm_x2darith_NormArith.dylib.trace",
                root / ".lake/build/lib/libnorm_x2darith_NormArith.a",
            ]
            for path in preserve + remove:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("preserve or invalidate")
            invalidated = benchmark.invalidate_tactic_artifacts(root)
            self.assertTrue(invalidated)
            self.assertTrue(all(path.exists() for path in preserve))
            self.assertFalse(any(path.exists() for path in remove))

    def test_source_headers_are_live_and_cached_dependencies_remain_resolved(self):
        setup = {
            "imports": [{"module": "Old.Header"}],
            "importArts": {"Mathlib.Foo": [["cached/Foo.olean"]]},
            "options": {"autoImplicit": False},
        }
        actual = benchmark.source_setup(setup, {"Mathlib.Bar": [["fresh/Bar.olean"]]})
        self.assertIsNone(actual["imports"])
        self.assertEqual(actual["importArts"]["Mathlib.Foo"], [["cached/Foo.olean"]])
        self.assertNotIn("Mathlib.Bar", actual["importArts"])
        self.assertEqual(actual["options"], {"autoImplicit": False})
        self.assertEqual(setup["imports"], [{"module": "Old.Header"}])

    def test_success_without_fresh_outputs_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            result = benchmark.run_process(
                [sys.executable, "-c", "pass"], root, root / "logs", timeout=5,
            )
            with self.assertRaisesRegex(benchmark.BenchmarkError, "missing compilation output"):
                benchmark.validate_compilation(result, [root / "result.olean"])

    def test_error_diagnostics_with_zero_exit_are_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            output = root / "result.olean"
            script = (
                "import pathlib; "
                f"pathlib.Path({str(output)!r}).write_text('artifact'); "
                "print('{\"severity\": \"error\", \"data\": \"proof failed\"}')"
            )
            result = benchmark.run_process(
                [sys.executable, "-c", script], root, root / "logs", timeout=5,
            )
            with self.assertRaisesRegex(benchmark.BenchmarkError, "error diagnostic"):
                benchmark.validate_compilation(result, [output])

    def test_nonzero_exit_with_outputs_is_not_a_success(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            result = benchmark.run_process(
                [sys.executable, "-c", "raise SystemExit(1)"], root, root / "logs", timeout=5,
            )
            with self.assertRaisesRegex(benchmark.BenchmarkError, "exit code 1"):
                benchmark.validate_compilation(result, [])

    def test_sorry_warning_does_not_validate_an_admitted_proof(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            output = root / "result.olean"
            diagnostic = json.dumps({"severity": "warning", "data": "declaration uses 'sorry'"})
            script = (
                "import pathlib; "
                f"pathlib.Path({str(output)!r}).write_text('artifact'); "
                f"print({diagnostic!r})"
            )
            result = benchmark.run_process(
                [sys.executable, "-c", script], root, root / "logs", timeout=5,
            )
            with self.assertRaisesRegex(benchmark.BenchmarkError, "admitted a proof"):
                benchmark.validate_compilation(result, [output])

    def test_aggregate_is_ratio_of_total_times_not_mean_of_speedups(self):
        measurements = [
            {"phase": "measured", "pair": pair, "variant": variant, "path": path, "seconds": seconds}
            for pair in [0, 1]
            for variant, path, seconds in [
                ("original", "large", 100), ("replacement", "large", 100),
                ("original", "small", 2), ("replacement", "small", 1),
            ]
        ]
        summary = benchmark.summarize(measurements, ["large", "small"], 2)
        self.assertAlmostEqual(summary["aggregate"]["speedup"], 102 / 101)


class LineCountingTests(unittest.TestCase):
    def test_census_instrumentation_is_separate_from_tactic_line_cost(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "NormArith").mkdir()
            (root / "NormArith.lean").write_text("import NormArith.Tactic\n")
            (root / "NormArith/Tactic.lean").write_text("-- comment\ndef tactic := 1\n")
            (root / "NormArith/Census.lean").write_text("def extractor := 1\ndef instrument := 2\n")
            self.assertEqual(benchmark.implementation_line_costs(root), {
                "tactic_implementation_code_lines": 2, "census_implementation_code_lines": 2,
            })

    def test_nested_comments_and_comment_markers_inside_literals(self):
        source = '''/- outer\n/- nested -/\n-/\n\ndef x := "-- /- literal -/" -- ignored\n+def «-- identifier» := '/'\n+r##"/- raw string -/"##\n+'''.replace("\n+", "\n")
        self.assertEqual(benchmark.code_line_count(source), 3)


class ConfirmatoryTests(unittest.TestCase):
    @staticmethod
    def measurements(pairs):
        return [
            {"phase": "measured", "pair": pair, "variant": variant,
             "path": path, "seconds": total * fraction}
            for pair, (original, replacement) in enumerate(pairs)
            for variant, total in ([("original", original), ("replacement", replacement)] if pair % 2 == 0
                                   else [("replacement", replacement), ("original", original)])
            for path, fraction in [("large", 0.75), ("small", 0.25)]
        ]

    def test_blocks_keep_adjacent_order_balanced_pairs_and_all_file_totals(self):
        rows = self.measurements([(1, 1)] * 5 + [(100, 1)])
        blocks = benchmark.paired_blocks(rows, ["large", "small"], 6, 2)
        self.assertEqual([block["pairs"] for block in blocks], [[0, 1], [2, 3], [4, 5]])
        self.assertEqual([block["original_seconds"] for block in blocks], [2, 2, 101])
        self.assertAlmostEqual(benchmark.ratio_of_totals(blocks), 17.5)

    def test_zero_exit_validation_failure_cannot_enter_paired_totals(self):
        rows = self.measurements([(2, 1)] * 4)
        rows[0].update(compilation_status="failed", returncode=0, timed_out=False)
        with self.assertRaisesRegex(benchmark.BenchmarkError, "failed"):
            benchmark.paired_totals(rows, ["large", "small"], 4)


    def test_bootstrap_resamples_whole_paired_blocks_with_a_fixed_seed(self):
        blocks = [{"original_seconds": 2, "replacement_seconds": 1},
                  {"original_seconds": 8, "replacement_seconds": 4},
                  {"original_seconds": 30, "replacement_seconds": 15}]
        draws = benchmark.bootstrap_ratios(blocks, 50, 123)
        self.assertEqual(draws, [2] * 50)
        varying = [dict(block, original_seconds=block["original_seconds"] + i)
                   for i, block in enumerate(blocks)]
        self.assertEqual(benchmark.bootstrap_ratios(varying, 50, 123),
                         benchmark.bootstrap_ratios(varying, 50, 123))
        self.assertNotEqual(benchmark.bootstrap_ratios(varying, 50, 123),
                            benchmark.bootstrap_ratios(varying, 50, 124))

    def test_bca_matches_small_enumerable_bootstrap_example(self):
        blocks = [{"original_seconds": value, "replacement_seconds": 1} for value in [2, 4, 9]]
        interval = benchmark.bca_interval(blocks)
        # The 27 exact resamples have BCa endpoints 8/3 and 9; jackknife values are 6.5, 5.5, 3.
        self.assertAlmostEqual(interval["acceleration"], 0.04525756964727324)
        self.assertAlmostEqual(interval["lower"], 8 / 3)
        self.assertAlmostEqual(interval["upper"], 9)
        self.assertTrue(benchmark.confidence_gate(interval))

    def test_blocks_reject_rows_that_do_not_follow_recorded_ab_ba_order(self):
        rows = self.measurements([(2, 1)] * 6)
        rows[4:8] = rows[6:8] + rows[4:6]
        with self.assertRaisesRegex(benchmark.BenchmarkError, "AB/BA order"):
            benchmark.paired_blocks(rows, ["large", "small"], 6, 2)

    def test_pilot_native_plugin_byte_mismatch_rejects_calibration(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            library = root / "native.dylib"
            library.write_text("native code")

            def resolve(run, *, init_fn="initialize_fixture", option=False, dependency="same artifact", module="NormArith"):
                run.mkdir(exist_ok=True)
                artifact = run / "dependency.olean"
                artifact.write_text(dependency)
                setup = {"name": "Mathlib.Example", "options": {"autoImplicit": option},
                         "importArts": {"Mathlib.Dependency": [[str(artifact)]]},
                         "plugins": [{"path": str(library), "initFn": init_fn}]}
                path = run / "setup.json"
                path.write_text(json.dumps(setup))
                report = {"source_header_setups": {"replacement": {"Mathlib/Example.lean": {
                    "setup_file": str(path), "header": {"isModule": True, "imports": [{"module": module}]},
                    "raw_setup_file": str(run / "server-options.json"),
                }}}, "provenance": {"lean_environment": {"PATH": str(run / "bin") + ":/bin"},
                                     "lean_version": "Lean fixture", "lake_version": "Lake fixture"}}
                return benchmark.resolved_runtime_provenance(report, root, run)

            expected = resolve(root / "pilot")
            current = root / "confirmatory"
            calibration = {"resolved_runtime": expected}
            benchmark.validate_resolved_calibration(calibration, resolve(current))
            library.write_text("changed native code")
            with self.assertRaisesRegex(benchmark.BenchmarkError, "resolved runtime"):
                benchmark.validate_resolved_calibration(calibration, resolve(current))
            library.write_text("native code")
            for changes in [{"init_fn": "different_initializer"}, {"option": True},
                            {"dependency": "changed artifact"}, {"module": "Other.Header"}]:
                with self.subTest(changes=changes), self.assertRaises(benchmark.BenchmarkError):
                    benchmark.validate_resolved_calibration(calibration, resolve(current, **changes))

    def test_undefined_interval_and_boundary_do_not_pass_the_gate(self):
        rows = self.measurements([(2, 1)] * 6)
        result = benchmark.confirmatory_statistics(rows, ["large", "small"], 6, 2, 10000, 9)
        self.assertEqual(result["interval"]["status"], "undefined")
        self.assertFalse(result["success_criterion_met"])
        self.assertFalse(benchmark.confidence_gate({"status": "valid", "lower": 1}))
        self.assertFalse(benchmark.confidence_gate({"status": "undefined", "lower": 2}))
        self.assertTrue(benchmark.confidence_gate({"status": "valid", "lower": 1.01}))

    def test_blocking_rejects_incomplete_imbalanced_and_too_few_blocks(self):
        rows = self.measurements([(2, 1)] * 8)
        for pairs, block_pairs in [(8, 3), (7, 2), (8, 4), (8, 0)]:
            with self.subTest(pairs=pairs, block_pairs=block_pairs):
                with self.assertRaises(benchmark.BenchmarkError):
                    benchmark.paired_blocks(rows, ["large", "small"], pairs, block_pairs)
        with self.assertRaisesRegex(benchmark.BenchmarkError, "incomplete or duplicated"):
            benchmark.paired_blocks(rows[:-1], ["large", "small"], 8, 2)

    def test_mean_ratio_keeps_large_slowdown_even_when_median_is_fast(self):
        rows = self.measurements([(2, 1)] * 7 + [(2, 100)])
        result = benchmark.confirmatory_statistics(rows, ["large", "small"], 8, 2, 10000, 9)
        self.assertAlmostEqual(result["estimate"], 16 / 107)
        self.assertAlmostEqual(result["original_mean_seconds"], 2)
        self.assertAlmostEqual(result["replacement_mean_seconds"], 107 / 8)
        self.assertFalse(result["success_criterion_met"])
        self.assertEqual(benchmark.summarize(rows, ["large", "small"], 8)["aggregate"]["speedup"], 2)


class FrozenPlanTests(unittest.TestCase):
    def test_protocol_hash_changes_when_input_fingerprinting_changes(self):
        original = benchmark.measurement_protocol_sha256()

        def changed_fingerprints(paths):
            return {}

        with mock.patch.object(benchmark, "fingerprint_inputs", changed_fingerprints):
            self.assertNotEqual(benchmark.measurement_protocol_sha256(), original)

    def test_confirmatory_cli_requires_calibration_before_creating_a_run(self):
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / "result"
            error = io.StringIO()
            with contextlib.redirect_stderr(error), self.assertRaises(SystemExit) as raised:
                benchmark.main(["manifest.json", "--confirmatory", "--output", str(output)])
            self.assertEqual(raised.exception.code, 2)
            self.assertIn("--calibration is required", error.getvalue())
            self.assertFalse(output.exists())

    def test_changed_or_removed_input_invalidates_frozen_plan(self):
        with tempfile.TemporaryDirectory() as tmp:
            source = Path(tmp) / "source.lean"
            source.write_text("original")
            frozen = benchmark.fingerprint_inputs([source])
            benchmark.verify_frozen_inputs(frozen)
            source.write_text("changed")
            with self.assertRaisesRegex(benchmark.BenchmarkError, "frozen input changed"):
                benchmark.verify_frozen_inputs(frozen)
            source.unlink()
            with self.assertRaisesRegex(benchmark.BenchmarkError, "frozen input missing"):
                benchmark.verify_frozen_inputs(frozen)

    def test_calibration_is_bound_to_pilot_bytes_and_current_workload(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            provenance = {key: "same" for key in benchmark.CALIBRATION_MATCH_KEYS}
            provenance["project_lean_sources"] = {"NormArith.lean": "a" * 64}
            provenance["repetitions"] = 6
            provenance["warmups"] = 1
            report = {"status": "complete", "selection_status": "frozen",
                      "provenance": provenance, "resolved_runtime": {"schema_version": 1, "variants": {}},
                      "measurements": ConfirmatoryTests.measurements([(2, 1)] * 6),
                      "summary": {"files": [{"path": "large"}, {"path": "small"}]}}
            pilot = root / "pilot.json"
            pilot.write_text(json.dumps(report))
            measurements = root / "measurements.jsonl"
            measurements.write_text("".join(json.dumps(row) + "\n" for row in report["measurements"]))
            calibration = {"schema_version": 1, "date": datetime.now(timezone.utc).date().isoformat(), "block_pairs": 2,
                           "rationale": "Pilot serial diagnostics justify two-pair blocks.",
                           "pilot_report": {"path": pilot.name, "sha256": benchmark.sha256(pilot.read_bytes())},
                           "pilot_measurements": {"path": measurements.name,
                                                  "sha256": benchmark.sha256(measurements.read_bytes())}}
            path = root / "calibration.json"
            path.write_text(json.dumps(calibration))
            validated = benchmark.validate_calibration(path, provenance, ["large", "small"])
            self.assertEqual(validated["block_pairs"], 2)
            with self.assertRaisesRegex(benchmark.BenchmarkError, "current workload"):
                benchmark.validate_calibration(path, dict(provenance, proposed_patch_sha256="different"), ["large", "small"])
            measurements.write_text(measurements.read_text() + "{}\n")
            with self.assertRaisesRegex(benchmark.BenchmarkError, "hash mismatch"):
                benchmark.validate_calibration(path, provenance, ["large", "small"])


class RunPlanTests(unittest.TestCase):
    def test_prepare_only_freezes_full_workload_before_any_process_is_timed(self):
        with tempfile.TemporaryDirectory() as tmp:
            project = Path(tmp) / "project"
            project.mkdir()
            mathlib = project / ".lake/packages/mathlib"
            (mathlib / "Mathlib").mkdir(parents=True)
            source = "import Mathlib.Init\nexample : True := by\n  trivial\n"
            (mathlib / "Mathlib/Example.lean").write_text(source)
            for root in [mathlib, project]:
                subprocess.run(["git", "init", "-q", str(root)], check=True)
                subprocess.run(["git", "-C", str(root), "add", "."], check=True,
                               stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                subprocess.run(["git", "-C", str(root), "-c", "user.name=Test", "-c",
                                "user.email=test@example.org", "commit", "-qm", "fixture", "--allow-empty"],
                               check=True)
            revision = subprocess.check_output(["git", "-C", str(mathlib), "rev-parse", "HEAD"], text=True).strip()
            for name, text in {"lean-toolchain": "leanprover/lean4:test\n", "lake-manifest.json": "{}\n",
                               "lakefile.toml": 'name = "fixture"\n', "NormArith.lean": "-- source\n"}.items():
                (project / name).write_text(text)
            manifest = {"schema_version": 1, "selection_status": "frozen", "mathlib_revision": revision,
                        "files": [{"path": "Mathlib/Example.lean", "source_sha256": benchmark.sha256(source)}],
                        "candidates": [{"id": "example", "path": "Mathlib/Example.lean", "status": "replace",
                                        "start_line": 3, "end_line": 3, "original_sha256": benchmark.sha256("  trivial\n"),
                                        "replacement": "  exact True.intro\n"}]}
            manifest_path = Path(tmp) / "manifest.json"
            manifest_path.write_text(json.dumps(manifest))
            output = Path(tmp) / "run"
            with contextlib.redirect_stdout(io.StringIO()):
                code = benchmark.main([str(manifest_path), "--project", str(project),
                                       "--output", str(output), "--prepare-only"])
            self.assertEqual(code, 0)
            report = json.loads((output / "report.json").read_bytes())
            plan = json.loads((output / "analysis-plan.json").read_bytes())
            self.assertEqual(report["status"], "prepared")
            launch = json.loads((output / "launch.json").read_text())
            self.assertEqual(launch["pid"], os.getpid())
            self.assertEqual(launch["interrupt_signal"], "SIGINT")
            self.assertEqual(report["setup"], [])
            self.assertEqual(report["measurements"], [])
            self.assertEqual(plan["measured_pairs"], 10)
            self.assertEqual(plan["affected_files"], ["Mathlib/Example.lean"])
            self.assertEqual(plan["mode"], "exploratory")
            self.assertFalse(report["inference"]["success_criterion_met"])
            pilot = dict(report, status="complete", provenance=dict(report["provenance"], repetitions=6),
                         resolved_runtime={"schema_version": 1, "variants": {}})
            pilot["summary"] = {"files": [{"path": "Mathlib/Example.lean"}]}
            pilot["measurements"] = [
                {"phase": "measured", "pair": pair, "variant": variant,
                 "path": "Mathlib/Example.lean", "seconds": 2 if variant == "original" else 1}
                for pair in range(6)
                for variant in (["original", "replacement"] if pair % 2 == 0 else ["replacement", "original"])
            ]
            pilot_path = Path(tmp) / "pilot.json"
            pilot_path.write_text(json.dumps(pilot))
            raw_path = Path(tmp) / "pilot.jsonl"
            raw_path.write_text("".join(json.dumps(row) + "\n" for row in pilot["measurements"]))
            calibration = Path(tmp) / "calibration.json"
            calibration.write_text(json.dumps({
                "schema_version": 1, "date": datetime.now(timezone.utc).date().isoformat(),
                "block_pairs": 2, "rationale": "Fixture calibration.",
                "pilot_report": {"path": pilot_path.name, "sha256": benchmark.sha256(pilot_path.read_bytes())},
                "pilot_measurements": {"path": raw_path.name, "sha256": benchmark.sha256(raw_path.read_bytes())},
            }))
            confirmed_output = Path(tmp) / "confirmatory"
            with contextlib.redirect_stdout(io.StringIO()):
                code = benchmark.main([str(manifest_path), "--project", str(project),
                                       "--output", str(confirmed_output), "--prepare-only",
                                       "--confirmatory", "--calibration", str(calibration)])
            self.assertEqual(code, 0)
            confirmed = json.loads((confirmed_output / "analysis-plan.json").read_bytes())
            self.assertEqual(confirmed["measured_pairs"], 40)
            self.assertEqual(confirmed["interval"]["block_pairs"], 2)
            self.assertEqual(confirmed["primary_statistic"], "ratio_of_mean_pass_totals")
            confirmed_report = json.loads((confirmed_output / "report.json").read_bytes())
            self.assertFalse(confirmed_report["inference"]["success_criterion_met"])
            frozen = dict(plan["input_sha256"], **{str(output / "analysis-plan.json"): report["analysis_plan"]["sha256"]})
            benchmark.verify_frozen_inputs(frozen)
            (output / "sources/replacement/Mathlib/Example.lean").write_text("example : True := by sorry\n")
            with self.assertRaisesRegex(benchmark.BenchmarkError, "frozen input changed"):
                benchmark.verify_frozen_inputs(frozen)


if __name__ == "__main__":
    unittest.main()
