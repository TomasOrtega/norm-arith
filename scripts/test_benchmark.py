import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest


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
                root / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Init.olean",
            ]
            remove = [
                root / ".lake/build/lib/lean/NormArith/Tactic.olean",
                root / ".lake/build/ir/NormArith.c",
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
    def test_nested_comments_and_comment_markers_inside_literals(self):
        source = '''/- outer\n/- nested -/\n-/\n\ndef x := "-- /- literal -/" -- ignored\n+def «-- identifier» := '/'\n+r##"/- raw string -/"##\n+'''.replace("\n+", "\n")
        self.assertEqual(benchmark.code_line_count(source), 3)


if __name__ == "__main__":
    unittest.main()
