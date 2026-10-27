"""Checks for benchmark accounting and failure handling, independent of Lean."""

import tempfile
import unittest
from pathlib import Path

from benchmark_snippets import code_lines, inspect_pair, snippet_parts, strip_comments, summarize, variant_order


class BenchmarkAccountingTests(unittest.TestCase):
    def test_nested_comments_do_not_count_as_code(self):
        source = "-- header\n/- outer\n /- nested -/\n-/\nexample : True := by\n  trivial -- end\n"
        self.assertEqual(code_lines(source), 2)
        self.assertEqual(strip_comments(source).count("\n"), source.count("\n"))

    def test_comments_inside_strings_are_preserved(self):
        source = '#check "-- not a comment /- nor this -/" -- actual comment\n'
        self.assertEqual(code_lines(source), 1)
        self.assertIn('"-- not a comment /- nor this -/"', strip_comments(source))

    def test_unterminated_block_is_rejected(self):
        with self.assertRaises(ValueError):
            strip_comments("/- incomplete")

    def test_missing_or_duplicate_markers_are_rejected(self):
        with self.assertRaises(ValueError):
            snippet_parts("example : True := by trivial")

    def test_order_alternates_within_every_case(self):
        for index in range(5):
            self.assertEqual(variant_order(0, index), variant_order(1, index)[::-1])

    def test_statement_mismatch_is_rejected(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            for variant, target in (("Baseline", "True"), ("Tactic", "False")):
                path = root / "Benchmarks" / variant / "Example.lean"
                path.parent.mkdir(parents=True)
                path.write_text(
                    f"-- BENCHMARK-STATEMENT\nexample : {target} := by\n"
                    "  -- BENCHMARK-PROOF\n  trivial\n  -- BENCHMARK-END\n"
                )
            with self.assertRaisesRegex(ValueError, "statements differ"):
                inspect_pair(root, {"id": "Example"})

    def test_source_theorem_cannot_close_its_own_benchmark(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            for variant in ("Baseline", "Tactic"):
                path = root / "Benchmarks" / variant / "Example.lean"
                path.parent.mkdir(parents=True)
                path.write_text(
                    "-- BENCHMARK-STATEMENT\nexample : True := by\n"
                    "  -- BENCHMARK-PROOF\n  exact source_lemma\n  -- BENCHMARK-END\n"
                )
            with self.assertRaisesRegex(ValueError, "source theorem"):
                inspect_pair(root, {"id": "Example", "forbidden_identifiers": ["source_lemma"]})

    def test_custom_paths_and_backend_options(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            for name, option in (("Old", "useLP false"), ("New", "forceLP true")):
                (root / f"{name}.lean").write_text(
                    f"set_option norm_arith.{option}\n"
                    "-- BENCHMARK-STATEMENT\nexample : True := by\n"
                    "  -- BENCHMARK-PROOF\n  trivial\n  -- BENCHMARK-END\n"
                )
            result = inspect_pair(root, {"id": "Example", "baseline": "Old.lean", "tactic": "New.lean"})
            self.assertEqual(result["Baseline"]["file"], "Old.lean")
            self.assertEqual(result["Tactic"]["file"], "New.lean")
            self.assertEqual(result["net_code_lines_saved"], 0)

    def test_different_local_contexts_are_rejected(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            for name, domain in (("Old", "Nat"), ("New", "Real")):
                (root / f"{name}.lean").write_text(
                    f"variable (x : {domain})\n"
                    "-- BENCHMARK-STATEMENT\nexample : x = x := by\n"
                    "  -- BENCHMARK-PROOF\n  rfl\n  -- BENCHMARK-END\n"
                )
            with self.assertRaisesRegex(ValueError, "contexts differ"):
                inspect_pair(root, {"id": "Example", "baseline": "Old.lean", "tactic": "New.lean"})

    def test_failed_sample_prevents_aggregate_ratio(self):
        cases = [{"id": "A", "kind": "exact theorem"}]
        metrics = {"A": {
            "Baseline": {"code_lines": 8, "proof_lines": 3},
            "Tactic": {"code_lines": 7, "proof_lines": 1},
            "net_code_lines_saved": 1, "proof_lines_saved": 2,
        }}
        rows = [
            {"phase": "measure", "pair": 0, "id": "A", "variant": variant,
             "seconds": 1.0, "success": variant == "Baseline"}
            for variant in ("Baseline", "Tactic")
        ]
        result = summarize(cases, rows, metrics, 1)
        self.assertFalse(result["all_compilations_succeeded"])
        self.assertIsNone(result["ratio_of_median_totals"])
        self.assertEqual(result["net_code_lines_saved"], 1)


if __name__ == "__main__":
    unittest.main()
