import copy
import importlib.util
import math
from pathlib import Path
import unittest


spec = importlib.util.spec_from_file_location("pilot_serial_diagnostics", Path(__file__).with_name("pilot_serial_diagnostics.py"))
diagnostic = importlib.util.module_from_spec(spec)
spec.loader.exec_module(diagnostic)


def fixture():
    rows = []
    for pair in range(24):
        order = ["original", "replacement"] if pair % 2 == 0 else ["replacement", "original"]
        for variant in order:
            for path in ["A.lean", "B.lean"]:
                seconds = (pair + 1) * (2 if variant == "original" else 1)
                rows.append({"phase": "measured", "pair": pair, "variant": variant,
                             "path": path, "seconds": seconds, "returncode": 0})
    return {"schema_version": 1, "status": "complete", "provenance": {"repetitions": 24},
            "compilation_order": ["A.lean", "B.lean"], "measurements": rows}, rows


class DiagnosticsTests(unittest.TestCase):
    def test_autocorrelation_uses_full_series_mean_and_denominator(self):
        actual = diagnostic.autocorrelations([1, 2, 3, 4])
        self.assertAlmostEqual(actual["1"], 0.25)
        self.assertAlmostEqual(actual["2"], -0.3)
        self.assertAlmostEqual(actual["3"], -0.45)
        self.assertIsNone(actual["4"])
        self.assertTrue(all(value is None for value in diagnostic.autocorrelations([7, 7, 7]).values()))

    def test_chronology_aggregation_sequence_drift_and_blocks(self):
        report, rows = fixture()
        result = diagnostic.diagnostics(report, rows)
        self.assertEqual(len(result["chronological_pairs"]), 24)
        self.assertEqual(result["chronological_pairs"][1]["sequence"], "BA")
        self.assertEqual(result["chronological_pairs"][1]["original_seconds"], 8)
        self.assertAlmostEqual(result["chronological_pairs"][1]["log_paired_ratio"], math.log(2))
        self.assertEqual(result["sequence_means"]["AB"]["original_mean_seconds"], 48)
        self.assertEqual(result["sequence_means"]["BA"]["original_mean_seconds"], 52)
        self.assertEqual(result["half_run_drift"]["first_half"]["original_mean_seconds"], 26)
        self.assertEqual(result["half_run_drift"]["second_half"]["original_mean_seconds"], 74)
        for length, count in [(2, 12), (4, 6), (8, 3)]:
            block = result["compatible_block_diagnostics"][str(length)]
            self.assertEqual(block["pilot_blocks"], count)
            self.assertEqual(block["confirmatory_blocks_at_40_pairs"], 40 // length)
            self.assertEqual([i for row in block["block_rows"] for i in row["pairs"]], list(range(24)))
            self.assertEqual(block["summary_of_block_pair_means"]["ratio_of_means"], 2)
            self.assertTrue(all(row["AB_pairs"] == row["BA_pairs"] for row in block["block_rows"]))

    def test_refuses_raw_report_mismatch(self):
        report, rows = fixture()
        with self.assertRaisesRegex(ValueError, "differ"):
            diagnostic.diagnostics(report, rows[:-1])

    def test_refuses_incomplete_pair_and_wrong_sequence(self):
        report, rows = fixture()
        report["measurements"] = rows[:-1]
        with self.assertRaises(diagnostic.BenchmarkError):
            diagnostic.diagnostics(report, rows[:-1])
        report, rows = fixture()
        bad = copy.deepcopy(rows)
        bad[:4] = bad[2:4] + bad[:2]
        report["measurements"] = bad
        with self.assertRaisesRegex(diagnostic.BenchmarkError, "order"):
            diagnostic.diagnostics(report, bad)

    def test_refuses_noncomplete_or_non24_pair_runs(self):
        for key, value in [("status", "running"), ("schema_version", 2)]:
            report, rows = fixture()
            report[key] = value
            with self.assertRaises(ValueError):
                diagnostic.diagnostics(report, rows)
        report, rows = fixture()
        report["provenance"]["repetitions"] = 40
        with self.assertRaisesRegex(ValueError, "exactly 24"):
            diagnostic.diagnostics(report, rows)


if __name__ == "__main__":
    unittest.main()
