import copy
import importlib.util
import json
import math
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


CHECKER = Path(__file__).with_name("verify_style_statistics.py")
spec = importlib.util.spec_from_file_location("verify_style_statistics", CHECKER)
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)


def totals():
    return {"original": [100 + i for i in range(40)],
            "replacement": [80 + 3 * (i % 4) for i in range(40)]}


def fixture(block_pairs):
    values = totals()
    rows = []
    for phase, count in [("warmup", 1), ("measured", 40)]:
        for pair in range(count):
            order = ["original", "replacement"] if pair % 2 == 0 else ["replacement", "original"]
            for variant in order:
                for path in checker.FILES:
                    rows.append({"phase": phase, "pair": pair, "variant": variant, "path": path,
                                 "seconds": values[variant][pair] / 10,
                                 "returncode": 0, "timed_out": False})
    passes = checker.read_passes(rows)
    inference, _ = checker.analyze(passes, block_pairs)
    plan = {"schema_version": 1, "mode": "confirmatory", "measured_pairs": 40,
            "warmup_pairs": 1, "selection_status": "frozen", "affected_files": list(checker.FILES),
            "pair_order": "even: original then replacement; odd: replacement then original",
            "all_affected_files_and_pairs_retained": True, "primary_statistic": "ratio_of_mean_pass_totals",
            "interval": {"method": "paired_nonoverlapping_equal_block_BCa", "confidence_level": 0.95,
                         "block_pairs": block_pairs, "resamples": 10000, "seed": 20261020,
                         "bias_ties": "half_weight", "quantile": "linear_interpolation_at_p_times_n_minus_one",
                         "acceleration": "delete_one_whole_block_jackknife",
                         "success": "valid calibrated interval with lower endpoint strictly greater than one"},
            "calibration": {"block_pairs": block_pairs}}
    plan_bytes = (json.dumps(plan) + "\n").encode()
    report = {"schema_version": 1, "status": "complete", "compilation_order": list(checker.FILES),
              "provenance": {"repetitions": 40, "warmups": 1}, "resolved_calibration_match": True,
              "inference": dict(inference, mode="confirmatory", calibration_validated=True, inputs_unchanged=True),
              "analysis_plan": {"sha256": checker.digest(plan_bytes)}, "measurements": rows,
              "summary": {"aggregate": {variant: {"seconds": numbers} for variant, numbers in passes.items()}}}
    return report, rows, plan_bytes


class ArithmeticTests(unittest.TestCase):
    def test_all_explicit_block_lengths_preserve_the_known_mean_ratio(self):
        for length in [2, 4, 8]:
            with self.subTest(block_pairs=length):
                result, derivation = checker.analyze(totals(), length)
                self.assertAlmostEqual(result["estimate"], 239 / 169, places=14)
                self.assertEqual(result["original_mean_seconds"], 119.5)
                self.assertEqual(result["replacement_mean_seconds"], 84.5)
                self.assertEqual(result["block_count"], 40 // length)
                self.assertEqual(derivation["indices_per_replicate"], 40 // length)
                self.assertEqual(derivation["measured_record_count"], 800)
                self.assertEqual([p for block in result["blocks"] for p in block["pairs"]], list(range(40)))
                first = result["blocks"][0]
                self.assertEqual(first["original_seconds"], sum(range(100, 100 + length)))
                self.assertEqual(first["replacement_seconds"], sum(totals()["replacement"][:length]))
                self.assertEqual(result["success_criterion_met"], result["interval"]["lower"] > 1)
                self.assertLess(result["interval"]["lower"], result["interval"]["upper"])
                if length in (4, 8):
                    self.assertAlmostEqual(result["interval"]["acceleration"], 0, places=12)
                    expected = (4780 - first["original_seconds"]) / (3380 - first["replacement_seconds"])
                    self.assertAlmostEqual(derivation["whole_block_jackknife_estimates"][0], expected, places=14)

    def test_block_length_and_total_validation(self):
        for length in [None, True, 3, 10]:
            with self.assertRaises(ValueError):
                checker.analyze(totals(), length)
        short = totals()
        short["original"].pop()
        with self.assertRaisesRegex(ValueError, "exactly40"):
            checker.analyze(short, 4)
        invalid = totals()
        invalid["replacement"][0] = math.nan
        with self.assertRaisesRegex(ValueError, "finite and positive"):
            checker.analyze(invalid, 4)


class CommandTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.cases = {length: fixture(length) for length in [2, 4, 8]}

    def invoke(self, length, mutate=None, explicit=None):
        report, rows, plan = copy.deepcopy(self.cases[length])
        if mutate:
            mutate(report, rows)
        report["measurements"] = rows
        with tempfile.TemporaryDirectory(prefix="style-statistics-synthetic-") as tmp:
            directory = Path(tmp)
            (directory / "report.json").write_text(json.dumps(report))
            (directory / "measurements.jsonl").write_text("".join(json.dumps(row) + "\n" for row in rows))
            (directory / "analysis-plan.json").write_bytes(plan)
            command = [sys.executable, str(CHECKER), str(directory / "report.json")]
            if explicit is not False:
                command.extend(["--block-pairs", str(length if explicit is None else explicit)])
            result = subprocess.run(command, capture_output=True, text=True)
        return result

    def test_complete_synthetic_cases_for_all_three_lengths(self):
        for length in [2, 4, 8]:
            with self.subTest(block_pairs=length):
                result = self.invoke(length)
                self.assertEqual(result.returncode, 0, result.stderr)
                data = json.loads(result.stdout)
                self.assertEqual(data["status"], "verified")
                self.assertEqual(data["derivation"]["raw_record_count"], 820)
                self.assertEqual(data["derivation"]["blocks"], 40 // length)
                self.assertIn(f"{40 // length} successive randrange({40 // length})", data["methods"]["PRNG"])

    def test_required_block_argument_and_frozen_plan_match(self):
        self.assertEqual(self.invoke(4, explicit=False).returncode, 2)
        mismatch = self.invoke(4, explicit=2)
        self.assertEqual(mismatch.returncode, 1)
        self.assertIn("plan.interval.block_pairs", mismatch.stderr)

    def test_missing_duplicate_order_and_report_tampering_are_rejected(self):
        def order_swap(report, rows):
            rows[40:60] = rows[50:60] + rows[40:50]
        mutations = [
            (lambda report, rows: rows.pop(), "missing or extra raw records"),
            (lambda report, rows: rows.append(copy.deepcopy(rows[-1])), "missing or extra raw records"),
            (lambda report, rows: rows.__setitem__(-1, copy.deepcopy(rows[-2])), "wrong key/order"),
            (order_swap, "wrong key/order"),
            (lambda report, rows: report["inference"].__setitem__("estimate", 1), "inference.estimate"),
            (lambda report, rows: rows[-1].__setitem__("returncode", 1), "failed/missing compiler result"),
        ]
        for mutation, message in mutations:
            with self.subTest(rejection=message):
                result = self.invoke(4, mutation)
                self.assertEqual(result.returncode, 1)
                self.assertIn(message, result.stderr)


if __name__ == "__main__":
    unittest.main()
