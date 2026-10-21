import contextlib
import hashlib
import importlib.util
import io
import json
import math
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


CHECKER = module("expanded_independent_statistics", Path(__file__).with_name("verify_expanded_statistics.py"))
BENCHMARK = module("timing_reference", ROOT / "scripts/benchmark.py")


class ExpandedStatisticsTests(unittest.TestCase):
    def check(self, pairs=40, block=4, *, degenerate=False, mutate=None):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            paths = ["Mathlib/A.lean", "Mathlib/Other.lean"]
            rows = []
            for phase, count in [("warmup", 1), ("measured", pairs)]:
                for pair in range(count):
                    order = ["original", "replacement"] if pair % 2 == 0 else ["replacement", "original"]
                    for variant in order:
                        for index, path in enumerate(paths):
                            seconds = (10 if variant == "original" else 9) + index
                            if not degenerate:
                                seconds += math.sin(pair + (0 if variant == "original" else 1)) / 5
                            rows.append({"phase": phase, "pair": pair, "variant": variant, "path": path,
                                         "seconds": seconds, "returncode": 0, "timed_out": False,
                                         "compilation_status": "verified", "artifact_sha256": {"fresh.olean": "a" * 64}})
            plan = {"schema_version": 1, "mode": "confirmatory", "measured_pairs": pairs,
                    "warmup_pairs": 1, "selection_status": "frozen", "affected_files": list(reversed(paths)),
                    "pair_order": "even: original then replacement; odd: replacement then original",
                    "all_affected_files_and_pairs_retained": True,
                    "primary_statistic": "ratio_of_mean_pass_totals",
                    "interval": {"method": "paired_nonoverlapping_equal_block_BCa", "confidence_level": 0.95,
                                 "block_pairs": block, "resamples": 10000, "seed": 20261020,
                                 "bias_ties": "half_weight", "quantile": "linear_interpolation_at_p_times_n_minus_one",
                                 "acceleration": "delete_one_whole_block_jackknife",
                                 "success": "valid calibrated interval with lower endpoint strictly greater than one"},
                    "calibration": {"block_pairs": block}}
            (root / "analysis-plan.json").write_text(json.dumps(plan))
            report = {"schema_version": 1, "status": "complete", "compilation_order": paths,
                      "provenance": {"repetitions": pairs, "warmups": 1}, "resolved_calibration_match": True,
                      "manifest": {"candidates": [{"path": path, "status": "replace"} for path in paths]},
                      "measurements": rows, "analysis_plan": {"sha256": hashlib.sha256((root / "analysis-plan.json").read_bytes()).hexdigest()},
                      "inference": {"mode": "confirmatory", "calibration_validated": True, "inputs_unchanged": True,
                                    **BENCHMARK.confirmatory_statistics(rows, paths, pairs, block, 10000, 20261020)},
                      "summary": BENCHMARK.summarize(rows, paths, pairs)}
            if mutate:
                mutate(report, rows)
            (root / "report.json").write_text(json.dumps(report))
            (root / "measurements.jsonl").write_text("".join(json.dumps(row) + "\n" for row in rows))
            with mock.patch.object(sys, "argv", ["checker", str(root / "report.json")]), \
                    contextlib.redirect_stdout(io.StringIO()) as stdout, contextlib.redirect_stderr(io.StringIO()):
                code = CHECKER.main()
            return code, json.loads(stdout.getvalue()) if code == 0 else None

    def test_both_predeclared_designs_match_the_independent_implementation(self):
        for pairs, block in [(40, 4), (80, 8)]:
            with self.subTest(pairs=pairs):
                code, result = self.check(pairs, block)
                self.assertEqual(code, 0)
                self.assertEqual(result["derivation"]["affected_file_count"], 2)
                self.assertEqual(result["derivation"]["blocks"], 10)

    def test_undefined_interval_is_verified_as_unsuccessful(self):
        code, result = self.check(degenerate=True)
        self.assertEqual(code, 0)
        self.assertEqual(result["recomputed_inference"]["interval"]["status"], "undefined")
        self.assertFalse(result["recomputed_inference"]["success_criterion_met"])

    def test_missing_output_evidence_or_selected_file_cannot_pass(self):
        for mutate in [lambda report, rows: rows[0].pop("artifact_sha256"),
                       lambda report, rows: report["manifest"]["candidates"].pop()]:
            code, _ = self.check(mutate=mutate)
            self.assertEqual(code, 1)


if __name__ == "__main__":
    unittest.main()
