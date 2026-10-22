"""Keep plot accounting, file coverage, and aggregate uncertainty faithful."""

import copy
import unittest

from plots import plot_data, plot_source


def fixture():
    return {"patch": {
        "affected_files": ["A.lean", "B.lean", "C.lean"],
        "accounting": {"original_proof_lines": 20, "replacement_proof_lines": 8,
                       "added_helper_lines": 1, "added_import_lines": 2,
                       "net_lines_saved_including_imports": 9}},
        "timing": {"files": [
            {"path": "A.lean", "original_mean_seconds": 10, "replacement_mean_seconds": 5, "ratio": 2},
            {"path": "B.lean", "original_mean_seconds": 10, "replacement_mean_seconds": 10, "ratio": 1},
            {"path": "C.lean", "original_mean_seconds": 3, "replacement_mean_seconds": 5, "ratio": 0.6}],
            "primary_statistic": "ratio_of_mean_pass_totals", "estimate": 1.15,
            "original_mean_seconds": 23, "replacement_mean_seconds": 20,
            "interval": {"status": "valid", "confidence_level": 0.95, "lower": 1.1, "upper": 1.2},
            "block_count": 10, "block_pairs": 4}}


class PlotTests(unittest.TestCase):
    def test_all_files_and_costs_survive_with_distinct_aggregate(self):
        evidence = fixture()
        original = copy.deepcopy(evidence)
        data = plot_data(evidence)
        self.assertEqual(evidence, original)
        self.assertEqual([row["path"] for row in data["files"]], ["C.lean", "B.lean", "A.lean"])
        self.assertEqual(data["slower_file_count"], 1)
        self.assertEqual(data["replacement_total_lines"], 11)
        self.assertEqual(data["aggregate"]["ratio"], 1.15)
        self.assertNotAlmostEqual(data["aggregate"]["ratio"], sum(row["ratio"] for row in data["files"]) / 3)
        source = plot_source(data)
        self.assertIn("(0.6,1)", source)
        self.assertIn("(1,2) (2,3)", source)
        self.assertIn("(1.15,-7)", source)
        self.assertIn("(axis cs:1.1,-7) -- (axis cs:1.2,-7)", source)
        self.assertNotIn("@", source)

    def test_missing_or_duplicate_files_are_rejected(self):
        for change in (lambda rows: rows.pop(), lambda rows: rows.append(copy.deepcopy(rows[0]))):
            evidence = fixture()
            change(evidence["timing"]["files"])
            with self.assertRaisesRegex(ValueError, "each affected file"):
                plot_data(evidence)

    def test_mismatched_line_costs_are_rejected(self):
        evidence = fixture()
        evidence["patch"]["accounting"]["added_import_lines"] = 0
        with self.assertRaisesRegex(ValueError, "accounting"):
            plot_data(evidence)

    def test_inconsistent_file_ratio_is_rejected(self):
        evidence = fixture()
        evidence["timing"]["files"][2]["ratio"] = 1.6
        with self.assertRaisesRegex(ValueError, "recorded means"):
            plot_data(evidence)


if __name__ == "__main__":
    unittest.main()
