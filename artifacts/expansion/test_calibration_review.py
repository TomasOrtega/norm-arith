import importlib.util
import json
import math
from pathlib import Path
import unittest


SPEC = importlib.util.spec_from_file_location("calibration_review", Path(__file__).with_name("calibration_review.py"))
REVIEW = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(REVIEW)


class CalibrationReviewTests(unittest.TestCase):
    def test_blinded_fields_are_invariant_to_constant_speed_effects(self):
        def make(scale):
            rows = []
            for pair in range(24):
                original = 100 + math.sin(pair) + pair / 10
                replacement = (90 + math.cos(pair) + pair / 12) * scale
                variants = [("original", original), ("replacement", replacement)]
                if pair % 2:
                    variants.reverse()
                rows.extend({"phase": "measured", "pair": pair, "path": "file", "variant": variant,
                             "seconds": seconds} for variant, seconds in variants)
            report = {"schema_version": 1, "status": "complete", "provenance": {"repetitions": 24},
                      "compilation_order": ["file"], "measurements": rows}
            return REVIEW.blinded_review(report, rows)

        def compare(left, right):
            if isinstance(left, dict):
                self.assertEqual(set(left), set(right))
                for key in left:
                    compare(left[key], right[key])
            elif isinstance(left, float):
                self.assertAlmostEqual(left, right, places=10)
            else:
                self.assertEqual(left, right)

        compare(make(1), make(4))
        text = json.dumps(make(1))
        self.assertNotIn("ratio_of_means", text)
        self.assertNotIn('"original_mean_seconds":', text)
        self.assertNotIn('"replacement_mean_seconds":', text)


if __name__ == "__main__":
    unittest.main()
