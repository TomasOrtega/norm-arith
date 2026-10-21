import unittest

from benchmark import sha256
from select_census import SelectionError, candidate_from_proposal, choose_intervals, select_file


class SelectionTests(unittest.TestCase):
    def proposal(self, source, text, replacement="by norm_arith"):
        start = source.index(text)
        return {
            "path": "Mathlib/Test.lean", "key": "term:example", "parent_declaration": "example",
            "status": "success", "kernel_checked": True, "replacement_eligible": True,
            "start_byte": start, "end_byte": start + len(text), "replacement": replacement,
            "body_start_byte": start, "body_end_byte": start + len(text),
            "source_sha256": sha256(source), "original_sha256": sha256(text),
        }

    def test_utf8_partial_lines_preserve_surrounding_source(self):
        source = "-- α\nexample : True := by\n  trivial\n  done\n".encode()
        proposal = self.proposal(source, b"by\n  trivial\n  done")
        result = candidate_from_proposal(proposal, source)
        self.assertEqual((result["start_line"], result["end_line"]), (2, 4))
        self.assertEqual(result["replacement"], "example : True := by norm_arith\n")
        self.assertEqual(result["proof_lines_saved"], 2)

    def test_long_proof_is_formatted_before_savings_and_import_cost(self):
        source = (
            "      _ = ‖newton_seq (n + k + 1) - newton_seq (n + k) + "
            "(newton_seq (n + k) - newton_seq n)‖ := by\n"
            "        rw [← sub_add_sub_cancel]\n"
        ).encode()
        proposal = self.proposal(source, "by\n        rw [← sub_add_sub_cancel]".encode())
        result = candidate_from_proposal(proposal, source)
        self.assertEqual(result["replacement"], source.decode().splitlines()[0] + "\n        norm_arith\n")
        self.assertEqual(result["proof_lines_saved"], 0)
        second = {**result, "id": "second", "start_line": 4, "end_line": 5,
                  "replacement": "      _ = 0 := by norm_arith\n", "proof_lines_saved": 1}
        selected, ledger = select_file([result, second], import_lines=1)
        self.assertEqual(selected, [])
        self.assertEqual(ledger[result["id"]], "no_line_saving")
        self.assertEqual(ledger["second"], "import_cost_offsets_savings")

    def test_wrapping_retains_genuine_line_savings(self):
        source = ("      _ = ‖newton_seq (n + k + 1) - newton_seq (n + k) + "
                  "(newton_seq (n + k) - newton_seq n)‖ := by\n"
                  "        rw [← sub_add_sub_cancel]\n        skip\n        done\n").encode()
        proof = "by\n        rw [← sub_add_sub_cancel]\n        skip\n        done".encode()
        result = candidate_from_proposal(self.proposal(source, proof), source)
        self.assertEqual(result["replacement_proof_lines"], 2)
        self.assertEqual(result["proof_lines_saved"], 2)
        self.assertTrue(all(len(line) <= 100 for line in result["replacement"].splitlines()))

    def test_line_limit_counts_unicode_characters(self):
        source = ("example : " + "α" * 66 + " := by\n  trivial\n").encode()
        result = candidate_from_proposal(self.proposal(source, b"by\n  trivial"), source)
        line = result["replacement"].rstrip("\n")
        self.assertGreater(len(line.encode()), 100)
        self.assertLessEqual(len(line), 100)
        self.assertEqual(result["replacement_proof_lines"], 1)

    def test_hash_and_checked_proof_are_required(self):
        source = b"example : True := by trivial\n"
        proposal = self.proposal(source, b"by trivial")
        for changes in [{"original_sha256": "bad"}, {"source_sha256": "bad"},
                        {"kernel_checked": False}, {"replacement_eligible": False}]:
            with self.subTest(changes=changes), self.assertRaises(SelectionError):
                candidate_from_proposal({**proposal, **changes}, source)

    def test_proof_arguments_in_declaration_headers_cannot_be_edited(self):
        source = b"example (h : True := by trivial) : True := by trivial\n"
        proposal = self.proposal(source, b"by trivial")
        body = source.rindex(b"by trivial")
        with self.assertRaises(SelectionError):
            candidate_from_proposal({**proposal, "body_start_byte": body,
                                     "body_end_byte": len(source)}, source)

    def test_interval_selection_maximizes_total_savings(self):
        candidates = [
            {"id": "outer", "start_line": 1, "end_line": 9, "proof_lines_saved": 3},
            {"id": "first", "start_line": 1, "end_line": 3, "proof_lines_saved": 2},
            {"id": "second", "start_line": 5, "end_line": 9, "proof_lines_saved": 2},
        ]
        expected = ["first", "second"]
        self.assertEqual([item["id"] for item in choose_intervals(candidates)], expected)
        self.assertEqual([item["id"] for item in choose_intervals(list(reversed(candidates)))], expected)

    def test_equal_weight_prefers_fewer_replacements(self):
        candidates = [
            {"id": "outer", "start_line": 1, "end_line": 9, "proof_lines_saved": 4},
            {"id": "first", "start_line": 1, "end_line": 3, "proof_lines_saved": 2},
            {"id": "second", "start_line": 5, "end_line": 9, "proof_lines_saved": 2},
        ]
        self.assertEqual([item["id"] for item in choose_intervals(candidates)], ["outer"])

    def test_import_cost_and_duplicate_observations_are_charged_once(self):
        candidate = {"id": "a", "start_line": 1, "end_line": 3,
                     "replacement": "by norm_arith\n", "proof_lines_saved": 2}
        duplicate = {**candidate, "id": "b"}
        selected, ledger = select_file([duplicate, candidate], import_lines=1)
        self.assertEqual([item["id"] for item in selected], ["a"])
        self.assertEqual(ledger["b"], "duplicate_replacement")
        selected, ledger = select_file([{**candidate, "proof_lines_saved": 1}], import_lines=1)
        self.assertEqual(selected, [])
        self.assertEqual(ledger["a"], "import_cost_offsets_savings")


if __name__ == "__main__":
    unittest.main()
