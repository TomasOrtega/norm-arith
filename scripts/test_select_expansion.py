import json
from pathlib import Path
import tempfile
import unittest

from benchmark import BenchmarkError, sha256
from select_expansion import merge_manifests


class ExpansionSelectionTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        (self.root / "Mathlib").mkdir()
        self.source = b"import Mathlib.Init\nexample : True := by\n  skip\n  trivial\nexample : True := by\n  skip\n  trivial\n"
        (self.root / "Mathlib/A.lean").write_bytes(self.source)

    def manifest(self, first, last, replacement, identifier):
        first, last = first + 1, last + 1
        lines = self.source.splitlines(keepends=True)
        left = sum(map(len, lines[:first - 1]))
        right = sum(map(len, lines[:last]))
        start = left + lines[first - 1].index(b"by")
        return {"mathlib_revision": "a" * 40, "files": [
            {"path": "Mathlib/A.lean", "source_sha256": sha256(self.source),
             "imports": [], "helpers": []}], "candidates": [
            {"id": identifier, "path": "Mathlib/A.lean", "declaration": identifier,
             "status": "unchanged", "start_line": first, "end_line": last,
             "original_sha256": sha256(self.source[left:right]), "replacement": replacement,
             "source_start_byte": start, "source_end_byte": right - 1,
             "body_start_byte": start, "body_end_byte": right - 1}]}

    def test_combines_import_offset_candidates_and_charges_preparation(self):
        first = self.manifest(1, 3, "example : True := by\n  norm_arith\n", "a")
        second = self.manifest(4, 6, "example : True := by\n  norm_arith\n", "b")
        merged, _, accounting = merge_manifests([first, second], self.root)
        self.assertEqual(sum(c["status"] == "replace" for c in merged["candidates"]), 2)
        self.assertEqual(accounting["net_lines_saved_including_imports"], 1)
        self.assertEqual(accounting["added_import_lines"], 1)
        self.assertEqual(merged["candidates"][0]["proof_replacement"], "by\n  norm_arith")

    def test_duplicates_do_not_inflate_savings(self):
        original = self.manifest(1, 3, "example : True := by norm_arith\n", "a")
        merged, _, accounting = merge_manifests([original, original], self.root)
        self.assertEqual(len(merged["candidates"]), 1)
        self.assertEqual(accounting["net_lines_saved_including_imports"], 1)

    def test_same_id_with_different_replacement_is_an_error(self):
        original = self.manifest(1, 3, "example : True := by norm_arith\n", "a")
        different = json.loads(json.dumps(original))
        different["candidates"][0]["replacement"] = "example : True := by\n  norm_arith\n"
        with self.assertRaisesRegex(BenchmarkError, "conflicting candidate"):
            merge_manifests([original, different], self.root)

    def test_changed_statement_is_rejected(self):
        original = self.manifest(1, 3, "example : False := by norm_arith\n", "a")
        with self.assertRaisesRegex(BenchmarkError, "outside the proof"):
            merge_manifests([original], self.root)

    def test_stale_source_is_rejected(self):
        original = self.manifest(1, 3, "example : True := by norm_arith\n", "a")
        (self.root / "Mathlib/A.lean").write_text("changed")
        with self.assertRaisesRegex(BenchmarkError, "source hash"):
            merge_manifests([original], self.root)


if __name__ == "__main__":
    unittest.main()
