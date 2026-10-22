"""Check extraction of the community request from verified source bytes."""

import hashlib
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import generate


REQUEST = (
    '-- The 2020 motivating example: 2a + b = 3a + (b - a).\n'
    'example (a b : E) : ‖(2 : ℝ) • a + b‖ ≤ 3 * ‖a‖ + ‖b - a‖ := by\n'
    '  norm_arith [le_refl ‖a‖, le_refl ‖b - a‖]\n'
)


class CommunityRequestTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name)
        self.source = self.directory / 'project/NormArithTest/Tactic.lean'
        self.source.parent.mkdir(parents=True)
        self.source.write_text('-- Synthetic unit-test text, not Lean evidence.\n\n' + REQUEST + '\n')
        self.inventory = {'NormArithTest/Tactic.lean': self.sha(self.source.read_bytes())}
        self.evidence = {'project_source_root': self.directory / 'project',
                         'patch': {'verification': {'project_lean_sources': self.inventory}}}
        self.generated = self.directory / 'generated'
        self.generated.mkdir()

    @staticmethod
    def sha(data):
        return hashlib.sha256(data).hexdigest()

    def extract(self):
        with patch.object(generate, 'GENERATED', self.generated):
            return generate.community_request_data(self.evidence)

    def test_extracts_exact_source_bytes_with_line_and_hash_provenance(self):
        result = self.extract()
        self.assertEqual((self.generated / 'community-request.lean').read_bytes(), REQUEST.encode())
        self.assertEqual((self.generated / 'community-request.tex').read_text(),
                         '\\VerbatimInput{generated/community-request.lean}\n')
        self.assertEqual((result['start_line'], result['end_line']), (3, 5))
        self.assertEqual(result['source'], 'NormArithTest/Tactic.lean')
        self.assertEqual(result['source_sha256'], self.inventory[result['source']])
        self.assertEqual(result['sha256'], self.sha(REQUEST.encode()))

    def test_changed_source_hash_is_rejected(self):
        self.source.write_text(self.source.read_text() + '-- drift\n')
        with self.assertRaisesRegex(ValueError, 'source hash'):
            self.extract()
        self.assertFalse((self.generated / 'community-request.lean').exists())

    def test_changed_body_is_rejected_even_with_updated_source_hash(self):
        self.source.write_text(self.source.read_text().replace('norm_arith [', 'other_tactic ['))
        self.inventory['NormArithTest/Tactic.lean'] = self.sha(self.source.read_bytes())
        with self.assertRaisesRegex(ValueError, 'community request.*anchor'):
            self.extract()

    def test_duplicate_anchor_is_rejected(self):
        self.source.write_text(self.source.read_text() + REQUEST)
        self.inventory['NormArithTest/Tactic.lean'] = self.sha(self.source.read_bytes())
        with self.assertRaisesRegex(ValueError, 'community request.*anchor'):
            self.extract()

    def test_missing_source_fails_without_workspace_fallback(self):
        self.source.unlink()
        with self.assertRaisesRegex(ValueError, 'missing.*source'):
            self.extract()

    def test_source_requires_verification_fingerprint(self):
        self.inventory.clear()
        with self.assertRaisesRegex(ValueError, 'verification fingerprint'):
            self.extract()


if __name__ == '__main__':
    unittest.main()
