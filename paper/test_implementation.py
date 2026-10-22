"""Check exact measured-source appendix generation without invoking Lean."""

import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import evidence
import generate


class ImplementationAppendixTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name)
        self.project = self.directory / 'portable/project'
        self.sources = {
            'NormArith.lean': b'module\npublic import NormArith.Tactic\n',
            'NormArith/Tactic.lean': (b'module\npublic import NormArith.Certificate\n'
                                     b'public meta import NormArith.Search\n'
                                     b'public meta import NormArith.Metric\n-- final bytes  \n\n'),
            'NormArith/Certificate.lean': b'module\n-- synthetic certificate\n',
            'NormArith/Search.lean': b'module\n-- synthetic search\n',
            'NormArith/Metric.lean': b'module\n-- synthetic metric\n',
            'NormArith/Census.lean': b'-- extractor is outside runtime import closure\n',
        }
        for name, data in self.sources.items():
            path = self.project / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
        self.inventory = {name: hashlib.sha256(data).hexdigest() for name, data in self.sources.items()}
        self.result = {'project_source_root': self.project,
                       'patch': {'verification': {'project_lean_sources': self.inventory}}}
        self.aggregate = evidence.implementation_sha(self.project)
        self.generated = self.directory / 'generated'
        self.generated.mkdir()
        self.excerpts = [
            {'id':'certificate', 'relative_source':'NormArith/Certificate.lean',
             'first_line':2, 'last_line':2, 'first_anchor':'-- synthetic certificate',
             'last_anchor':'-- synthetic certificate'},
            {'id':'search', 'relative_source':'NormArith/Search.lean',
             'first_line':2, 'last_line':2, 'first_anchor':'-- synthetic search',
             'last_anchor':'-- synthetic search'},
            {'id':'tactic', 'relative_source':'NormArith/Tactic.lean',
             'first_line':2, 'last_line':4, 'first_anchor':'public import NormArith.Certificate',
             'last_anchor':'public meta import NormArith.Metric'},
        ]

    def generate(self):
        with patch.object(generate, 'GENERATED', self.generated):
            return generate.implementation_data(self.result, self.aggregate, excerpt_specs=self.excerpts)

    def test_exact_bytes_and_selected_excerpt_wrappers_exclude_extractor(self):
        manifest = self.generate()
        self.assertEqual(manifest['implementation_sha256'], self.aggregate)
        self.assertEqual(len(manifest['modules']), 5)
        self.assertEqual(json.loads((self.generated / 'implementation.json').read_bytes()), manifest)
        self.assertEqual({row['relative_source'] for row in manifest['modules']},
                         set(self.sources) - {'NormArith/Census.lean'})
        for row in manifest['modules']:
            data = self.sources[row['relative_source']]
            self.assertEqual((self.generated / row['generated_path']).read_bytes(), data)
            self.assertEqual(row['sha256'], hashlib.sha256(data).hexdigest())
            self.assertEqual(row['bytes'], len(data))
        self.assertEqual(len(manifest['excerpts']), 3)
        for row in manifest['excerpts']:
            selected = b''.join(self.sources[row['relative_source']].splitlines(keepends=True)[
                row['first_line']-1:row['last_line']])
            self.assertEqual(row['excerpt_sha256'], hashlib.sha256(selected).hexdigest())
            self.assertEqual((self.generated / row['wrapper']).read_text(),
                             '\\VerbatimInput[firstline=' + str(row['first_line']) +
                             ',lastline=' + str(row['last_line']) + ',firstnumber=' + str(row['first_line']) +
                             ']{generated/implementation/' + row['relative_source'] + '}\n')
        self.assertFalse((self.generated / 'implementation-metric.tex').exists())
        self.assertFalse((self.generated / 'implementation-entry.tex').exists())

    def test_out_of_range_reversed_and_noninteger_excerpt_ranges_are_rejected(self):
        for first, last in [(0,2), (2,3), (2,1), (1.0,2), (True,2)]:
            with self.subTest(first=first,last=last):
                self.excerpts[0].update(first_line=first,last_line=last)
                with self.assertRaisesRegex(ValueError, 'excerpt range'):
                    self.generate()
                self.assertFalse((self.generated / 'implementation.json').exists())

    def test_excerpt_boundary_drift_is_rejected_even_with_new_source_fingerprints(self):
        path = self.project / 'NormArith/Search.lean'
        path.write_bytes(b'module\n-- renamed search\n')
        self.inventory['NormArith/Search.lean'] = hashlib.sha256(path.read_bytes()).hexdigest()
        self.aggregate = evidence.implementation_sha(self.project)
        with self.assertRaisesRegex(ValueError, 'boundary anchor'):
            self.generate()
        self.assertFalse((self.generated / 'implementation.json').exists())

    def test_excerpt_cannot_silently_expand_past_its_start_anchor(self):
        self.excerpts[0]['first_line'] = 1
        with self.assertRaisesRegex(ValueError, 'boundary anchor'):
            self.generate()

    def test_excerpt_end_anchor_drift_is_rejected(self):
        path = self.project / 'NormArith/Tactic.lean'
        path.write_bytes(path.read_bytes().replace(b'import NormArith.Metric\n', b'import NormArith.Metric  \n'))
        self.inventory['NormArith/Tactic.lean'] = hashlib.sha256(path.read_bytes()).hexdigest()
        self.aggregate = evidence.implementation_sha(self.project)
        with self.assertRaisesRegex(ValueError, 'boundary anchor'):
            self.generate()

    def test_excerpt_cannot_reference_a_nonruntime_source(self):
        self.excerpts[0]['relative_source'] = 'NormArith/Census.lean'
        with self.assertRaisesRegex(ValueError, 'runtime source'):
            self.generate()

    def test_changed_measured_source_is_rejected_before_output(self):
        (self.project / 'NormArith/Tactic.lean').write_bytes(b'-- changed\n')
        with self.assertRaisesRegex(ValueError, 'source hash'):
            self.generate()
        self.assertFalse((self.generated / 'implementation.json').exists())

    def test_missing_import_does_not_fall_back_to_workspace(self):
        (self.project / 'NormArith/Search.lean').unlink()
        with patch.object(generate, 'ROOT', Path(__file__).resolve().parents[1]):
            with self.assertRaisesRegex(ValueError, 'missing.*source'):
                self.generate()

    def test_import_without_final_verification_fingerprint_is_rejected(self):
        del self.inventory['NormArith/Metric.lean']
        with self.assertRaisesRegex(ValueError, 'verification.*source|source.*verification'):
            self.generate()

    def test_aggregate_mismatch_is_rejected(self):
        self.aggregate = '0' * 64
        with self.assertRaisesRegex(ValueError, 'aggregate'):
            self.generate()

    def test_source_root_is_required(self):
        del self.result['project_source_root']
        with self.assertRaisesRegex(ValueError, 'source root'):
            self.generate()

    def test_synthetic_facade_can_be_the_entire_import_closure(self):
        data = b'-- minimal synthetic implementation  \n\n'
        (self.project / 'NormArith.lean').write_bytes(data)
        self.inventory['NormArith.lean'] = hashlib.sha256(data).hexdigest()
        self.aggregate = evidence.implementation_sha(self.project)
        self.excerpts = None
        manifest = self.generate()
        self.assertEqual([row['relative_source'] for row in manifest['modules']], ['NormArith.lean'])
        self.assertEqual((self.generated / 'implementation/NormArith.lean').read_bytes(), data)
        self.assertEqual(manifest['excerpts'], [])
        self.assertFalse((self.generated / 'implementation-tactic.tex').exists())


if __name__ == '__main__':
    unittest.main()
