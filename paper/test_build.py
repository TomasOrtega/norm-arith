"""Check portable default build routing without invoking external tools."""

import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import build


class PortableBuildTests(unittest.TestCase):
    def test_portable_default_needs_no_lean_source_or_lake(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            paper = root / 'paper'; output = paper / 'output'; pdf = output / 'pdf'
            pdf.mkdir(parents=True)
            (paper / 'status.json').write_text(json.dumps({'evidence_bundle': 'bundle'}))
            (output / 'language-candidates.json').write_text(json.dumps({
                'candidates': [], 'unreviewed_words': [], 'record_matches_current_corpus': True}))
            (pdf / 'paper.pdf').write_bytes(b'Synthetic PDF fixture; not a rendered document.')
            (pdf / 'paper.log').write_text('')
            (pdf / 'paper.aux').write_text(r'\newlabel{main-end}{{}{4}}')
            commands = []
            def run(command, **kwargs):
                commands.append(command)
                self.assertNotEqual(command[0], 'lake')
                return SimpleNamespace(stdout='Synthetic metadata.')
            with patch.object(build, 'ROOT', root), patch.object(build, 'HERE', paper), \
                    patch.object(build, 'run', side_effect=run), patch.object(build, 'record_toolchain'), \
                    patch('sys.argv', ['build.py']), patch('builtins.print'):
                build.main()
            result = json.loads((output / 'validation.json').read_text())
            self.assertEqual(result['lean_validation'], 'checked release artifacts')
            self.assertTrue(any('generate.py' in str(command) for command in commands))
            self.assertFalse((root / '.lake').exists())


if __name__ == '__main__':
    unittest.main()
