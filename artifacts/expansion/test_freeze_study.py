import importlib.util
import json
from pathlib import Path
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("freeze_study", Path(__file__).with_name("freeze_study.py"))
FREEZE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(FREEZE)
VERIFICATION = ROOT / ".lake/expansion-combined-verification-08"
AUDIT = ROOT / "artifacts/expansion/combined-08-audit.json"


@unittest.skipUnless((VERIFICATION / "verification.json").exists() and AUDIT.exists(),
                     "requires the preserved live verification08 evidence")
class FreezeStudyTests(unittest.TestCase):
    def test_coherently_referenced_but_false_count_audit_cannot_freeze(self):
        audit = json.loads(AUDIT.read_bytes())
        audit["net_file_code_lines_saved"] = 0
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "audit.json"
            path.write_text(json.dumps(audit))
            with self.assertRaisesRegex(ValueError, "independent.*count"):
                FREEZE.validate(ROOT, VERIFICATION, path)


if __name__ == "__main__":
    unittest.main()
