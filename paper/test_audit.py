"""Check the contextual-review record, using an empty synthetic corpus."""

from datetime import datetime, timezone
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import audit


class ReviewRecordTests(unittest.TestCase):
    def test_record_uses_current_utc_review_date(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "output").mkdir()
            (root / "vocabulary-review.tsv").write_text("word\tlemma\n")
            with patch.object(audit, "HERE", root), patch.object(audit, "blocks", return_value=[]), \
                    patch("sys.argv", ["audit.py", "--record-review"]), patch("builtins.print"):
                audit.main()
            record = json.loads((root / "language-review.json").read_text())
            self.assertEqual(record["date"], datetime.now(timezone.utc).date().isoformat())


if __name__ == "__main__":
    unittest.main()
