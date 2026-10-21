"""Compile the actual paper preamble and inspect all twelve font faces."""

import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import unittest

HERE = Path(__file__).resolve().parent
EXPECTED = {"TeXGyreTermes-" + shape for shape in ["Regular", "Bold", "Italic", "BoldItalic"]}
EXPECTED |= {"TeXGyreHeros-" + shape for shape in ["Regular", "Bold", "Italic", "BoldItalic"]}
EXPECTED |= {"JuliaMono-" + shape for shape in ["Regular", "Bold", "RegularItalic", "BoldItalic"]}


@unittest.skipUnless(all(shutil.which(tool) for tool in ["xelatex", "pdffonts"]), "XeLaTeX and pdffonts are required for real font integration")
class FontIntegrationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.output = HERE / "tmp/font-integration"
        cls.output.mkdir(parents=True, exist_ok=True)
        preamble = (HERE / "paper.tex").read_text().split(r"\begin{document}", 1)[0]
        samples = "\n".join(
            "{" + family + r" Regular sample. \textbf{Bold sample.} \textit{Italic sample.} \textbf{\textit{Bold italic sample.}}}\par"
            for family in [r"\rmfamily", r"\sffamily", r"\ttfamily"])
        source = cls.output / "font-test.tex"
        source.write_text(preamble + r"\begin{document}\pagestyle{empty}" + "\n" + samples + "\n" + r"\end{document}" + "\n")
        command = ["xelatex", "-interaction=nonstopmode", "-halt-on-error", "-recorder", "-output-directory=" + str(cls.output), str(source)]
        result = subprocess.run(command, cwd=HERE, text=True, capture_output=True)
        (cls.output / "process.log").write_text(result.stdout + result.stderr)
        if result.returncode:
            raise AssertionError("font integration compilation failed: " + str(cls.output / "process.log"))
        cls.log = (cls.output / "font-test.log").read_text()
        listing = subprocess.check_output(["pdffonts", str(cls.output / "font-test.pdf")], text=True)
        (cls.output / "pdffonts.txt").write_text(listing)
        cls.faces = {line.split()[0].split("+")[-1].removesuffix("-Identity-H") for line in listing.splitlines()[2:] if line.strip()}
        cls.warnings = re.findall(r"(?:LaTeX Font Warning:|Package fontspec Warning:).*?(?=\n\s*\n|\Z)", cls.log, flags=re.S)
        record = {"status": "pass" if not cls.warnings and EXPECTED <= cls.faces else "fail",
                  "command": command, "paper_preamble_sha256": hashlib.sha256(preamble.encode()).hexdigest(),
                  "expected_faces": sorted(EXPECTED), "embedded_faces": sorted(cls.faces), "font_warnings": cls.warnings,
                  "pdf_sha256": hashlib.sha256((cls.output / "font-test.pdf").read_bytes()).hexdigest()}
        (HERE / "output/font-integration.json").write_text(json.dumps(record, indent=2) + "\n")

    def test_no_font_substitution_warnings(self):
        self.assertEqual(self.warnings, [], "font substitution recorded in " + str(self.output / "font-test.log"))

    def test_every_requested_face_is_embedded(self):
        self.assertTrue(EXPECTED <= self.faces, "missing embedded faces: " + ", ".join(sorted(EXPECTED - self.faces)))


if __name__ == "__main__":
    unittest.main()
