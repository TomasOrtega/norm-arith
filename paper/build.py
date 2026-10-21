#!/usr/bin/env python3
"""Check paper examples, regenerate data, and build the PDF with XeLaTeX."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

from generate import implementation_sha

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def run(command, cwd=ROOT, log=None):
    result = subprocess.run(command, cwd=cwd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if log is not None:
        log.write_text(result.stdout)
    if result.returncode:
        print(result.stdout, file=sys.stderr)
        raise SystemExit(result.returncode)
    return result




def layout_issues(log):
    pattern = r"Missing character:|undefined references|Citation .* undefined|Overfull \\[hv]box|LaTeX Font Warning:|Package fontspec Warning:|defaults substituted"
    return [line for line in log.splitlines() if re.search(pattern, line)]


def record_toolchain(output, pdf_dir, *, mode="build"):
    commands = {"xelatex": ["xelatex", "--version"], "latexmk": ["latexmk", "-v"],
                "bibtex": ["bibtex", "--version"], "pdfinfo": ["pdfinfo", "-v"]}
    versions = {}
    for name, command in commands.items():
        result = subprocess.run(command, text=True, capture_output=True, check=True)
        versions[name] = {"command": command, "stdout": result.stdout, "stderr": result.stderr}
    log_path, recorder = pdf_dir / "paper.log", pdf_dir / "paper.fls"
    log = log_path.read_text() if log_path.exists() else ""
    fonts, tex_inputs, records, missing, lookup = {}, {}, {}, set(), {}

    def locate(name):
        if name not in lookup:
            path = Path(name)
            if not path.is_absolute():
                path = HERE / path
            if not path.is_file():
                result = subprocess.run(["kpsewhich", name], text=True, capture_output=True)
                path = Path(result.stdout.strip()) if result.returncode == 0 and result.stdout.strip() else None
            lookup[name] = path.resolve() if path is not None and path.is_file() else None
        return lookup[name]

    def font(name, reason):
        path = locate(name)
        if path is None:
            missing.add(name)
        else:
            fonts.setdefault(str(path), {"sha256": hashlib.sha256(path.read_bytes()).hexdigest(), "identified_by": set()})["identified_by"].add(reason)

    for name in set(re.findall(r"['\[]([A-Za-z0-9_-]+\.(?:otf|ttf|pfb|tfm|vf))(?=['\](])", log)):
        font(name, "XeLaTeX log")
    if recorder.exists():
        lines = recorder.read_text().splitlines()
        base = next((Path(line[4:]) for line in lines if line.startswith("PWD ")), HERE)
        for line in lines:
            if not line.startswith("INPUT "):
                continue
            path = Path(line[6:])
            path = path if path.is_absolute() else base / path
            if not path.is_file():
                continue
            if path.suffix.lower() in {".otf", ".ttf", ".pfb", ".tfm", ".vf"}:
                font(str(path), "XeLaTeX file recorder")
            elif path.suffix.lower() in {".sty", ".cls", ".bst", ".cfg", ".def", ".fd", ".tex"}:
                tex_inputs[str(path.resolve())] = hashlib.sha256(path.read_bytes()).hexdigest()
    for family in ["texgyretermes", "texgyreheros"]:
        for shape in ["regular", "bold", "italic", "bolditalic"]:
            font(family + "-" + shape + ".otf", "explicit family variant; availability does not imply use")
    for shape in ["Regular", "Bold", "RegularItalic", "BoldItalic"]:
        font("JuliaMono-" + shape + ".ttf", "explicit family variant; availability does not imply use")
    pdf = pdf_dir / "paper.pdf"
    embedded = []
    if pdf.exists():
        result = subprocess.run(["pdffonts", str(pdf)], text=True, capture_output=True, check=True)
        embedded = [line.split()[0].split("+")[-1] for line in result.stdout.splitlines()[2:] if line.strip()]
        for name in embedded:
            name = name.removesuffix("-Identity-H")
            if name.startswith("TeXGyre"):
                font(name.lower() + ".otf", "embedded PDF font name")
            elif name.startswith("JuliaMono"):
                font(name + ".ttf", "embedded PDF font name")
            else:
                font(name.lower() + ".pfb", "embedded PDF font name")
    bib_log = pdf_dir / "paper.blg"
    if bib_log.exists():
        for name in re.findall(r"The style file: (\S+\.bst)", bib_log.read_text()):
            path = locate(name)
            if path is not None:
                tex_inputs[str(path)] = hashlib.sha256(path.read_bytes()).hexdigest()
    for path in [log_path, recorder, bib_log]:
        if path.exists():
            records[str(path)] = hashlib.sha256(path.read_bytes()).hexdigest()
    for item in fonts.values():
        item["identified_by"] = sorted(item["identified_by"])
    metadata = {"schema_version": 1, "captured_at_utc": datetime.now(timezone.utc).isoformat(),
                "capture_mode": mode, "tools": versions, "fonts": dict(sorted(fonts.items())),
                "tex_inputs": dict(sorted(tex_inputs.items())), "build_record_sha256": records,
                "embedded_pdf_font_names": embedded, "unresolved_font_files": sorted(missing),
                "font_warnings": re.findall(r"(?:LaTeX Font Warning:|Package fontspec Warning:).*?(?=\n\s*\n|\Z)", log, flags=re.S),
                "pdf_sha256": hashlib.sha256(pdf.read_bytes()).hexdigest() if pdf.exists() else None}
    (output / "toolchain.json").write_text(json.dumps(metadata, indent=2) + "\n")
    return metadata


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--draft", action="store_true", help="allow unfinished Lean example integration, with visible PDF labels")
    parser.add_argument("--render", action="store_true", help="render all PDF pages as PNGs for visual review")
    parser.add_argument("--reuse-checked-examples", action="store_true", help="use a validated portable bundle's checked examples without launching Lean")
    parser.add_argument("--fresh-examples", action="store_true", help="build Lean examples in a live checkout instead of reusing a portable check")
    args = parser.parse_args()
    portable = bool(json.loads((HERE / "status.json").read_text()).get("evidence_bundle"))
    if args.fresh_examples and (args.draft or args.reuse_checked_examples):
        parser.error("--fresh-examples cannot use --draft or --reuse-checked-examples")
    args.reuse_checked_examples = args.reuse_checked_examples or (portable and not args.draft and not args.fresh_examples)
    if args.reuse_checked_examples and (args.draft or not portable):
        parser.error("--reuse-checked-examples requires a portable evidence bundle and cannot use --draft")
    output = HERE / "output"
    pdf_dir = output / "pdf"
    temporary = HERE / "tmp"
    for path in (output, pdf_dir, temporary, temporary / "pdfs", temporary / "lean"):
        path.mkdir(exist_ok=True)
    source = ROOT / "NormArithTest/Paper.lean"
    if not args.draft and not args.reuse_checked_examples:
        if not source.exists():
            raise SystemExit("NormArithTest/Paper.lean is required for a checked build")
        run(["lake", "build", "NormArith"], log=output / "lean-dependencies.log")
        source_hash = hashlib.sha256(source.read_bytes()).hexdigest()
        implementation_hash = implementation_sha()
        for artifact in (temporary / "lean").glob("Paper.*"):
            artifact.unlink()
        command = ["lake", "env", "lean", "-R", ".", "-o", "paper/tmp/lean/Paper.olean", "NormArithTest/Paper.lean"]
        run(command, log=output / "lean-check.log")
        checked_object = temporary / "lean/Paper.olean"
        if not checked_object.exists() or checked_object.stat().st_size == 0:
            raise SystemExit("Lean did not produce the fresh checked example artifact")
        if source_hash != hashlib.sha256(source.read_bytes()).hexdigest() or implementation_hash != implementation_sha():
            raise SystemExit("Lean source changed during the paper example check; rebuild from a stable snapshot")
        check = {"command": command, "returncode": 0, "source_sha256": source_hash, "implementation_sha256": implementation_hash}
        (output / "lean-check.json").write_text(json.dumps(check, indent=2) + "\n")
    generation = [sys.executable, str(HERE / "generate.py")]
    if args.draft:
        generation.append("--draft")
    run(generation, log=output / "generation.log")
    run([sys.executable, str(HERE / "audit.py")], log=output / "language-audit.log")
    language = json.loads((output / "language-candidates.json").read_text())
    if not args.draft and (language["candidates"] or language["unreviewed_words"] or not language["record_matches_current_corpus"]):
        raise SystemExit("The prose changed or has unresolved review items. Review language-candidates.json and renew the full contextual language pass before the release build.")
    command = ["latexmk", "-xelatex", "-interaction=nonstopmode", "-halt-on-error", "-outdir=output/pdf", "paper.tex"]
    run(command, cwd=HERE, log=output / "latexmk.log")
    log = (pdf_dir / "paper.log").read_text()
    issues = layout_issues(log)
    if issues:
        raise SystemExit("PDF validation failed:\n" + "\n".join(issues))
    aux = (pdf_dir / "paper.aux").read_text()
    match = re.search(r"\\newlabel\{main-end\}\{\{[^}]*\}\{(\d+)\}", aux)
    if match is None:
        raise SystemExit("main-end page marker was not generated")
    main_pages = int(match[1])
    if main_pages > 4:
        raise SystemExit(f"main body is {main_pages} pages; maximum is four")
    metadata = run(["pdfinfo", str(pdf_dir / "paper.pdf")]).stdout
    (output / "pdfinfo.txt").write_text(metadata)
    run(["pdftotext", str(pdf_dir / "paper.pdf"), str(output / "paper.txt")])
    if args.render:
        for old in (temporary / "pdfs").glob("page-*.png"):
            old.unlink()
        run(["pdftoppm", "-scale-to", "1500", "-png", str(pdf_dir / "paper.pdf"), str(temporary / "pdfs/page")])
    (output / "validation.json").write_text(json.dumps({"main_pages": main_pages, "draft": args.draft,
        "pdf_sha256": hashlib.sha256((pdf_dir / "paper.pdf").read_bytes()).hexdigest(), "layout_log_issues": issues,
        "lean_validation": "checked release artifacts" if args.reuse_checked_examples else "draft" if args.draft else "fresh compilation"}, indent=2) + "\n")
    record_toolchain(output, pdf_dir)
    print(f"Built {pdf_dir / 'paper.pdf'}; {main_pages} main pages")


if __name__ == "__main__":
    main()
