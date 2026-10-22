#!/usr/bin/env python3
"""Check prose lengths and coverage of the project vocabulary review."""

import argparse
import csv
from datetime import datetime, timezone
import hashlib
import json
import re
from collections import Counter, defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
GENERATED_PROSE = (
    "implementation-status.tex", "example-status.tex", "census-status.tex",
    "census-detail.tex", "confirmatory-status.tex", "timing-main.tex", "census-example-provenance.tex", "calibration-status.tex",
)


def prose(text):
    text = re.sub(r"(?m)^\s*%.*$", "", text)
    text = re.sub(r"\\href\{[^}]*\}", "", text)
    text = re.sub(r"\\begin\{(?:equation|align|tabular)\}(.*?)\\end\{(?:equation|align|tabular)\}", lambda m: " FORMULA" + (". " if m[1].rstrip().endswith(".") else " "), text, flags=re.S)
    text = re.sub(r"\\\[(.*?)\\\]", lambda m: " FORMULA" + (". " if m[1].rstrip().endswith(".") else " "), text, flags=re.S)
    text = re.sub(r"\$[^$]*\$", " FORMULA ", text)
    text = re.sub(r"\\(?:texttt|sourcepath)\{[^}]*\}", " IDENTIFIER ", text)
    text = re.sub(r"\\(?:cite\w*|label|ref|eqref|input|VerbatimInput|bibliography|bibliographystyle)\{[^}]*\}", "", text)
    text = re.sub(r"\\(?:section|subsection|paragraph|title|author|newcommand|newtheorem)\{[^}]*\}", "", text)
    text = re.sub(r"\\(?:begin|end)\{[^}]*\}(?:\[[^]]*\])?", "", text)
    text = re.sub(r"\\[A-Za-z]+\*?(?:\[[^]]*\])?", "", text)
    return text.replace("{", "").replace("}", "").replace("~", " ").replace(r"\%", "%")


def blocks():
    for name in ("paper.tex", "appendix.tex", "implementation.tex", *("generated/" + x for x in GENERATED_PROSE)):
        source = (HERE / name).read_text()
        if name == "paper.tex":
            title = re.search(r"\\title\{([^}]*)\}", source)
            if title:
                yield name + ":title", " ".join(prose(title[1]).replace("\\", " ").split())
            source = source.split(r"\begin{document}", 1)[1].split(r"\clearpage", 1)[0]
        for heading in re.findall(r"\\(?:section|subsection|paragraph)\{([^}]*)\}", source):
            yield name + ":heading", " ".join(prose(heading).split())
        for heading in re.findall(r"\\begin\{(?:theorem|lemma)\}\[([^]]*)\]", source):
            yield name + ":heading", " ".join(prose(heading).split())
        source = re.sub(r"\\(?:begin|end)\{(?:theorem|lemma|proof)\}(?:\[[^]]*\])?", "\n\n", source)
        for block in re.split(r"\n\s*\n", source):
            clean = " ".join(prose(block).split())
            if clean:
                yield name, clean
    for name in ("census-table.tex", "census-outcomes.tex",
                 "census-fragments.tex", "selector-outcomes.tex", "line-costs.tex", "timing-table.tex", "timing-setup.tex", "calibration-table.tex",
                 "evaluation-figure.tex"):
        path = HERE / "generated" / name
        if not path.exists():
            continue
        source = path.read_text()
        for caption in re.findall(r"\\caption\{([^}]*)\}", source):
            yield "generated/" + name, " ".join(prose(caption).split())


def vocabulary(paragraphs):
    contexts = defaultdict(list)
    counts = Counter()
    for source, paragraph in paragraphs:
        words = re.findall(r"[A-Za-z]+(?:[-'][A-Za-z]+)*", paragraph)
        for word in words:
            if word in ("FORMULA", "IDENTIFIER"):
                continue
            word = word.lower()
            counts[word] += 1
            context = {"source": source, "text": paragraph}
            if context not in contexts[word]:
                contexts[word].append(context)
    return {word: {"occurrences": counts[word], "contexts": contexts[word]} for word in sorted(counts)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record-review", action="store_true", help="record the current corpus after a complete editorial review")
    args = parser.parse_args()
    paragraphs = list(blocks())
    results = []
    for source, clean in paragraphs:
        sentences = [s.strip() for s in re.split(r"(?<=[.!?])\s+", clean) if s.strip()]
        long = []
        for sentence in sentences:
            count = len(re.findall(r"[A-Za-z0-9]+(?:[-'][A-Za-z0-9]+)*", sentence))
            procedural = re.match(r"(?:Count|Charge|Keep|Emit|Give|Measure|Assign explicit|Use paired|Do not discard|Before the run, select)\b", sentence) is not None
            limit = 20 if procedural else 25
            if count > limit:
                long.append({"words": count, "limit": limit, "text": sentence})
        if len(sentences) > 6 or long:
            results.append({"source": source, "paragraph_sentences": len(sentences), "long_sentences": long, "paragraph": clean})
    lexicon = vocabulary(paragraphs)
    review_path = HERE / "vocabulary-review.tsv"
    reviewed = {}
    if review_path.exists():
        with review_path.open() as stream:
            reviewed = {row["word"]: row for row in csv.DictReader(stream, delimiter="\t")}
    missing = sorted(set(lexicon) - reviewed.keys())
    output = {
        "status": "editorial-review-aid",
        "limitations": "Formula placeholders make length counts candidates. Vocabulary coverage cannot establish contextual correctness or ASD certification.",
        "candidates": results, "vocabulary": lexicon, "unreviewed_words": missing,
    }
    corpus_hash = hashlib.sha256(json.dumps(paragraphs, ensure_ascii=False).encode()).hexdigest()
    ledger_hash = hashlib.sha256(review_path.read_bytes()).hexdigest() if review_path.exists() else None
    output["corpus_sha256"] = corpus_hash
    output["vocabulary_review_sha256"] = ledger_hash
    record_path = HERE / "language-review.json"
    if args.record_review:
        if missing or results:
            raise SystemExit("Resolve length candidates and vocabulary gaps before recording review")
        record_path.write_text(json.dumps({"date": datetime.now(timezone.utc).date().isoformat(), "reviewer": "Codex assisted editorial review",
            "corpus_sha256": corpus_hash, "vocabulary_review_sha256": ledger_hash,
            "scope": "Main and appendix explanatory prose and headings, title, generated status prose, and table/figure captions; mathematical notation and imported code are excluded.",
            "conformance": "STE-based explanatory prose with the mathematical exceptions declared in language-audit.md; no unqualified ASD conformance or external certification."}, indent=2) + "\n")
    recorded = json.loads(record_path.read_text()) if record_path.exists() else {}
    output["record_matches_current_corpus"] = (recorded.get("corpus_sha256") == corpus_hash and recorded.get("vocabulary_review_sha256") == ledger_hash)
    (HERE / "output/language-candidates.json").write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps({key: value for key, value in output.items() if key != "vocabulary"}, indent=2))


if __name__ == "__main__":
    main()
