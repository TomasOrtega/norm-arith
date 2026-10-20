# Paper writing and LaTeX support

Checked 20 October 2026. Research only; no paper draft or submission venue was
selected. The requested layout is a short mathematical-reasoning/AI workshop
paper in NeurIPS style. Explain the proof-assistant context for that audience
while preserving the project's mathematical and implementation claims.

## Writing decisions carried into the paper plan

1. **Language review:** apply ASD-STE100 to explanatory prose, declare the
   mathematical vocabulary and necessary exceptions, and audit before making
   a compliance claim. Short sentences alone do not establish conformance.
2. **Review scope:** cover the abstract, prose, captions,
   and explanatory footnotes. Preserve mathematical notation, Lean identifiers,
   code, quotations, bibliographic titles, and official names; document how each
   is treated. These are proposed project boundaries, not a blanket exemption
   granted by ASD.
3. **Terminology:** approve a small project glossary before drafting. Define
   terms such as *certificate*, *decomposition*, *bound*, and *affected file*;
   distinguish mathematical terms from general verbs. Use one term consistently.
4. **Deliverable:** LaTeX source and a reproducible PDF build, with evaluation
   tables generated from archived measurements. NeurIPS style is a format
   choice; it does not commit the author to a NeurIPS submission.

## MATH-AI workshop format and provisional four-page budget

The organizers' MATH-AI 2026 call specifies **four content pages** in NeurIPS
format, with unlimited references and supplementary pages. It warns that
reviewers may not read the supplement and recommends using it only for minor
details. It specifies double-blind workshop formatting and provides its own
template. These are a concrete format reference, not a commitment to submit to
that workshop. The superseded nine-page main-conference budget does not apply
to this project.
[MATH-AI 2026 call for papers, Submission Requirements](https://mathai-2026.github.io/cfp/)

The workshop specifies `\usepackage[dblblindworkshop]{neurips_2026}` for review.
Use a draft mode appropriate to the artifact without an acceptance or
submission notice. Workshop-specific instructions take precedence over generic
main-track instructions if a venue is selected later.
[MATH-AI 2026 template](https://mathai-2026.github.io/files/mathai_neurips2026_template.zip)

Provisional allocation, totaling **four content pages**, is a project proposal:

| Main-body material | Pages |
| --- | ---: |
| Abstract, problem, contributions, hidden rational-decomposition example | 0.75 |
| Input grammar, semantics, and exact guarantees | 0.50 |
| Core procedure, automatic bounds, certificates, and correctness argument | 1.25 |
| Semantic census, actual-search timings with paired confidence interval, and mathlib before/after example | 1.10 |
| Related work, group-extension limits, and conclusion | 0.40 |

Keep the central theorem statements, meaningful correctness argument, claim
boundaries, principal evaluation protocol, and decisive results in the main
body. A reader who skips the appendix must still understand the contribution
and the evidence for it. Full proof details, exhaustive census and preprocessing
definitions, extraction ledgers, complete tables, and build instructions belong
in appendices. Those appendices support the main argument rather than substitute
for it.

The four checked examples remain part of the deliverable: two worked examples
in the main body, and the strict/reverse-norm and boundary/failure examples in
appendices. These locations are provisional. Frame the tactic as a checked
automation tool for mathematical reasoning, with claims tied to its mathematical
guarantees and measured library results. No manuscript or template files were
added to the repository during this research.

## What the official STE sources establish

The current issue is **Issue 9, dated 15 January 2025**. It has 53 writing rules
and a controlled dictionary. The official site describes use beyond maintenance
documentation, including academia.
[ASD overview](https://www.asd-ste100.org/about_STE.html)

STE controls a general word's meaning, part of speech, and permitted forms.
It also permits subject-specific technical nouns and technical verbs. Issue 9
uses *technical noun* where earlier issues used *technical name*. Mathematical
and scientific terms have an explicit category; the examples do not form a
complete list. Thus a mathematical paper can retain necessary terminology.
[Issue 9, rules 1.1–1.6 and 1.12](https://www.asd-ste100.org/assets/files/ASD-STE100_ISSUE9.pdf)

The current FAQ distinguishes the standard's procedural and descriptive scope
from adopting its principles in other writing. It permits technical terms from
subject-field sources and glossaries; this does not permit arbitrary general
vocabulary. It also requires attention to meaning, grammar, and reader needs.
[ASD FAQ](https://asd-ste100.org/STE_faq.html)

Request the free official PDF through ASD's downloads page. It contains both
the writing rules and dictionary; an unofficial condensed rules file is not an
authoritative replacement. ASD warns that plausible AI output can still violate
the standard.
[ASD downloads](https://asd-ste100.org/STE_downloads.html)

## A practical review

For strict review, maintain a rule-by-rule record against the official PDF.
For STE-guided prose, state that narrower claim and record the selected checks.
The following is a proposed project workflow, not certification:

- Review general words against their approved meaning and part of speech.
  Maintain the project's technical nouns and verbs separately.
- Treat research exposition as descriptive text. The standard permits at most
  25 words per descriptive sentence and six sentences per paragraph. Procedural
  instructions have a 20-word sentence limit. Follow section 8 when counting;
  a whitespace-only counter is insufficient.
  [Issue 9, rules 5.1, 6.3, 6.6, and section 8](https://www.asd-ste100.org/assets/files/ASD-STE100_ISSUE9.pdf)
- Check one topic per paragraph, explicit actors, defined notation, consistent
  terms, and unambiguous references. Review equations and surrounding sentences
  together so a shorter sentence does not alter a mathematical claim.
- Use automated reports as review aids. ASD does not certify STE software or
  AI tools, and it leaves responsibility with the writer. A checker cannot
  establish technical correctness or complete compliance.
  [ASD tools guidance](https://asd-ste100.org/STEsoftware.html)

## Usage and redistribution

The copyright notice reserves reproduction and publication rights and lists
special permissions, including universities and research institutes for
educational purposes. Free access is not a general open license. Recommendation:
cite and link the standard; store project glossaries and review records unless
permission for redistribution is established. Do not assume a research paper
falls under the educational permission.
[Issue 9, copyright notices, PDF page 2](https://www.asd-ste100.org/assets/files/ASD-STE100_ISSUE9.pdf#page=2)

## Local LaTeX support

The machine has TeX Live 2026, `latexmk` 4.88, pdfLaTeX, XeLaTeX, LuaLaTeX,
BibTeX, and Biber. `fontspec`, `fvextra`, `listings`, `minted`, `unicode-math`,
and `biblatex` are installed. These are local observations, not build guarantees.

A scratch smoke test **passed** with XeLaTeX, `fontspec`, the installed
`JuliaMono-Regular.ttf`, `fvextra` verbatim, and a BibTeX bibliography. The log
has no missing-character or unresolved-reference warnings. PDF text extraction
preserves Lean characters including `𝕜`, `ℝ`, `‖`, `≤`, `₁`, and `↦`.
`fontspec` supports XeTeX/LuaTeX font selection; JuliaMono is designed for
scientific programming with extensive technical Unicode coverage.
[fontspec source documentation](https://ctan.org/tex-archive/macros/unicodetex/latex/fontspec),
[JuliaMono](https://juliamono.netlify.app/),
[fvextra documentation](https://ctan.org/tex-archive/macros/latex/contrib/fvextra)

That smoke test used a basic article class, not the NeurIPS template. Integrating
Unicode code with the selected style still needs build and layout verification;
preserve its body typography and geometry rather than applying the code font
to the whole paper.

Two alternatives failed locally: LuaLaTeX stopped during font-cache setup, and
`biber --version` failed during macOS binary extraction with `lipo`. Neither is
needed for the verified XeLaTeX/BibTeX route. No system installation was changed.
BibLaTeX normally uses Biber and supports a reduced BibTeX backend, so select a
bibliography tool only after the paper class requirements are known.
[BibLaTeX documentation](https://www.ctan.org/tex-archive/macros/latex/contrib/biblatex/)

Recommended initial build route: `latexmk -xelatex -interaction=nonstopmode
-halt-on-error`. Latexmk reruns the engine and bibliography tools as needed.
Prefer code imported from checked Lean files over retyped examples. Pin the
TeX environment and fonts, record the build command, and fail on missing glyphs,
unresolved references, or unintended overfull boxes. Rebuilding the paper from
source and producing byte-identical PDF files are different targets; do not
claim the latter without testing it.
[latexmk author documentation](https://www.cantab.net/users/johncollins/latexmk/)
