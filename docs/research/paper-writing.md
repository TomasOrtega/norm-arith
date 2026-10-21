# Paper writing and LaTeX support

Sources checked 20 October 2026. These findings now support the working
manuscript in [paper/](../../paper/README.md); no submission venue was selected.
The requested layout is a short mathematical-reasoning/AI workshop
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

## MATH-AI workshop format and four-page budget

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
guarantees and measured library results. The implemented draft and its build instructions are in [paper/](../../paper/README.md).

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

The working manuscript now uses the unchanged official NeurIPS 2026 style,
Times-compatible TeX Gyre Termes for prose, and JuliaMono for imported Lean
code. Its release build validates a maximum of four main pages and renders
every PDF page for visual review. The initial smoke test was a separate basic
article; its success alone did not establish template compatibility.

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

## Implemented language-review boundary

The manuscript now has a [53-rule applicability matrix](../../paper/language-audit.md),
a complete project surface-word/POS/sense ledger, occurrence contexts, and a
hash-bound review record. The release build rejects a changed prose snapshot,
missing vocabulary entries, or open length candidates. Generated status prose
and captions are part of the review, so new census or timing inputs also need
a fresh pass.

The pass found an important boundary: mathematical technical-noun permission
does not by itself permit predicative mathematical adjectives, quantifier
syntax, or proof imperatives in descriptive writing. Those uses and specified
research/artifact properties are declared exceptions, in addition to preserved
formal notation and source quotations. Avoidable general-vocabulary, tense,
voice, semicolon, and noun-group issues were edited. The resulting claim is
STE-based explanatory prose with declared mathematical and research-format
exceptions. Unqualified ASD-STE100 conformance is not established, and there
is no external certification. This is an explicit audit result rather than a
claim that sentence length alone satisfies the standard.
[Issue 9, rules 1.2–1.6, 3.2–3.6, and descriptive-writing scope](https://www.asd-ste100.org/assets/files/ASD-STE100_ISSUE9.pdf)

## Mathematical abstraction and implementation review

The manuscript now states validity over independent scalar/vector atom
assignments. Norm-free scalar expressions and unsupported vector subterms,
including variable-coefficient terms, can supply opaque atoms. The completeness
theorem does not restore their internal operation semantics. An abstract
countermodel can therefore differ from the meaning of a concrete Lean
expression; every successful concrete proof still passes Lean validation.
This matches the atomization in `scalarCore` and `linearize` in
[Tactic.lean](../../NormArith/Tactic.lean).

The independent-support status in [Search.lean](../../NormArith/Search.lean)
concerns enumeration. It does not certify that every proposed constraint
elaborated: the frontend can catch and skip a failed certificate construction.
Thus a completed enumeration alone is insufficient for a stronger claim of
whole-program completeness. The fixed mathematical norm in each seminormed
space is also part of the abstraction; multiple incompatible explicit Lean
`Norm` dictionaries on one type are not covered by that assumption.

The zero-norm encoding of vector equalities and the target-self deletion
argument have no identified mathematical defect in this review. The model proof
uses the quotient by the seminorm kernel to realize the vector equalities.
Native imports can change compilation costs; the paper's timing protocol now
requires matched runtime/import conditions for an algorithmic efficiency claim.


## Timing-methods correction

The appendix now identifies the actual resampling units: equal, nonoverlapping
blocks of paired full-pass totals. The same full blocks form the delete-one
jackknife observations, so there are `K = N / b` units. The citations distinguish
the BCa probability transformation, jackknife acceleration, and model-dependent
cluster resampling. Half-ties and linear empirical quantiles are implementation
choices. See the primary-source review in
[benchmark-statistics.md](benchmark-statistics.md).

The wording makes independent, representative timing blocks a model assumption.
Pilot diagnostics do not prove it, and the paper claims no coverage theorem for
arbitrary timing dependence or generalization to other hardware and revisions.
The source records the measured Apple M4 Max MacBook Pro, 36 GB, and logical
processor count of 14. The draft author line is *Anonymous Authors*. These source
edits received a full corpus-bound language renewal. The final evidence integration now includes the rebuilt PDF and its page review.


## Final release verification

The completed paper has four main pages, one reference page, and nine appendix
pages. Its final tables and source cutouts come from the validated portable
evidence bundle. The release build uses `--reuse-checked-examples --render`;
it validates the saved proof checks and launches no Lean or native build.
Every page received visual review. Font substitutions, missing glyphs,
unresolved references, and overfull boxes are absent. The final metadata is in
[paper/output/release.json](../../paper/output/release.json),
[visual-review.json](../../paper/output/visual-review.json), and
[toolchain.json](../../paper/output/toolchain.json).

The result stays within the stated empirical scope: the proposed local patch
saves proof code after preparation and import costs, while the compilation
comparison concerns the affected files with built dependencies and the recorded
variant-specific native imports. The paper reports incomplete census files,
known missing outcomes, the slower Uniform file, conditional timing-block
assumptions, and unmeasured dependency/native build costs. The superseded
source-style study and earlier negative prototype pilot remain separate.
