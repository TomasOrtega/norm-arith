# Research paper plan

Status: scope interview. This extends the completed prototype evaluation; no new
paper results or broader tactic guarantees have been established.

## Requested outcome

A full paper with LaTeX source, Simplified Technical English, checked examples,
a more general and efficient tactic, and a systematic mathlib evaluation with
proof-line accounting.

## Established starting point

- Five verified local mathlib replacements across three files.
- Proof blocks decrease from 57 to 18 nonblank, noncomment lines: 39 fewer proof
  lines, or 36 after charging new imports.
- Final paired measurements show 6.3% slower affected-file Lean compilation.
- The current tactic uses explicit bounds, bounded rational decomposition search,
  additive certificates, and real-scalar certificates for fractional coefficients.
- Existing mathlib proofs remain the evaluation baseline. Preparation and helpers
  count toward replacement size; implementation costs are separate.
- Claims about accepted mathlib savings require an upstream merge. Current claims
  concern a reproducible local patch.

See [the measured results](../benchmarks/RESULTS.md).

## Accepted paper-phase decisions

- Target proof-assistant researchers. The contribution is a general Lean tactic,
  a precise supported fragment and correctness arguments, and a systematic
  mathlib evaluation. Claim algorithmic novelty only when established by related
  work.
- Require an aggregate affected-file compilation speedup over the existing
  mathlib proofs. A speedup over the prototype alone is insufficient. If the
  new tactic remains slower, this efficiency goal is unmet.
- Define coverage through a semantic mathlib census: every eligible source-backed
  goal found during complete elaboration of a pinned revision, under published
  eligibility, preparation, and resource limits. Record extraction and tactic
  failures, overlaps, and no-saving outcomes.
- Default to bare `norm_arith` with automatic selection of relevant local bounds.
  Retain `norm_arith [facts]` for explicit control.
- Apply ASD-STE100 to explanatory prose. Maintain the mathematical vocabulary,
  preserve formal notation and Lean code, record necessary exceptions, and audit
  the manuscript before claiming compliance.
- The real-vector-space core handles rational vector combinations and linear
  scalar arithmetic involving norms, including equalities, strict inequalities,
  and distances. Products of norms and normalization of variable vector
  coefficients remain outside the core.
- Retain arbitrary seminormed additive groups as a separate, sound extension with
  explicitly weaker guarantees.
- The main census universe is every tracked Lean source under `Mathlib/` at the
  pinned revision. Include tactic-style and term-style proofs. Tests, `Archive`,
  and external dependencies are outside this denominator. Record an extraction
  outcome for every file.
- Select the final combined patch by correctness and total net line reduction,
  with a deterministic overlap rule. Include every resulting affected file in
  the aggregate timing, including regressions.
- Require Lean-checked normalization and certificate soundness, plus a
  mathematical completeness proof in the paper. End-to-end Lean formalization
  of search completeness is outside the first paper's required deliverables.
  State the theorem relative to the declared grammar and recognized assumptions;
  resource exhaustion returns unknown.
- Use vector-equality assumptions in the core while limiting its advertised
  conclusions to scalar comparisons involving norms. Zero norm does not imply
  vector equality in a seminormed space.
- Use a fixed, documented preprocessing and bound-discovery rule set. One-off
  human-invented lemmas are outside the headline census; additional manual case
  studies can be reported separately. Count generated preparation in replacement
  size.
- Include actual `norm_arith` search in the required compilation speedup. Report
  norm-certificate replay separately if that mode is implemented.
- Require a predeclared confirmatory paired timing experiment. Use the ratio of
  mean total affected-file compilation times as the primary speedup measure;
  its paired 95% confidence interval must lie entirely above one. Freeze code,
  patch, sample count, and analysis before the confirmatory run. Retain medians
  and per-file results, and do not add samples until significance appears.
- Include four checked examples: a hidden rational decomposition, a strict or
  reverse-triangle argument, a real mathlib before/after replacement, and a
  boundary or failure case. Import snippets from checked Lean sources and link
  empirical examples to their census entries.
- Use one normalized rational representation and one checked certificate layer,
  with a complete finite-constraint reference algorithm and existing mathlib
  scalar arithmetic. Optimized paths share that interface and retain the
  reference fallback; accept optimizations through whole-file measurements.
- Target a short NeurIPS math-and-AI workshop-style paper. The proposed nine-page
  main body was rejected as too long. A specific submission venue and submission
  action have not been selected.

See [ADR-0003](adr/0003-paper-and-semantic-census.md) and
[ADR-0004](adr/0004-automatic-bound-discovery.md) for contribution and interface,
and [ADR-0005](adr/0005-core-fragment-and-group-extension.md) and
[ADR-0006](adr/0006-census-universe-and-patch-selection.md) for the fragment and
evaluation scope. [ADR-0007](adr/0007-paper-completeness-and-checked-soundness.md)
sets the theorem and formalization obligations.
[ADR-0008](adr/0008-normalized-core-and-shared-certificates.md) records the solver
architecture.

## Decisions to resolve next

Confirm the consolidated scope with a proposed four-page main body in the
NeurIPS workshop style. The
[MATH-AI 2026 call](https://mathai-2026.github.io/cfp/)
uses four content pages, excluding references and supplementary material. Keep
the main argument, theorem statements and proof sketch, and decisive evaluation
in those pages; put full proofs, detailed methods, and additional examples in
appendices. This is a format model, not a claim of submission or acceptance.

Address readers in mathematical reasoning and AI while preserving the accepted
technical contribution in proof automation. No model-training experiment or
changed comparison baseline follows from the shorter workshop format.

Extraction and per-goal resource limits will be calibrated deterministically and
fixed before the final census; exhausted and unprocessed cases remain visible
in its ledger.

Primary-source findings are in [algorithm research](research/norm-arithmetic-algorithms.md),
[census research](research/mathlib-census.md), and
[writing research](research/paper-writing.md). They are evidence for the design
discussion, not new tactic or paper results.

Earlier decisions remain in force unless this interview explicitly revises them.
