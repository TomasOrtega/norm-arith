# Expand the Mathlib patch

The continued study must exceed the verified 232-line milestone, measure the
complete expanded patch against the existing proofs, update the short LaTeX
paper and PDF, then commit and push the checked release. The
[fresh timing protocol](../artifacts/expansion/expanded-study-protocol.md)
requires a new frozen workload, calibration pilot and confirmatory run. The
310-line final patch has passed combined verification and independent accounting:
87 replacements in 46 files, with 582 original proof lines reduced to 226 and
46 added imports. The final fixed 885-file discovery pass has valid integrity:
875 complete files, ten incomplete files, and 158 isolated checked proposals.
The final patch and implementation are frozen. The 24-pair pilot and 40-pair
confirmation finished, with four-pair blocks selected from blinded diagnostics.
The mean warm affected-file compilation time decreases from 131.19 to 122.33
seconds: a 1.0724× ratio, with conditional 95% block-BCa interval
[1.0669, 1.0814]. All 46 files and 40 pairs remain in the result. The final paper
passed scientific review, STE review, all-page visual inspection, and a clean
offline default rebuild. Its main body is four pages; references and appendices
bring the total to 17. The [release receipt](../paper/output/release.json) records
the checked sources and evidence.

The user requests substantially more uses and line savings than the original
41-line patch. Preserve that completed experiment and its portable paper evidence.
Develop a larger patch against the same pinned Mathlib source, preserving theorem
statements and charging all replacement code, preparations, helpers, and imports.

Work proceeds on three connected tasks:

1. Recover missed proof tails from actual tactic-sequence syntax and original
   contexts. Recognize proof finalizers without widening the guard to statements.
2. Improve checked fact processing from concrete failures. Current additions
   project conjunctions, supply real norm and min/max order facts, and specialize
   selected quantified norm bounds. A separate metric pass checks finite
   distance chains in pseudometric spaces.
3. Replace longer analytic estimates with concise preparation and `norm_arith`.
   Recompile the complete combined patch, remove overlap, and independently count
   literal source changes before reporting savings.

The earlier 232-line combined expansion passed source verification and independent audit:
74 replacements in 40 files, with 454 original proof code lines replaced by
182 lines including preparation. The 272 proof lines saved minus 40 imports give
**232 net code lines saved**, with no added helpers. Its
[independent audit](../artifacts/expansion/combined-07-audit.json) rechecks literal
source spans, patch application, and all 280 fresh compilation artifacts.
The [preserved patch](../benchmarks/expansion/verified-03/manifest.json) remains
untimed. The [result report](../benchmarks/expansion/RESULTS.md) records scope,
source accounting, examples, and the separate 847-line tactic implementation and
470-line census implementation. Earlier 109- and 157-line milestones remain
available. These earlier milestones do not inherit the final patch's timing
result.

The earlier expanded discovery selected 906 files: 885 with norm observations in
the original census, plus incomplete outcomes not already included. The previous
targeted rerun processed the 885 norm-observation files: 875 completed and 10
remain incomplete, with 140 isolated checked proposals. The
[targeted archive](../artifacts/expansion/discovery-v3-archive/archive.json)
retains raw observations and outcomes. This is not a new complete Mathlib census.
Exploratory runs and their source snapshots remain preserved, including
interrupted versions and incomplete outcomes. A new tactic version requires new
compiled evidence for any subsequent patch.

The quantified extension passed 26 regression examples and full copied-file
checks in Analytic and FDeriv. It matches observed vector terms, constructs exact
or conjunction premises, and uses restricted scalar arithmetic for real premises.
Its fixed rewrites cover distances, balls, closed balls, and `Icc`, `Ico`, `Ioc`,
and `Ioo`. Supplied `[facts]` still control norm and distance premises, including
transparent aliases and norm-bearing `Fact` instances. Failed specializations
restore state. Scalar let names remain intact in retained proof types.

The fixed specialization limits are 12 templates, 12 binders per template,
32 observed vectors, 32 retained new bounds, and 128 candidate attempts. Each
attempt tries at most 8 additive patterns of depth at most 8; premise construction
has depth 4. Norm-alias filtering has depth 8 and a 256-node budget, and excludes
uncertain expressions conservatively. These bounds do not provide quantified
completeness. The simplified proposals and development receipts are retained in
[`quantified/`](../benchmarks/expansion/quantified/).

The metric extension generates checked self-distance, nonnegativity, symmetry,
and triangle facts for at most 8 observed points total, then calls restricted `linarith`.
It runs only when comparison syntax and inferred space instances select the
metric route. A failed metric attempt restores state before the existing norm
pipeline runs; unrelated metric facts cannot prevent that fallback from using
selected norm bounds. Generic metric and mixed-space controls are regression
tested. The extension has no completeness claim and leaves the paper's
quantifier-free real-core theorem unchanged.
The [final regression receipt](../artifacts/expansion/regressions/general-extensions-v3-receipt.json)
retains the completed build log and hashes of the current source snapshots. It
distinguishes the earlier generic-metric build from the final routing controls.

Completed baseline timing cannot be transferred to new code or a new workload.
Keep the expansion's timing status explicit until it has its own measurements.
The current quantified and metric implementation and the 310-line patch have
their own completed 1.0724× timing result. The historical 1.105× result applies
only to the original frozen 41-line patch and implementation. That paper and its
portable evidence remain preserved separately. The new interval assumes
independent, representative blocks; power snapshots and the pilot diagnostics
do not prove constant machine conditions or independence.
