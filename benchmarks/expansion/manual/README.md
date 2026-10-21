# Reviewed proof-block expansion

This exploration preserves the published 41-line baseline. It tests larger proof
spans and explicit local preparation that the bare single-node census did not
propose. Timing does not select these candidates, and these trials make no speed
claim.

`confirmed-v3.json` is the immutable latest checked batch: 23 replacements in
15 complete copied Mathlib files. `confirmed.json` currently has the same content.
Trials 06–08, 10–11, and 13 compiled every current complete file with fresh nonempty
Lean/C artifacts and no warnings or long-line diagnostics. The edits use 118 proof code
lines in place of 254, with 15 added imports: **121 net lines as a standalone
patch**. Combining them with the baseline requires overlap selection and a fresh
combined compilation. Imports must be charged once per affected file.

`confirmed-v1.json` preserves the earlier 15-edit, ten-file batch, with 83 net
lines. `confirmed-v2.json` has the same 23-edit count as v3; v3 fixes its one
unused-assumption warning without changing the statement or line count. These
snapshots do not change the published baseline or its timing claim.

The confirmed files cover analytic series, asymptotics, differentiability,
projections, operator theory, polynomial growth, Jacobians, the strong law of large numbers, controlled closure, compact-image bounds,
and exponential/logarithm estimates. Local preparation includes explicit applications of quantified
bounds, `map_sub`/`sub_smul`, and finite-sum normalization. Its lines are charged.
The four polynomial-growth edits use the new checked real scalar norm bridge.

`manifest.json` is the complete current proposal inventory. It includes failed
and untested candidates and is **not** a verified selection. `prepare.py`
regenerates its exact source hashes and proof-body provenance from the pinned
Mathlib source and original census. Each edit retains the original whole-line
hash, first-token/last-token byte span, exact internal replacement, declaration
body bounds, and an original observation key/event path. `confirmed.py` publishes
only replacements whose complete current edited file matches a successful trial
source hash; it also checks every retained compiler artifact's bytes.

Run exploratory full-file checks with the already-built tactic:

```sh
python3 benchmarks/expansion/manual/prepare.py
lake env python3 benchmarks/expansion/manual/trial.py --output .lake/manual-expansion-new
```

The output directory must be new. The wrapper uses `lake --no-build setup-file`,
original census build options, actual edited headers, fresh compiler outputs,
and the existing compiler/style validator. It does not change the baseline or
relax the production census verifier. Final integration uses the separate
reviewed-preparation verification mode.

## Search and attempts

The search started with all 2,753 recorded solver failures in the original full
census, ranking source spans by length. It found 1,044 failed spans of at least
five lines, including overlapping nested observations. Large proofs that require
integration, analytic continuation, or new nonlinear estimates were reviewed as
poor direct targets. The smaller-span review concentrated on additive identities,
triangles, local quantified estimates, and scalar comparisons.

Additional source searches used:

```text
rg -n 'norm_add₃_le|norm_sub_le|abs_norm_sub_norm_le|norm_sub_norm_le' Mathlib/Analysis Mathlib/Topology
rg -n 'congr.*abel|abel.*norm|norm.*abel' Mathlib/Analysis
```

The following trials are retained under `.lake/manual-expansion-trial-XX/`:

| Trial | Outcome |
| --- | --- |
| 01 | Analytic file passed; derivative file had two solver failures. |
| 02 | Analytic passed; derivative, Banach, and Uniform variants failed. |
| 03 | Setup stopped during a concurrent in-progress tactic build; no proof claim. The wrapper then disabled builds explicitly. |
| 04 | Analytic, projection, and Banach files passed. Asymptotic and Uniform variants failed; dependent files were blocked. |
| 05 | Eight complete files passed. Uniform lower estimate still failed; its two edits are excluded from `confirmed.json`. |
| 06 | Nine files passed, including finite additive measures. Unitization variants failed and are excluded from the confirmed patch. |
| 07 | Uniform upper alone passed. Shorter StrongLaw preparation failed because `hn` retained pointwise subtraction. |
| 08 | StrongLaw passed with explicit pointwise normalization and a five-line replacement. |
| 09 | New Banach, controlled-closure, and little-o preparation variants failed; later dependent files were blocked. |
| 10 | Banach and controlled-closure corrections passed; the exponential Lipschitz proof passed. Little-o had a no-progress `dsimp`; compact-bound membership required a typed witness. |
| 11 | Corrected little-o, compact-bound, and both logarithm estimates passed in complete files. |
| 12 | Exponential proof still warned about its unused `hr_nonneg` input: redundant `nlinarith` hints were removed from the generated proof. |
| 13 | Direct `mul_le_mul` preparation used that input and passed without warnings, preserving all assumptions and the five-line count. |

The failed right-derivative proposal is retained with `status: failed` rather
than silently dropped. Its first attempt could not find a certificate after
`sub_smul`. Uniform's larger reverse-triangle estimate also failed with explicit
bounds; the existing verified baseline remains available. Some initial failures
were preparation errors: omitted source bounds, pointwise-function subtraction,
or incomplete distance normalization. Corrections and copied sources remain in
the successive trial directories.

`reviewed-no-saving.json` records further reviewed spans with exact hashes. These
sites were not compiled as replacements and are not solver failures. In
particular, the Tannery and completion drafts appeared to need as much
preparation as their triangle steps saved.
