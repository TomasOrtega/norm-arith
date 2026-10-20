# Proposed mathlib replacements

Status: **complete**.

Mathlib revision: `2f3c7c8a8949b04a32f9303f59163acffb766996`.
Manifest SHA256: `b240953708b89feaa5522b0d6d196fe6c733084679cae9cbe9c9b362fa71ad4e`.

5 verified replacements from 14 catalogued candidates in 3 affected files.
Proof code: 57 → 18 lines, plus 0 added helper lines: **39 net proof lines saved**.
Added imports: 3 lines; savings including imports: 36 lines.
Helper declarations are charged in full once. Preparation is included in replacement spans. Tactic implementation and tests are separate from proof savings.

Warm whole-file Lean compilation emits `.olean`, `.ilean`, module sidecars and C. Every trial uses fresh outputs and actual variant imports. Dependencies are already built; import loading, search, proof construction, checking, serialization and C generation occur within each measurement. Native C object compilation and Lake dispatch are excluded.

| File | Original median (s) | Replacement median (s) | Before / after |
| --- | ---: | ---: | ---: |
| Mathlib/Analysis/Convex/Uniform.lean | 1.394 | 1.714 | 0.813× |
| Mathlib/Analysis/Calculus/FDeriv/Measurable.lean | 4.620 | 5.147 | 0.898× |
| Mathlib/Analysis/Analytic/Basic.lean | 5.363 | 5.541 | 0.968× |
| **Total** | 11.480 | 12.650 | 0.907× |

Ratios below 1 indicate a slowdown. Totals are per-pass sums before taking medians. Raw times and minimum/maximum values are in `report.json`; no samples are discarded.

Recorded setup/build/query processes: 13.160 s. These depend on the starting cache state; individual commands and logs are under `setup/` and are excluded from warm compile totals.

The separate NormArith rebuild after invalidating its own generated artifacts took **6.610 s** with dependency artifacts retained and artifact-cache retrieval disabled.

| Candidate | Status | Reason |
| --- | --- | --- |
| uniform-upper | verified replacement | Compiled replacement: combine the three existing bounds without spelling out the additive decomposition. |
| uniform-lower | unsupported | Reviewed only: the current goal has a difference of norms on the left, outside the initial norm-upper-bound interface. |
| fderiv-telescope | verified replacement | Compiled replacement: telescope three supplied differences over a general normed scalar field. |
| right-deriv-telescope | verified replacement | Compiled replacement: telescope three supplied differences in the right-derivative proof. |
| fderiv-param | verified replacement | Compiled replacement: retain explicitly prepared distance bounds and replace the additive triangle argument. |
| fderiv-map | unsupported | Reviewed only: target and source applications of the derivative require map_sub normalization; this trial keeps algebraic-map preprocessing outside the tactic. |
| right-deriv-symbolic | unsupported | Reviewed only: discovering the decomposition requires distributing a symbolic scalar across subtraction; symbolic scalar normalization is deferred. |
| fderiv-operator | unsupported | Reviewed only: needs application of an operator-norm bound to a vector; that is not a norm-vector source bound until prepared explicitly. |
| direct-triangle-no-saving | unchanged | Reviewed only: the existing direct norm_sub_le proof already takes one line; explicitly supplying both reflexive norm bounds to norm_arith provides no line reduction. No replacement was compiled. |
| analytic-partial-sums | verified replacement | Compiled trial: count the finite-sum unfolding/splitting preparation, then combine three existing bounds. Explicit z and y avoid projection-valued inferred arguments. |
| cstar-before-normed-instance | unsupported | Reviewed mathlib-wide discovery hit: proves a squared-norm inequality while constructing the normed-group instance, outside the initial norm-upper-bound interface. |
| rademacher-symbolic-prep | unsupported | Reviewed mathlib-wide discovery hit: symbolic scalar and Lipschitz/operator bounds need explicit preparation; retained for later expansion rather than extending the frozen pilot ad hoc. |
| strong-law-sums | unsupported | Reviewed mathlib-wide discovery hit: needs finite-sum distribution and a symbolic inverse-scalar norm estimate before additive decomposition; not attempted in this pilot. |
| mean-value-additive | unchanged | Initial source-hint and typed-bound attempts failed to find a decomposition after map_sub left the source and target in syntactically different forms. Adding an explicit change compiled, but takes five proof lines, equal to the existing proof, plus a new import. Keep the original. |
