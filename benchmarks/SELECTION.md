# Candidate selection

The source revision is `2f3c7c8a8949b04a32f9303f59163acffb766996`.
`candidates.json` pins full-file and original-block SHA-256 hashes. It records
replacement proposals and reviewed exclusions; an exclusion is not a failed
Lean compilation. The evaluation harness establishes compilation success.

The two pilot files were selected before implementation:

- `Mathlib/Analysis/Convex/Uniform.lean`
- `Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`

The pilot trials cover the two three-difference telescoping proofs, the upper
estimate in uniform convexity, and the parameterized derivative estimate.
Preparation of distance bounds is included in the replacement block.

## Wider discovery

Run `python3 benchmarks/discover.py` to reproduce `discovery.json`. The script
searches the pinned checkout with `rg`, records every matching line, and sorts
results by path and line. At this revision `Mathlib` contains 8,637 Lean files.

| Query | Scope | Matching lines | Files |
| --- | --- | ---: | ---: |
| `norm_add₃_le` | all `Mathlib` | 10 | 7 |
| `norm_sub_le.*norm_sub_le\|norm_add_le.*norm_add_le` | all `Mathlib` | 3 | 3 |
| `congr.*abel\|abel.*norm\|norm.*abel` | `Mathlib/Analysis` | 18 | 11 |

These lexical searches are a reproducible expansion of the pilot, not an
exhaustive survey of every proof that the tactic could shorten. All executable
three-term-triangle hits were inspected. The two `Normed/Group/Basic.lean` hits
declare generated aliases rather than candidate proofs.

| Discovered proof | Review outcome |
| --- | --- |
| `Analytic/Basic.lean`, partial-sum convergence | Included: count unfolding and splitting finite sums, then combine three existing bounds. |
| `CStarAlgebra/Module/Defs.lean`, `norm_triangle` | Squares of norms while constructing a normed-group instance; excluded from this pilot. |
| `Calculus/Rademacher.lean`, `hasFDerivAt_of_hasLineDerivAt_of_closure` | Symbolic scalar, Lipschitz, and operator bounds need preparation; retained for later work. |
| `Probability/StrongLaw.lean`, `strong_law_ae_of_measurable` | Finite-sum distribution and inverse-scalar norm bounds need preparation; retained for later work. |
| `Calculus/MeanValue.lean`, `norm_image_sub_le_of_norm_hasFDerivWithin_le'` | Trial compiled after explicit target preparation; five replacement proof lines equal the original five, and an added import would cost another line. Keep the original. |

The repeated-triangle query also finds `CStarAlgebra/PositiveLinearFunctional.lean`
(multiplication, powers, and symbolic complex scalar estimates) and
`Normed/Algebra/UnitizationL1.lean` (construction of a submultiplicative norm).
Both require substantial domain-specific preparation and were reviewed only.

The remaining additive-identity hits are non-norm algebra
(`Analytic/ChangeOrigin.lean`, `UniformLimitsDeriv.lean`, `Gamma/Beta.lean`),
strict convexity (`StrictConvexBetween.lean`), extended norms
(`BoundedVariation.lean`), documentation (`Normed/Group/Hom.lean` and
`SemiNormedGrp.lean`), or an equality using a nonlinear right inverse
(`InverseFunctionTheorem/ApproximatesLinearOn.lean`). They were not submitted to
the tactic in this pilot. Pilot hits in these queries refer to the same candidate
blocks rather than additional examples.

## Outcomes and limits

Each candidate's reason distinguishes a proposed replacement, an unsupported
goal shape, preparation deferred from this pilot, and an unchanged direct proof.
The single-line `norm_sub_le` proof in the pilot is retained as a no-saving
example. Supplying reflexive norm bounds would add source text without removing
any proof lines.

The initial full-file trial accepted the uniform-convexity replacement. The
telescoping and mean-value trials exposed metadata on Lean goals that the
prototype did not consume. The first parameter-bound preparation also exposed
a `simpa only` instance-opacity mismatch; explicit distance rewrites avoid that
preparation issue. The metadata bug was fixed with a regression test, and the
parameter bound uses explicit rewrites. The analytic trial initially inferred a
projection expression for a vector; explicit `I z h'z` and `I y yr'` arguments
make the existing source expressions match the goal. These unsuccessful initial
trials guide fixes and are not benchmark measurements.

The mean-value trial initially failed to find a decomposition after `map_sub`
because the source and target used syntactically different atom expressions. An explicit
typed bound and `change` produced a compiling five-line replacement, so it was
retained as a verified no-saving outcome rather than added to the patch.
`candidates.json` includes that trial's complete replacement text.

The final candidate set is frozen after all five replacements passed full-file
integration checks and before headline timing runs. It contains 14 reviewed
sites, five replacements across three files, seven deferred exclusions, and two
unchanged examples. No statement or assumption is changed. Expanding the search,
preparing more bounds, or supporting more goal forms may find
additional improvements; the pilot does not claim that the excluded arguments
are mathematically impossible for norm arithmetic.
