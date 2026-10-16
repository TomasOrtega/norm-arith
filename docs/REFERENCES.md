# References

## Algorithm and history

- [Isabelle's `Norm_Arith` theory](https://isabelle.in.tum.de/library/HOL/HOL-Analysis/Norm_Arith.html)
  supplies proof rules and exposes the `norm` method.
- [Amine Chaieb's `normarith.ML`](https://github.com/isabelle-prover/mirror-isabelle/blob/master/src/HOL/Analysis/normarith.ML)
  is the algorithmic reference: rational vector expressions, decomposition search,
  and proof-producing arithmetic. No ML source is included here.
- [Isabelle2009 `Euclidean_Space`](https://isabelle.in.tum.de/website-Isabelle2009/dist/library/HOL/Library/Euclidean_Space.html)
  already uses `by norm` for triangle and distance estimates.
- [Lean discussion, 8 May 2020](https://leanprover-community.github.io/archive/stream/187764-Lean-for-teaching/topic/Real.20analysis.html#196946153)
  requests automation for discovering the decomposition behind a norm inequality.

## Existing Lean tools and potential benchmarks

- [`module`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Tactic/Module.lean): vector-expression equality normalization.
- [`bound`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Tactic/Bound.lean): structural inequality automation.
- [`Uniform.lean`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Analysis/Convex/Uniform.lean): norm estimates with explicitly chosen decompositions.
- [`Measurable.lean`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean): telescoping vector differences and norm estimates.

## Contribution and CI guidance

- [mathlib contribution guide and AI policy](https://leanprover-community.github.io/contribute/index.html)
- [PR workflow](https://leanprover-community.github.io/contribute/how-to-contribute.html) and [style guide](https://leanprover-community.github.io/contribute/style.html)
- [`Common.lean` import boundary](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Tactic/Common.lean)
- [`module` tests](https://github.com/leanprover-community/mathlib4/blob/master/MathlibTest/module.lean): an example of tactic-test placement.
- [Official `lean-action`](https://github.com/leanprover/lean-action): standalone Lean CI.

Links to `master` are for navigation; record exact revisions when reporting benchmarks.
