# Start with explicit upper bounds and additive certificates

The first useful version supports additive norm arguments in seminormed additive
commutative groups without requiring a real vector-space structure. A candidate
telescoping proof in `FDeriv/Measurable.lean` does not assume real scalar structure,
so the current real-scalar certificate path imposes an unnecessary restriction.
Retain the existing rational-real fragment alongside additive support.

Callers initially select the source bounds explicitly with
`norm_arith [h₁, ..., hₙ]`. Pilot goals remain of the form `‖v‖ ≤ B`, and short
preparation steps are allowed and counted. Automatic context search, general
norm comparisons, strict inequalities, distance preprocessing, and symbolic
scalar coefficients are deferred until actual examples justify the added scope.
