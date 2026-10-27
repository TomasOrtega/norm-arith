# Mathematics of the compact LP core

This page explains the reduction behind the code. The certificate lemmas and
applications are checked in Lean. The full semantic completeness argument below
is a mathematical explanation, not a machine-checked completeness theorem for
the bounded tactic.

## Finite observations

Fix atoms $x_1,\ldots,x_d$ and observed rational combinations

$$
v_i=\sum_{k=1}^{d}a_{ik}x_k,\qquad a_{ik}\in\mathbb Q,
\quad i=1,\ldots,m.
$$

Let $r_i$ denote the proposed value of $\lVert v_i\rVert$. Scalar hypotheses
and the negated goal are affine comparisons in these variables and additional
scalar atoms. The matrix $A=(a_{ik})$ is fixed data; a product of unknowns is
not an LP coefficient.

Introduce one functional row $f_i\in\mathbb R^d$ for each observation:

$$
r_i\ge0,\qquad f_i\cdot a_i=r_i,\qquad
-r_j\le f_i\cdot a_j\le r_j\quad(1\le i,j\le m).
$$

This has $m+md$ norm/function variables and $O(m^2)$ support constraints.
Extra scalar atoms add variables. Different ambient spaces have separate blocks.

## Necessity and finite realization

Actual norm values satisfy these constraints. Choose a real norming functional
for each nonzero observed vector and evaluate it on the atoms; choose zero at a
zero observation. The seminorm version follows from a functional dominated by
that seminorm. This semantic argument uses Hahn–Banach, but runtime certificate
checking uses only finite triangle and homogeneity proofs.

Conversely, given feasible rows, put

$$
x_k=(f_{1k},\ldots,f_{mk})\in\ell_\infty^m.
$$

Coordinate $i$ of $v_j$ is $f_i\cdot a_j$. Every coordinate is bounded
in absolute value by $r_j$, and coordinate $j$ equals $r_j$. Therefore

$$
\lVert v_j\rVert_\infty=\max_i|f_i\cdot a_j|=r_j.
$$

The finite constraints characterize observable values when the normed space
may vary. Rational feasible data yield a rational finite-dimensional realization.
For a required vector relation $e=0$, a zero-norm observation forces every
functional to vanish on its coordinate vector, so the relation holds in this
realization. The frontend derives such zero observations from Lean equalities.

## The actual inequality encoding

The code uses one anchor and two support rows:

$$
r_i-f_i\cdot a_i\le0,\qquad
f_i\cdot a_j-r_j\le0,\qquad
-f_i\cdot a_j-r_j\le0.
$$

The support row with $j=i$ supplies the opposite anchor, giving equality.
Nonnegativity is included separately. Rational denominators are cleared by a
positive common multiple; the extractor retains that scale factor.

Mathlib's sparse simplex oracle returns nonnegative integer multipliers. The
code rechecks exact coefficient cancellation and a positively weighted strict
row. A valid extra row $-1<0$ allows this convention to certify a positive
constant contradiction arising entirely from weak input constraints.

To prove $L\le0$, negate with $-L<0$. To prove $L<0$, negate with
$-L\le0$. Equality needs both strict refutation branches. Strict and weak
comparisons must remain distinct.

## Eliminate the auxiliary functionals

For functional block $i$, let its restored rational multipliers be
$\alpha_i\ge0$ on the anchor and $\beta^+_{ij},\beta^-_{ij}\ge0$ on the
support rows. Functional-coordinate cancellation gives

$$
\alpha_i a_i=\sum_j(\beta^+_{ij}-\beta^-_{ij})a_j.
$$

For $\alpha_i>0$, set
$c_{ij}=(\beta^+_{ij}-\beta^-_{ij})/\alpha_i$. Lean checks the vector identity
$v_i=\sum_j c_{ij}v_j$ and proves

$$
\lVert v_i\rVert\le\sum_j|c_{ij}|\lVert v_j\rVert
\le\frac1{\alpha_i}\sum_j(\beta^+_{ij}+\beta^-_{ij})\lVert v_j\rVert.
$$

The first bound is at least as strong as the scalar contribution used by the LP,
since $|u-v|\le u+v$ for nonnegative $u,v$. A block with $\alpha_i=0$
contributes only a consequence of norm nonnegativity; it is skipped without
division. The final goal is proved from original Lean hypotheses and checked
norm certificates. No LP support assumption becomes a new axiom.

## Scope of exactness

The semantic reduction is exact for conjunctions of rational-affine comparisons
on finitely many rational-linear observations in generic real normed spaces.
Additional scalar atoms must be free real variables for the converse realization
claim. Treating an actual product or another structured expression as an opaque
atom gives a sound relaxation, whose feasible points need not realize that
expression's hidden relations.
The finite realization supplies the converse direction. The implementation
still has syntax restrictions and finite budgets, so it may return unknown
even when a certificate exists.

| Extension | What follows |
| --- | --- |
| Real rational vector combinations | Exact generic norm reduction |
| A complex space with real rational combinations | Same argument when the necessary real-space instance is available |
| Arbitrary complex coefficients | Outside this rational LP claim |
| Additive groups without real homogeneity | Only certificates justified by group lemmas are allowed |
| Several explicit seminorms | A separate-block mathematical realization exists; current frontend uses structural rules |
| Several genuine norms on a shared vector space | Additional kernel compatibility is needed; no blanket exactness claim |
| Products, variable powers, Sobolev/interpolation structure | Need additional proved analytic rules |
| Hilbert-specific quadratic inequalities | Need quadratic information beyond the generic norm LP |

Several arbitrary seminorms can be realized on a direct sum, each seminorm
inspecting its own coordinate block. Genuine norms cannot simply ignore the
other blocks because they must be definite. This distinction matters when
extending the frontend. Every required shared vector equality must be enforced
in every relevant functional block: a zero observation for one seminorm alone
does not force equality of the shared vectors.

## Analytic composition is a further layer

Hölder and interpolation require their exponent and membership hypotheses.
Young's inequality transforms a product into powers that fit an absorption
budget. These are theorem applications, not consequences of making all norm
values independent LP variables. For example, from
$E+\nu D^2\le FD$ and $\nu>0$,

$$
FD\le\frac\nu2D^2+\frac{F^2}{2\nu},\qquad
E+\frac\nu2D^2\le\frac{F^2}{2\nu}.
$$

`NormArith.energy_absorb` checks this. The longer-term task is to discover such
theorem and parameter choices while proving every side condition.

## Sources

Pinned mathlib sources:
[simplex oracle](https://github.com/leanprover-community/mathlib4/blob/2f3c7c8a8949b04a32f9303f59163acffb766996/Mathlib/Tactic/Linarith/Oracle/SimplexAlgorithm.lean),
[linarith frontend](https://github.com/leanprover-community/mathlib4/blob/2f3c7c8a8949b04a32f9303f59163acffb766996/Mathlib/Tactic/Linarith/Frontend.lean),
[Hahn–Banach](https://github.com/leanprover-community/mathlib4/blob/2f3c7c8a8949b04a32f9303f59163acffb766996/Mathlib/Analysis/Normed/Module/HahnBanach.lean).
The [roadmap](roadmap.md) includes the wider literature, PDE examples, exponent
planning, and proposed later certificate layers.
