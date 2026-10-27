# Proofs and the trust boundary

## What is checked

All successful tactic applications produce Lean proof terms. The library has no
new analytic axioms. The mathematical realization/completeness argument in
[math.md](math.md) and the future algorithms in [roadmap.md](roadmap.md) are
explanations and proposals; they are not new formal completeness theorems.

| Claim or component | Checked source |
| --- | --- |
| Finite sums, rational scalar bounds, vector decomposition certificates | [`Certificate.lean`](../NormArith/Certificate.lean) |
| Actual vector identities and final scalar consequences | [`Tactic.lean`](../NormArith/Tactic.lean) |
| Exact LP coefficient/strictness checks and extraction tests | [`LP.lean`](../NormArith/LP.lean), [`NormArithTest/LP.lean`](../NormArithTest/LP.lean) |
| Explicit seminorm triangle, homogeneity, and reverse triangle | [`Seminorm.lean`](../NormArith/Seminorm.lean) |
| Young, absorption, operator and bilinear perturbation bounds | [`Analysis.lean`](../NormArith/Analysis.lean) |
| Positive and rejected analytic applications, including actual `Lp` Hölder operators | [`NormArithTest/Analysis.lean`](../NormArithTest/Analysis.lean) |
| Multiple seminorms and rejected cross-seminorm/definiteness inferences | [`NormArithTest/Seminorm.lean`](../NormArithTest/Seminorm.lean) |

`LP.checkCertificate` is an exact metaprogram check, not a kernel theorem stating
the correctness of the solver. Soundness does not depend on trusting this check:
the frontend separately builds proofs of the recovered identities and bounds.
The original context and these proved bounds must entail the original goal.

## Young and absorption

`NormArith.young_mul` proves, for real `a`, `b` and positive `ε`,

$$
ab\le\varepsilon a^2+\frac{b^2}{4\varepsilon}.
$$

It starts from the nonnegative square $(2\varepsilon a-b)^2$, clears a
positive denominator, and uses checked polynomial arithmetic. No sign restriction
on `a` or `b` is needed. `energy_absorb` applies it with $\varepsilon=\nu/2$
to turn $E+\nu A^2\le FA$ into
$E+(\nu/2)A^2\le F^2/(2\nu)$.

`absorb` uses `0 ≤ A`, `θ ≤ q`, `q < 1` and `A ≤ B + θ*A` to conclude
`A ≤ B/(1-q)`. The strict positivity of the denominator is part of the proof.
`absorb_half` specializes the budget. A regression example rejects absorption
when the available coefficient is one.

For coupled linear estimates,

$$
A\le F+\tfrac14B,\qquad B\le G+\tfrac12A,
$$

the checked conclusions are
$A\le8F/7+2G/7$ and $B\le4F/7+8G/7$. This is scalar linear arithmetic;
it does not need a nonlinear optimizer.

## Bilinear perturbation

For a continuous bilinear map `B`, the code proves

$$
B(x,y)-B(x',y')=B(x-x',y)+B(x',y-y').
$$

Triangle inequality and the operator norm bound give

$$
\|B(x,y)-B(x',y')\|
\le\|B\|\bigl(\|x-x'\|\|y\|+\|x'\|\|y-y'\|\bigr).
$$

The frontend recognizes this pattern. Tests instantiate it with mathlib's
actual Hölder bilinear operator on bundled `Lp` spaces. The `HolderTriple` and
normed-space exponent assumptions remain explicit in the Lean statement.

## An elliptic estimate block

`elliptic_absorb` is a scalar theorem representing the last step of an energy
argument. It assumes

$$
U\le SG,\quad SB\le\nu/2,\quad
\nu G^2\le FU+BGU,
$$

with $\nu>0$ and $S,F,B,G\ge0$, and proves

$$
G\le\frac{2SF}{\nu},\qquad
U\le\frac{2S^2F}{\nu}.
$$

Monotonicity substitutes the Sobolev-type bound into both right-hand terms.
The smallness inequality absorbs half the coercivity. The proof handles `G = 0`
separately before cancelling a positive `G` in the remaining case.

This theorem does not establish a Sobolev embedding, integrate by parts, or
formalize an elliptic PDE. Those analytic estimates are inputs. The roadmap
explains how the scalar quantities can arise from forcing, coefficient, function,
and derivative norms in an actual PDE argument.

## Quadratic fixed-point estimates

Let $\Phi(u)=a+B(u,u)$, with $\|a\|\le A$, $A\ge0$, and
$8\|B\|A\le1$. The checked ball estimate shows
$\|u\|\le2A\Rightarrow\|\Phi(u)\|\le2A$. The checked contraction estimate
shows, on this ball,

$$
\|\Phi(u)-\Phi(v)\|\le\tfrac12\|u-v\|.
$$

The radius `2*A` is a chosen template; the LP does not discover that nonlinear
choice. A stability lemma turns
$\|u-v\|\le\|a-b\|+\tfrac12\|u-v\|$ into
$\|u-v\|\le2\|a-b\|$. These are estimate lemmas, not an existence or global
uniqueness theorem. Applying Banach's fixed-point theorem on the complete closed
ball, and proving its hypotheses at the function-space level, remains separate.

## Finite `Lp` bridges

`eLpNorm_le_of_lpNorm_le` requires `MemLp` before transporting a real-valued bound
back to an extended-real norm. `lpNorm_le_of_eLpNorm_le` instead starts from a
finite extended-real upper bound. The raw-function triangle wrapper retains the
membership and `1 ≤ p` hypotheses required by the pinned mathlib API.

A negative regression checks that `lpNorm f p μ = 0` alone does not justify
`eLpNorm f p μ = 0`. Real-valued conversion can hide an infinite value; membership
or finiteness must be established rather than inferred from that conversion.

## What the tests do and do not prove

Expected-success examples check usability and reconstruction. Expected-failure
examples guard important boundaries. Forced LP examples prevent the old fallback
from masking a broken new backend. The benchmark pairs test the same statements
with source proofs and replacement proofs. None of these finite test collections
establish frontend completeness or a speedup on all analysis proofs.
