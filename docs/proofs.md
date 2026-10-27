# Proofs and the trust boundary

Every successful tactic call produces a Lean proof. Search and numeric data are
checked against the original mathematical expressions.

| Claim | Checked source |
| --- | --- |
| Finite norm combinations | [Certificate](../NormArith/Certificate.lean) |
| Seminorm blocks and strict scalar certificates | [SeminormCertificate](../NormArith/SeminormCertificate.lean) |
| Finite sup-norm realization, relations, and several seminorms | [Realization](../NormArith/Realization.lean) |
| LP extraction and actual vector identities | [LP](../NormArith/LP.lean), [Tactic](../NormArith/Tactic.lean), [Seminorm](../NormArith/Seminorm.lean) |
| Operators, products, Young, and absorption | [Analysis](../NormArith/Analysis.lean) |
| Finite interpolation, Hölder, mixed norms, and elliptic estimates | [FunctionSpace](../NormArith/FunctionSpace.lean) |
| Banach fixed points and error bounds | [FixedPoint](../NormArith/FixedPoint.lean) |
| Quadratic identities and nonnegative square weights | [Hilbert](../NormArith/Hilbert.lean) |

## Realization and certificates

`Realization.Supports` states nonnegativity, an anchor equality, and bounds on
all observed vectors. Hahn–Banach proves that actual norm values give support
rows. The columns of those rows give vectors in a finite sup-norm space with
exactly the required norms. Every supplied vector relation is checked in every
support row. The proof allows dependent atoms, zero values, and no observations.

For several seminorms, one common coordinate space contains every family block.
Each seminorm reads its own block. This proves the finite seminorm statement;
it does not identify several genuine norms with arbitrary independent kernels.

The runtime checker uses elementary certificates. It proves the selected vector
identities and applies triangle inequality and homogeneity. The generalized
seminorm block lemma also permits a zero target multiplier without division.
A strict scalar conclusion requires a positively weighted strict premise.

`LP.checkCertificate` is a metaprogram check. Soundness also has an independent
kernel boundary: the frontend builds actual Lean proofs of the recovered bounds
and the final conclusion. The finite realization theorem does not prove that a
bounded frontend always finds a certificate.

## Analytic estimates

`young_mul` starts from a nonnegative square and clears a positive denominator.
`energy_absorb` spends half the positive coercive coefficient. `absorb` requires
a coefficient strictly below one. All zero-factor cases stay in the statements
and proofs.

The bilinear perturbation theorem proves

$$B(x,y)-B(x',y')=B(x-x',y)+B(x',y-y')$$

before it applies norm bounds. Symbolic constants use proved monotonicity or
polynomial arithmetic; they are not rational vector coefficients.

The elliptic wrapper proves the required Hölder bounds for the forcing and drift
terms. It then uses the supplied energy and Sobolev bounds to obtain

$$G\le 2SF/\nu,\qquad U\le 2S^2F/\nu.$$

It handles `G = 0` before cancelling a positive factor. The vector-valued version
uses a bounded pairing for the drift. Membership, the energy inequality, the
Sobolev constant, and smallness remain explicit inputs. Deriving an energy
identity from a differential equation is outside this estimate block.

## Fixed points

A complete closed ball is invariant under the supplied map, and its Lipschitz
constant is strictly below one. The wrapper applies mathlib's Banach theorem to
the restricted map. The quadratic template uses radius `2*A` and
`8*K*A ≤ 1`; a separate wrapper accepts any radius that passes both scalar checks.

Uniqueness is on the certified ball. The same contraction estimate gives
stability and residual bounds. Zero radius is checked directly and needs no
division. Tests show why global uniqueness and a contraction constant of one
would be invalid extensions.

## Finite function norms

Real conversion requires `MemLp` or a finite extended-real bound. Tests reject
an attempted finite conversion from the real-valued junk value alone.
Interpolation uses a checked Hölder triple for the scaled endpoint exponents.
The planner checks exact rational equations, including infinity endpoints.
Nested `Lp` spaces fix the order of mixed norms.

## Quadratic proofs and tests

Hilbert search factors a rational symmetric matrix. It checks the full matrix
identity and nonnegative weights. Lean then proves the sum-of-squares identity.
The replay proof does not call the factor search. Two held-out mathlib identities
check the public tactic after rule development.

Regression proofs check successful applications. Expected failures guard signs,
strictness, family identity, missing premises, circular rules, and stale replay.
These tests establish finite coverage, not universal frontend completeness or a
speedup on all analytic proofs.
