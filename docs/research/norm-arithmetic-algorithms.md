# Norm arithmetic: algorithm and completeness questions

Research date: 20 October 2026. This note supports the design interview. It does
not select an algorithm or claim a new implementation result.

The local project pins Lean `4.36.0-rc1` and mathlib
`2f3c7c8a8949b04a32f9303f59163acffb766996`. Local implementation observations
refer to the current working tree, which includes changes beyond its Git HEAD.

## What the project currently establishes

The tactic reads explicit upper bounds `‖vᵢ‖ ≤ bᵢ` and an upper-bound goal
`‖w‖ ≤ B`. It reifies vector syntax into rational coefficient arrays. Search
enumerates source subsets, solves each selected linear system, and sets free
variables to zero. Its default limits are 12 sources, support 3, 128 subset
attempts, and 16 returned results. Search does not inspect the scalar bounds.
These are direct observations of [Search.lean](../../NormArith/Search.lean) and
[Tactic.lean](../../NormArith/Tactic.lean).

Integral coefficients now use natural multiples and negation. Fractional
coefficients use real scalar multiplication. `module` checks the vector identity;
proved norm lemmas construct the bound; `norm_num` and `linarith` finish scalar
arithmetic. A restricted scalar attempt uses the constructed certificate before
falling back to the full local context. Search results are proposals, not trusted
facts. See [Certificate.lean](../../NormArith/Certificate.lean) and
[Tactic.lean](../../NormArith/Tactic.lean).

The current procedure is incomplete. Its tests and measured proof replacements
do not establish completeness, coverage of all mathlib norm arguments, or a
runtime bound that is independent of its budgets.

## Primary related work

Solovay, Arthan, and Harrison prove decidability of the universal fragment of the
theory of real normed spaces. Section 7 gives a finite-norm extension argument;
Corollary 42 gives the decidability result. The authors identify parameterized
linear programming as a more efficient route for the additive case. Their full
language also allows scalar multiplication and is broader than a rational linear
tactic. The result does not establish decidability of arbitrary quantified normed
space statements. See the [2012 paper, section 7](https://arxiv.org/pdf/0904.3482).

HOL Light already contains `NORM_ARITH` in
[Multivariate/vectors.ml](https://github.com/jrh13/hol-light/blob/master/Multivariate/vectors.ml).
Isabelle exposes a `norm` method for real normed vector spaces. Its preprocessing
includes distance-to-norm rewriting, vector equations, and strict comparisons.
The [theory](https://isabelle.in.tum.de/library/HOL/HOL-Analysis/Norm_Arith.html)
contains examples with strict distance bounds.

The inspected Isabelle search enumerates coefficient sign choices and vertices,
checks the resulting equations, and removes candidates whose absolute
coefficients are dominated coordinate by coordinate. It constructs norm bounds
and passes them to real linear arithmetic. Thus, a complete finite family of
useful bounds, rather than one arbitrary decomposition, is part of its design.
The source file's latest recorded change is commit
`e29bb4ce04cdb891585ff18b1750b8ec8c805b4c`. See
[vertex construction and dominance pruning](https://github.com/isabelle-prover/mirror-isabelle/blob/e29bb4ce04cdb891585ff18b1750b8ec8c805b4c/src/HOL/Analysis/normarith.ML#L126-L143)
and [bound generation](https://github.com/isabelle-prover/mirror-isabelle/blob/e29bb4ce04cdb891585ff18b1750b8ec8c805b4c/src/HOL/Analysis/normarith.ML#L279-L328).

A paper about this project must distinguish an implementation in Lean, its
mathematical guarantees, and its library evaluation from these earlier results.
An assertion that this is the first decision procedure for linear norm arguments
would conflict with this evidence.

## A precise small real-vector-space problem

The following is a proposed specification, not a theorem proved in this repo.
Let the atoms be vector variables. Let every vector expression be a rational
linear combination of these atoms. Assume a real seminormed vector space, a
finite set of source bounds, and a single weak upper-bound goal. First restrict
the scalar bounds `bᵢ` and `B` to rational constants, with `bᵢ ≥ 0`.

Write the source columns as a rational matrix `A` and the target as a rational
column `t`. A certificate is a rational vector `c` satisfying

\[
A c = t, \qquad \sum_i |c_i| b_i \le B.
\]

The triangle inequality and real homogeneity prove the goal from this certificate.
Split `c = p - q`, where `p,q ≥ 0`. It suffices to find a solution to the rational
linear system

\[
A(p-q)=t, \qquad b^T(p+q)\le B, \qquad p,q\ge0.
\]

This is an LP feasibility problem. Its successful result can use the project's
existing certificate boundary. The generic LP ideas are standard: the authors'
[Convex Optimization slides](https://web.stanford.edu/~boyd/cvxbook/bv_cvxslides.pdf)
give absolute-value LP formulations in section 6 and Farkas alternatives in
section 5. These facts do not establish that a particular implementation is fast.

A defensible completeness target is: for this exact rational grammar and constant
bound problem, find a certificate whenever the bound is valid for all assignments
of the vector atoms in all real seminormed spaces. A proof must address zero-cost
sources, targets outside the source span, and inconsistent scalar assumptions.
It must distinguish a timeout from a mathematical negative answer.

This specification omits symbolic scalar coefficients, applications of linear
maps, finite-sum expansion, and relations hidden by definitions. Treating such
terms as independent opaque atoms limits completeness to the reified grammar.

## Why symbolic bounds and broader goals need a separate specification

Real proofs use scalar variables and side conditions, not only rational bounds.
Examples include `a ≤ b`, positive error terms, and lower bounds on norms.
Strict comparisons also require a strictness rule or a positive scalar gap.

For a broader linear fragment, one possible specification permits rational
linear combinations of norm terms and scalar variables on either side of an
equality or comparison. Vector arguments still use rational coefficients. The
procedure must then combine the relevant norm inequalities with scalar arithmetic;
finding one decomposition and rejecting its scalar bound is insufficient as a
general design.

An eager algorithm can construct a complete finite family of decomposition
inequalities and call scalar arithmetic. A possible alternative is to generate
constraints on demand: ask scalar arithmetic for a candidate assignment of norm
values, find a violated norm inequality, check it, and repeat. The latter is a
design idea, not an implemented or proved procedure here. A completeness claim
would need a finite or otherwise terminating refinement argument.

Vector equalities and disequalities are an additional boundary. A normed space
can turn a zero norm into vector equality; a seminormed space generally cannot.
An extension must state which class assumptions its grammar uses.

## Arbitrary additive groups are a different mathematical fragment

An arbitrary seminormed additive commutative group need not satisfy
`‖n • x‖ = n * ‖x‖`. The available general inequality has the other strength:
`‖n • x‖ ≤ n * ‖x‖`. See the pinned
[norm_nsmul_le definition](https://github.com/leanprover-community/mathlib4/blob/2f3c7c8a8949b04a32f9303f59163acffb766996/Mathlib/Analysis/Normed/Group/Basic.lean#L435-L438).

For example, give `ℤ` the discrete norm: zero at zero and one elsewhere. This is
a normed additive group. At `x = 1`, both `‖x‖` and `‖2 • x‖` equal one. A source
bound `‖2 • x‖ ≤ 1` therefore does not imply `‖x‖ ≤ 1/2`. This is a mathematical
counterexample to applying the rational real-space rule to arbitrary groups.

Integral certificates are sound, but the present rational search is not a
complete integer search. Source vectors `x+x` and `x+x+x` imply the bound
`‖x‖ ≤ a+b` from bounds `a` and `b`, since `x = -(x+x)+(x+x+x)`. For columns
`[2]` and `[3]` and target `[1]`, the current solver instead proposes fractional
singleton solutions and sets the free variable of the dependent pair to zero.
Lifting the subset budgets does not produce the integral solution `(-1,1)`.
This conclusion follows from [solve](../../NormArith/Search.lean).

Possible promises are therefore different: completeness for the real rational
fragment with a partial group extension, or a separate integral search with a
precise group-level specification. The latter is more work than a change in
certificate syntax. This interview has not selected either promise.

## Algorithm choices and tradeoffs

| Approach | Potential benefit | Limit or required evidence |
| --- | --- | --- |
| Rank-aware basis enumeration | Small exact algorithm close to the current code; can enumerate sparse real certificates | The number of subsets can grow rapidly; fixed budgets remain incomplete; integer group certificates can require dependent supports |
| Exact rational LP | Directly states the constant-bound real problem; avoids enumerating all bases eagerly | Needs a suitable exact solver interface, termination argument for the advertised fragment, and proof reconstruction measurements |
| Full vertex family plus scalar arithmetic | Closest to the inspected Isabelle design; naturally serves symbolic bounds | Sign choices and vertex counts can grow rapidly; dominance pruning needs the source-bound nonnegativity argument |
| Lazy norm constraints | Can avoid building unused inequalities in a broad linear fragment | Requires a model/refinement interface and a completeness/termination argument; more moving parts |
| Graph path before general search | Cheap certificates for telescoping differences, valid even in additive groups | Covers a special input shape; symbolic weights cannot be ordered by Dijkstra without further reasoning |

The graph case represents a bound on `‖u-v‖` as an edge between `u` and `v`.
A path gives a telescoping identity and the sum of its bounds. With fixed
nonnegative rational edge weights, shortest-path search can select the smallest
path bound. Dijkstra's original
[paper](https://doi.org/10.1007/BF01386390) supplies the shortest-path algorithm;
the application to norm certificates is our design observation. With symbolic
weights, fewest edges need not mean the strongest bound.

The pinned mathlib already has an exact rational simplex oracle. Its
[positive-vector interface](https://github.com/leanprover-community/mathlib4/blob/2f3c7c8a8949b04a32f9303f59163acffb766996/Mathlib/Tactic/Linarith/Oracle/SimplexAlgorithm/PositiveVector.lean)
finds a nonnegative vector in a matrix kernel with a positive selected coordinate.
Its [scalar arithmetic interface](https://github.com/leanprover-community/mathlib4/blob/2f3c7c8a8949b04a32f9303f59163acffb766996/Mathlib/Tactic/Linarith/Datatypes.lean#L265-L284)
returns a contradiction certificate. It is not directly an API for minimizing a
norm decomposition cost. Reuse would need a reduction, not merely a call to
`linarith`. The
[simplex source](https://github.com/leanprover-community/mathlib4/blob/2f3c7c8a8949b04a32f9303f59163acffb766996/Mathlib/Tactic/Linarith/Oracle/SimplexAlgorithm/SimplexAlgorithm.lean)
uses Bland's pivot rule and checks Lean's resource limits. These implementation
facts do not amount to a formal correctness theorem for the oracle.

All these search choices can share a small, Lean-checked certificate layer. A
complete formal verification of the search algorithm is a different deliverable
from proving that every accepted certificate gives a theorem.

## Efficiency hypotheses to measure

The current frontend converts expressions back to syntax and elaborates a
vector equality, a certificate, and scalar tactics for each attempted candidate.
This is visible in [proveCandidate](../../NormArith/Tactic.lean). Possible changes
include constructing proof expressions directly, reusing normalization proofs,
and rejecting weak bounds before expensive proof construction. These are
hypotheses to profile, not established improvements.

A complete search may inspect more candidates than a small partial search. A
small graph case may therefore help common telescoping proofs even if an LP
solver handles the broad fragment. Conversely, several solver stages can add
overhead on small goals. The same frozen corpus and resource limits are needed
to assess this tradeoff.

Generated explicit certificates are another possible user interface. They can
move search out of later compilations. The present `norm_arith?` prints only a
decomposition, so certificate replay is a new feature. A paper must report
search-based tactic compilation and replay-based compilation as separate modes.

## Decisions the interview still needs

1. Is the paper's main claim a complete procedure for a defined fragment, or an
   effective Lean tactic with a partial search and systematic corpus results?
2. Does the main fragment cover rational real vector expressions, arbitrary
   additive groups, or both with different guarantees?
3. Are general linear norm comparisons, strict bounds, distance rewriting, and
   context discovery part of the first paper's specification or later extensions?
4. Does "all mathlib use cases" mean all sites found by a declared detector,
   every semantically eligible site under a declared grammar, or every existing
   norm proof? These define different coverage claims and amounts of work.
5. Is completeness to be proved in Lean, proved in the paper, or deliberately
   excluded from the contribution? What behavior is required after a timeout?
6. Which efficiency claim matters: tactic execution, proof checking, importing
   the tactic, affected-file compilation, or a clean library build? A shorter
   proof does not settle any of these measurements.
