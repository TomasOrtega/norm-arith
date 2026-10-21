# Norm arithmetic

Language for evaluating norm-inequality automation on mathlib proofs.

## Language

**Supplied norm bound**:
A fact of the form `‖v‖ ≤ b` explicitly selected by the caller for a `norm_arith`
proof.

**Discovered norm bound**:
A norm bound selected automatically from the local proof context for a
`norm_arith` proof.

**Semantic mathlib census**:
An inventory of eligible source-backed proof goals from complete elaboration of
a pinned mathlib revision, with extraction and tactic failures recorded.
_Avoid_: Every conceivable norm-arithmetic replacement

**Eligible proof goal**:
A source-backed proof obligation within the declared real core or a separately
reported sound extension, under the census preparation rules.

**Real norm-arithmetic core**:
The paper's real-vector-space fragment: rational vector combinations and linear
scalar comparisons involving norms, with distances expressed as norms of differences.

**Additive-group extension**:
Sound norm arithmetic in seminormed additive commutative groups, with guarantees
stated separately from the real norm-arithmetic core.

**Opaque upper-bound extension**:
Sound automation for a norm upper bound whose scalar right side is outside the
real core's recognized affine grammar. It has no separate completeness claim.

**Norm certificate**:
Finite mathematical evidence that vector relations and valid norm inequalities
imply a scalar comparison.

**Core completeness**:
The property that the mathematical procedure derives every comparison implied
by the declared real norm-arithmetic fragment and its recognized assumptions.

**Norm-certificate replay**:
Checking a previously generated norm certificate without repeating its search.

**Mathlib replacement patch**:
A reproducible set of proof replacements against a pinned mathlib revision.
An unmerged patch establishes proposed savings, not changes accepted into mathlib.

**Proof-line reduction**:
The decrease in nonblank, noncomment proof lines between existing mathlib proofs
and their `norm_arith` replacements, after charging added helper proofs and setup.
_Avoid_: Unqualified claims of total code saved

**Affected-file speedup**:
The ratio of total existing-proof compilation time to total replacement
compilation time over the same mathlib files, including files that become slower.
_Avoid_: Mathlib-wide speedup
