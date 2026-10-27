# Design

Search finds a candidate. Lean checks the proof. No optimizer output is accepted
as a mathematical assumption.

## Modules

| Module | Role |
| --- | --- |
| `Certificate`, `SeminormCertificate` | Elementary norm and seminorm proof lemmas |
| `Reify` | Shared rational vector and scalar data |
| `Search` | Short decompositions and finite reference enumeration |
| `LP` | Exact supporting-functional encoding, simplex search, and extraction |
| `Tactic`, `Metric` | Norm and distance frontends |
| `Seminorm` | Separate LP blocks for exact seminorm expressions |
| `Facts`, `Rules` | Explicit fact selection and bounded analytic rule search |
| `Analysis` | Operators, products, Young's inequality, and absorption |
| `Parameters`, `FunctionSpace` | Exact exponent choices and finite function estimates |
| `FixedPoint` | Existence on a ball, uniqueness on that ball, and error bounds |
| `Hilbert` | Rational quadratic forms and checked sums of squares |
| `Replay`, `ReplayData` | Store and check a proof without repeating search |
| `Realization` | Formal meaning of finite support constraints |

`import NormArith` exposes the core tactic. Function-space, fixed-point, Hilbert,
and realization modules are optional. Runtime proof checking does not import the
Hahn–Banach realization proof.

## Arithmetic

The norm frontend tries scalar arithmetic, structural bounds, and short vector
decompositions first. It then tries the compact LP. Finite reference enumeration
remains available for comparison and fallback.

```mermaid
flowchart LR
    A[Goal and selected facts] --> B[Normalize]
    B --> C[Short search]
    C --> D[Exact LP]
    D --> E[Vector identities and scalar proof]
    E --> F[Lean check]
```

An LP support row is search data. It is never added to the Lean context as an
assumption. The extractor recovers rational vector decompositions. The frontend
proves each identity, uses triangle and homogeneity lemmas, and finishes with
checked scalar arithmetic.

Explicit seminorms use the same rational representation and LP solver. The family
key includes the actual seminorm expression. A pullback along one linear map is
distinct from a pullback along another map. Supplied vector equalities give zero
observations for every relevant family. A zero seminorm value alone does not give
a vector equality.

The LP has a quadratic number of support rows. This bounds the encoding size,
not the running time. Exact rational coefficients and Lean proof construction
can still be expensive.

## Analytic rules

The frontend first adds a bounded set of proved structural estimates. It then
tries registered theorems whose conclusions match the target. Each premise is
proved by arithmetic or another registered rule. Search restores the previous
state when a branch fails. A repeated target cannot justify itself.

`@[analytic_rule]` supports global, local, and scoped rules. The default limits
are six rules along a branch and 128 attempted applications. These limits and
Lean's heartbeat budget can cause failure on a valid goal.

An explicit fact list restricts all later rule applications. Selected proofs
are copied into the search context before omitted analytic assumptions are
removed. Pure scalar comparisons remain available. The filter also checks
proposition-valued classes so an omitted bound cannot return through an instance.

## Parameters and representations

Hölder planning uses rational reciprocal exponents. Zero represents infinity.
Interpolation chooses a convex weight between fixed endpoints. Lean checks the
chosen exponent equation, its range, and the applicable theorem instance.
Membership and measurability are separate premises.

Raw `lpNorm` is not treated as a seminorm on all functions. Its conversion from
`eLpNorm` needs finiteness or `MemLp`. Mixed norms use nested `Lp` spaces in a
fixed order. The library does not exchange that order without a theorem.

The elliptic wrapper uses supplied energy and Sobolev estimates. The fixed-point
wrapper checks the ball and contraction conditions, then applies mathlib's
Banach theorem. It states uniqueness on that ball.

## Replay and diagnostics

The `?` forms report selected rules, decompositions, or parameters and return a
proof that can be replayed without LP or rule search.
Replay checks the data and its type in the current context. Changed premises or
a changed target can invalidate it. Declared universe names and global theorem
names are also part of the saved data. There is no fallback from replay to search.
Hilbert replay gives explicit squares and uses only algebraic normalization.

Failures distinguish unsupported inputs, missing proofs, and resource limits
where the frontend can identify the cause. No failure is called a counterexample.
The contradiction oracle does not return a feasible model.

## Package boundary

The package owns the `NormArith` namespace and uses pinned mathlib without
patches. Tests, paired benchmarks, and a separate Git consumer check its public
imports. A future mathlib contribution needs a separate API and dependency review.
