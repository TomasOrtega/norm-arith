# Progress

The roadmap milestone gates are implemented for the bounded fragments below. Each row
lists the supported features and tests for its acceptance gate. The research
questions at the end of the roadmap remain open questions.

## Roadmap gates

| Gate | Implemented result | Main checks |
| --- | --- | --- |
| M0: baseline | Original sources, reports, dependency pin, and reference backend are retained | Existing 20 mathlib pairs and five backend pairs |
| M1: certificates and realization | Elementary seminorm certificates; finite sup-norm realization; zero values, dependent atoms, relations, and several families | `NormArithTest.Realization` |
| M2: compact LP and replay | Exact encoding and extraction; checked identities; strict and equality goals; stored proof graphs with no search fallback | `LP`, `LPAgreement`, `Replay`, and original core tests |
| M3: seminorms | Shared LP for ordinary norms and seminorms; separate families; local relations; supplied bridges; linear-map pullbacks, sums, and maxima | `NormArithTest.Seminorm` |
| M4: finite function norms | Bundled `Lp`, real `lpNorm`, and finite `eLpNorm` bridges; membership and infinity endpoints | `Analysis` and `FunctionSpace` tests |
| M5: analytic rules | Registered theorem search, operator and product bounds, Young, scalar energy, and coupled absorption | `Analysis` and `Rules` tests |
| M6: exponents and elliptic estimate | Exact rational exponent and weight choices; L2/L6 product bound; scalar and vector-valued drift estimates with supplied energy and Sobolev bounds | `Parameters` and `FunctionSpace` tests |
| M7: fixed points | Ball invariance, contraction, Banach existence, uniqueness on the ball, custom radii, zero radius, stability, and residual bounds | `NormArithTest.FixedPoint` |
| M8: corpus extensions | Nested `Lp` Hölder and rational Hilbert sums of squares | Two held-out analytic pairs and `HilbertHeldOut` |

The compact LP is compared with complete support enumeration on 25 small rational
problems. Each problem also checks that a stronger, false bound is rejected.
Forced backend tests prevent the short search from hiding an LP failure.

## Public interfaces

- `norm_arith` and `seminorm_arith` prove rational-linear estimates.
- `analytic_estimate` composes supplied facts and `@[analytic_rule]` theorems.
- `choose_holder` and `choose_interpolation` find exact arithmetic witnesses.
- `lp_interpolate` applies the finite interpolation theorem with the chosen weight.
  `lp_interpolate?` reports that weight and offers checked replay.
- `hilbert_arith` checks rational quadratic estimates in real inner-product spaces.
- `norm_arith?` and `analytic_estimate?` report selected rules or decompositions and offer checked replay code. Set
  `norm_arith.replayText true` to print the full code in a command-line run.
- `hilbert_arith?` offers explicit squares and algebraic normalization.

A fact list selects the analytic premises for all later search. Pure scalar
comparisons and the listed structural classes remain available. Custom classes
that contain bounds must be selected through their proofs or bound projections.
Without a list, the full local context is available.

## Scope

The formal realization theorem is for real rational-coefficient observations.
It does not prove completeness of the bounded tactic or provide a feasible-model
solver. Real coefficient combinations in complex spaces work when Lean supplies
the required real-space instances; no separate complex realization theorem is
claimed.

The LP defaults allow 48 observations, 64 vector atoms, 6000 support rows, and
4096 variable slots. Analytic search defaults to depth six and 128 rule attempts.
Hilbert search allows 24 vector atoms. Lean's heartbeat budget also applies.

The elliptic example takes the energy inequality and a valid Sobolev bridge as
inputs. It proves the Hölder and absorption steps. It does not derive the energy
identity from a PDE. The fixed-point result is local to its certified ball.
Mixed norms keep their stated order. The Hilbert tactic handles rational
quadratic forms, without a general semidefinite optimizer.

Countermodel extraction, arbitrary complex coefficients, quasi-norm rule packs,
nonlinear time selection, and an upstream mathlib contribution remain separate
extensions. None is required by the completed bounded APIs above.

## Verification

The final code at `cd9083f` passed:

- `lake build --wfail NormArith NormArithTest`.
- All 17 Python runner tests.
- All 20 original mathlib pairs and all five backend pairs.
- All five analytic pairs, including all 40 timing samples.
- Both cross-file replay captures and all 24 core timing samples.
- All six README examples in a separate project using this commit as a local Git dependency.

The repository has no `prek` configuration. The configured Lean check treats
warnings as errors. Documentation links and `git diff --check` also passed.

The [results page](results.md) records measured costs, helper source size, and
limits. Earlier reports and failed trial runs remain available. The code was
not tuned after the final held-out measurements.
