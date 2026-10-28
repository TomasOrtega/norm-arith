# norm-arith

A Lean package for **checked norm arithmetic and analytic estimates**.
It combines supplied bounds and checks the resulting proof in Lean.

The package pins mathlib and does not change its source. Development is on
`feature/analytic-estimates`.

## Use in another project

Put `leanprover/lean4:v4.36.0-rc1` in `lean-toolchain`. Add this dependency to
`lakefile.toml`:

```toml
[[require]]
name = "norm-arith"
git = "https://github.com/TomasOrtega/norm-arith.git"
rev = "feature/analytic-estimates"
```

Run `lake update` and `lake exe cache get`. Use a commit instead of the branch
name for a fixed version. The pinned mathlib commit is
`2f3c7c8a8949b04a32f9303f59163acffb766996`.

```lean
import NormArith

example {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) (a b : ℝ)
    (h₁ : ‖x + y‖ ≤ a) (h₂ : ‖x - y‖ ≤ b) :
    ‖x‖ ≤ (a + b) / 2 := by
  norm_arith
```

## Public modules

| Import | Main use |
| --- | --- |
| `NormArith` | Rational norm arithmetic, distances, and vector equalities |
| `NormArith.Seminorm` | Exact LP arithmetic for several explicit real seminorms |
| `NormArith.Analysis` | Operator estimates, products, absorption, and registered analytic rules |
| `NormArith.Parameters` | Exact Hölder exponents and interpolation weights |
| `NormArith.FunctionSpace` | Finite `Lp` estimates, interpolation, mixed norms, and an elliptic estimate |
| `NormArith.FixedPoint` | Fixed points on a certified ball, stability, and residual bounds |
| `NormArith.Hilbert` | Rational quadratic estimates in real inner-product spaces |
| `NormArith.Realization` | Formal finite realization theorem; optional for tactic users |

`norm_arith`, `seminorm_arith`, and `analytic_estimate` use local facts.
An explicit list, such as `norm_arith [h₁, h₂]`, selects the analytic premises.
Local scalar comparisons remain available. Include membership and other analytic
premises in the list when a rule needs them.

`norm_arith?` and `analytic_estimate?` report the selected proof steps and offer
checked replay code. `lp_interpolate?` also reports the chosen weight.
Replay checks the stored proof without running the search again. Set
`norm_arith.replayText true` to print its full source in command-line output.
`hilbert_arith?` gives an explicit sum-of-squares proof.

## Analytic estimates

```lean
import NormArith.Analysis

example (E ν A F : ℝ) (hν : 0 < ν) (h : E + ν * A ^ 2 ≤ F * A) :
    E + (ν / 2) * A ^ 2 ≤ F ^ 2 / (2 * ν) := by
  analytic_estimate

example {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : Seminorm ℝ E) (x y : E) :
    2 * p x ≤ p (x + y) + p (x - y) := by
  seminorm_arith
```

Mark a proved theorem with `@[analytic_rule]` to use it in bounded rule search.
Local and scoped rules are supported. Every premise must be proved. The options
`analytic_estimate.maxDepth` and `analytic_estimate.maxApplications` set the limits.

```lean
import NormArith.FunctionSpace

open MeasureTheory
open scoped ENNReal

example {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ)
    (h₂ : MemLp f 2 μ) (h₆ : MemLp f 6 μ) :
    lpNorm f 4 μ ≤ lpNorm f 2 μ ^ (1 / 4 : ℝ) *
      lpNorm f 6 μ ^ (3 / 4 : ℝ) := by
  lp_interpolate 2 6 4
```

```lean
import NormArith.FixedPoint
import NormArith.Hilbert

example {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (B : X →L[ℝ] X →L[ℝ] X) (a : X) (A : ℝ)
    (hA : 0 ≤ A) (ha : ‖a‖ ≤ A) (hsmall : 8 * ‖B‖ * A ≤ 1) :
    ∃! u, ‖u‖ ≤ 2 * A ∧ a + B u u = u := by
  analytic_estimate

example {X : Type*} [SeminormedAddCommGroup X] [InnerProductSpace ℝ X]
    (x y : X) : ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  hilbert_arith
```

The function-space rules keep the measure, exponent, and membership assumptions
in the proof. The elliptic example takes its energy and Sobolev bounds as inputs.
The fixed-point theorem gives uniqueness on the stated ball. Hilbert search
handles rational quadratic forms and checks the signs of the square weights.

## Scope

The core uses a compact supporting-functional LP and mathlib's exact simplex
oracle. Lean checks the recovered vector identities and scalar bounds.
Structural search runs first; finite support enumeration remains available for
comparison. Set `norm_arith.forceLP` or `seminorm_arith.forceLP` to test the LP path.

The finite realization theorem proves the mathematical encoding. Runtime search
has resource limits. A failed search means unknown. The solver does not return a
counterexample. General nonlinear parameter search, new PDE hypotheses, and
arbitrary changes of mixed-norm order are outside the supported fragment.

See [progress](docs/progress.md) for the roadmap gates and [results](docs/results.md)
for measurements. The mathlib benchmark corpus contains 52 paired snippets,
including 36 complete theorem statements. Every tactic proof is shorter or equal
in proof-body line count; imports do not count toward savings.

## Build and check

```sh
lake exe cache get
lake build --wfail NormArith NormArithTest
python3 -m unittest discover -s scripts
python3 scripts/benchmark_snippets.py --check
python3 scripts/benchmark_snippets.py --manifest Benchmarks/backends.json --check
python3 scripts/benchmark_snippets.py --manifest Benchmarks/analytic.json --check
python3 scripts/check_consumer.py
```

To check an unpublished commit as a Git dependency, use
`python3 scripts/check_consumer.py --repository "$PWD"`.
The [benchmark guide](Benchmarks/README.md) explains timing and source accounting.
The [documentation index](docs/README.md) links the proofs, design, and roadmap.

Code and text were developed with AI assistance.
License: [Apache-2.0](LICENSE). Mathlib excerpts retain their source attribution.
