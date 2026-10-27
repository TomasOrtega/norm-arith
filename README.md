# norm-arith

An independent Lean package for **checked norm arithmetic and analytic estimates**.
The direction is to shorten estimate blocks in analysis and PDE proofs: combine
norm bounds, compose operator estimates, and discharge arithmetic while Lean
checks the resulting proof.

Development happens on **`feature/analytic-estimates`**. This package depends on
mathlib without modifying it. A later contribution to mathlib should be possible;
no mathlib port is part of this branch.

## Use it in another project

Use `leanprover/lean4:v4.36.0-rc1` in `lean-toolchain` and add to `lakefile.toml`:

```toml
[[require]]
name = "norm-arith"
git = "https://github.com/TomasOrtega/norm-arith.git"
rev = "feature/analytic-estimates"
```

Run `lake update` and `lake exe cache get`. For reproducible work, replace the
branch name with a commit. The package pins mathlib to
`2f3c7c8a8949b04a32f9303f59163acffb766996`; projects already using mathlib should
use a compatible revision.

```lean
import NormArith

example {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) (a b : ℝ)
    (h₁ : ‖x + y‖ ≤ a) (h₂ : ‖x - y‖ ≤ b) :
    ‖x‖ ≤ (a + b) / 2 := by
  norm_arith
```

## Features

| Entry point | Purpose |
| --- | --- |
| `import NormArith` | Rational-linear norm arithmetic, distances, local vector equalities, checked certificates |
| `norm_arith` / `norm_arith?` | Prove an estimate; `?` also explains a successful search |
| `norm_arith [h₁, h₂]` | Select norm premises; local scalar comparisons remain available |
| `import NormArith.Seminorm` | `seminorm_arith` for explicit, possibly different, bundled seminorms |
| `import NormArith.Analysis` | `analytic_estimate`, operator/bilinear estimates, Young/absorption templates, finite-`Lp` bridges |

The new **LP backend** uses a compact supporting-functional formulation and
mathlib's exact simplex oracle. It recovers rational triangle certificates and
checks actual vector identities in Lean. Short searches still run first;
finite decomposition enumeration remains a fallback.

```lean
import NormArith.Analysis

example (E ν A F : ℝ) (hν : 0 < ν) (h : E + ν * A ^ 2 ≤ F * A) :
    E + (ν / 2) * A ^ 2 ≤ F ^ 2 / (2 * ν) := by
  analytic_estimate

example {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : Seminorm ℝ E) (x y : E) (A B : ℝ)
    (hx : p x ≤ A) (hy : p y ≤ B) : p (x - y) ≤ A + B := by
  seminorm_arith
```

`analytic_estimate [facts]` and `seminorm_arith [facts]` add proved hints to the
local context. Analytic inputs such as Sobolev or Hölder estimates must come with
their required side conditions. Raw `eLpNorm` values are not assumed finite.

## Scope and direction

The LP addresses generic rational-linear norm arithmetic. The analytic frontend
also uses bounded theorem templates and nonlinear scalar arithmetic. Explicit
seminorm automation is currently structural. Exponent synthesis, general
interpolation planning, mixed-norm search, and Hilbert certificates are later
milestones, described in the [roadmap](docs/roadmap.md).

Every successful tactic call produces a Lean proof. Failure or resource limits
mean **unknown**, not a counterexample. [Progress](docs/progress.md) distinguishes
working features from proposals; [results](docs/results.md) records measured
proof-size and compilation costs, including slower cases.

The current 20-snippet workload saves 56 net lines and takes 11.6% longer to
compile in fresh processes. The five-case backend comparison shows no aggregate
LP speedup. These are starting measurements for further development.

## Build, test, and measure

With [elan](https://github.com/leanprover/elan) installed:

```sh
lake exe cache get
lake build --wfail NormArith NormArithTest
python3 -m unittest discover -s scripts
python3 scripts/check_consumer.py
python3 scripts/benchmark_snippets.py --check
python3 scripts/benchmark_snippets.py --pairs 5 --warmups 1
```

The benchmark corpus contains standalone pairs from pinned mathlib sources.
Both versions state the same proposition, with attribution and adaptations
recorded for every pair. Counts charge extra imports and setup. The runner
alternates compilation order, uses fresh outputs, and retains raw samples.
Dependency builds are excluded from warm timings. Synthetic backend comparisons
are measured separately; see the [benchmark guide](Benchmarks/README.md).

## Repository map

| Path | Contents |
| --- | --- |
| `NormArith/` | Importable implementation and checked analytic lemmas |
| `NormArithTest/` | Regression proofs, expected failures, analytic examples |
| `Benchmarks/Baseline/`, `Benchmarks/Tactic/` | Original mathlib snippets and replacement proofs |
| `Benchmarks/manifest.json` | Source revision, theorem, span, and adaptations |
| `Benchmarks/BackendBaseline/`, `Benchmarks/BackendLP/` | Separate synthetic reference-versus-LP cases |
| `scripts/` | Benchmark runner and accounting tests |
| `docs/` | Mathematics, proofs, tradeoffs, roadmap, progress, results |

Start with the [documentation index](docs/README.md). Earlier paper and census
artifacts remain accessible through [history](docs/history.md).

Code and documentation were developed with AI assistance. Contributions should
include checked examples and report failures as well as successes.
License: [Apache-2.0](LICENSE). Mathlib snippets retain their source attribution.
