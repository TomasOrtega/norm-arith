# norm-arith

A small, working Lean prototype for the step **“add and subtract the right
vectors, then apply the triangle inequality.”** It is a starting point for a
mathlib contribution, with an exact search engine, proved certificate lemmas,
and integration tests.

**Status:** bounded rational-decomposition search, not a complete port of
Isabelle's `norm` method. The code is an independent implementation informed by
that strategy. The remaining porting and contribution work is described below.

## Run it

With Git and [elan](https://github.com/leanprover/elan) installed, run from this
checkout:

```bash
lake exe cache get Mathlib.Analysis.Normed.Module.Basic \
  Mathlib.Tactic.Module Mathlib.Tactic.Linarith Mathlib.Tactic.NormNum
lake build --wfail
```

Lean is selected by `lean-toolchain`. The toolchain and dependencies download on
first use. `lake build` checks both libraries, including every test file.

The project pins Lean **4.36.0-rc1** and mathlib commit
`2f3c7c8a8949b04a32f9303f59163acffb766996` (16 October 2026).
The checked-in `lake-manifest.json` pins transitive dependencies as well.

## Validation

The pinned project passes `lake build --wfail`. Its 44 checks comprise 22 exact
arithmetic and search checks, 3 certificate examples, and 19 tactic examples,
including expected failures and recovery from an unsuccessful candidate.
The benchmark harness has a separate Python regression suite:

```sh
python3 -m unittest discover -s scripts
```

## Mathlib evaluation

Five compiled replacements shorten 57 proof lines to 18 at the pinned mathlib
revision: 39 fewer proof lines, or 36 fewer lines after charging three imports.
The patch is local and has not been merged into mathlib. Tactic implementation
and evaluation tooling are separate from these proof savings.

In ten paired runs with one Lean thread, the affected files compiled in 10.757 s
before and 11.435 s after: **6.3% slower**. A compilation-speedup claim is not
supported by these measurements.

See [the results](benchmarks/RESULTS.md) for compilation measurements and
[the selection ledger](benchmarks/SELECTION.md) for unsuccessful and deferred
candidates. To reproduce the evaluation:

```sh
lake exe cache get Mathlib.Analysis.Convex.Uniform \
  Mathlib.Analysis.Calculus.FDeriv.Measurable Mathlib.Analysis.Analytic.Basic \
  Mathlib.Tactic.Module Mathlib.Tactic.Linarith Mathlib.Tactic.NormNum
python3 scripts/benchmark.py benchmarks/candidates.json \
  --output .lake/reproduction --rebuild-tactic --threads 1
```

The output directory must be empty. [Harness documentation](scripts/README.md)
describes the measured work, raw artifacts, and manifest format.

## Try the tactic

```lean
module

import NormArith

example {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) (a b : ℝ)
    (h₁ : ‖x + (2 : ℝ) • y‖ ≤ a)
    (h₂ : ‖(3 : ℝ) • x - y‖ ≤ b) :
    ‖x + y‖ ≤ (4 * a + b) / 7 := by
  norm_arith [h₁, h₂]
```

The search finds `x + y = (4/7) • (x + 2 • y) + (1/7) • (3 • x - y)`.
Use `norm_arith? [h₁, h₂]` to print the successful decomposition.
It prints an identity, not a replacement tactic script.

The three-source approximation example also works:

```lean
example {E : Type*} [SeminormedAddCommGroup E]
    (x y x' y' : E) (a b M : ℝ)
    (hx : ‖x - x'‖ ≤ a) (hy : ‖y - y'‖ ≤ b)
    (hM : ‖x' + y'‖ ≤ M) :
    ‖x + y‖ ≤ M + a + b := by
  norm_arith [hx, hy, hM]
```

All supplied facts must have the shape `‖v‖ ≤ b`, and the goal must have the
shape `‖w‖ ≤ B`. Supply strict bounds as `h.le` when a weak bound suffices.
For bounds written directly in the goal, pass facts such as `le_refl ‖x‖`.

## Where to work

| File | Role |
| --- | --- |
| `NormArith/Search.lean` | Exact rational Gauss–Jordan elimination and bounded subset search |
| `NormArith/Certificate.lean` | Proved lemmas for scaling, addition, and finite certificates |
| `NormArith/Tactic.lean` | Read expressions, search, check vector identities, and finish scalar arithmetic |
| `NormArithTest/` | Algorithm tests, certificate tests, successful proofs, and expected failures |
| `benchmarks/` | Pinned mathlib candidates, discovery results, and proof replacements |
| `scripts/benchmark.py` | Source-checked patch generation and paired full-file compilation |
| `docs/UPSTREAM.md` | Concrete route from this prototype to a mathlib PR |
| `docs/REFERENCES.md` | Isabelle, mathlib APIs, and potential real-proof benchmarks |

The search proposes coefficients. The frontend checks the corresponding identity
with `module`, applies the proved certificate lemmas, and closes scalar arithmetic
with `norm_num` and `linarith`. Failed candidates restore the proof state.
No additional axioms, `sorry`, `unsafe`, or `native_decide` are used.

## Scope and next milestones

Vector addition, subtraction, negation, zero, and rational **real** scalar
expressions are recognized. Write `(2 : ℝ) • x`, not a natural-number scalar,
when you want scalar normalization. Other expressions are opaque atoms.
Integral decomposition coefficients use repeated addition and negation, requiring
only a seminormed additive commutative group. Fractional coefficients require a
real normed-space structure.
Reducible aliases and `let` definitions are not automatically unfolded.
Strict goals, normed-algebra products, symbolic scalar coefficients, and discovery
of new source bounds are outside the initial scope.

Search examines at most the first 12 supplied bounds, subsets of size at most 3,
128 subsets total, and 16 candidate results. Limits are in `Search.Config`.
Bounds are considered in the supplied order. The procedure is intentionally
incomplete, and it can miss a proof even when a suitable decomposition exists.

Suggested next steps:

1. Expand the documented mathlib candidate search and test more proof replacements.
2. Improve normalization, search limits, and diagnostics as those examples require.
3. Investigate compilation costs using the recorded affected-file measurements.
4. Discuss the measured result with mathlib contributors, then prepare a focused PR.

See [PLAN.md](docs/PLAN.md) for the agreed initial scope and implementation plan,
and [EVALUATION.md](docs/EVALUATION.md) for measurement and reporting rules.

See [UPSTREAM.md](docs/UPSTREAM.md) for placement, review, and AI-assistance policy.
This starter was generated with ChatGPT. Understand and review the code before
contributing it, disclose the assistance, and write community comments yourself.

License: Apache-2.0. Isabelle ML code is not bundled.
