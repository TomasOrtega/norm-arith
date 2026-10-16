# norm-arith

A small, working Lean prototype for the step **“add and subtract the right
vectors, then apply the triangle inequality.”** It is a starting point for a
mathlib contribution, with an exact search engine, proved certificate lemmas,
integration tests, and CI.

**Status:** bounded rational-decomposition search, not a complete port of
Isabelle's `norm` method. The code is an independent implementation informed by
that strategy. The remaining porting and contribution work is described below.

## Run it

With Git and [elan](https://github.com/leanprover/elan) installed:

```bash
unzip norm-arith-starter.zip
cd norm-arith
lake exe cache get Mathlib.Analysis.Normed.Module.Basic \
  Mathlib.Tactic.Module Mathlib.Tactic.Linarith Mathlib.Tactic.NormNum
lake build --wfail
```

Lean is selected by `lean-toolchain`. The toolchain and dependencies download on
first use. The ZIP contains source only, so these downloads are much larger than
the ZIP. `lake build` checks both libraries, including every test file.

The project pins Lean **4.36.0-rc1** and mathlib commit
`2f3c7c8a8949b04a32f9303f59163acffb766996` (16 October 2026).
The checked-in `lake-manifest.json` pins transitive dependencies as well.

After unpacking, create your own repository:

```bash
git init -b main
git add .
git commit -m "Start norm-arithmetic prototype"
```

## Validation

The pinned project passes `lake build --wfail`. Its 38 checks comprise 22 exact
arithmetic and search checks, 3 certificate examples, and 13 tactic examples,
including expected failures and recovery from an unsuccessful candidate.
The included GitHub Actions workflow uses the same build command.

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
example {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
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
Reducible aliases and `let` definitions are not automatically unfolded.
Strict goals, normed-algebra products, symbolic scalar coefficients, and discovery
of new source bounds are outside the initial scope.

Search examines at most the first 12 supplied bounds, subsets of size at most 3,
128 subsets total, and 16 candidate results. Limits are in `Search.Config`.
Bounds are considered in the supplied order. The procedure is intentionally
incomplete, and it can miss a proof even when a suitable decomposition exists.

Suggested next steps:

1. Port Isabelle's broader candidate generation and dominance pruning into the
   isolated search layer, keeping the existing proof checker.
2. Improve normalization, user-configurable search limits, and diagnostics.
3. Compile and time actual mathlib proof replacements against existing tactics.
4. Discuss the measured result with mathlib contributors, then prepare a focused PR.

See [UPSTREAM.md](docs/UPSTREAM.md) for placement, review, and AI-assistance policy.
This starter was generated with ChatGPT. Understand and review the code before
contributing it, disclose the assistance, and write community comments yourself.

License: Apache-2.0. Isabelle ML code is not bundled.
