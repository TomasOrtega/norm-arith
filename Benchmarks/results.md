# Standalone snippet benchmark

Measured at 2026-10-27T15:57:29.725507+00:00. 20 paired snippets, 1 warmup pass(es), 5 recorded pairs.

**Workload:** selected standalone mathlib-derived snippets.

Selected standalone mathlib-derived estimates. Exact theorem copies, extracted local blocks, and adaptations are classified separately. This is not a census or a whole-file benchmark.

Case definitions: [manifest.json](manifest.json). This is not a census, a whole-file compilation study, or a claim about all PDE proofs.

## Source size

| Metric | Baseline | Tactic | Saved |
| --- | ---: | ---: | ---: |
| Proof-body code lines | 128 | 52 | 76 |
| Whole-snippet code lines | 266 | 210 | 56 |

Counts exclude blank and comment-only lines. Proof bodies are delimited in every file. Whole-snippet counts include imports, statements, and all preparation. The added tactic import is charged once in every standalone snippet.

## Compilation

Median total time per corpus pass: **51.098 s baseline**, **57.040 s tactic**. Their ratio is **0.896×** (baseline/tactic; above one favors the tactic).

Each sample launches `lake env lean -DwarningAsError=true` with fresh `.olean` and `.ilean` outputs. Recorded pairs alternate compilation order. Dependencies are already built and imports are warmed. Times include process startup, imports, tactic execution, checking, and output writing. They exclude the separately recorded dependency-build/setup step. Background machine load is uncontrolled. These descriptive medians do not establish statistical significance.

| Snippet | Kind | Proof lines (old → new) | Net code saved | Baseline median (s) | Tactic median (s) | Ratio |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| [LatticeInf](Tactic/LatticeInf.lean) | exact theorem | 11 → 4 | 6 | 2.355 | 2.676 | 0.880× |
| [LatticeSup](Tactic/LatticeSup.lean) | exact theorem | 11 → 4 | 6 | 2.274 | 2.555 | 0.890× |
| [BoundedRange](Tactic/BoundedRange.lean) | exact theorem | 4 → 1 | 2 | 2.331 | 2.582 | 0.903× |
| [ComplexLogHalf](Tactic/ComplexLogHalf.lean) | exact theorem | 14 → 7 | 6 | 2.753 | 3.283 | 0.839× |
| [ComplexExpLipschitz](Tactic/ComplexExpLipschitz.lean) | exact theorem | 14 → 5 | 8 | 2.477 | 2.709 | 0.915× |
| [IntegrableOfNormSub](Tactic/IntegrableOfNormSub.lean) | exact theorem | 7 → 5 | 1 | 2.733 | 2.844 | 0.961× |
| [LProjectionMul](Tactic/LProjectionMul.lean) | exact theorem | 14 → 11 | 2 | 2.442 | 2.928 | 0.834× |
| [UniformSmallLeft](Tactic/UniformSmallLeft.lean) | extracted block | 2 → 1 | 0 | 2.364 | 2.582 | 0.916× |
| [UniformSmallRight](Tactic/UniformSmallRight.lean) | extracted block | 2 → 1 | 0 | 2.640 | 2.555 | 1.033× |
| [UniformDifference](Tactic/UniformDifference.lean) | extracted block | 3 → 1 | 1 | 2.391 | 2.644 | 0.905× |
| [UniformSum](Tactic/UniformSum.lean) | extracted block | 3 → 1 | 1 | 2.419 | 2.636 | 0.918× |
| [DerivativeLipschitz](Tactic/DerivativeLipschitz.lean) | extracted block | 4 → 1 | 2 | 2.477 | 2.811 | 0.881× |
| [DerivativeThreeStep](Tactic/DerivativeThreeStep.lean) | adapted estimate | 8 → 1 | 6 | 2.479 | 2.664 | 0.930× |
| [BanachApproximation](Tactic/BanachApproximation.lean) | adapted estimate | 7 → 2 | 4 | 2.819 | 3.300 | 0.854× |
| [DualSeparationHalf](Tactic/DualSeparationHalf.lean) | adapted estimate | 3 → 1 | 1 | 2.569 | 2.874 | 0.894× |
| [JacobianBall](Tactic/JacobianBall.lean) | extracted block | 4 → 1 | 2 | 2.487 | 2.728 | 0.912× |
| [LpApproximationSum](Tactic/LpApproximationSum.lean) | extracted block | 5 → 1 | 3 | 2.697 | 3.178 | 0.848× |
| [BoundedLimit](Tactic/BoundedLimit.lean) | extracted block | 4 → 1 | 2 | 2.552 | 2.583 | 0.988× |
| [PolishTriangle](Tactic/PolishTriangle.lean) | extracted block | 6 → 2 | 3 | 2.504 | 3.151 | 0.795× |
| [ComplexLogBasic](Tactic/ComplexLogBasic.lean) | exact theorem | 2 → 1 | 0 | 2.423 | 2.772 | 0.874× |

Raw samples, failures, source hashes, versions, and timing order are retained in [results.json](results.json).
