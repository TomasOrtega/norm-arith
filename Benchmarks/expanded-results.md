# Standalone snippet benchmark

Measured at 2026-10-27T21:32:44.333550+00:00. 41 paired snippets, 1 warmup pass(es), 3 recorded pairs.

**Workload:** selected standalone mathlib-derived snippets.

Selected standalone mathlib-derived estimates. Exact theorem copies, extracted local blocks, and adaptations are classified separately. This is not a census or a whole-file benchmark.

Case definitions: [expanded-41.json](expanded-41.json). This is not a census, a whole-file compilation study, or a claim about all PDE proofs.

## Source size

| Metric | Baseline | Tactic | Saved |
| --- | ---: | ---: | ---: |
| Proof-body code lines | 235 | 143 | 92 |
| Whole-snippet code lines | 512 | 461 | 51 |

Counts exclude blank and comment-only lines. Proof bodies are delimited in every file. Whole-snippet counts include imports, statements, and all preparation. Imports and local preparation are counted in each file.

## Compilation

Median total time per corpus pass: **106.918 s baseline**, **119.564 s tactic**. Their ratio is **0.894×** (baseline/tactic; above one favors the tactic).

Each sample launches `lake env lean -DwarningAsError=true` with fresh `.olean` and `.ilean` outputs. Recorded pairs alternate compilation order. Dependencies are already built and imports are warmed. Times include process startup, imports, tactic execution, checking, and output writing. They exclude the separately recorded dependency-build/setup step. Background machine load is uncontrolled. These descriptive medians do not establish statistical significance.

| Snippet | Kind | Proof lines (old → new) | Net code saved | Baseline median (s) | Tactic median (s) | Ratio |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| [LatticeInf](Tactic/LatticeInf.lean) | exact theorem | 11 → 4 | 6 | 2.559 | 2.883 | 0.888× |
| [LatticeSup](Tactic/LatticeSup.lean) | exact theorem | 11 → 4 | 6 | 2.615 | 2.824 | 0.926× |
| [BoundedRange](Tactic/BoundedRange.lean) | exact theorem | 4 → 1 | 2 | 2.548 | 2.860 | 0.891× |
| [ComplexLogHalf](Tactic/ComplexLogHalf.lean) | exact theorem | 14 → 7 | 6 | 2.749 | 3.064 | 0.897× |
| [ComplexExpLipschitz](Tactic/ComplexExpLipschitz.lean) | exact theorem | 14 → 5 | 8 | 2.696 | 2.894 | 0.932× |
| [IntegrableOfNormSub](Tactic/IntegrableOfNormSub.lean) | exact theorem | 7 → 5 | 1 | 2.562 | 2.901 | 0.883× |
| [LProjectionMul](Tactic/LProjectionMul.lean) | exact theorem | 14 → 11 | 2 | 2.572 | 2.952 | 0.871× |
| [UniformSmallLeft](Tactic/UniformSmallLeft.lean) | extracted block | 2 → 1 | 0 | 2.540 | 2.791 | 0.910× |
| [UniformSmallRight](Tactic/UniformSmallRight.lean) | extracted block | 2 → 1 | 0 | 2.677 | 2.920 | 0.917× |
| [UniformDifference](Tactic/UniformDifference.lean) | extracted block | 3 → 1 | 1 | 2.524 | 2.845 | 0.887× |
| [UniformSum](Tactic/UniformSum.lean) | extracted block | 3 → 1 | 1 | 2.513 | 2.785 | 0.902× |
| [DerivativeLipschitz](Tactic/DerivativeLipschitz.lean) | extracted block | 4 → 1 | 2 | 2.505 | 2.806 | 0.893× |
| [DerivativeThreeStep](Tactic/DerivativeThreeStep.lean) | adapted estimate | 8 → 1 | 6 | 2.681 | 2.846 | 0.942× |
| [BanachApproximation](Tactic/BanachApproximation.lean) | adapted estimate | 7 → 2 | 4 | 2.651 | 2.894 | 0.916× |
| [DualSeparationHalf](Tactic/DualSeparationHalf.lean) | adapted estimate | 3 → 1 | 1 | 2.755 | 3.055 | 0.902× |
| [JacobianBall](Tactic/JacobianBall.lean) | extracted block | 4 → 1 | 2 | 2.753 | 2.836 | 0.971× |
| [LpApproximationSum](Tactic/LpApproximationSum.lean) | extracted block | 5 → 1 | 3 | 2.642 | 3.037 | 0.870× |
| [BoundedLimit](Tactic/BoundedLimit.lean) | extracted block | 4 → 1 | 2 | 2.593 | 2.958 | 0.877× |
| [PolishTriangle](Tactic/PolishTriangle.lean) | extracted block | 6 → 2 | 3 | 2.538 | 3.164 | 0.802× |
| [ComplexLogBasic](Tactic/ComplexLogBasic.lean) | exact theorem | 2 → 1 | 0 | 2.640 | 2.834 | 0.932× |
| [RingSubMul](Tactic/RingSubMul.lean) | exact theorem | 6 → 4 | 1 | 2.530 | 2.834 | 0.893× |
| [TorsorVSub](Tactic/TorsorVSub.lean) | exact theorem | 2 → 2 | -1 | 2.498 | 2.739 | 0.912× |
| [TorsorVAdd](Tactic/TorsorVAdd.lean) | exact theorem | 1 → 2 | -2 | 2.512 | 2.784 | 0.902× |
| [BoundedLinearAdd](Tactic/BoundedLinearAdd.lean) | exact theorem | 6 → 5 | 0 | 2.577 | 2.787 | 0.925× |
| [ConvexOnNorm](Tactic/ConvexOnNorm.lean) | exact theorem | 5 → 6 | -2 | 2.561 | 2.833 | 0.904× |
| [NormedHomAdd](Tactic/NormedHomAdd.lean) | extracted block | 4 → 1 | 2 | 2.646 | 2.947 | 0.898× |
| [RingCommutator](Tactic/RingCommutator.lean) | exact theorem | 10 → 9 | 0 | 2.725 | 2.933 | 0.929× |
| [CircleMapBound](Tactic/CircleMapBound.lean) | exact theorem | 2 → 2 | -1 | 2.604 | 2.983 | 0.873× |
| [CircleMapSeparation](Tactic/CircleMapSeparation.lean) | exact theorem | 11 → 11 | -1 | 2.721 | 3.076 | 0.885× |
| [GaussianCutoffDistance](Tactic/GaussianCutoffDistance.lean) | exact theorem | 3 → 4 | -2 | 2.559 | 2.919 | 0.877× |
| [NormOneAddMultipliable](Tactic/NormOneAddMultipliable.lean) | exact theorem | 3 → 4 | -2 | 2.629 | 2.957 | 0.889× |
| [LogNormSummable](Tactic/LogNormSummable.lean) | exact theorem | 7 → 5 | 1 | 2.682 | 2.989 | 0.897× |
| [ComplexLogInverseBound](Tactic/ComplexLogInverseBound.lean) | exact theorem | 12 → 7 | 4 | 2.736 | 2.995 | 0.914× |
| [MetricTriangleFour](Tactic/MetricTriangleFour.lean) | exact theorem | 3 → 1 | 1 | 2.532 | 2.814 | 0.900× |
| [MetricTriangleEight](Tactic/MetricTriangleEight.lean) | exact theorem | 5 → 1 | 3 | 2.524 | 3.365 | 0.750× |
| [MetricAbsDifference](Tactic/MetricAbsDifference.lean) | exact theorem | 2 → 2 | -1 | 2.519 | 2.789 | 0.903× |
| [MetricClosedBallDisjoint](Tactic/MetricClosedBallDisjoint.lean) | exact theorem | 2 → 5 | -4 | 2.557 | 2.788 | 0.917× |
| [MetricBallExpansion](Tactic/MetricBallExpansion.lean) | exact theorem | 5 → 4 | 0 | 2.517 | 2.716 | 0.927× |
| [MetricIntersectingBalls](Tactic/MetricIntersectingBalls.lean) | exact theorem | 4 → 4 | -1 | 2.547 | 2.811 | 0.906× |
| [FinMeasAdditiveSum](Tactic/FinMeasAdditiveSum.lean) | exact theorem | 3 → 3 | -1 | 2.658 | 2.888 | 0.920× |
| [FinMeasAdditiveMeasureSum](Tactic/FinMeasAdditiveMeasureSum.lean) | exact theorem | 11 → 9 | 1 | 2.646 | 2.957 | 0.895× |

Raw samples, failures, source hashes, versions, and timing order are retained in [expanded-results.json](expanded-results.json).
