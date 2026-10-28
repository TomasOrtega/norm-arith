/-
Copyright (c) 2024 Jakob Stiefel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Stiefel, Rémy Degenne, Thomas Zhu
-/
/-
Standalone exact theorem from Mathlib/MeasureTheory/Measure/CharacteristicFunction/Basic.lean.
Pinned source and adaptations: Benchmarks/manifest.json (ProbabilityCharFunBound).
-/
module

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Tactic

open MeasureTheory
variable {E : Type*} [MeasurableSpace E] [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {μ : Measure E} {t : E}

-- BENCHMARK-STATEMENT
example [IsProbabilityMeasure μ] : ‖1 - charFun μ t‖ ≤ 2 := by
  -- BENCHMARK-PROOF
  calc ‖1 - charFun μ t‖
  _ ≤ ‖(1 : ℂ)‖ + ‖charFun μ t‖ := norm_sub_le _ _
  _ ≤ 1 + 1 := by simp [norm_charFun_le_one]
  _ = 2 := by norm_num
  -- BENCHMARK-END
