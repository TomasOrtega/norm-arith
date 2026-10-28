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
import NormArith

open MeasureTheory
variable {E : Type*} [MeasurableSpace E] [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {μ : Measure E} {t : E}

-- BENCHMARK-STATEMENT
example [IsProbabilityMeasure μ] : ‖1 - charFun μ t‖ ≤ 2 := by
  -- BENCHMARK-PROOF
  norm_arith [norm_charFun_le_one (μ := μ) t, norm_one (α := ℂ)]
  -- BENCHMARK-END
