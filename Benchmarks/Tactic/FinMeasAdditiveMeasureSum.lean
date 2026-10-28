/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Sébastien Gouëzel, Rémy Degenne
-/
/-
Standalone exact theorem from Mathlib/MeasureTheory/Integral/FinMeasAdditive.lean.
Pinned source and adaptations: Benchmarks/manifest.json (FinMeasAdditiveMeasureSum).
-/
module

import Mathlib.MeasureTheory.Integral.FinMeasAdditive
import Mathlib.Tactic
import NormArith

open MeasureTheory
open scoped ENNReal
variable {α β : Type*} [MeasurableSpace α] [SeminormedAddCommGroup β]
variable {μ : Measure α} {T T' : Set α → β} {C C' : ℝ}

-- BENCHMARK-STATEMENT
example (μ ν : Measure α)
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive ν T' C') :
    DominatedFinMeasAdditive (μ + ν) (T + T') (max C C') := by
  -- BENCHMARK-PROOF
  refine ⟨hT.1.add_measure hT'.1, fun s hs hsf ↦ ?_⟩
  have hμs : μ s < ∞ := (Measure.le_add_right le_rfl s).trans_lt hsf
  have hνs : ν s < ∞ := (Measure.le_add_left le_rfl s).trans_lt hsf
  rw [Pi.add_apply, measureReal_add_apply hμs.ne hνs.ne, mul_add]
  have hC : C * μ.real s ≤ max C C' * μ.real s :=
    mul_le_mul_of_nonneg_right (le_max_left C C') measureReal_nonneg
  have hC' : C' * ν.real s ≤ max C C' * ν.real s :=
    mul_le_mul_of_nonneg_right (le_max_right C C') measureReal_nonneg
  norm_arith [hT.2 s hs hμs, hT'.2 s hs hνs, hC, hC']
  -- BENCHMARK-END
