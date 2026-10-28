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
  calc
    ‖T s + T' s‖ ≤ ‖T s‖ + ‖T' s‖ := norm_add_le _ _
    _ ≤ C * μ.real s + C' * ν.real s := add_le_add (hT.2 s hs hμs) (hT'.2 s hs hνs)
    _ ≤ max C C' * μ.real s + max C C' * ν.real s := by
      gcongr
      · exact le_max_left C C'
      · exact le_max_right C C'
  -- BENCHMARK-END
