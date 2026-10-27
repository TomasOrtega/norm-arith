/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
/-
Standalone exact theorem from Mathlib/MeasureTheory/Function/L1Space/Integrable.lean.
Pinned source and adaptations: Benchmarks/manifest.json (IntegrableOfNormSub).
-/
module

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic

open MeasureTheory
variable {α β : Type*} [MeasurableSpace α] [NormedAddCommGroup β] {μ : Measure α}

-- BENCHMARK-STATEMENT
example {f₀ f₁ : α → β} {g : α → ℝ} (hf₁_m : AEStronglyMeasurable f₁ μ)
    (hf₀_i : Integrable f₀ μ) (hg_i : Integrable g μ)
    (h : ∀ᵐ a ∂μ, ‖f₀ a - f₁ a‖ ≤ g a) : Integrable f₁ μ := by
  -- BENCHMARK-PROOF
  have : ∀ᵐ a ∂μ, ‖f₁ a‖ ≤ ‖f₀ a‖ + g a := by
    apply h.mono
    intro a ha
    calc
      ‖f₁ a‖ ≤ ‖f₀ a‖ + ‖f₀ a - f₁ a‖ := norm_le_insert _ _
      _ ≤ ‖f₀ a‖ + g a := by gcongr
  exact Integrable.mono' (hf₀_i.norm.add hg_i) hf₁_m this
  -- BENCHMARK-END

