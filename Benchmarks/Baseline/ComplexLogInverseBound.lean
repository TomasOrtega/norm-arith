/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
/-
Standalone exact theorem from Mathlib/Analysis/SpecialFunctions/Complex/LogBounds.lean.
Pinned source and adaptations: Benchmarks/manifest.json (ComplexLogInverseBound).
-/
module

import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Tactic

open Complex

-- BENCHMARK-STATEMENT
example {t : ℝ} (ht : t ∈ Set.Icc 0 1) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖(1 + t * z)⁻¹‖ ≤ (1 - ‖z‖)⁻¹ := by
  -- BENCHMARK-PROOF
  rw [Set.mem_Icc] at ht
  rw [norm_inv]
  refine inv_anti₀ (by linarith) ?_
  calc 1 - ‖z‖
    _ ≤ 1 - t * ‖z‖ := by
      nlinarith [norm_nonneg z]
    _ = 1 - ‖t * z‖ := by
      rw [norm_mul, Complex.norm_of_nonneg ht.1]
    _ ≤ ‖1 + t * z‖ := by
      rw [← norm_neg (t * z), ← sub_neg_eq_add]
      convert norm_sub_norm_le 1 (-(t * z))
      exact norm_one.symm
  -- BENCHMARK-END
