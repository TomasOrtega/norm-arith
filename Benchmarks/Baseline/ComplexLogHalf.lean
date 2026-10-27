/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
/-
Standalone exact theorem from Mathlib/Analysis/SpecialFunctions/Complex/LogBounds.lean.
Pinned source and adaptations: Benchmarks/manifest.json (ComplexLogHalf).
-/
module

import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Tactic

open Complex

-- BENCHMARK-STATEMENT
example {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) : ‖log (1 + z)‖ ≤ (3 / 2) * ‖z‖ := by
  -- BENCHMARK-PROOF
  apply le_trans (norm_log_one_add_le (lt_of_le_of_lt hz one_half_lt_one))
  have hz3 : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀]
    · linarith
    · linarith
  have hz4 : ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 ≤ ‖z‖ / 2 * 2 / 2 := by
    gcongr
    · rw [inv_nonneg]
      linarith
    · rw [sq, div_eq_mul_one_div]
      gcongr
  simp only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    IsUnit.div_mul_cancel] at hz4
  linarith
  -- BENCHMARK-END

