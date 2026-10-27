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
import NormArith

open Complex

-- BENCHMARK-STATEMENT
example {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) : ‖log (1 + z)‖ ≤ (3 / 2) * ‖z‖ := by
  -- BENCHMARK-PROOF
  have hlog := norm_log_one_add_le (lt_of_le_of_lt hz one_half_lt_one)
  have hinv : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀] <;> linarith
  have hsq : ‖z‖ ^ 2 ≤ ‖z‖ / 2 := by nlinarith [norm_nonneg z]
  have hb : ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 ≤ ‖z‖ / 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hinv) (sq_nonneg ‖z‖)]
  norm_arith [hlog, hb]
  -- BENCHMARK-END

