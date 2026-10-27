/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
/-
Standalone exact theorem from Mathlib/Analysis/SpecialFunctions/Complex/LogBounds.lean.
Pinned source and adaptations: Benchmarks/manifest.json (ComplexLogBasic).
-/
module

import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Tactic

open Complex

-- BENCHMARK-STATEMENT
example {z : ℂ} (hz : ‖z‖ < 1) :
    ‖log (1 + z)‖ ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 + ‖z‖ := by
  -- BENCHMARK-PROOF
  rw [← sub_add_cancel (log (1 + z)) z]
  exact norm_add_le_of_le (Complex.norm_log_one_add_sub_self_le hz) le_rfl
  -- BENCHMARK-END

