/-
Copyright (c) 2024 Jakob Stiefel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Stiefel
-/
/-
Standalone exact theorem from Mathlib/Analysis/SpecialFunctions/MulExpNegMulSq.lean.
Pinned source and adaptations: Benchmarks/manifest.json (GaussianCutoffDistance).
-/
module

import Mathlib.Analysis.SpecialFunctions.MulExpNegMulSq
import Mathlib.Tactic

open Real

variable {ε : ℝ}

-- BENCHMARK-STATEMENT
example (hε : 0 < ε) (x y : ℝ) :
    dist (mulExpNegMulSq ε x) (mulExpNegMulSq ε y) ≤ 2 * (√ε)⁻¹ := by
  -- BENCHMARK-PROOF
  apply le_trans (dist_triangle (mulExpNegMulSq ε x) 0 (mulExpNegMulSq ε y))
  simp only [dist_zero_right, norm_eq_abs, dist_zero_left, two_mul]
  exact add_le_add (abs_mulExpNegMulSq_le hε) (abs_mulExpNegMulSq_le hε)
  -- BENCHMARK-END
