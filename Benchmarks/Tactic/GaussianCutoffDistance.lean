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
import NormArith

open Real

variable {ε : ℝ}

-- BENCHMARK-STATEMENT
example (hε : 0 < ε) (x y : ℝ) :
    dist (mulExpNegMulSq ε x) (mulExpNegMulSq ε y) ≤ 2 * (√ε)⁻¹ := by
  -- BENCHMARK-PROOF
  have hx := abs_mulExpNegMulSq_le hε (x := x)
  have hy := abs_mulExpNegMulSq_le hε (x := y)
  rw [← Real.norm_eq_abs] at hx hy
  norm_arith [hx, hy]
  -- BENCHMARK-END
