/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
-/
/-
Standalone exact theorem from Mathlib/Analysis/SpecialFunctions/Exp.lean.
Pinned source and adaptations: Benchmarks/manifest.json (ComplexExpLipschitz).
-/
module

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
import NormArith

open Complex

-- BENCHMARK-STATEMENT
example {r : ℝ} (hr_nonneg : 0 ≤ r) (hr_le : r ≤ 1) (x y : ℂ)
    (hyx : ‖y - x‖ < r) : ‖exp y - exp x‖ ≤ (1 + r) * ‖exp x‖ * ‖y - x‖ := by
  -- BENCHMARK-PROOF
  have hbound := exp_bound_sq x (y - x) (hyx.le.trans hr_le)
  have hsq := mul_le_mul hyx.le (le_refl ‖y - x‖) (norm_nonneg _) hr_nonneg
  have hpow := mul_le_mul_of_nonneg_left hsq (norm_nonneg (exp x))
  rw [show x + (y - x) = y by abel] at hbound
  norm_arith [hbound, (norm_smul (y - x) (exp x)).le, hpow]
  -- BENCHMARK-END

