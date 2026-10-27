/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
/-
Standalone adapted estimate from Mathlib/Analysis/Normed/Operator/Banach.lean.
Pinned source and adaptations: Benchmarks/manifest.json (BanachApproximation).
-/
module

import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

-- BENCHMARK-STATEMENT
example (f : E →L[ℝ] F) (x₁ x₂ : E) (a y : F) (d δ : ℝ)
    (h₁ : dist (a + d • y) (f x₁) < δ) (h₂ : dist a (f x₂) < δ) :
    ‖f (x₁ - x₂) - d • y‖ ≤ 2 * δ := by
  -- BENCHMARK-PROOF
  calc
    ‖f (x₁ - x₂) - d • y‖ = ‖f x₁ - (a + d • y) - (f x₂ - a)‖ := by
      congr 1
      simp only [f.map_sub]
      abel
    _ ≤ ‖f x₁ - (a + d • y)‖ + ‖f x₂ - a‖ := norm_sub_le _ _
    _ ≤ 2 * δ := by grind [dist_eq_norm']
  -- BENCHMARK-END

