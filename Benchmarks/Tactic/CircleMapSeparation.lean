/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Fabrizio Barroero, Christopher Hoskin
-/
/-
Standalone exact theorem from Mathlib/Analysis/SpecialFunctions/Complex/CircleMap.lean.
Pinned source and adaptations: Benchmarks/manifest.json (CircleMapSeparation).
-/
module

import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Tactic
import NormArith

open Complex Function Metric Real

-- BENCHMARK-STATEMENT
example {R : ℝ} {c w : ℂ} (hw : w ∉ sphere c |R|) :
    ∃ d > 0, ∀ x ∈ ball w d, ∀ θ : ℝ, d ≤ ‖circleMap c R θ - x‖ := by
  -- BENCHMARK-PROOF
  have hd₀ : 0 < abs (dist w c - |R|) :=
    abs_pos.2 (sub_ne_zero.2 fun h ↦ hw (mem_sphere.2 h))
  refine ⟨abs (dist w c - |R|) / 2, by positivity, fun x hx θ ↦ ?_⟩
  rw [mem_ball] at hx
  have h₁ : dist (circleMap c R θ) c = |R| := mem_sphere.1 (circleMap_mem_sphere' c R θ)
  have h₂ : abs (dist w c - |R|) ≤ dist (circleMap c R θ) w := by
    calc abs (dist w c - |R|) = |dist (circleMap c R θ) c - dist w c| := by rw [h₁, abs_sub_comm]
      _ ≤ dist (circleMap c R θ) w := abs_dist_sub_le _ _ _
  rw [← dist_eq_norm]
  generalize abs (dist w c - |R|) = d at hx h₂ ⊢
  norm_arith [h₂, hx]
  -- BENCHMARK-END
