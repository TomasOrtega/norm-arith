/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudryashov
-/
/-
Standalone exact theorem from Mathlib/Analysis/Normed/Module/Convex.lean.
Pinned source and adaptations: Benchmarks/manifest.json (ConvexOnNorm).
-/
module

import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic

open Set

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}

-- BENCHMARK-STATEMENT
example (hs : Convex ℝ s) : ConvexOn ℝ s norm := by
  -- BENCHMARK-PROOF
  exact ⟨hs, fun x _ y _ a b ha hb _ =>
    calc
      ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      _ = a * ‖x‖ + b * ‖y‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]⟩
  -- BENCHMARK-END
