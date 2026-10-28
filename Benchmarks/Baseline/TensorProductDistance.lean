/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
/-
Standalone exact theorem from Mathlib/Analysis/InnerProductSpace/TensorProduct.lean.
Pinned source and adaptations: Benchmarks/manifest.json (TensorProductDistance).
-/
module

import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Tactic

open scoped TensorProduct
open TensorProduct

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

-- BENCHMARK-STATEMENT
example (x x' : E) (y y' : F) :
    dist (x ⊗ₜ[𝕜] y) (x' ⊗ₜ y') ≤ ‖x‖ * ‖y‖ + ‖x'‖ * ‖y'‖ := by
  -- BENCHMARK-PROOF
  grw [dist_eq_norm, norm_sub_le]; simp
  -- BENCHMARK-END
