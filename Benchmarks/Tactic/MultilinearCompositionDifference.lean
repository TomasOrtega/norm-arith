/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
/-
Standalone exact theorem from Mathlib/Analysis/Calculus/ContDiff/FaaDiBruno.lean.
Pinned source and adaptations: Benchmarks/manifest.json (MultilinearCompositionDifference).
-/
module

import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
import Mathlib.Tactic
import NormArith

open Set Fin Filter Function OrderedFinpartition

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {n : ℕ} (c : OrderedFinpartition n)

-- BENCHMARK-STATEMENT
example
    (f₁ f₂ : F [×c.length]→L[𝕜] G) (g₁ g₂ : ∀ i, E [×c.partSize i]→L[𝕜] F) :
    ‖c.compAlongOrderedFinpartition f₁ g₁ - c.compAlongOrderedFinpartition f₂ g₂‖ ≤
      ‖f₁‖ * c.length * max ‖g₁‖ ‖g₂‖ ^ (c.length - 1) * ‖g₁ - g₂‖ + ‖f₁ - f₂‖ * ∏ i, ‖g₂ i‖ := by
  -- BENCHMARK-PROOF
  calc
    _ ≤ ‖c.compAlongOrderedFinpartition f₁ g₁ - c.compAlongOrderedFinpartition f₁ g₂‖ +
        ‖c.compAlongOrderedFinpartition f₁ g₂ - c.compAlongOrderedFinpartition f₂ g₂‖ :=
      by norm_arith
    _ ≤ ‖f₁‖ * c.length * (max ‖g₁‖ ‖g₂‖) ^ (c.length - 1) * ‖g₁ - g₂‖ + ‖f₁ - f₂‖ * ∏ i, ‖g₂ i‖ := by
      gcongr ?_ + ?_
      · refine ((c.compAlongOrderedFinpartitionL 𝕜 E F G f₁).norm_image_sub_le g₁ g₂).trans ?_
        simp only [Fintype.card_fin]
        gcongr
        apply norm_compAlongOrderedFinpartitionL_apply_le
      · exact c.norm_compAlongOrderedFinpartition_le (f₁ - f₂) g₂
  -- BENCHMARK-END
