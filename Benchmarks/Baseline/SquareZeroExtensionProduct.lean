/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
/-
Standalone extracted block from Mathlib/Analysis/Normed/Algebra/TrivSqZeroExt.lean.
Pinned source and adaptations: Benchmarks/manifest.json (SquareZeroExtensionProduct).
-/
module

import Mathlib.Analysis.Normed.Algebra.TrivSqZeroExt
import Mathlib.Tactic

variable {R M : Type*} [SeminormedRing R] [SeminormedAddCommGroup M]
  [Module R M] [IsBoundedSMul R M] [Module Rᵐᵒᵖ M] [IsBoundedSMul Rᵐᵒᵖ M]
  [SMulCommClass R Rᵐᵒᵖ M]

-- BENCHMARK-STATEMENT
example (r₁ r₂ : R) (m₁ m₂ : M) :
    ‖r₁ * r₂‖ + ‖r₁ • m₂ + MulOpposite.op r₂ • m₁‖ ≤
      (‖r₁‖ + ‖m₁‖) * (‖r₂‖ + ‖m₂‖) := by
  -- BENCHMARK-PROOF
  calc ‖r₁ * r₂‖ + ‖r₁ • m₂ + MulOpposite.op r₂ • m₁‖
  _ ≤ ‖r₁‖ * ‖r₂‖ + (‖r₁‖ * ‖m₂‖ + ‖r₂‖ * ‖m₁‖) := by
    gcongr
    · apply norm_mul_le
    · refine norm_add_le_of_le ?_ ?_ <;>
      apply norm_smul_le
  _ ≤ ‖r₁‖ * ‖r₂‖ + (‖r₁‖ * ‖m₂‖ + ‖r₂‖ * ‖m₁‖) + (‖m₁‖ * ‖m₂‖) := by
    apply le_add_of_nonneg_right
    positivity
  _ = (‖r₁‖ + ‖m₁‖) * (‖r₂‖ + ‖m₂‖) := by ring
  -- BENCHMARK-END
