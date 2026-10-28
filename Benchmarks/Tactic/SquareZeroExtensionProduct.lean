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
import NormArith

variable {R M : Type*} [SeminormedRing R] [SeminormedAddCommGroup M]
  [Module R M] [IsBoundedSMul R M] [Module Rᵐᵒᵖ M] [IsBoundedSMul Rᵐᵒᵖ M]
  [SMulCommClass R Rᵐᵒᵖ M]

-- BENCHMARK-STATEMENT
example (r₁ r₂ : R) (m₁ m₂ : M) :
    ‖r₁ * r₂‖ + ‖r₁ • m₂ + MulOpposite.op r₂ • m₁‖ ≤
      (‖r₁‖ + ‖m₁‖) * (‖r₂‖ + ‖m₂‖) := by
  -- BENCHMARK-PROOF
  have h₁ := norm_smul_le r₁ m₂
  have h₂ : ‖MulOpposite.op r₂ • m₁‖ ≤ ‖r₂‖ * ‖m₁‖ := norm_smul_le _ _
  have hsum : ‖r₁ • m₂ + MulOpposite.op r₂ • m₁‖ ≤
      ‖r₁‖ * ‖m₂‖ + ‖r₂‖ * ‖m₁‖ := by norm_arith [h₁, h₂]
  nlinarith [norm_mul_le r₁ r₂, mul_nonneg (norm_nonneg m₁) (norm_nonneg m₂)]
  -- BENCHMARK-END
