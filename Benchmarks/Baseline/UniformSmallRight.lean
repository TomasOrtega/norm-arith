/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
/-
Standalone extracted block from Mathlib/Analysis/Convex/Uniform.lean.
Pinned source and adaptations: Benchmarks/manifest.json (UniformSmallRight).
-/
module

import Mathlib.Analysis.Convex.Uniform
import Mathlib.Tactic

variable {E : Type*} [SeminormedAddCommGroup E]

-- BENCHMARK-STATEMENT
example (x y : E) (δ' : ℝ) (hx : ‖x‖ ≤ 1) (hy' : ‖y‖ ≤ 1 - δ') :
    ‖x + y‖ ≤ 2 - δ' := by
  -- BENCHMARK-PROOF
  rw [← one_add_one_eq_two]
  exact (norm_add_le_of_le hx hy').trans (add_sub_assoc _ _ _).ge
  -- BENCHMARK-END

