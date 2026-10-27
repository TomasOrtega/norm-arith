/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
/-
Standalone extracted block from Mathlib/Analysis/Convex/Uniform.lean.
Pinned source and adaptations: Benchmarks/manifest.json (UniformSum).
-/
module

import Mathlib.Analysis.Convex.Uniform
import Mathlib.Tactic

variable {E : Type*} [SeminormedAddCommGroup E]

-- BENCHMARK-STATEMENT
example (x y x' y' : E) : ‖x + y‖ ≤ ‖x' + y'‖ + ‖x' - x‖ + ‖y' - y‖ := by
  -- BENCHMARK-PROOF
  have : ∀ x' y', x + y = x' + y' + (x - x') + (y - y') := fun _ _ => by abel
  rw [norm_sub_rev, norm_sub_rev y', this]
  exact norm_add₃_le
  -- BENCHMARK-END

