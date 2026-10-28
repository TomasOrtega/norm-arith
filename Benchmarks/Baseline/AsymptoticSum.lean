/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Yury Kudryashov
-/
/-
Standalone exact theorem from Mathlib/Analysis/Asymptotics/Arith.lean.
Pinned source and adaptations: Benchmarks/manifest.json (AsymptoticSum).
-/
module

import Mathlib.Analysis.Asymptotics.Arith
import Mathlib.Tactic

open Set Filter Asymptotics

variable {α E' F : Type*} [SeminormedAddCommGroup E'] [Norm F]
variable {c₁ c₂ : ℝ} {f₁ f₂ : α → E'} {g : α → F} {l : Filter α}

-- BENCHMARK-STATEMENT
example (h₁ : IsBigOWith c₁ l f₁ g) (h₂ : IsBigOWith c₂ l f₂ g) :
    IsBigOWith (c₁ + c₂) l (fun x => f₁ x + f₂ x) g := by
  -- BENCHMARK-PROOF
  rw [IsBigOWith_def] at *
  filter_upwards [h₁, h₂] with x hx₁ hx₂ using
    calc
      ‖f₁ x + f₂ x‖ ≤ c₁ * ‖g x‖ + c₂ * ‖g x‖ := norm_add_le_of_le hx₁ hx₂
      _ = (c₁ + c₂) * ‖g x‖ := (add_mul _ _ _).symm
  -- BENCHMARK-END
