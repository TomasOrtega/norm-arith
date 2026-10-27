/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
/-
Standalone exact theorem from Mathlib/Analysis/Normed/Module/MStructure.lean.
Pinned source and adaptations: Benchmarks/manifest.json (LProjectionMul).
-/
module

import Mathlib.Analysis.Normed.Module.MStructure
import Mathlib.Tactic

variable {X M : Type*} [NormedAddCommGroup X] [Ring M] [Module M X] [FaithfulSMul M X]

-- BENCHMARK-STATEMENT
example {P Q : M} (h₁ : IsLprojection X P) (h₂ : IsLprojection X Q) :
    IsLprojection X (P * Q) := by
  -- BENCHMARK-PROOF
  refine ⟨IsIdempotentElem.mul_of_commute (h₁.commute h₂) h₁.proj h₂.proj, ?_⟩
  intro x
  refine le_antisymm ?_ ?_
  · calc
      ‖x‖ = ‖(P * Q) • x + (x - (P * Q) • x)‖ := by rw [add_sub_cancel ((P * Q) • x) x]
      _ ≤ ‖(P * Q) • x‖ + ‖x - (P * Q) • x‖ := by apply norm_add_le
      _ = ‖(P * Q) • x‖ + ‖(1 - P * Q) • x‖ := by rw [sub_smul, one_smul]
  · calc
      ‖x‖ = ‖P • Q • x‖ + (‖Q • x - P • Q • x‖ + ‖x - Q • x‖) := by
        rw [h₂.Lnorm x, h₁.Lnorm (Q • x), sub_smul, one_smul, sub_smul, one_smul, add_assoc]
      _ ≥ ‖P • Q • x‖ + ‖Q • x - P • Q • x + (x - Q • x)‖ :=
        ((add_le_add_iff_left ‖P • Q • x‖).mpr (norm_add_le (Q • x - P • Q • x) (x - Q • x)))
      _ = ‖(P * Q) • x‖ + ‖(1 - P * Q) • x‖ := by
        rw [sub_add_sub_cancel', sub_smul, one_smul, mul_smul]
  -- BENCHMARK-END

