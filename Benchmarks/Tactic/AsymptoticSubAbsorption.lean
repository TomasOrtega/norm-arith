/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Yury Kudryashov
-/
/-
Standalone exact theorem from Mathlib/Analysis/Asymptotics/Lemmas.lean.
Pinned source and adaptations: Benchmarks/manifest.json (AsymptoticSubAbsorption).
-/
module

import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic
import NormArith

open Set Filter Asymptotics

variable {α E' : Type*} [SeminormedAddCommGroup E'] {c : ℝ} {l : Filter α}

-- BENCHMARK-STATEMENT
example {f₁ f₂ : α → E'} (h : IsBigOWith c l f₁ f₂) (hc : c < 1) :
    IsBigOWith (1 / (1 - c)) l f₂ fun x => f₂ x - f₁ x := by
  -- BENCHMARK-PROOF
  exact IsBigOWith.of_bound <|
    mem_of_superset h.bound fun x hx => by
      simp only [mem_ofPred_eq] at hx ⊢
      rw [mul_comm, one_div, ← div_eq_mul_inv, le_div_iff₀, mul_sub, mul_one, mul_comm]
      · exact (sub_le_sub_left hx _).trans (by norm_arith)
      · exact sub_pos.2 hc
  -- BENCHMARK-END
