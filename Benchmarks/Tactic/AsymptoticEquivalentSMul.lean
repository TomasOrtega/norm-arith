/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
/-
Standalone exact theorem from Mathlib/Analysis/Asymptotics/AsymptoticEquivalent.lean.
Pinned source and adaptations: Benchmarks/manifest.json (AsymptoticEquivalentSMul).
-/
module

import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Tactic
import NormArith

open Filter Function Asymptotics
open scoped Topology

-- BENCHMARK-STATEMENT
example {α E 𝕜 : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {a b : α → 𝕜} {u v : α → E} {l : Filter α} (hab : a ~[l] b) (huv : u ~[l] v) :
    (fun x ↦ a x • u x) ~[l] fun x ↦ b x • v x := by
  -- BENCHMARK-PROOF
  rcases hab.exists_eq_mul with ⟨φ, hφ, habφ⟩
  have : ((fun x ↦ a x • u x) - (fun x ↦ b x • v x)) =ᶠ[l] fun x ↦ b x • (φ x • u x - v x) := by
    convert
      (habφ.comp₂ (· • ·) <| EventuallyEq.refl _ u).fun_sub
        (EventuallyEq.refl _ fun x ↦ b x • v x) using 1
    ext
    rw [Pi.mul_apply, mul_comm, mul_smul, ← smul_sub]
  refine (isLittleO_congr this.symm EventuallyEq.rfl).mp ((isBigO_refl b l).smul_isLittleO ?_)
  rcases huv.isBigO.exists_pos with ⟨C, hC, hCuv⟩
  rw [IsEquivalent] at *
  rw [isLittleO_iff] at *
  rw [IsBigOWith] at hCuv
  simp only [Metric.tendsto_nhds, dist_eq_norm] at hφ
  intro c hc
  specialize hφ (c / 2 / C) (div_pos (div_pos hc zero_lt_two) hC)
  specialize huv (div_pos hc zero_lt_two)
  refine hφ.mp (huv.mp <| hCuv.mono fun x hCuvx huvx hφx ↦ ?_)
  have key :=
    calc
      ‖φ x - 1‖ * ‖u x‖ ≤ c / 2 / C * ‖u x‖ := by gcongr
      _ ≤ c / 2 / C * (C * ‖v x‖) := by gcongr
      _ = c / 2 * ‖v x‖ := by field
  have hscaled : ‖(φ x - 1) • u x‖ ≤ c / 2 * ‖v x‖ := by
    simpa only [norm_smul] using key
  calc
    ‖((fun x : α ↦ φ x • u x) - v) x‖ = ‖(φ x - 1) • u x + (u x - v x)‖ := by
      simp [sub_smul, sub_add]
    _ ≤ c * ‖v x‖ := by norm_arith [hscaled, huvx]
  -- BENCHMARK-END
