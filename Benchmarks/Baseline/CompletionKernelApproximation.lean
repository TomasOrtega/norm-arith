/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
/-
Standalone extracted block from Mathlib/Analysis/Normed/Group/HomCompletion.lean.
Pinned source and adaptations: Benchmarks/manifest.json (CompletionKernelApproximation).
-/
module

import Mathlib.Analysis.Normed.Group.HomCompletion
import Mathlib.Tactic

open UniformSpace

variable {G H : Type*} [SeminormedAddCommGroup G] [SeminormedAddCommGroup H]

-- BENCHMARK-STATEMENT
example (f : NormedAddGroupHom G H) (hatg : Completion G) (g g' : G) (C' δ ε : ℝ)
    (C'_pos : 0 < C') (hg : ‖hatg - g‖ < δ) (hfg : ‖g'‖ ≤ C' * ‖f g‖)
    (hbound : ‖f g‖ ≤ ‖f‖ * δ) (hδ : (1 + C' * ‖f‖) * δ < ε) :
    ‖hatg - ↑(g - g')‖ < ε := by
  -- BENCHMARK-PROOF
  calc ‖hatg - ↑(g - g')‖ = ‖hatg - g + g'‖ := by rw [Completion.coe_sub, sub_add]
    _ ≤ ‖hatg - g‖ + ‖(g' : Completion G)‖ := norm_add_le _ _
    _ = ‖hatg - g‖ + ‖g'‖ := by rw [Completion.norm_coe]
    _ < δ + C' * ‖f g‖ := add_lt_add_of_lt_of_le hg hfg
    _ ≤ δ + C' * (‖f‖ * δ) := by gcongr
    _ < ε := by simpa only [add_mul, one_mul, mul_assoc] using hδ
  -- BENCHMARK-END
