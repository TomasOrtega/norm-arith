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
import NormArith

open UniformSpace

variable {G H : Type*} [SeminormedAddCommGroup G] [SeminormedAddCommGroup H]

-- BENCHMARK-STATEMENT
example (f : NormedAddGroupHom G H) (hatg : Completion G) (g g' : G) (C' δ ε : ℝ)
    (C'_pos : 0 < C') (hg : ‖hatg - g‖ < δ) (hfg : ‖g'‖ ≤ C' * ‖f g‖)
    (hbound : ‖f g‖ ≤ ‖f‖ * δ) (hδ : (1 + C' * ‖f‖) * δ < ε) :
    ‖hatg - ↑(g - g')‖ < ε := by
  -- BENCHMARK-PROOF
  have hscaled := mul_le_mul_of_nonneg_left hbound C'_pos.le
  have hsmall : δ + C' * (‖f‖ * δ) < ε := by
    simpa only [add_mul, one_mul, mul_assoc] using hδ
  have hg' : ‖(g' : Completion G)‖ ≤ C' * (‖f‖ * δ) := by
    rw [Completion.norm_coe]
    exact hfg.trans hscaled
  rw [Completion.coe_sub]
  generalize C' * (‖f‖ * δ) = B at hg' hsmall
  norm_arith [hg, hg', hsmall]
  -- BENCHMARK-END
