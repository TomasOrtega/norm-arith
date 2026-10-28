/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
/-
Standalone extracted block from Mathlib/Analysis/Normed/Group/Hom.lean.
Pinned source and adaptations: Benchmarks/manifest.json (NormedHomAdd).
-/
module

import Mathlib.Analysis.Normed.Group.Hom
import Mathlib.Tactic

variable {V₁ V₂ : Type*} [SeminormedAddCommGroup V₁] [SeminormedAddCommGroup V₂]

open NormedAddGroupHom

-- BENCHMARK-STATEMENT
example (f g : NormedAddGroupHom V₁ V₂) (v : V₁) :
    ‖f v + g v‖ ≤ (‖f‖ + ‖g‖) * ‖v‖ := by
  -- BENCHMARK-PROOF
  calc
    ‖f v + g v‖ ≤ ‖f v‖ + ‖g v‖ := norm_add_le _ _
    _ ≤ ‖f‖ * ‖v‖ + ‖g‖ * ‖v‖ := by gcongr <;> apply le_opNorm
    _ = (‖f‖ + ‖g‖) * ‖v‖ := by rw [add_mul]
  -- BENCHMARK-END
