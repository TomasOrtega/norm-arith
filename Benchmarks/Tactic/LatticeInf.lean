/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
/-
Standalone exact theorem from Mathlib/Analysis/Normed/Order/Lattice.lean.
Pinned source and adaptations: Benchmarks/manifest.json (LatticeInf).
-/
module

import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Tactic
import NormArith

open HasSolidNorm
variable {α : Type*} [NormedAddCommGroup α] [Lattice α]
  [HasSolidNorm α] [IsOrderedAddMonoid α]

-- BENCHMARK-STATEMENT
example (a b c d : α) : ‖a ⊓ b - c ⊓ d‖ ≤ ‖a - c‖ + ‖b - d‖ := by
  -- BENCHMARK-PROOF
  have h1 : ‖a ⊓ b - c ⊓ b‖ ≤ ‖a - c‖ := solid (abs_inf_sub_inf_le_abs _ _ _)
  have h2 : ‖c ⊓ b - c ⊓ d‖ ≤ ‖b - d‖ := by
    simpa only [inf_comm c] using solid (abs_inf_sub_inf_le_abs b d c)
  norm_arith [h1, h2]
  -- BENCHMARK-END

