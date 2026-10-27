/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
/-
Standalone exact theorem from Mathlib/Analysis/Normed/Order/Lattice.lean.
Pinned source and adaptations: Benchmarks/manifest.json (LatticeSup).
-/
module

import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Tactic

open HasSolidNorm
variable {α : Type*} [NormedAddCommGroup α] [Lattice α]
  [HasSolidNorm α] [IsOrderedAddMonoid α]

-- BENCHMARK-STATEMENT
example (a b c d : α) : ‖a ⊔ b - c ⊔ d‖ ≤ ‖a - c‖ + ‖b - d‖ := by
  -- BENCHMARK-PROOF
  rw [← norm_abs_eq_norm (a - c), ← norm_abs_eq_norm (b - d)]
  refine le_trans (solid ?_) (norm_add_le |a - c| |b - d|)
  rw [abs_of_nonneg (add_nonneg (abs_nonneg (a - c)) (abs_nonneg (b - d)))]
  calc
    |a ⊔ b - c ⊔ d| = |a ⊔ b - c ⊔ b + (c ⊔ b - c ⊔ d)| := by rw [sub_add_sub_cancel]
    _ ≤ |a ⊔ b - c ⊔ b| + |c ⊔ b - c ⊔ d| := abs_add_le _ _
    _ ≤ |a - c| + |b - d| := by
      gcongr ?_ + ?_
      · exact abs_sup_sub_sup_le_abs _ _ _
      · rw [sup_comm c, sup_comm c]
        exact abs_sup_sub_sup_le_abs _ _ _
  -- BENCHMARK-END

