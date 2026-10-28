/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
/-
Standalone extracted block from Mathlib/Analysis/Normed/Group/ControlledClosure.lean.
Pinned source and adaptations: Benchmarks/manifest.json (ControlledClosureInitial).
-/
module

import Mathlib.Analysis.Normed.Group.ControlledClosure
import Mathlib.Tactic

variable {G H : Type*} [NormedAddCommGroup G] [NormedAddCommGroup H]

-- BENCHMARK-STATEMENT
example (u : ℕ → G) (v : ℕ → H) (h : H) (b : ℕ → ℝ) (C : ℝ)
    (hC : 0 < C) (hv₀ : ‖-v 0 + h‖ < b 0) (hnorm_u : ∀ n, ‖u n‖ ≤ C * ‖v n‖) :
    ‖u 0‖ ≤ C * b 0 + C * ‖h‖ := by
  -- BENCHMARK-PROOF
  have :=
    calc
      ‖v 0‖ ≤ ‖h‖ + ‖v 0 - h‖ := norm_le_insert' _ _
      _ ≤ ‖h‖ + b 0 := by rw [← norm_neg_add]; gcongr
  calc
    ‖u 0‖ ≤ C * ‖v 0‖ := hnorm_u 0
    _ ≤ C * (‖h‖ + b 0) := by gcongr
    _ = C * b 0 + C * ‖h‖ := by rw [add_comm, mul_add]
  -- BENCHMARK-END
