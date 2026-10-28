/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
/-
Standalone extracted block from Mathlib/Analysis/Normed/Ring/Lemmas.lean.
Pinned source and adaptations: Benchmarks/manifest.json (RingMultiplicationDifference).
-/
module

import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Tactic

variable {α : Type*} [NonUnitalSeminormedRing α]

-- BENCHMARK-STATEMENT
example (x e : α × α) :
    ‖e.1 * e.2 - x.1 * x.2‖ ≤ ‖e.1‖ * ‖e.2 - x.2‖ + ‖e.1 - x.1‖ * ‖x.2‖ := by
  -- BENCHMARK-PROOF
  calc
    ‖e.1 * e.2 - x.1 * x.2‖ ≤ ‖e.1 * (e.2 - x.2) + (e.1 - x.1) * x.2‖ := by
      rw [mul_sub, sub_mul, sub_add_sub_cancel]
    _ ≤ ‖e.1‖ * ‖e.2 - x.2‖ + ‖e.1 - x.1‖ * ‖x.2‖ :=
      norm_add_le_of_le (norm_mul_le _ _) (norm_mul_le _ _)
  -- BENCHMARK-END
