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
import NormArith

variable {α : Type*} [NonUnitalSeminormedRing α]

-- BENCHMARK-STATEMENT
example (x e : α × α) :
    ‖e.1 * e.2 - x.1 * x.2‖ ≤ ‖e.1‖ * ‖e.2 - x.2‖ + ‖e.1 - x.1‖ * ‖x.2‖ := by
  -- BENCHMARK-PROOF
  have h₁ := norm_mul_le e.1 (e.2 - x.2)
  have h₂ := norm_mul_le (e.1 - x.1) x.2
  rw [mul_sub] at h₁
  rw [sub_mul] at h₂
  norm_arith [h₁, h₂]
  -- BENCHMARK-END
