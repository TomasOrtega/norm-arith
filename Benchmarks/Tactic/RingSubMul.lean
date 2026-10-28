/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
/-
Standalone exact theorem from Mathlib/Analysis/Normed/Ring/Basic.lean.
Pinned source and adaptations: Benchmarks/manifest.json (RingSubMul).
-/
module

import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic
import NormArith

variable {α : Type*} [SeminormedRing α] {a b c : α}

-- BENCHMARK-STATEMENT
example (ha : ‖a‖ ≤ 1) : ‖c - a * b‖ ≤ ‖c - a‖ + ‖1 - b‖ := by
  -- BENCHMARK-PROOF
  have hmul : ‖a * (1 - b)‖ ≤ ‖1 - b‖ := by
    exact (norm_mul_le _ _).trans (by simpa using mul_le_mul_of_nonneg_right ha (norm_nonneg (1 - b)))
  rw [mul_one_sub] at hmul
  norm_arith [hmul]
  -- BENCHMARK-END
