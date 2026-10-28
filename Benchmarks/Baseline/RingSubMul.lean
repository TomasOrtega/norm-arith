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

variable {α : Type*} [SeminormedRing α] {a b c : α}

-- BENCHMARK-STATEMENT
example (ha : ‖a‖ ≤ 1) : ‖c - a * b‖ ≤ ‖c - a‖ + ‖1 - b‖ := by
  -- BENCHMARK-PROOF
  calc
    _ ≤ ‖c - a‖ + ‖a * (1 - b)‖ := by
        simpa [mul_one_sub] using norm_sub_le_norm_sub_add_norm_sub c a (a * b)
    _ ≤ ‖c - a‖ + ‖a‖ * ‖1 - b‖ := by gcongr; exact norm_mul_le ..
    _ ≤ ‖c - a‖ + 1 * ‖1 - b‖ := by gcongr
    _ = ‖c - a‖ + ‖1 - b‖ := by simp
  -- BENCHMARK-END
