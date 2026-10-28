/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
/-
Standalone exact theorem from Mathlib/Analysis/Normed/Ring/Basic.lean.
Pinned source and adaptations: Benchmarks/manifest.json (RingCommutator).
-/
module

import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic
import NormArith

variable {α : Type*} [SeminormedRing α]

-- BENCHMARK-STATEMENT
example (a b : αˣ) :
    ‖(a * b * a⁻¹ * b⁻¹).val - 1‖ ≤ 2 * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ * ‖a.val - 1‖ * ‖b.val - 1‖ := by
  -- BENCHMARK-PROOF
  calc
    ‖(a * b * a⁻¹ * b⁻¹).val - 1‖ = ‖(a * b - b * a) * a⁻¹.val * b⁻¹.val‖ := by simp [sub_mul, *]
    _ ≤ ‖(a * b - b * a : α)‖ * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ := norm_mul₃_le
    _ = ‖(a - 1 : α) * (b - 1) - (b - 1) * (a - 1)‖ * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ := by
      simp_rw [sub_one_mul, mul_sub_one]; abel_nf
    _ ≤ (2 * (‖a.val - 1‖ * ‖b.val - 1‖)) * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ := by
      gcongr
      norm_arith [norm_mul_le (a.val - 1) (b.val - 1), norm_mul_le (b.val - 1) (a.val - 1)]
    _ = 2 * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ * ‖a.val - 1‖ * ‖b.val - 1‖ := by ring
  -- BENCHMARK-END
