/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
/-
Standalone exact theorem from Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean.
Pinned source and adaptations: Benchmarks/manifest.json (WeierstrassSeriesBound).
-/
module

import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Tactic
import NormArith

open PeriodPair

-- BENCHMARK-STATEMENT
example (r : ℝ) (hr : 0 < r) (s : ℂ) (hs : ‖s‖ < r) (l : ℂ) (h : 2 * r ≤ ‖l‖) :
    ‖1 / (s - l) ^ 2 - 1 / l ^ 2‖ ≤ 10 * r * ‖l‖ ^ (-3 : ℝ) := by
  -- BENCHMARK-PROOF
  have : s ≠ ↑l := by rintro rfl; linarith
  have : 0 < ‖l‖ := by linarith
  calc
    _ = ‖(↑l ^ 2 - (s - ↑l) ^ 2) / ((s - ↑l) ^ 2 * ↑l ^ 2)‖ := by
      rw [div_sub_div, one_mul, mul_one]
      · simpa [sub_eq_zero]
      · simpa
    _ = ‖l ^ 2 - (s - l) ^ 2‖ / (‖s - l‖ ^ 2 * ‖l‖ ^ 2) := by simp
    _ ≤ ‖l ^ 2 - (s - l) ^ 2‖ / ((‖l‖ / 2) ^ 2 * ‖l‖ ^ 2) := by
      gcongr
      norm_arith
    _ = ‖s * (2 * l - s)‖ / (‖l‖ ^ 4 / 4) := by
      congr 1
      · rw [sq_sub_sq]; simp [← sub_add, two_mul, sub_add_eq_add_sub]
      · ring
    _ = (‖s‖ * ‖2 * l - s‖) / (‖l‖ ^ 4 / 4) := by simp
    _ = (4 * ‖s‖ * ‖2 * l - s‖) / ‖l‖ ^ 4 := by field
    _ ≤ (4 * r * (2.5 * ‖l‖)) / ‖l‖ ^ 4 := by
      gcongr (4 * ?_ * ?_) / ‖l‖ ^ 4
      have hmul : ‖(2 : ℂ) * l‖ = 2 * ‖l‖ := by simp
      have hsub : ‖2 * l - s‖ ≤ ‖2 * l‖ + ‖s‖ := by norm_arith
      rw [hmul] at hsub
      linarith
    _ = 10 * r / ‖l‖ ^ 3 := by field
    _ = _ := by norm_cast
  -- BENCHMARK-END
