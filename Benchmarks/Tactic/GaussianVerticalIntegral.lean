/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
/-
Standalone exact theorem from Mathlib/Analysis/SpecialFunctions/Gaussian/FourierTransform.lean.
Pinned source and adaptations: Benchmarks/manifest.json (GaussianVerticalIntegral).
-/
module

import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Tactic
import NormArith

open Real Set MeasureTheory Filter intervalIntegral
open Complex hiding exp continuous_exp
open GaussianFourier
open scoped Real Topology

variable {b : ℂ}

-- BENCHMARK-STATEMENT
example (hb : 0 < b.re) (c : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ‖verticalIntegral b c T‖ ≤
      (2 : ℝ) * |c| * exp (-(b.re * T ^ 2 - (2 : ℝ) * |b.im| * |c| * T - b.re * c ^ 2)) := by
  -- BENCHMARK-PROOF
  -- first get uniform bound for integrand
  have vert_norm_bound :
    ∀ {T : ℝ},
      0 ≤ T →
        ∀ {c y : ℝ},
          |y| ≤ |c| →
            ‖cexp (-b * (T + y * I) ^ 2)‖ ≤
              exp (-(b.re * T ^ 2 - (2 : ℝ) * |b.im| * |c| * T - b.re * c ^ 2)) := by
    intro T hT c y hy
    rw [norm_cexp_neg_mul_sq_add_mul_I b]
    gcongr exp (-(_ - ?_ * _ - _ * ?_))
    · (conv_lhs => rw [mul_assoc]); (conv_rhs => rw [mul_assoc])
      gcongr _ * ?_
      refine (le_abs_self _).trans ?_
      rw [abs_mul]
      gcongr
    · rwa [sq_le_sq]
  -- now main proof
  apply (intervalIntegral.norm_integral_le_of_norm_le_const _).trans
  · rw [sub_zero]
    conv_lhs => simp only [mul_comm _ |c|]
    conv_rhs =>
      conv =>
        congr
        rw [mul_comm]
      rw [mul_assoc]
  · intro y hy
    have absy : |y| ≤ |c| := by
      simpa using abs_sub_left_of_mem_uIcc (uIoc_subset_uIcc hy)
    rw [norm_mul, norm_I, one_mul, two_mul]
    have hpos := vert_norm_bound hT absy
    have hneg : ‖cexp (-b * (T - y * I) ^ 2)‖ ≤
        exp (-(b.re * T ^ 2 - (2 : ℝ) * |b.im| * |c| * T - b.re * c ^ 2)) := by
      rw [← abs_neg y] at absy
      simpa only [neg_mul, ofReal_neg] using! vert_norm_bound hT absy
    norm_arith [hpos, hneg]
  -- BENCHMARK-END
