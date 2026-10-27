module

import NormArith.Parameters
import Mathlib.Basic.Real.Basic

open NormArith.Parameters
open scoped ENNReal

#guard holderPartner? (1 / 3) (1 / 2) == some (1 / 6)
#guard holderPartner? (1 / 2) (1 / 2) == some 0
#guard holderPartner? (1 / 2) (1 / 3) == none
#guard interpolationWeight? (1 / 2) (1 / 6) (1 / 4) == some (1 / 4)
#guard interpolationWeight? (1 / 2) 0 (1 / 4) == some (1 / 2)
#guard interpolationWeight? (1 / 2) (1 / 2) (1 / 2) == some 1
#guard interpolationWeight? (1 / 2) (1 / 2) (1 / 3) == none
#guard interpolationWeight? (1 / 2) (1 / 6) 1 == none
#guard interpolationWeight? (-1) 0 0 == none

example : ∃ q : ℝ≥0∞, ENNReal.HolderTriple 3 q 2 := by
  choose_holder 3 2

example : ∃ q : ℝ≥0∞, ENNReal.HolderTriple 2 q 2 := by
  choose_holder 2 2

example : ∃ q : ℝ≥0∞, ENNReal.HolderTriple (6 / 5) q 1 := by
  choose_holder (6 / 5) 1

example : ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ 1 / 4 = θ / 2 + (1 - θ) / 6 := by
  choose_interpolation 2 6 4

example : ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ 1 / 4 = θ / 2 + (1 - θ) * 0 := by
  choose_interpolation 2 ∞ 4

example : True := by
  fail_if_success
    have : ∃ q : ℝ≥0∞, ENNReal.HolderTriple 2 q 3 := by choose_holder 2 3
  fail_if_success
    have : ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ 1 = θ / 2 + (1 - θ) / 6 := by
      choose_interpolation 2 6 1
  fail_if_success
    have : ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ 1 / 3 = θ / 2 + (1 - θ) / 6 := by
      choose_interpolation 2 6 4
  trivial
