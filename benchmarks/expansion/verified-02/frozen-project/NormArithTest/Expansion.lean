module

import NormArith

section

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

example (x y : E) (a b : ℝ) (h : ‖x‖ ≤ a ∧ ‖y‖ ≤ b) :
    ‖x + y‖ ≤ a + b := by
  norm_arith

example (x y : E) (a b : ℝ) (h : ‖x‖ ≤ a ∧ True ∧ ‖y‖ < b) :
    ‖x + y‖ < a + b := by
  norm_arith [h]

example (x y : E) (a b : ℝ) (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ b) :
    ‖x + y‖ ≤ a + b := by
  fail_if_success norm_arith [hx]
  norm_arith [And.intro hx hy]

example (x y : E) (a b : ℝ) (h : dist x 0 ≤ a ∧ dist y 0 ≤ b) :
    dist (x + y) 0 ≤ a + b := by
  norm_arith [h]

example (x : E) (ε δ : ℝ) (_hx : ‖x‖ ≤ 1) :
    let δ' := min (1 / 2) (min (ε / 3) (δ / 3))
    2 - δ + δ' + δ' ≤ 2 - δ' := by
  norm_arith

example (x : E) (a b : ℝ) (hx : ‖x‖ ≤ a) : ‖x‖ ≤ max a b := by
  norm_arith

example (a r : ℝ) (h : ‖a‖ ≤ r) : a ≤ r := by
  norm_arith

example (a r : ℝ) (h : ‖a‖ ≤ r) : -r ≤ a := by
  norm_arith

example (x y : E) (a b : ℝ) (h : ‖x‖ ≤ a ∧ ‖y‖ ≤ b) :
    ‖x + y‖ ≤ a + b := by
  fail_if_success
    have : ‖x + y‖ < a + b := by norm_arith [h]
  norm_arith [h]

end
