module

import NormArith

section

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

-- paper:begin hidden
example (x y : E) (a b : ℝ)
    (h₁ : ‖x + y‖ ≤ a) (h₂ : ‖x - y‖ ≤ b) :
    ‖x‖ ≤ (a + b) / 2 := by
  norm_arith
-- paper:end hidden

-- paper:begin reverse
example (x y : E) : ‖x‖ - ‖y‖ ≤ ‖x - y‖ := by
  norm_arith
-- paper:end reverse

-- paper:begin boundary
example (x : E) : 0 ≤ ‖x‖ * ‖x‖ := by
  fail_if_success norm_arith
  exact mul_self_nonneg _
-- paper:end boundary

-- paper:begin quantified
example (f : E → E) (x y z c : E) (r R a : ℝ)
    (h : ∀ t ∈ Metric.ball x R, ‖f t - c‖ ≤ a)
    (hy : y ∈ Metric.ball x r) (hz : z ∈ Metric.ball x r) (hr : r < R) :
    ‖f z - f y‖ ≤ a + a := by
  norm_arith
-- paper:end quantified

end

section

variable {X : Type*} [PseudoMetricSpace X]

-- paper:begin metric
example (a b c d : X) (r s t : ℝ)
    (h₁ : dist a b ≤ r) (h₂ : dist c b ≤ s) (h₃ : dist c d ≤ t) :
    dist a d ≤ r + s + t := by
  norm_arith
-- paper:end metric

end

section

variable {E : Type*} [SeminormedAddCommGroup E]

-- The `fderiv-telescope` census pilot has this shape, with four operator values.
-- paper:begin mathlib
example (w x y z : E) (b : ℝ)
    (J1 : ‖w - x‖ ≤ b) (J2 : ‖x - y‖ ≤ b) (J3 : ‖y - z‖ ≤ b) :
    ‖w - z‖ ≤ 3 * b := by
  norm_arith [J1, J2, J3]
-- paper:end mathlib

end
