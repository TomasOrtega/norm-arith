example (w x y z : E) (b : ℝ)
    (J1 : ‖w - x‖ ≤ b) (J2 : ‖x - y‖ ≤ b) (J3 : ‖y - z‖ ≤ b) :
    ‖w - z‖ ≤ 3 * b := by
  norm_arith [J1, J2, J3]
