example (x : E) : 0 ≤ ‖x‖ * ‖x‖ := by
  fail_if_success norm_arith
  exact mul_self_nonneg _
