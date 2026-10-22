-- The 2020 motivating example: 2a + b = 3a + (b - a).
example (a b : E) : ‖(2 : ℝ) • a + b‖ ≤ 3 * ‖a‖ + ‖b - a‖ := by
  norm_arith [le_refl ‖a‖, le_refl ‖b - a‖]
