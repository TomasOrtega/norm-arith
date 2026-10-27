import NormArith.Tactic

set_option maxHeartbeats 4000000
set_option norm_arith.forceLP true

-- Dense Walsh-Hadamard coordinate observations; the target needs eight independent source terms.
-- BENCHMARK-STATEMENT
example {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (x1 x2 x3 x4 x5 x6 x7 x8 : E) (a1 a2 a3 a4 a5 a6 a7 a8 : ℝ)
    (h1 : ‖x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8‖ ≤ a1)
    (h2 : ‖x1 - x2 + x3 - x4 + x5 - x6 + x7 - x8‖ ≤ a2)
    (h3 : ‖x1 + x2 - x3 - x4 + x5 + x6 - x7 - x8‖ ≤ a3)
    (h4 : ‖x1 - x2 - x3 + x4 + x5 - x6 - x7 + x8‖ ≤ a4)
    (h5 : ‖x1 + x2 + x3 + x4 - x5 - x6 - x7 - x8‖ ≤ a5)
    (h6 : ‖x1 - x2 + x3 - x4 - x5 + x6 - x7 + x8‖ ≤ a6)
    (h7 : ‖x1 + x2 - x3 - x4 - x5 - x6 + x7 + x8‖ ≤ a7)
    (h8 : ‖x1 - x2 - x3 + x4 - x5 + x6 + x7 - x8‖ ≤ a8)
    : 8 * ‖x1‖ ≤ a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 := by
  -- BENCHMARK-PROOF
  norm_arith [h1, h2, h3, h4, h5, h6, h7, h8]
  -- BENCHMARK-END
