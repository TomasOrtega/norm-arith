import NormArith.Tactic

set_option maxHeartbeats 4000000
set_option norm_arith.forceLP true

-- A triangular rational identity requiring all 8 source norm terms; source support cannot be shortened.
-- BENCHMARK-STATEMENT
example {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (x1 x2 x3 x4 x5 x6 x7 x8 : E) (a1 a2 a3 a4 a5 a6 a7 a8 : ℝ)
    (h1 : ‖(2 : ℝ) • x1 - x2‖ ≤ a1)
    (h2 : ‖(2 : ℝ) • x2 - x3‖ ≤ a2)
    (h3 : ‖(2 : ℝ) • x3 - x4‖ ≤ a3)
    (h4 : ‖(2 : ℝ) • x4 - x5‖ ≤ a4)
    (h5 : ‖(2 : ℝ) • x5 - x6‖ ≤ a5)
    (h6 : ‖(2 : ℝ) • x6 - x7‖ ≤ a6)
    (h7 : ‖(2 : ℝ) • x7 - x8‖ ≤ a7)
    (h8 : ‖(2 : ℝ) • x8‖ ≤ a8) :
    2 * ‖x1‖ ≤ a1 + a2 / 2 + a3 / 4 + a4 / 8 + a5 / 16 + a6 / 32 + a7 / 64 + a8 / 128 := by
  -- BENCHMARK-PROOF
  norm_arith [h1, h2, h3, h4, h5, h6, h7, h8]
  -- BENCHMARK-END
