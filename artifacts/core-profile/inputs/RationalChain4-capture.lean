import NormArith.Tactic

set_option norm_arith.replayText true
set_option maxHeartbeats 4000000
set_option norm_arith.forceLP true
set_option trace.norm_arith.profile true

-- A triangular rational identity requiring all 4 source norm terms; source support cannot be shortened.
-- BENCHMARK-STATEMENT
example {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (x1 x2 x3 x4 : E) (a1 a2 a3 a4 : ℝ)
    (h1 : ‖(2 : ℝ) • x1 - x2‖ ≤ a1)
    (h2 : ‖(2 : ℝ) • x2 - x3‖ ≤ a2)
    (h3 : ‖(2 : ℝ) • x3 - x4‖ ≤ a3)
    (h4 : ‖(2 : ℝ) • x4‖ ≤ a4) :
    2 * ‖x1‖ ≤ a1 + a2 / 2 + a3 / 4 + a4 / 8 := by
  -- BENCHMARK-PROOF
  norm_arith? [h1, h2, h3, h4]
  -- BENCHMARK-END
