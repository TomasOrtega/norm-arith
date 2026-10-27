import NormArith.Tactic

set_option maxHeartbeats 4000000
set_option norm_arith.forceLP true
set_option trace.norm_arith.profile true

-- Two coupled bounds require separate reverse-triangle certificates before joint scalar absorption.
-- BENCHMARK-STATEMENT
example {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (x y u v : E) (F G A B : ℝ)
    (hx : ‖x + y‖ ≤ F + ‖u‖ / 4)
    (hu : ‖u + v‖ ≤ G + ‖x‖ / 2)
    (hy : ‖y‖ ≤ A) (hv : ‖v‖ ≤ B) :
    7 * ‖x‖ ≤ 8 * F + 8 * A + 2 * G + 2 * B := by
  -- BENCHMARK-PROOF
  norm_arith [hx, hu, hy, hv]
  -- BENCHMARK-END
