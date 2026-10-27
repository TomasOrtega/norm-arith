import NormArith.FixedPoint

open NormArith
open scoped NNReal

-- BENCHMARK-STATEMENT
example {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (B : X →L[ℝ] X →L[ℝ] X) (a : X) (A : ℝ)
    (hA : 0 ≤ A) (ha : ‖a‖ ≤ A) (hsmall : 8 * ‖B‖ * A ≤ 1) :
    ∃! u, ‖u‖ ≤ 2 * A ∧ a + B u u = u := by
  -- BENCHMARK-PROOF
  apply existsUnique_fixed_point_in_ball (fun u => a + B u u)
    (q := (1 / 2 : ℝ≥0)) (by positivity) (by norm_num)
  · intro u hu
    exact quadratic_ball_bound B a u hA ha hu hsmall
  · intro u v hu hv
    simpa only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using
      quadratic_contraction_bound B a u v hu hv hsmall
  -- BENCHMARK-END
