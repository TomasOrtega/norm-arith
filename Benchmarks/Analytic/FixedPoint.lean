import NormArith.FixedPoint

open NormArith
open scoped NNReal

-- BENCHMARK-STATEMENT
example {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (B : X →L[ℝ] X →L[ℝ] X) (a : X) (A : ℝ)
    (hA : 0 ≤ A) (ha : ‖a‖ ≤ A) (hsmall : 8 * ‖B‖ * A ≤ 1) :
    ∃! u, ‖u‖ ≤ 2 * A ∧ a + B u u = u := by
  -- BENCHMARK-PROOF
  analytic_estimate
  -- BENCHMARK-END
