import NormArith.FunctionSpace

open NormArith MeasureTheory
open scoped ENNReal NNReal

-- BENCHMARK-STATEMENT
example {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (u f b du : α → ℝ) (ν S : ℝ) (hν : 0 < ν) (hS : 0 ≤ S)
    (hu : MemLp u 6 μ) (hf : MemLp f (6 / 5) μ)
    (hb : MemLp b 3 μ) (hdu : MemLp du 2 μ)
    (hs : lpNorm u 6 μ ≤ S * lpNorm du 2 μ)
    (hbsmall : S * lpNorm b 3 μ ≤ ν / 2)
    (he : ν * lpNorm du 2 μ ^ 2 ≤
      |∫ x, f x * u x ∂μ| + |∫ x, (b x * du x) * u x ∂μ|) :
    lpNorm du 2 μ ≤ 2 * S * lpNorm f (6 / 5) μ / ν ∧
    lpNorm u 6 μ ≤ 2 * S ^ 2 * lpNorm f (6 / 5) μ / ν := by
  -- BENCHMARK-PROOF
  analytic_estimate
  -- BENCHMARK-END
