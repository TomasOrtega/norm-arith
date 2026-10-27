import NormArith.FunctionSpace

open NormArith MeasureTheory
open scoped ENNReal NNReal

-- BENCHMARK-STATEMENT
example {α : Type*} [MeasurableSpace α] {μ : Measure α} (f g : α → ℝ)
    (hf2 : MemLp f 2 μ) (hf6 : MemLp f 6 μ)
    (hg2 : MemLp g 2 μ) (hg6 : MemLp g 6 μ) :
    lpNorm (f * g) 2 μ ≤
      (lpNorm f 2 μ ^ (1 / 4 : ℝ) * lpNorm f 6 μ ^ (3 / 4 : ℝ)) *
      (lpNorm g 2 μ ^ (1 / 4 : ℝ) * lpNorm g 6 μ ^ (3 / 4 : ℝ)) := by
  -- BENCHMARK-PROOF
  analytic_estimate
  -- BENCHMARK-END
