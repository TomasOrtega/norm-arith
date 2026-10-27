import NormArith.FunctionSpace

open NormArith MeasureTheory
open scoped ENNReal NNReal

-- BENCHMARK-STATEMENT
example {α : Type*} [MeasurableSpace α] {μ : Measure α} (f : α → ℝ)
    (hf3 : MemLp f 3 μ) (hf12 : MemLp f 12 μ) :
    lpNorm f 6 μ ≤ lpNorm f 3 μ ^ (1 / 3 : ℝ) * lpNorm f 12 μ ^ (2 / 3 : ℝ) := by
  -- BENCHMARK-PROOF
  lp_interpolate 3 12 6
  -- BENCHMARK-END
