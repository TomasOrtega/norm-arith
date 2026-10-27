import NormArith.FunctionSpace

open NormArith MeasureTheory
open scoped ENNReal NNReal

-- BENCHMARK-STATEMENT
example {α : Type*} [MeasurableSpace α] {μ : Measure α} (f : α → ℝ)
    (hf3 : MemLp f 3 μ) (hf12 : MemLp f 12 μ) :
    lpNorm f 6 μ ≤ lpNorm f 3 μ ^ (1 / 3 : ℝ) * lpNorm f 12 μ ^ (2 / 3 : ℝ) := by
  -- BENCHMARK-PROOF
  have : ENNReal.HolderTriple
      (3 / ENNReal.ofReal (1 / 3)) (12 / ENNReal.ofReal (1 - (1 / 3))) 6 := by
    holder_arith
  have h := finite_lp_interpolate (r := 6) (by norm_num : (0 : ℝ) < 1 / 3)
    (by norm_num : (1 / 3 : ℝ) < 1) hf3 hf12
  norm_num at h
  exact h
  -- BENCHMARK-END
