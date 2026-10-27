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
  have : ENNReal.HolderTriple
      (2 / ENNReal.ofReal (1 / 4)) (6 / ENNReal.ofReal (1 - (1 / 4))) 4 := by
    holder_arith
  have hf4 := memLp_interpolate (r := 4) (by norm_num : (0 : ℝ) < 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1) hf2 hf6
  have hg4 := memLp_interpolate (r := 4) (by norm_num : (0 : ℝ) < 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1) hg2 hg6
  have hfb := finite_lp_interpolate (r := 4) (by norm_num : (0 : ℝ) < 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1) hf2 hf6
  have hgb := finite_lp_interpolate (r := 4) (by norm_num : (0 : ℝ) < 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1) hg2 hg6
  have : ENNReal.HolderTriple 4 4 2 := by holder_arith
  calc
    lpNorm (f * g) 2 μ ≤ lpNorm f 4 μ * lpNorm g 4 μ := finite_lp_mul hf4 hg4
    _ ≤ _ := by
      convert mul_le_mul hfb hgb lpNorm_nonneg (le_trans lpNorm_nonneg hfb) using 1
      norm_num
  -- BENCHMARK-END
