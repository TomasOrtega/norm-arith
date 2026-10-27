import NormArith.FunctionSpace

open NormArith MeasureTheory
open scoped ENNReal NNReal

local instance : ENNReal.HolderTriple 4 4 2 := by holder_arith
local instance : ENNReal.HolderTriple 3 6 2 := by holder_arith
local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩
local instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance : Fact ((1 : ℝ≥0∞) ≤ 6) := ⟨by norm_num⟩

-- BENCHMARK-STATEMENT
example {T X E F G : Type*} [MeasurableSpace T] [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
    [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G]
    (μ : Measure X) (ν : Measure T) (B : E →L[ℝ] F →L[ℝ] G)
    (f : Lp (Lp E 4 μ) 3 ν) (g : Lp (Lp F 4 μ) 6 ν) :
    ‖(B.holderL μ 4 4 2).holder 2 f g‖ ≤ ‖B‖ * ‖f‖ * ‖g‖ := by
  -- BENCHMARK-PROOF
  apply ((B.holderL μ 4 4 2).norm_holder_apply_apply_le (r := 2) f g).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right B.norm_holderL_le (norm_nonneg f)) (norm_nonneg g)
  -- BENCHMARK-END
