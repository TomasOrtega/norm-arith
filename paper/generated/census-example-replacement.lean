  simp only [Pi.sub_apply] at hn
  have hsum : ‖(n : ℝ)⁻¹ • ∑ i ∈ range n, (X i ω - Y k i ω)‖ ≤ δ := by
    grw [norm_smul, norm_inv, RCLike.norm_natCast, norm_sum_le, ← div_eq_inv_mul, hn.le]
  simp only [sum_sub_distrib, smul_sub] at hsum
  norm_arith
