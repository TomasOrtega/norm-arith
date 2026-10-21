# Expanded patch example: a Strong Law estimate

This is the selected proof fragment `manual-strong-law-sums` in
`ProbabilityTheory.strong_law_ae_of_measurable`,
`Mathlib/Probability/StrongLaw.lean`, original lines 760–780.
It is a fragment of the existing theorem; its statement and assumptions stay the same.

Before:

```lean
  -- at such an `n`, the strong law is realized up to `ε`.
  calc
  ‖(n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω - μ[X 0]‖
    = ‖(n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, (X i ω - Y k i ω) +
        ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, Y k i ω - μ[Y k 0]) + (μ[Y k 0] - μ[X 0])‖ := by
      congr
      simp only [sum_sub_distrib, smul_sub]
      abel
  _ ≤ ‖(n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, (X i ω - Y k i ω)‖ +
        ‖(n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, Y k i ω - μ[Y k 0]‖ + ‖μ[Y k 0] - μ[X 0]‖ :=
      norm_add₃_le
  _ ≤ (∑ i ∈ Finset.range n, ‖X i ω - Y k i ω‖) / n + δ + δ := by
      gcongr
      simp only [norm_smul, norm_inv, RCLike.norm_natCast,
        div_eq_inv_mul]
      gcongr
      exact norm_sum_le _ _
  _ ≤ δ + δ + δ := by
      gcongr
      exact hn.le
  _ < ε := hδ
```

After, including all preparation:

```lean
  simp only [Pi.sub_apply] at hn
  have hsum : ‖(n : ℝ)⁻¹ • ∑ i ∈ range n, (X i ω - Y k i ω)‖ ≤ δ := by
    grw [norm_smul, norm_inv, RCLike.norm_natCast, norm_sum_le, ← div_eq_inv_mul, hn.le]
  simp only [sum_sub_distrib, smul_sub] at hsum
  norm_arith
```

The replacement retains the analytic estimate: the norm of the finite sum is
bounded using the existing hypothesis `hn`, norm homogeneity, and `norm_sum_le`.
It then distributes the sum and scalar multiplication. `norm_arith` combines that
bound with the existing centered-average bound `h'n`, expectation bound, and
`hδ : δ + δ + δ < ε`. The tactic closes the finite algebraic estimate; it does
not prove the Strong Law or derive the convergence hypotheses.

The accounting records 20 nonblank proof-code lines before and five after:
15 proof lines saved, including four preparation lines. This file has one added
`import NormArith` and no helpers, so the isolated file contributes 14 net lines.
The import is charged once in the combined patch. These line facts come from the
selected manifest; the combined verifier owns final compilation and accounting.
No compilation-speed result is inferred from this example.

Source span SHA256: `2e35cadb09cea58a6e4afe592db6fb4c0bdb33f1416b82a1a08434f5120819d4`.
Selection-07 manifest SHA256:
`a72f1b725bfaf827bb3a8e4db50570be915788ba4a85cc0fbf8c1449685ea617`.
