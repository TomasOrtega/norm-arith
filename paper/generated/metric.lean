example (a b c d : X) (r s t : ℝ)
    (h₁ : dist a b ≤ r) (h₂ : dist c b ≤ s) (h₃ : dist c d ≤ t) :
    dist a d ≤ r + s + t := by
  norm_arith
