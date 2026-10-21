import NormArith

example (f : ℝ → ℝ → ℝ) (a b x y ε M : ℝ)
    (h₁ : ∀ p : ℝ × ℝ, dist (Function.uncurry f p) (Function.uncurry f (a, p.2)) ≤ ε)
    (h₂ : ‖f a y - f a x‖ ≤ M) : ‖f b y - f b x‖ ≤ 2 * ε + M := by
  norm_arith [h₁ (b, y), h₁ (b, x), h₂]

example {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : X → ℝ → E) (q p : X) (x M δ : ℝ)
    (hM : ‖Function.uncurry f (q, x)‖ ≤ M)
    (hv : ‖f p x - f q x‖ < δ) : ‖f p x‖ < M + δ := by
  norm_arith [hM, hv]
