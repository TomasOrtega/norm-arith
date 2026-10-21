module

import NormArith

section

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

example (x y : E) (a b : ℝ) (h : ‖x‖ ≤ a ∧ ‖y‖ ≤ b) :
    ‖x + y‖ ≤ a + b := by
  norm_arith

example (x y : E) (a b : ℝ) (h : ‖x‖ ≤ a ∧ True ∧ ‖y‖ < b) :
    ‖x + y‖ < a + b := by
  norm_arith [h]

example (x y : E) (a b : ℝ) (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ b) :
    ‖x + y‖ ≤ a + b := by
  fail_if_success norm_arith [hx]
  norm_arith [And.intro hx hy]

example (x y : E) (a b : ℝ) (h : dist x 0 ≤ a ∧ dist y 0 ≤ b) :
    dist (x + y) 0 ≤ a + b := by
  norm_arith [h]

example (x : E) (ε δ : ℝ) (_hx : ‖x‖ ≤ 1) :
    let δ' := min (1 / 2) (min (ε / 3) (δ / 3))
    2 - δ + δ' + δ' ≤ 2 - δ' := by
  norm_arith

example (x : E) (a b : ℝ) (hx : ‖x‖ ≤ a) : ‖x‖ ≤ max a b := by
  norm_arith

example (a r : ℝ) (h : ‖a‖ ≤ r) : a ≤ r := by
  norm_arith

example (a r : ℝ) (h : ‖a‖ ≤ r) : -r ≤ a := by
  norm_arith

example (x y : E) (a b : ℝ) (h : ‖x‖ ≤ a ∧ ‖y‖ ≤ b) :
    ‖x + y‖ ≤ a + b := by
  fail_if_success
    have : ‖x + y‖ < a + b := by norm_arith [h]
  norm_arith [h]

end

section Quantified

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

example (f : E → E) (z w : E) (S : Set E) (a b : ℝ)
    (hI : ∀ t ∈ S, ‖f t‖ ≤ a) (hz : z ∈ S) (hw : ‖w‖ ≤ b) :
    ‖f z + w‖ ≤ a + b := by
  norm_arith

example (f : E → E) (z : E) (S : Set E) (a : ℝ)
    (hI : ∀ {t}, t ∈ S → ‖f t‖ ≤ a) (hz : z ∈ S) : ‖f z‖ ≤ a := by
  norm_arith [hI]

example (f g : E → E) (z : E) (S : Set E) (a b : ℝ)
    (hI : ∀ t ∈ S, ‖f t‖ ≤ a ∧ ‖g t‖ ≤ b) (hz : z ∈ S) :
    ‖f z + g z‖ ≤ a + b := by
  norm_arith [hI]

example (f : E → E) (z : E) (a b : ℝ)
    (hI : ∀ t, ‖t‖ ≤ a → ‖f t‖ ≤ b) (hz : ‖z‖ ≤ a) : ‖f z‖ ≤ b := by
  fail_if_success norm_arith [hI]
  norm_arith [hI, hz]

example (f : ℝ → E) (x z r m a : ℝ)
    (hI : ∀ {t}, x ≤ t ∧ t < m → ‖f t‖ ≤ a)
    (hz : z ∈ Set.Icc x (x + r)) (hr : x + r < m) : ‖f z‖ ≤ a := by
  norm_arith [hI]

end Quantified

section DerivativeError
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

example (f : ℝ → E) (L : E) (x y z m a : ℝ)
    (hI : ∀ t, x ≤ t ∧ t < m → ‖f t - f x - (t - x) • L‖ ≤ a)
    (hy : x ≤ y ∧ y < m) (hz : x ≤ z ∧ z < m) :
    ‖f z - f y - (z - y) • L‖ ≤ a + a := by
  simp only [sub_smul] at hI ⊢
  norm_arith [hI]

example (f : E → E) (z : E) (a b : ℝ)
    (hI : ∀ t, ‖t‖ ≤ a → ‖f t‖ ≤ b) (hz : (‖z‖₊ : ℝ) ≤ a) : ‖f z‖ ≤ b := by
  fail_if_success norm_arith [hI]
  have hz' : ‖z‖ ≤ a := hz
  norm_arith [hI, hz']

example (f : E → E) (_z : E) (S : Set E) (a : ℝ)
    (_hI : ∀ t ∈ S, ‖f t‖ ≤ a) : True := by
  fail_if_success
    have : ‖f _z‖ ≤ a := by norm_arith [_hI]
  trivial

end DerivativeError

section DistanceControl
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

example (f : E → E) (z : E) (a b : ℝ)
    (hI : ∀ t, (edist t 0).toReal ≤ a → ‖f t‖ ≤ b)
    (hz : (edist z 0).toReal ≤ a) : ‖f z‖ ≤ b := by
  fail_if_success norm_arith [hI]
  norm_arith [hI, hz]

example (f : E → E) (z : E) (a b : ℝ)
    (hI : ∀ t, (‖t‖ₑ).toReal ≤ a → ‖f t‖ ≤ b)
    (hz : (‖z‖ₑ).toReal ≤ a) : ‖f z‖ ≤ b := by
  fail_if_success norm_arith [hI]
  norm_arith [hI, hz]

example (f : E → E) (z : E) (a b : ℝ)
    (hI : ∀ t, (nndist t 0 : ℝ) ≤ a → ‖f t‖ ≤ b)
    (hz : (nndist z 0 : ℝ) ≤ a) : ‖f z‖ ≤ b := by
  fail_if_success norm_arith [hI]
  norm_arith [hI, hz]

end DistanceControl

section HiddenControl
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
abbrev hiddenNorm (z : E) : ℝ := ‖z‖

example (f : E → E) (z : E) (a b : ℝ)
    (hI : ∀ t, ‖t‖ ≤ a → ‖f t‖ ≤ b) (hz : hiddenNorm z ≤ a) : ‖f z‖ ≤ b := by
  fail_if_success norm_arith [hI]
  norm_arith [hI, hz]

example (f : E → E) (z : E) (a b : ℝ)
    (hI : ∀ t, [Fact (‖t‖ ≤ a)] → ‖f t‖ ≤ b) [hz : Fact (‖z‖ ≤ a)] : ‖f z‖ ≤ b := by
  fail_if_success norm_arith [hI]
  norm_arith [hI, hz]

end HiddenControl

section OrdinaryAliasControl
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
def ordinaryHiddenNorm (z : E) : ℝ := ‖z‖

example (f : E → E) (z : E) (a b : ℝ)
    (hI : ∀ t, ‖t‖ ≤ a → ‖f t‖ ≤ b)
    (hz : ordinaryHiddenNorm z ≤ a) : ‖f z‖ ≤ b := by
  fail_if_success norm_arith [hI]
  norm_arith [hI, hz]
end OrdinaryAliasControl

section BallPremise
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
example (f : E → E) (x z : E) (r R a : ℝ)
    (hI : ∀ t ∈ Metric.ball x R, ‖f t‖ ≤ a)
    (hz : z ∈ Metric.ball x r) (hr : r < R) : ‖f z‖ ≤ a := by
  norm_arith
end BallPremise

section QuantifiedCertificate
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
example (f : E → E) (x y z c : E) (r R a : ℝ)
    (hI : ∀ t ∈ Metric.ball x R, ‖f t - c‖ ≤ a)
    (hy : y ∈ Metric.ball x r) (hz : z ∈ Metric.ball x r) (hr : r < R) :
    ‖f z - f y‖ ≤ a + a := by
  norm_arith
end QuantifiedCertificate

section QuantifiedVariableBound
variable {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
example (f L : E → F) (x y z : E) (r R ε : ℝ) :
    let δ := (ε / 2) / 2
    (∀ t ∈ Metric.ball x R, ‖f t - f x - (L t - L x)‖ ≤ δ * ‖t - x‖) →
    y ∈ Metric.ball x r → z ∈ Metric.ball x r → r < R →
    ‖f z - f y - (L z - L y)‖ ≤ δ * ‖z - x‖ + δ * ‖y - x‖ := by
  intro δ hI hy hz hr
  norm_arith
end QuantifiedVariableBound

section DefinitionallyEqualAtoms

example (f : ℝ → ℝ → ℝ) (a b x y ε M : ℝ)
    (h₁ : ∀ p : ℝ × ℝ, dist (Function.uncurry f p) (Function.uncurry f (a, p.2)) ≤ ε)
    (h₂ : ‖f a y - f a x‖ ≤ M) : ‖f b y - f b x‖ ≤ 2 * ε + M := by
  norm_arith [h₁ (b, y), h₁ (b, x), h₂]

example {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : X → ℝ → E) (q p : X) (x M δ : ℝ)
    (hM : ‖Function.uncurry f (q, x)‖ ≤ M)
    (hv : ‖f p x - f q x‖ < δ) : ‖f p x‖ < M + δ := by
  fail_if_success norm_arith [hv]
  norm_arith [hM, hv]

end DefinitionallyEqualAtoms

section PropositionViews
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

example (x y : E) (a b : ℝ) (hx : x ∈ {z | ‖z‖ ≤ a}) (hy : ‖y‖ ≤ b) :
    ‖x + y‖ ≤ a + b := by
  fail_if_success norm_arith [hy]
  norm_arith [hx, hy]

example (f g : E → E) (x y : E) (s : Set E) (ε δ : ℝ)
    (h : s ⊆ {y | ‖f y - f x - g (y - x)‖ ≤ ε}) (hy : y ∈ s)
    (hg : ‖g (y - x)‖ ≤ δ) : ‖f y - f x‖ ≤ ε + δ := by
  norm_arith [h hy, hg]

end PropositionViews
