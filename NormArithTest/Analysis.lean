module

import NormArith.Analysis

set_option linter.unusedVariables false

/-! Analytic estimates: positive examples and soundness boundaries. -/

open NormArith
open scoped ENNReal NNReal

section Scalar

example (A B F G : ℝ) (hA : A ≤ F + B / 4) (hB : B ≤ G + A / 2) :
    A ≤ 8 * F / 7 + 2 * G / 7 ∧ B ≤ 4 * F / 7 + 8 * G / 7 := by
  constructor <;> analytic_estimate

example (A B θ : ℝ) (hA : 0 ≤ A) (hθ : θ ≤ 1 / 2)
    (h : A ≤ B + θ * A) : A ≤ 2 * B := by
  analytic_estimate

example (a b ε : ℝ) (hε : 0 < ε) :
    a * b ≤ ε * a ^ 2 + b ^ 2 / (4 * ε) := by
  analytic_estimate

example (E ν A F : ℝ) (hν : 0 < ν) (h : E + ν * A ^ 2 ≤ F * A) :
    E + (ν / 2) * A ^ 2 ≤ F ^ 2 / (2 * ν) := by
  analytic_estimate

example (ν S F B G U : ℝ)
    (hν : 0 < ν) (hS : 0 ≤ S) (hF : 0 ≤ F) (hB : 0 ≤ B) (hG : 0 ≤ G)
    (hSobolev : U ≤ S * G) (hsmall : S * B ≤ ν / 2)
    (henergy : ν * G ^ 2 ≤ F * U + B * G * U) :
    G ≤ 2 * S * F / ν ∧ U ≤ 2 * S ^ 2 * F / ν := by
  analytic_estimate

-- At theta = 1, an absorption conclusion is not justified.
example (A B : ℝ) (hA : 0 ≤ A) (h : A ≤ B + A) : True := by
  fail_if_success
    have : A ≤ 2 * B := by analytic_estimate
  trivial

end Scalar

section Operators

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
  [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G]

example (T : E →L[ℝ] F) (x : E) : ‖T x‖ ≤ ‖T‖ * ‖x‖ := by
  analytic_estimate

example (T : E →L[ℝ] F) (x : E) (C R : ℝ)
    (hT : ‖T‖ ≤ C) (hx : ‖x‖ ≤ R) : ‖T x‖ ≤ C * R := by
  analytic_estimate

example (B : E →L[ℝ] F →L[ℝ] G) (x : E) (y : F) :
    ‖B x y‖ ≤ ‖B‖ * ‖x‖ * ‖y‖ := by
  analytic_estimate

example (B : E →L[ℝ] F →L[ℝ] G) (x x' : E) (y y' : F) :
    ‖B x y - B x' y'‖ ≤
      ‖B‖ * (‖x - x'‖ * ‖y‖ + ‖x'‖ * ‖y - y'‖) := by
  analytic_estimate

example (B : E →L[ℝ] E →L[ℝ] E) (a u : E) (A : ℝ)
    (hA : 0 ≤ A) (ha : ‖a‖ ≤ A) (hu : ‖u‖ ≤ 2 * A)
    (hsmall : 8 * ‖B‖ * A ≤ 1) : ‖a + B u u‖ ≤ 2 * A := by
  analytic_estimate

example (B : E →L[ℝ] E →L[ℝ] E) (a u v : E) (A : ℝ)
    (hu : ‖u‖ ≤ 2 * A) (hv : ‖v‖ ≤ 2 * A)
    (hsmall : 8 * ‖B‖ * A ≤ 1) :
    ‖(a + B u u) - (a + B v v)‖ ≤ (1 / 2 : ℝ) * ‖u - v‖ := by
  analytic_estimate

example (u v a b : E)
    (h : ‖u - v‖ ≤ ‖a - b‖ + (1 / 2 : ℝ) * ‖u - v‖) :
    ‖u - v‖ ≤ 2 * ‖a - b‖ := by
  analytic_estimate

end Operators

section Lp

open MeasureTheory

variable {α E F G : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
  [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G]
  {μ : Measure α} {p q r : ℝ≥0∞}

example (f g : α → E) (hf : MemLp f p μ) (hp : 1 ≤ p)
    (A B : ℝ) (hA : lpNorm f p μ ≤ A) (hB : lpNorm g p μ ≤ B) :
    lpNorm (f + g) p μ ≤ A + B := by
  analytic_estimate [finite_lp_add (g := g) hf hp]

example (f : α → E) (hf : MemLp f p μ) (A : ℝ)
    (hA : lpNorm f p μ ≤ A) : eLpNorm f p μ ≤ ENNReal.ofReal A := by
  exact eLpNorm_le_of_lpNorm_le hf hA

example (f : α → E) (A : ℝ≥0)
    (hA : eLpNorm f p μ ≤ (A : ℝ≥0∞)) : lpNorm f p μ ≤ (A : ℝ) := by
  exact lpNorm_le_of_eLpNorm_le hA

-- The finite conversion must not infer finiteness from the real-valued junk value.
example (f : α → E) (h : lpNorm f p μ = 0) : True := by
  fail_if_success
    have : eLpNorm f p μ = 0 := by analytic_estimate
  trivial

variable [p.HolderTriple q r]

example (B : E →L[ℝ] F →L[ℝ] G) (f : Lp E p μ) (g : Lp F q μ) :
    ‖B.holder r f g‖ ≤ ‖B‖ * ‖f‖ * ‖g‖ := by
  analytic_estimate [B.norm_holder_apply_apply_le (r := r) f g]

variable [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]

-- An actual function-space bilinear estimate, through mathlib's Hölder operator.
example (B : E →L[ℝ] F →L[ℝ] G)
    (f f' : Lp E p μ) (g g' : Lp F q μ) :
    ‖B.holderL μ p q r f g - B.holderL μ p q r f' g'‖ ≤
      ‖B.holderL μ p q r‖ * (‖f - f'‖ * ‖g‖ + ‖f'‖ * ‖g - g'‖) := by
  analytic_estimate

end Lp
