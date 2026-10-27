module

import NormArith.FixedPoint

open NormArith
open scoped NNReal

section Banach

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

example (B : X →L[ℝ] X →L[ℝ] X) (a : X) (A : ℝ)
    (hA : 0 ≤ A) (ha : ‖a‖ ≤ A) (hsmall : 8 * ‖B‖ * A ≤ 1) :
    ∃! u, ‖u‖ ≤ 2 * A ∧ a + B u u = u := by
  analytic_estimate

example (B : X →L[ℝ] X →L[ℝ] X) (a : X) (A K : ℝ)
    (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hB : ∀ x y, ‖B x y‖ ≤ K * ‖x‖ * ‖y‖)
    (ha : ‖a‖ ≤ A) (hsmall : 8 * K * A ≤ 1) :
    ∃! u, ‖u‖ ≤ 2 * A ∧ a + B u u = u := by
  exact quadratic_existsUnique B a hA hK hB ha hsmall

-- A supplied radius can differ from the default template.
example (B : X →L[ℝ] X →L[ℝ] X) (a : X)
    (hB : ∀ x y, ‖B x y‖ ≤ (1 / 12 : ℝ) * ‖x‖ * ‖y‖)
    (ha : ‖a‖ ≤ 2) : ∃! u, ‖u‖ ≤ 3 ∧ a + B u u = u := by
  exact quadratic_existsUnique_of_radius B a (q := (1 / 2 : ℝ≥0))
    (by norm_num) (by norm_num) (by norm_num) hB ha (by norm_num) (by norm_num)

example (a : X) (A : ℝ) (hA : 0 ≤ A) (ha : ‖a‖ ≤ A) :
    ∃! u, ‖u‖ ≤ 2 * A ∧ a + (0 : X →L[ℝ] X →L[ℝ] X) u u = u := by
  apply quadratic_existsUnique (0 : X →L[ℝ] X →L[ℝ] X) a hA (K := 0)
    (by norm_num) (by simp) ha
  norm_num

end Banach

section Estimates

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

example (B : X →L[ℝ] X →L[ℝ] X) (a b u v : X) (A K : ℝ)
    (hK : 0 ≤ K) (hB : ∀ x y, ‖B x y‖ ≤ K * ‖x‖ * ‖y‖)
    (hu : ‖u‖ ≤ 2 * A) (hv : ‖v‖ ≤ 2 * A) (hsmall : 8 * K * A ≤ 1)
    (hfu : a + B u u = u) (hfv : b + B v v = v) :
    ‖u - v‖ ≤ 2 * ‖a - b‖ := by
  exact quadratic_stability B hK hB hu hv hsmall hfu hfv

example (B : X →L[ℝ] X →L[ℝ] X) (a u w : X) (A K : ℝ)
    (hK : 0 ≤ K) (hB : ∀ x y, ‖B x y‖ ≤ K * ‖x‖ * ‖y‖)
    (hu : ‖u‖ ≤ 2 * A) (hw : ‖w‖ ≤ 2 * A) (hsmall : 8 * K * A ≤ 1)
    (hfix : a + B u u = u) : ‖u - w‖ ≤ 2 * ‖w - (a + B w w)‖ := by
  exact quadratic_residual B hK hB hu hw hsmall hfix

-- This result needs no completeness assumption or division by the radius.
example (B : X →L[ℝ] X →L[ℝ] X) :
    ∃! u, ‖u‖ ≤ (0 : ℝ) ∧ (0 : X) + B u u = u := by
  exact quadratic_zero_radius B

end Estimates

-- The quadratic equation can have more fixed points outside the chosen ball.
example : ¬ ∃! u : ℝ, u * u = u := by
  rintro ⟨u, _, hu⟩
  have hzero := hu 0 (by norm_num)
  have hone := hu 1 (by norm_num)
  linarith

-- A Lipschitz constant equal to one does not give uniqueness, even on a ball.
example : ¬ ∃! u : ℝ, ‖u‖ ≤ 1 ∧ id u = u := by
  rintro ⟨u, _, hu⟩
  have hzero := hu 0 (by norm_num)
  have hone := hu 1 (by norm_num)
  linarith
