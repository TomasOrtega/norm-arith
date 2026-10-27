module

public import NormArith.Analysis
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# Fixed points of small quadratic maps

The radius and contraction constant are explicit inputs. The template `R = 2 * A`
uses the condition `8 * K * A ≤ 1`. Uniqueness is restricted to the stated ball.
The same contraction bound proves stability and residual estimates.
-/

public section

namespace NormArith

open scoped NNReal

section Ball

variable {X : Type*} [NormedAddCommGroup X]

/-- A contraction bound on a closed ball gives a residual estimate. -/
theorem ball_residual_bound (f : X → X) {R q : ℝ}
    (hq : q < 1)
    (hcontract : ∀ u v, ‖u‖ ≤ R → ‖v‖ ≤ R → ‖f u - f v‖ ≤ q * ‖u - v‖)
    {u w : X} (hu : ‖u‖ ≤ R) (hw : ‖w‖ ≤ R) (hfix : f u = u) :
    ‖u - w‖ ≤ ‖w - f w‖ / (1 - q) := by
  have hc := hcontract u w hu hw
  have ht := norm_sub_le_norm_sub_add_norm_sub (f u) (f w) w
  rw [hfix] at hc ht
  rw [norm_sub_rev (f w) w] at ht
  apply (le_div_iff₀ (sub_pos.mpr hq)).2
  nlinarith

/-- Two fixed points in one certified ball must agree. -/
theorem ball_fixed_point_unique (f : X → X) {R q : ℝ}
    (hq : q < 1)
    (hcontract : ∀ u v, ‖u‖ ≤ R → ‖v‖ ≤ R → ‖f u - f v‖ ≤ q * ‖u - v‖)
    {u v : X} (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R) (hfu : f u = u) (hfv : f v = v) :
    u = v := by
  have h := ball_residual_bound f hq hcontract hu hv hfu
  rw [hfv, sub_self, norm_zero, zero_div] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

/-- Apply Banach's theorem to the restricted map on a nonempty closed ball. -/
theorem existsUnique_fixed_point_in_ball [CompleteSpace X]
    (f : X → X) {R : ℝ} {q : ℝ≥0} (hR : 0 ≤ R) (hq : q < 1)
    (hmap : ∀ u, ‖u‖ ≤ R → ‖f u‖ ≤ R)
    (hcontract : ∀ u v, ‖u‖ ≤ R → ‖v‖ ≤ R →
      ‖f u - f v‖ ≤ (q : ℝ) * ‖u - v‖) :
    ∃! u, ‖u‖ ≤ R ∧ f u = u := by
  let s := Metric.closedBall (0 : X) R
  have hs : Set.MapsTo f s s := by
    intro u hu
    exact (mem_closedBall_zero_iff).2 (hmap u ((mem_closedBall_zero_iff).1 hu))
  have hc : ContractingWith q (hs.restrict f s s) := by
    refine ⟨hq, LipschitzWith.of_dist_le_mul fun u v => ?_⟩
    change dist (f u) (f v) ≤ (q : ℝ) * dist (u : X) (v : X)
    simpa only [dist_eq_norm] using
      hcontract u v ((mem_closedBall_zero_iff).1 u.property)
        ((mem_closedBall_zero_iff).1 v.property)
  obtain ⟨u, hu, hfix, _⟩ := hc.exists_fixedPoint'
    (Metric.isClosed_closedBall.isComplete) hs
    (show (0 : X) ∈ s from (mem_closedBall_zero_iff).2 (by simpa using hR))
    (edist_ne_top _ _)
  have hur : ‖u‖ ≤ R := (mem_closedBall_zero_iff).1 hu
  refine ⟨u, ⟨hur, hfix⟩, ?_⟩
  intro v hv
  exact ball_fixed_point_unique f (show (q : ℝ) < 1 from hq)
    hcontract hv.1 hur hv.2 hfix

end Ball

section Quadratic

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Check a radius using a supplied bilinear bound. -/
theorem quadratic_ball_bound_of_radius (B : X →L[𝕜] X →L[𝕜] X) (a u : X)
    {A K R : ℝ} (hK : 0 ≤ K)
    (hB : ∀ x y, ‖B x y‖ ≤ K * ‖x‖ * ‖y‖)
    (ha : ‖a‖ ≤ A) (hu : ‖u‖ ≤ R) (hbudget : A + K * R ^ 2 ≤ R) :
    ‖a + B u u‖ ≤ R := by
  have hsq := mul_self_le_mul_self (norm_nonneg u) hu
  have hm := mul_le_mul_of_nonneg_left hsq hK
  have hb := hB u u
  have ht := norm_add_le a (B u u)
  nlinarith

/-- Check the Lipschitz constant using the same bilinear bound. -/
theorem quadratic_contraction_bound_of_radius (B : X →L[𝕜] X →L[𝕜] X)
    (a u v : X) {K R q : ℝ} (hK : 0 ≤ K)
    (hB : ∀ x y, ‖B x y‖ ≤ K * ‖x‖ * ‖y‖)
    (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R) (hbudget : 2 * K * R ≤ q) :
    ‖(a + B u u) - (a + B v v)‖ ≤ q * ‖u - v‖ := by
  have heq : B u u - B v v = B (u - v) u + B v (u - v) := by
    simp only [map_sub, sub_apply]
    abel
  have ht := norm_add_le (B (u - v) u) (B v (u - v))
  have hb₁ := hB (u - v) u
  have hb₂ := hB v (u - v)
  have hsum := mul_le_mul_of_nonneg_left (add_le_add hu hv) hK
  have hfinal := mul_le_mul_of_nonneg_right hbudget (norm_nonneg (u - v))
  have hscaled := mul_le_mul_of_nonneg_right hsum (norm_nonneg (u - v))
  rw [add_sub_add_left_eq_sub, heq]
  nlinarith

/-- Any radius that passes both scalar checks gives existence and ball uniqueness. -/
theorem quadratic_existsUnique_of_radius [CompleteSpace X]
    (B : X →L[𝕜] X →L[𝕜] X) (a : X) {A K R : ℝ} {q : ℝ≥0}
    (hK : 0 ≤ K) (hR : 0 ≤ R) (hq : q < 1)
    (hB : ∀ x y, ‖B x y‖ ≤ K * ‖x‖ * ‖y‖) (ha : ‖a‖ ≤ A)
    (hball : A + K * R ^ 2 ≤ R) (hcontraction : 2 * K * R ≤ q) :
    ∃! u, ‖u‖ ≤ R ∧ a + B u u = u := by
  apply existsUnique_fixed_point_in_ball (fun u => a + B u u) hR hq
  · intro u hu
    exact quadratic_ball_bound_of_radius B a u hK hB ha hu hball
  · intro u v hu hv
    exact quadratic_contraction_bound_of_radius B a u v hK hB hu hv hcontraction

/-- The radius `2 * A` also works when `A = 0` or `K = 0`. -/
theorem quadratic_existsUnique [CompleteSpace X]
    (B : X →L[𝕜] X →L[𝕜] X) (a : X) {A K : ℝ}
    (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hB : ∀ x y, ‖B x y‖ ≤ K * ‖x‖ * ‖y‖)
    (ha : ‖a‖ ≤ A) (hsmall : 8 * K * A ≤ 1) :
    ∃! u, ‖u‖ ≤ 2 * A ∧ a + B u u = u := by
  apply quadratic_existsUnique_of_radius B a (q := (1 / 2 : ℝ≥0)) hK
    (by positivity) (by norm_num) hB ha
  · have h := mul_le_mul_of_nonneg_right hsmall hA
    nlinarith
  · norm_num
    nlinarith

/-- Use the operator norm when no separate bilinear constant is supplied. -/
theorem quadratic_existsUnique_of_opNorm [CompleteSpace X]
    (B : X →L[𝕜] X →L[𝕜] X) (a : X) {A : ℝ}
    (hA : 0 ≤ A) (ha : ‖a‖ ≤ A) (hsmall : 8 * ‖B‖ * A ≤ 1) :
    ∃! u, ‖u‖ ≤ 2 * A ∧ a + B u u = u :=
  quadratic_existsUnique B a hA (norm_nonneg B) (bilinear_apply_bound B) ha hsmall

/-- Fixed points for nearby forcing terms remain close inside the common ball. -/
theorem quadratic_stability (B : X →L[𝕜] X →L[𝕜] X) {a b u v : X} {A K : ℝ}
    (hK : 0 ≤ K) (hB : ∀ x y, ‖B x y‖ ≤ K * ‖x‖ * ‖y‖)
    (hu : ‖u‖ ≤ 2 * A) (hv : ‖v‖ ≤ 2 * A) (hsmall : 8 * K * A ≤ 1)
    (hfu : a + B u u = u) (hfv : b + B v v = v) :
    ‖u - v‖ ≤ 2 * ‖a - b‖ := by
  have hc := quadratic_contraction_bound_of_radius B a u v hK hB hu hv
    (q := (1 / 2 : ℝ)) (by nlinarith)
  have heq : u - v = ((a + B u u) - (a + B v v)) + (a - b) := by
    calc
      u - v = (a + B u u) - (b + B v v) := by rw [hfu, hfv]
      _ = ((a + B u u) - (a + B v v)) + (a - b) := by abel
  have ht := norm_add_le ((a + B u u) - (a + B v v)) (a - b)
  rw [← heq] at ht
  linarith

/-- A residual controls the error of any approximate solution in the ball. -/
theorem quadratic_residual (B : X →L[𝕜] X →L[𝕜] X) {a u w : X} {A K : ℝ}
    (hK : 0 ≤ K) (hB : ∀ x y, ‖B x y‖ ≤ K * ‖x‖ * ‖y‖)
    (hu : ‖u‖ ≤ 2 * A) (hw : ‖w‖ ≤ 2 * A) (hsmall : 8 * K * A ≤ 1)
    (hfix : a + B u u = u) : ‖u - w‖ ≤ 2 * ‖w - (a + B w w)‖ := by
  have h := ball_residual_bound (fun v => a + B v v)
    (q := (1 / 2 : ℝ)) (by norm_num)
    (fun x y hx hy => quadratic_contraction_bound_of_radius B a x y hK hB hx hy
      (by nlinarith)) hu hw hfix
  norm_num at h
  linarith

/-- A zero radius contains only zero, so it needs no smallness argument. -/
theorem quadratic_zero_radius (B : X →L[𝕜] X →L[𝕜] X) :
    ∃! u, ‖u‖ ≤ (0 : ℝ) ∧ (0 : X) + B u u = u := by
  refine ⟨0, by simp, ?_⟩
  intro u hu
  exact norm_eq_zero.mp (le_antisymm hu.1 (norm_nonneg u))

attribute [analytic_rule] quadratic_existsUnique_of_opNorm quadratic_zero_radius

attribute [analytic_rule] quadratic_existsUnique_of_opNorm

end Quadratic

end NormArith
