module

public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Tactic.Linarith

/-!
# Elementary seminorm certificates

These lemmas check finite certificates without using an optimizer or supporting
functionals. The coefficient of the target may be zero; no division is used.
-/

public section

namespace NormArith

open scoped BigOperators

variable {E ι κ : Type*} [AddCommGroup E] [Module ℝ E]

theorem seminorm_sum_bound (p : Seminorm ℝ E) (s : Finset ι) (v : ι → E) :
    p (∑ i ∈ s, v i) ≤ ∑ i ∈ s, p (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (map_add_le_add p _ _).trans (add_le_add (le_refl _) ih)

/-- Check one eliminated support block, including its zero target coefficient. -/
theorem seminorm_block_certificate [Fintype ι]
    (p : Seminorm ℝ E) (v : ι → E) (w : E) (α : ℝ) (βplus βminus : ι → ℝ)
    (hα : 0 ≤ α) (hplus : ∀ i, 0 ≤ βplus i) (hminus : ∀ i, 0 ≤ βminus i)
    (hrep : α • w = ∑ i, (βplus i - βminus i) • v i) :
    α * p w ≤ ∑ i, (βplus i + βminus i) * p (v i) := by
  calc
    α * p w = p (α • w) := by
      rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg hα]
    _ = p (∑ i, (βplus i - βminus i) • v i) := congrArg p hrep
    _ ≤ ∑ i, p ((βplus i - βminus i) • v i) := seminorm_sum_bound p _ _
    _ ≤ ∑ i, (βplus i + βminus i) * p (v i) := by
      apply Finset.sum_le_sum
      intro i _
      rw [map_smul_eq_mul, Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_right _ (apply_nonneg p (v i))
      exact abs_sub_le_iff.mpr ⟨by linarith [hminus i], by linarith [hplus i]⟩

/-- Combine checked block bounds with nonnegative weights and scalar premises. -/
theorem certificate_le [Fintype ι] [Fintype κ]
    (lhs rhs : ι → ℝ) (premise weight : κ → ℝ) (a b : ℝ)
    (hblock : ∀ i, lhs i ≤ rhs i) (hpremise : ∀ k, premise k ≤ 0)
    (hweight : ∀ k, 0 ≤ weight k)
    (hidentity : a - b = ∑ i, (lhs i - rhs i) + ∑ k, weight k * premise k) :
    a ≤ b := by
  have h₁ : ∑ i, (lhs i - rhs i) ≤ 0 :=
    Finset.sum_nonpos fun i _ => sub_nonpos.mpr (hblock i)
  have h₂ : ∑ k, weight k * premise k ≤ 0 :=
    Finset.sum_nonpos fun k _ => mul_nonpos_of_nonneg_of_nonpos (hweight k) (hpremise k)
  linarith

/-- A positively weighted strict premise makes the scalar conclusion strict. -/
theorem certificate_lt [Fintype ι] [Fintype κ]
    (lhs rhs : ι → ℝ) (premise weight : κ → ℝ) (a b : ℝ) (strict : κ)
    (hblock : ∀ i, lhs i ≤ rhs i) (hpremise : ∀ k, premise k ≤ 0)
    (hweight : ∀ k, 0 ≤ weight k) (hstrict : premise strict < 0)
    (hpositive : 0 < weight strict)
    (hidentity : a - b = ∑ i, (lhs i - rhs i) + ∑ k, weight k * premise k) :
    a < b := by
  have h₁ : ∑ i, (lhs i - rhs i) ≤ 0 :=
    Finset.sum_nonpos fun i _ => sub_nonpos.mpr (hblock i)
  have h₂ : ∑ k, weight k * premise k < 0 := by
    apply Finset.sum_neg' (fun k _ =>
      mul_nonpos_of_nonneg_of_nonpos (hweight k) (hpremise k))
    exact ⟨strict, Finset.mem_univ _, mul_neg_of_pos_of_neg hpositive hstrict⟩
  linarith

end NormArith
