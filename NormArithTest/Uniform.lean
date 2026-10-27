module

import NormArith.Analysis

-- Choose the constant before introducing the vector.
example {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F] (T : E →L[ℝ] F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖T x‖ ≤ C * ‖x‖ := by
  refine ⟨‖T‖, norm_nonneg _, ?_⟩
  intro x
  analytic_estimate

example : (∀ x : ℝ, ∃ C, ‖x‖ ≤ C) ∧ ¬ ∃ C, ∀ x : ℝ, ‖x‖ ≤ C := by
  constructor
  · intro x
    exact ⟨‖x‖, le_refl _⟩
  · rintro ⟨C, hC⟩
    have h := hC (C + 1)
    have h' := Real.le_norm_self (C + 1)
    linarith

set_option linter.unusedVariables false in
example (hpoint : ∀ x : ℝ, ∃ C, ‖x‖ ≤ C) : True := by
  fail_if_success
    have : ∃ C, ∀ x : ℝ, ‖x‖ ≤ C := by analytic_estimate [hpoint]
  trivial
