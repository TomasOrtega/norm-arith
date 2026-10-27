module

import NormArith.Analysis

set_option linter.unusedVariables false

namespace RuleTests

open scoped ENNReal

private def firstStep (x : ℝ) := x + 1
private def secondStep (x : ℝ) := x + 2

private theorem first_bound {x a : ℝ} (h : x ≤ a) : firstStep x ≤ a + 1 := by
  unfold firstStep
  linarith

private theorem second_bound {x a : ℝ} (h : x ≤ a) : secondStep x ≤ a + 2 := by
  unfold secondStep
  linarith

section

attribute [local analytic_rule] first_bound second_bound

example (x a : ℝ) (h : x ≤ a) : secondStep (firstStep x) ≤ (a + 1) + 2 := by
  analytic_estimate

example (x a : ℝ) : True := by
  fail_if_success
    have : secondStep (firstStep x) ≤ (a + 1) + 2 := by analytic_estimate
  trivial

end

private theorem circular {x a : ℝ} (h : firstStep x ≤ a) : firstStep x ≤ a := h

section

attribute [local analytic_rule] circular

example (x a : ℝ) : True := by
  fail_if_success
    have : firstStep x ≤ a := by analytic_estimate
  trivial

end

-- A selected norm premise is available, and pure scalar comparisons remain local.
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (a b : ℝ) (hx : ‖x‖ ≤ a) (hab : a ≤ b) : ‖x‖ ≤ b := by
  analytic_estimate [hx]

private class HiddenBound {E : Type*} [NormedAddCommGroup E] (x : E) (a : ℝ) : Prop where
  bound : ‖x‖ ≤ a

private theorem hidden_bound {E : Type*} [NormedAddCommGroup E]
    (x : E) (a : ℝ) [HiddenBound x a] : ‖x‖ ≤ a := HiddenBound.bound

section

attribute [local analytic_rule] hidden_bound

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (a : ℝ) [HiddenBound x a] : True := by
  fail_if_success
    have : ‖x‖ ≤ a := by analytic_estimate []
  trivial

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (a : ℝ) [h : HiddenBound x a] : ‖x‖ ≤ a := by
  analytic_estimate [h]

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (a : ℝ) [HiddenBound x a] : ‖x‖ ≤ a := by
  analytic_estimate

end

private class HiddenDataBound {E : Type*} [NormedAddCommGroup E]
    (x : E) (a : ℝ) : Type where
  bound : ‖x‖ ≤ a

private theorem hidden_data_bound {E : Type*} [NormedAddCommGroup E]
    (x : E) (a : ℝ) [HiddenDataBound x a] : ‖x‖ ≤ a := HiddenDataBound.bound

section

attribute [local analytic_rule] hidden_data_bound

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (a : ℝ) [HiddenDataBound x a] : True := by
  fail_if_success
    have : ‖x‖ ≤ a := by analytic_estimate []
  trivial

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (a : ℝ) [HiddenDataBound x a] : ‖x‖ ≤ a := by
  analytic_estimate [HiddenDataBound.bound (x := x) (a := a)]

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (a : ℝ) [HiddenDataBound x a] : ‖x‖ ≤ a := by
  analytic_estimate

end

private theorem fact_bound {E : Type*} [NormedAddCommGroup E]
    (x : E) (a : ℝ) [Fact (‖x‖ ≤ a)] : ‖x‖ ≤ a := Fact.out

section

attribute [local analytic_rule] fact_bound

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (a : ℝ) [h : Fact (‖x‖ ≤ a)] : ‖x‖ ≤ a := by
  fail_if_success analytic_estimate []
  analytic_estimate [h]

end

private theorem nonempty_bound {E : Type*} [NormedAddCommGroup E]
    (x : E) (a : ℝ) [h : Nonempty (‖x‖ ≤ a)] : ‖x‖ ≤ a := Classical.choice h

section

attribute [local analytic_rule] nonempty_bound

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (a : ℝ) [Nonempty (‖x‖ ≤ a)] : True := by
  fail_if_success
    have : ‖x‖ ≤ a := by analytic_estimate []
  trivial

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (a : ℝ) (h : Nonempty (‖x‖ ≤ a)) : True := by
  let Bound := ‖x‖ ≤ a
  have : Nonempty Bound := h
  clear h
  fail_if_success
    have : ‖x‖ ≤ a := by analytic_estimate []
  trivial

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (a : ℝ) [h : Nonempty (‖x‖ ≤ a)] : ‖x‖ ≤ a := by
  analytic_estimate [h]

end

private theorem nontrivial_bound {E : Type*} [NormedAddCommGroup E]
    (x : E) (a : ℝ) [Nontrivial {n : ℕ // ‖x‖ ≤ a}] : ‖x‖ ≤ a :=
  (Classical.choice (inferInstance : Nonempty {n : ℕ // ‖x‖ ≤ a})).property

section

attribute [local analytic_rule] nontrivial_bound

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (a : ℝ) [Nontrivial {n : ℕ // ‖x‖ ≤ a}] : True := by
  fail_if_success
    have : ‖x‖ ≤ a := by analytic_estimate []
  trivial

end

private theorem subsingleton_bound {E : Type*} [NormedAddCommGroup E]
    (x : E) (a : ℝ) [Subsingleton {n : ℕ // ¬ ‖x‖ ≤ a}] : ‖x‖ ≤ a := by
  by_contra h
  have heq : (⟨0, h⟩ : {n : ℕ // ¬ ‖x‖ ≤ a}) = ⟨1, h⟩ := Subsingleton.elim _ _
  have := congrArg Subtype.val heq
  norm_num at this

section

attribute [local analytic_rule] subsingleton_bound

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (a : ℝ) [Subsingleton {n : ℕ // ¬ ‖x‖ ≤ a}] : True := by
  fail_if_success
    have : ‖x‖ ≤ a := by analytic_estimate []
  trivial

end

private theorem finite_bound {E : Type*} [NormedAddCommGroup E]
    (x : E) (a : ℝ) [Finite {n : ℕ // ¬ ‖x‖ ≤ a}] : ‖x‖ ≤ a := by
  by_contra h
  have : Finite ℕ := Finite.of_injective (fun n : ℕ => (⟨n, h⟩ : {n : ℕ // ¬ ‖x‖ ≤ a}))
    (fun _ _ heq => congrArg Subtype.val heq)
  exact not_finite ℕ

section

attribute [local analytic_rule] finite_bound

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (a : ℝ) [Finite {n : ℕ // ¬ ‖x‖ ≤ a}] : True := by
  fail_if_success
    have : ‖x‖ ≤ a := by analytic_estimate []
  trivial

end

example {α : Type*} [Nonempty α] : Nonempty α := by analytic_estimate []
example {α : Type*} [Nontrivial α] : Nontrivial α := by analytic_estimate []
example {α : Type*} [Subsingleton α] : Subsingleton α := by analytic_estimate []
example {α : Type*} [Finite α] : Finite α := by analytic_estimate []

private def completeReady {E : Type*} [NormedAddCommGroup E] (x : E) : Prop := ‖x‖ ≤ ‖x‖

private theorem complete_ready {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (x : E) : completeReady x := le_rfl

private def holderReady (p q r : ℝ≥0∞) : Prop := ENNReal.HolderTriple p q r

private theorem holder_ready (p q r : ℝ≥0∞) [ENNReal.HolderTriple p q r] :
    holderReady p q r := (inferInstance : ENNReal.HolderTriple p q r)

section

attribute [local analytic_rule] complete_ready holder_ready

example {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] (x : E) : completeReady x := by
  analytic_estimate []

example (p q r : ℝ≥0∞) [ENNReal.HolderTriple p q r] : holderReady p q r := by
  analytic_estimate []

end

end RuleTests

example {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : Seminorm ℝ E) (x y : E) : 2 * p x ≤ p (x + y) + p (x - y) := by
  analytic_estimate
