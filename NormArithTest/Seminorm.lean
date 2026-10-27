module

import NormArith.Seminorm

set_option linter.unusedVariables false

/-! Regression tests for explicit seminorms. -/

section

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

example (p : Seminorm ℝ E) (x y : E) : p (x + y) ≤ p x + p y := by
  seminorm_arith

example (p : Seminorm ℝ E) (x y : E) (a b : ℝ)
    (hx : p x ≤ a) (hy : p y ≤ b) : p ((2 : ℝ) • x - y) ≤ 2 * a + b := by
  seminorm_arith

example (p : Seminorm ℝ E) (x y : E) : p x - p y ≤ p (x - y) := by
  seminorm_arith

example (p : Seminorm ℝ E) (x y : E) : p y ≤ p (x + y) + p x := by
  seminorm_arith

example (p : Seminorm ℝ E) (x : E) : p (-((3 / 2 : ℝ) • x)) = (3 / 2) * p x := by
  seminorm_arith

example (p q : Seminorm ℝ E) (x y : E) (a b : ℝ)
    (hx : p x ≤ a) (hy : q y ≤ b) (hbridge : p y ≤ 3 * q y) :
    p ((2 : ℝ) • x - y) ≤ 2 * a + 3 * b := by
  seminorm_arith

example (p q : Seminorm ℝ E) (x y : E) (a b : ℝ)
    (hx : p x ≤ a) (hy : q y ≤ b) (hbridge : ∀ z, p z ≤ 3 * q z) :
    p ((2 : ℝ) • x - y) ≤ 2 * a + 3 * b := by
  seminorm_arith [hbridge y]

-- Different seminorms must never silently be identified.
example (p q : Seminorm ℝ E) (x : E) : True := by
  fail_if_success
    have : p x ≤ q x := by seminorm_arith
  trivial

-- A seminorm may have a nontrivial kernel. No positive-definiteness rule is added.
example (p : Seminorm ℝ E) (x : E) (hx : x ≠ 0) : True := by
  fail_if_success
    have : 0 < p x := by seminorm_arith
  trivial

-- Strict bounds are not obtained from non-strict bounds.
example (p : Seminorm ℝ E) (x : E) (a : ℝ) (hx : p x ≤ a) : True := by
  fail_if_success
    have : p x < a := by seminorm_arith
  trivial

end
