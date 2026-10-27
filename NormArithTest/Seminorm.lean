module

import NormArith.Seminorm
import Mathlib.Analysis.Normed.Module.Seminorm.Norm

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
  seminorm_arith [hx, hy, hbridge y]

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

section CompactLP

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

example (p : Seminorm ℝ E) (x y : E) :
    2 * p x ≤ p (x + y) + p (x - y) := by
  seminorm_arith

example (p q : Seminorm ℝ E) (x y : E) :
    2 * p x + 2 * q y ≤ p (x + y) + p (x - y) + q (x + y) + q (x - y) := by
  seminorm_arith

example (p : Seminorm ℝ E) (x y z : E)
    (h : (5 : ℝ) • x = (2 : ℝ) • y - (3 : ℝ) • z) :
    5 * p x ≤ 2 * p y + 3 * p z := by
  seminorm_arith [h]

example (p q : Seminorm ℝ E) (x y : E) (a b : ℝ)
    (hx : p x ≤ a) (hy : q y ≤ b) (hbridge : ∀ z, p z ≤ 3 * q z) :
    p ((2 : ℝ) • x - y) ≤ 2 * a + 3 * b := by
  seminorm_arith [hx, hy, hbridge]

example (p : Seminorm ℝ E) (x y : E) (a b : ℝ)
    (hx : p (x + y) < a) (hy : p (x - y) ≤ b) : 2 * p x < a + b := by
  seminorm_arith [hx, hy]

example (p : Seminorm ℝ E) (x : E) (a : ℝ) (hidden : p x ≤ a) : True := by
  fail_if_success
    have : p x ≤ a := by seminorm_arith []
  trivial

end CompactLP

set_option seminorm_arith.forceLP true
section ForcedLP

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

example (p : Seminorm ℝ E) (x y : E) :
    2 * p x ≤ p (x + y) + p (x - y) := by
  seminorm_arith

example (p q : Seminorm ℝ E) (x y : E) :
    2 * p x + 2 * q y ≤ p (x + y) + p (x - y) + q (x + y) + q (x - y) := by
  seminorm_arith

-- A derivative must be supplied as a linear map on its function space.
example (D : E →ₗ[ℝ] F) (p : Seminorm ℝ F) (u v : E) :
    2 * (p.comp D) u ≤ (p.comp D) (u + v) + (p.comp D) (u - v) := by
  seminorm_arith

example (p q : Seminorm ℝ E) (x y : E) :
    2 * (p + q) x ≤ (p + q) (x + y) + (p + q) (x - y) := by
  seminorm_arith

example (p q : Seminorm ℝ E) (x y : E) :
    2 * (p ⊔ q) x ≤ (p ⊔ q) (x + y) + (p ⊔ q) (x - y) := by
  seminorm_arith

example (p q : Seminorm ℝ E) (x : E) : True := by
  fail_if_success
    have : p x ≤ q x := by seminorm_arith
  trivial

example (D₁ D₂ : E →ₗ[ℝ] F) (p : Seminorm ℝ F) (u : E) : True := by
  fail_if_success
    have : (p.comp D₁) u ≤ (p.comp D₂) u := by seminorm_arith
  trivial

example (p : Seminorm ℝ E) (x y : E) (hx : p (x - y) = 0) : True := by
  fail_if_success
    have : x = y := by seminorm_arith
  trivial

example (p : Seminorm ℝ E) (x y : E) (a b : ℝ)
    (hx : p (x + y) ≤ a) (hy : p (x - y) ≤ b) : True := by
  fail_if_success
    have : 2 * p x < a + b := by seminorm_arith [hx, hy]
  trivial

end ForcedLP

set_option seminorm_arith.forceLP false

set_option seminorm_arith.forceLP true in
example {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    (p : Seminorm ℝ E) (x y : E) (u v : F) :
    2 * p x + 2 * ‖u‖ ≤ p (x + y) + p (x - y) + ‖u + v‖ + ‖u - v‖ := by
  seminorm_arith

set_option seminorm_arith.forceLP true in
example {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] (x y : E) :
    2 * (normSeminorm ℝ E) x ≤ ‖x + y‖ + ‖x - y‖ := by
  seminorm_arith

set_option seminorm_arith.forceLP true in
example (x y : ℝ) : 2 * ‖x‖ ≤ ‖x + y‖ + ‖x - y‖ := by
  seminorm_arith

-- An explicit different norm instance has no automatic bridge to the ambient norm.
set_option seminorm_arith.forceLP true in
example {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (other : Norm E) (x : E) : True := by
  fail_if_success
    have : @Norm.norm E other x ≤ ‖x‖ := by seminorm_arith
  trivial

-- A raw function does not supply a derivative linearity theorem.
set_option seminorm_arith.forceLP true in
example {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (D : E → F) (p : Seminorm ℝ F) (u v : E) : True := by
  fail_if_success
    have : p (D (u + v)) ≤ p (D u) + p (D v) := by seminorm_arith
  trivial
