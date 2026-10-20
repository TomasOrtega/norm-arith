module

import NormArith

/-! Integration tests and examples. Every successful example is checked by Lean. -/

-- Nested proof elaboration can annotate an otherwise ordinary norm goal.
example {E : Type*} [SeminormedAddCommGroup E] (x y : E) (a b : ℝ)
    (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ b) : ‖x + y‖ ≤ a + b := no_implicit_lambda% (by
  norm_arith [hx, hy])

section

variable {E : Type*} [SeminormedAddCommGroup E]

-- Telescoping bounds need no scalar structure.
example (w x y z : E) (a b c : ℝ)
    (h₁ : ‖w - x‖ ≤ a) (h₂ : ‖x - y‖ ≤ b) (h₃ : ‖y - z‖ ≤ c) :
    ‖w - z‖ ≤ a + b + c := by
  norm_arith [h₁, h₂, h₃]

-- Signed integer coefficients contribute their magnitudes.
example (x y : E) (a b : ℝ) (hxy : ‖x + y‖ ≤ a) (hy : ‖y‖ ≤ b) :
    ‖x + x + x + y‖ ≤ 3 * a + 2 * b := by
  fail_if_success
    have : ‖x + x + x + y‖ ≤ 3 * a - 2 * b := by norm_arith [hxy, hy]
  norm_arith [hxy, hy]

example (x : E) : ‖x - x‖ ≤ 0 := by
  norm_arith []

-- A failed scalar bound must restore the state before another candidate.
example (x y : E) (a b c : ℝ)
    (_hx : ‖x‖ ≤ c) (hxy : ‖x + y‖ ≤ a) (hy : ‖y‖ ≤ b) : ‖x‖ ≤ a + b := by
  norm_arith [_hx, hxy, hy]

-- Scalar hypotheses outside the supplied bounds remain available.
example (x : E) (a b : ℝ) (hx : ‖x‖ ≤ a) (hab : a ≤ b) : ‖x‖ ≤ b := by
  norm_arith [hx]

end

section

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

-- Discover the cancelling intermediate vector z.
example (x y z : E) (a b : ℝ)
    (hx : ‖x - z‖ ≤ a) (hy : ‖z - y‖ ≤ b) :
    ‖x - y‖ ≤ a + b := by
  norm_arith [hx, hy]

-- The 2020 motivating example: 2a + b = 3a + (b - a).
example (a b : E) : ‖(2 : ℝ) • a + b‖ ≤ 3 * ‖a‖ + ‖b - a‖ := by
  norm_arith [le_refl ‖a‖, le_refl ‖b - a‖]

-- Fractional coefficients: x = (x + y)/2 + (x - y)/2.
example (x y : E) (a b : ℝ)
    (h₁ : ‖x + y‖ ≤ a) (h₂ : ‖x - y‖ ≤ b) :
    ‖x‖ ≤ (a + b) / 2 := by
  norm_arith? [h₁, h₂]

-- A signed coefficient is charged its absolute value.
example (x y : E) (a b : ℝ)
    (h₁ : ‖x + y‖ ≤ a) (h₂ : ‖x - y‖ ≤ b) :
    ‖y‖ ≤ (a + b) / 2 := by
  norm_arith [h₁, h₂]

-- Three-source error decomposition, typical of approximation arguments.
example (x y x' y' : E) (a b M : ℝ)
    (hx : ‖x - x'‖ ≤ a) (hy : ‖y - y'‖ ≤ b)
    (hM : ‖x' + y'‖ ≤ M) :
    ‖x + y‖ ≤ M + a + b := by
  norm_arith [hx, hy, hM]

-- Nontrivial rational solution: x+y = 4/7*(x+2y) + 1/7*(3x-y).
example (x y : E) (a b : ℝ)
    (h₁ : ‖x + (2 : ℝ) • y‖ ≤ a)
    (h₂ : ‖(3 : ℝ) • x - y‖ ≤ b) :
    ‖x + y‖ ≤ (4 * a + b) / 7 := by
  norm_arith [h₁, h₂]

-- Try another decomposition when the first has a weaker bound.
example (x y : E) (a b c : ℝ)
    (_h₀ : ‖x‖ ≤ c) (h₁ : ‖x + y‖ ≤ a) (h₂ : ‖x - y‖ ≤ b) :
    ‖x‖ ≤ (a + b) / 2 := by
  norm_arith [_h₀, h₁, h₂]

-- The zero target has an empty certificate.
example (x : E) : ‖x - x‖ ≤ 0 := by
  norm_arith []

-- A rational scalar in the goal is parsed exactly.
example (x : E) (a : ℝ) (h : ‖x‖ ≤ a) :
    ‖(2 / 3 : ℝ) • x‖ ≤ 2 * a / 3 := by
  norm_arith [h]

-- Failure must leave the goal intact. This supplied bound cannot control y.
example (x y : E) (a : ℝ) (_hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ a) : ‖y‖ ≤ a := by
  fail_if_success norm_arith [_hx]
  exact hy

-- A deliberately unsupported goal shape is rejected.
example (x : E) : x = x := by
  fail_if_success norm_arith []
  rfl

-- A false scalar consequence must not be accepted by candidate search.
example (x : E) (a : ℝ) (h : ‖x‖ ≤ a) : ‖x‖ ≤ a := by
  fail_if_success
    have : ‖x‖ ≤ a - 1 := by norm_arith [h]
  norm_arith [h]

end

-- `norm_num` may already close a goal from an impossible supplied bound.
example (h : ‖(1 : ℝ)‖ ≤ 0) : ‖(2 : ℝ) • (1 : ℝ)‖ ≤ -5 := by
  norm_arith [h]
