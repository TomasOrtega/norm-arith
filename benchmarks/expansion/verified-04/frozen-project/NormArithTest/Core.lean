module

import NormArith

section

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

set_option linter.unusedTactic false in
example (x y : E) (a b : ℝ) (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ b) :
    ‖x + y‖ ≤ a + b := by
  run_tac Lean.Elab.Tactic.withMainContext do
    let target ← Lean.Elab.Tactic.getMainTarget
    let fragment ← NormArith.goalFragment target
    unless fragment == "core" && (← NormArith.isCoreGoal target) do
      throwError "expected real-space core classification, got {fragment}"
  norm_arith

example (x : E) : (‖x‖ ≤ ‖x‖) ∧ True := by
  constructor
  norm_arith
  trivial

example (x : E) (a : ℝ) (hx : ‖x‖ ≤ a) : 0 ≤ a := by
  norm_arith

example (t w x y z : E) (h : (2 : ℝ) • t = w + x + y + z) :
    2 * ‖t‖ ≤ ‖w‖ + ‖x‖ + ‖y‖ + ‖z‖ := by
  norm_arith

example (x y : E) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := by
  norm_arith

example (x y : E) (a b : ℝ) (hx : ‖x‖ < a) (hy : ‖y‖ ≤ b) :
    ‖x + y‖ < a + b := by
  norm_arith

example (x y : E) : ‖x‖ - ‖y‖ ≤ ‖x - y‖ := by
  norm_arith

example (x y : E) (a : ℝ) (hxy : x = y) (hy : ‖y‖ ≤ a) : ‖x‖ ≤ a := by
  norm_arith

example (x y z : E) (a b : ℝ) (hx : dist x z ≤ a) (hy : dist z y ≤ b) :
    dist x y ≤ a + b := by
  norm_arith

example (x y : E) : ‖x + y‖ + ‖x - y‖ ≥ 2 * ‖x‖ := by
  norm_arith

example (x : E) : ‖(3 / 2 : ℝ) • x‖ = 3 * ‖x‖ / 2 := by
  norm_arith

example (w x y z : E) (a b c d : ℝ)
    (hw : ‖w‖ ≤ a) (hx : ‖x‖ ≤ b) (hy : ‖y‖ ≤ c) (hz : ‖z‖ ≤ d) :
    ‖w + x + y + z‖ ≤ a + b + c + d := by
  norm_arith

example (x y : E) (a b : ℝ) (hx : ‖x + y‖ ≤ a) (hy : ‖x - y‖ ≤ b) :
    ‖x‖ ≤ (a + b) / 2 := by
  norm_arith

example (x y : E) (a b : ℝ) (hy : dist y x ≤ a)
    (h : y ∈ Metric.closedBall x a → ‖y‖ ≤ b) : ‖y‖ ≤ b := by
  norm_arith [h (Metric.mem_closedBall.2 hy)]

example (x y : E) (a b : ℝ) (h : ‖x + y‖ < a) (hy : ‖y‖ ≤ b) :
    ‖x‖ < a + b := by
  norm_arith

example (x y : E) (a b : ℝ) (hx : ‖x + y‖ ≤ a) (hy : ‖x - y‖ ≤ b) :
    ‖x‖ + ‖y‖ ≤ a + b := by
  norm_arith

example (x y z : E) (h : (2 : ℝ) • x = y + z) :
    ‖x‖ ≤ (‖y‖ + ‖z‖) / 2 := by
  norm_arith

example (x y : E) (a b : ℝ) (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ b) :
    ‖x + y‖ ≤ a + b := by
  fail_if_success
    have : ‖x + y‖ < a + b := by norm_arith
  norm_arith

example (x y : E) (a : ℝ) (_hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ a) : ‖y‖ ≤ a := by
  let t := ‖y‖
  have ht : t ≤ a := hy
  fail_if_success norm_arith [_hx]
  norm_arith

example (x y : E) (a b : ℝ) (_hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ b) :
    ‖x + y‖ ≤ a + b := by
  let t := ‖y‖
  have ht : t ≤ b := hy
  clear hy
  norm_arith

example {F : Type*} [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    (x y : E) (u v : F) : ‖x + y‖ + ‖u + v‖ ≤ ‖x‖ + ‖y‖ + ‖u‖ + ‖v‖ := by
  norm_arith

example (x : E) : ‖x‖ ≤ ‖x‖ := by
  fail_if_success
    have : ‖x‖ < 0 := by norm_arith
  norm_arith

end

section

variable {E : Type*} [SeminormedAddCommGroup E]

example [SMul ℝ E] (x y : E) :
    ‖(1 / 2 : ℝ) • x + y‖ ≤ ‖(1 / 2 : ℝ) • x‖ + ‖y‖ := by
  norm_arith

set_option linter.unusedTactic false in
example (x : E) : ‖x‖ ≤ ‖x‖ := by
  run_tac Lean.Elab.Tactic.withMainContext do
    let fragment ← NormArith.goalFragment (← Lean.Elab.Tactic.getMainTarget)
    unless fragment == "additive_group_extension" do
      throwError "expected additive-group classification, got {fragment}"
  norm_arith

example [Module ℝ E] (x : E) (a : ℝ) (h : ‖(2 : ℝ) • x‖ ≤ a) :
    ‖(2 : ℝ) • x‖ ≤ a := by
  fail_if_success
    have : ‖x‖ ≤ a / 2 := by norm_arith
  exact h

example (x y z : E) : ‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖ := by
  norm_arith

example (x : E) (a b : ℝ) (h₂ : ‖x + x‖ ≤ a) (h₃ : ‖x + x + x‖ ≤ b) :
    ‖x‖ ≤ a + b := by
  norm_arith

example (x : E) (a : ℝ) (h : ‖x + x‖ ≤ a) : ‖x + x‖ ≤ a := by
  fail_if_success
    have : ‖x‖ ≤ a / 2 := by norm_arith
  exact h

end

set_option linter.unusedTactic false in
example {X : Type*} [PseudoMetricSpace X] (x y : X) : dist x y ≤ dist x y := by
  run_tac Lean.Elab.Tactic.withMainContext do
    let target ← Lean.Elab.Tactic.getMainTarget
    let fragment ← NormArith.goalFragment target
    unless fragment == "metric_extension" && !(← NormArith.isCoreGoal target) do
      throwError "expected separate metric extension, got {fragment}"
  norm_arith
