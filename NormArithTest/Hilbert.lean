module

import NormArith.Hilbert

open scoped InnerProductSpace
open NormArith.Hilbert

meta section

#guard (factor #[#[1, -1], #[-1, 1]]).isOk
#guard (factor #[#[0, 0], #[0, 2]]).isOk
#guard !(factor #[#[0, 1], #[1, 0]]).isOk
#guard !(factor #[#[1, 2], #[2, 1]]).isOk
#guard !(factor #[#[1, 0], #[1, 1]]).isOk
#guard !checkFactor #[#[1, 0], #[0, 1]] #[{ weight := -1, row := #[1, 0] }]
#guard !checkFactor #[#[1, -1], #[-1, 1]] #[{ weight := 1, row := #[1, 1] }]

end

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

example (x y : E) : ‖x + y‖ ^ 2 ≤ (3 / 2 : ℝ) * ‖x‖ ^ 2 + 3 * ‖y‖ ^ 2 := by
  hilbert_arith

example (x y : E) : ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  hilbert_arith

example (x y : E) : 2 * ⟪x, y⟫_ℝ ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  hilbert_arith

example (x y : E) : ‖x - (2 : ℝ) • y‖ ^ 2 ≥ 0 := by
  hilbert_arith

example (x y z : E) : ‖x + y + z‖ ^ 2 ≤ 3 * (‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2) := by
  hilbert_arith

example (x y : E) : ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  fail_if_success
    have : ‖x + y‖ ^ 2 ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2 := by hilbert_arith
  hilbert_arith

example (x : E) : 0 ≤ ‖x‖ ^ 2 := by
  fail_if_success
    have : 0 < ‖x‖ ^ 2 := by hilbert_arith
  hilbert_arith

-- Replay names the square and checks its identity without factor search.
example (x y : E) : ‖x + y‖ ^ 2 ≤ (3 / 2 : ℝ) * ‖x‖ ^ 2 + 3 * ‖y‖ ^ 2 := by
  apply le_of_squares (s := (1 / 2 : ℝ) * ‖x - (2 : ℝ) • y‖ ^ 2)
  · positivity
  · hilbert_nf

-- Changing a square invalidates the replay identity.
example (x y : E) : ‖x + y‖ ^ 2 ≤ (3 / 2 : ℝ) * ‖x‖ ^ 2 + 3 * ‖y‖ ^ 2 := by
  fail_if_success
    solve
      | apply le_of_squares (s := (1 / 2 : ℝ) * ‖x + (2 : ℝ) • y‖ ^ 2)
        · positivity
        · hilbert_nf
  hilbert_arith
