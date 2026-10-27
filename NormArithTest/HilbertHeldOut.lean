module

import NormArith.Hilbert

open scoped InnerProductSpace

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

-- From mathlib Analysis/InnerProductSpace/Projection/Minimal.lean, lines 78–104.
-- The source uses `‖v‖ * ‖v‖`; this statement writes the same products as squares.
example (u wp wq : E) :
    4 * ‖u - (1 / 2 : ℝ) • (wq + wp)‖ ^ 2 + ‖wp - wq‖ ^ 2 =
      2 * (‖u - wq‖ ^ 2 + ‖u - wp‖ ^ 2) := by
  hilbert_arith

-- From mathlib Analysis/InnerProductSpace/Basic.lean, lines 525–528.
-- Restrict the scalar field to ℝ and write the norm products as squares.
example (x y : E) :
    ⟪x, y⟫_ℝ = (‖x + y‖ ^ 2 - ‖x - y‖ ^ 2) / 4 := by
  hilbert_arith
