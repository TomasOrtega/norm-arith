/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
/-
Standalone adapted estimate from Mathlib/Analysis/Calculus/FDeriv/Measurable.lean.
Pinned source and adaptations: Benchmarks/manifest.json (DerivativeThreeStep).
-/
module

import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Tactic
import NormArith

variable {E : Type*} [SeminormedAddCommGroup E]

-- BENCHMARK-STATEMENT
example (L : ℕ → ℕ → ℕ → E) (c : ℝ) (e p q e' p' q' r : ℕ)
    (J1 : ‖L e p q - L e p r‖ ≤ 4 * ‖c‖ * (1 / 2) ^ e)
    (J2 : ‖L e p r - L e' p' r‖ ≤ 4 * ‖c‖ * (1 / 2) ^ e)
    (J3 : ‖L e' p' r - L e' p' q'‖ ≤ 4 * ‖c‖ * (1 / 2) ^ e) :
    ‖L e p q - L e' p' q'‖ ≤ 12 * ‖c‖ * (1 / 2) ^ e := by
  -- BENCHMARK-PROOF
  norm_arith
  -- BENCHMARK-END

