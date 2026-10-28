/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
/-
Standalone exact theorem from Mathlib/Analysis/SpecialFunctions/Log/PosLog.lean.
Pinned source and adaptations: Benchmarks/manifest.json (PositiveLogNormAdd).
-/
module

import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Tactic

open Real
open scoped Real

-- BENCHMARK-STATEMENT
example {E : Type*} [SeminormedAddCommGroup E] (a b : E) :
    log⁺ ‖a + b‖ ≤ log⁺ ‖a‖ + log⁺ ‖b‖ + log 2 := by
  -- BENCHMARK-PROOF
  grw [norm_add_le, posLog_add, add_rotate]
  exact neg_one_lt_zero.le.trans (norm_nonneg _)
  -- BENCHMARK-END
