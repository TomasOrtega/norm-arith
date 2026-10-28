/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
/-
Standalone exact theorem from Mathlib/Analysis/SpecialFunctions/Log/Summable.lean.
Pinned source and adaptations: Benchmarks/manifest.json (LogNormSummable).
-/
module

import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Tactic
import NormArith

variable {ι R : Type*} [NormedCommRing R] [NormOneClass R] {f : ι → R}

-- BENCHMARK-STATEMENT
example (hu : Summable fun n ↦ ‖f n‖) :
    Summable fun i ↦ Real.log ‖1 + f i‖ := by
  -- BENCHMARK-PROOF
  suffices Summable (‖1 + f ·‖ - 1) from
    (Real.summable_log_one_add_of_summable this).congr (by simp)
  refine .of_norm (hu.of_nonneg_of_le (fun i ↦ by positivity) fun i ↦ ?_)
  simp only [Real.norm_eq_abs, abs_le]
  constructor <;> norm_arith [norm_one (α := R)]
  -- BENCHMARK-END
