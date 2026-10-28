/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
/-
Standalone exact theorem from Mathlib/Analysis/SpecialFunctions/Log/Summable.lean.
Pinned source and adaptations: Benchmarks/manifest.json (NormOneAddMultipliable).
-/
module

import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Tactic

variable {ι R : Type*} [NormedCommRing R] [NormOneClass R] {f : ι → R}

-- BENCHMARK-STATEMENT
example (hf : Summable fun i ↦ ‖f i‖) :
    Multipliable fun i ↦ ‖1 + f i‖ := by
  -- BENCHMARK-PROOF
  conv => enter [1, i]; rw [← sub_add_cancel ‖1 + f i‖ 1, add_comm]
  refine Real.multipliable_one_add_of_summable <| hf.of_norm_bounded (fun i ↦ ?_)
  simpa using abs_norm_sub_norm_le (1 + f i) 1
  -- BENCHMARK-END
