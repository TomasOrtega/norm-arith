/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Yaël Dillies
-/
/-
Standalone exact theorem from Mathlib/Analysis/Normed/Group/Basic.lean.
Pinned source and adaptations: Benchmarks/manifest.json (FinsetNormSum).
-/
module

import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic

variable {ι E : Type*} [SeminormedAddCommGroup E]

-- BENCHMARK-STATEMENT
example (s : Finset ι) (f : ι → E) : ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ := by
  -- BENCHMARK-PROOF
  exact s.le_sum_of_subadditive norm norm_zero.le norm_add_le f
  -- BENCHMARK-END
