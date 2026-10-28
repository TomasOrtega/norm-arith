/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Sébastien Gouëzel, Rémy Degenne
-/
/-
Standalone exact theorem from Mathlib/MeasureTheory/Integral/FinMeasAdditive.lean.
Pinned source and adaptations: Benchmarks/manifest.json (FinMeasAdditiveSum).
-/
module

import Mathlib.MeasureTheory.Integral.FinMeasAdditive
import Mathlib.Tactic

open MeasureTheory
variable {α β : Type*} [MeasurableSpace α] [SeminormedAddCommGroup β]
variable {μ : Measure α} {T T' : Set α → β} {C C' : ℝ}

-- BENCHMARK-STATEMENT
example (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C') :
    DominatedFinMeasAdditive μ (T + T') (C + C') := by
  -- BENCHMARK-PROOF
  refine ⟨hT.1.add hT'.1, fun s hs hμs => ?_⟩
  rw [Pi.add_apply, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hT.2 s hs hμs) (hT'.2 s hs hμs))
  -- BENCHMARK-END
