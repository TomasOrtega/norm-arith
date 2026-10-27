/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
/-
Standalone extracted block from Mathlib/MeasureTheory/Measure/SeparableMeasure.lean.
Pinned source and adaptations: Benchmarks/manifest.json (LpApproximationSum).
-/
module

import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Tactic
import NormArith

open MeasureTheory ENNReal
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  {μ : Measure X} {p : ℝ≥0∞} [Fact (1 ≤ p)]

-- BENCHMARK-STATEMENT
example (f g : X → E) (hf : MemLp f p μ) (hg : MemLp g p μ)
    (bf bg : Lp E p μ) (ε : ℝ)
    (hbf : ‖MemLp.toLp f hf - bf‖ < ε / 2)
    (hbg : ‖MemLp.toLp g hg - bg‖ < ε / 2) :
    ‖MemLp.toLp f hf + MemLp.toLp g hg - (bf + bg)‖ < ε := by
  -- BENCHMARK-PROOF
  norm_arith
  -- BENCHMARK-END

