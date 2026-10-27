/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
/-
Standalone adapted estimate from Mathlib/MeasureTheory/Function/AEEqOfIntegral.lean.
Pinned source and adaptations: Benchmarks/manifest.json (DualSeparationHalf).
-/
module

import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Tactic
import NormArith

variable {E : Type*} [NormedAddCommGroup E]

-- BENCHMARK-STATEMENT
example (a x : E) (hx : dist a x < ‖a‖ / 2) : ‖a‖ / 2 < ‖(x : E)‖ := by
  -- BENCHMARK-PROOF
  norm_arith
  -- BENCHMARK-END

