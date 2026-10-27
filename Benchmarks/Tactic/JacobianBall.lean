/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
/-
Standalone extracted block from Mathlib/MeasureTheory/Function/Jacobian.lean.
Pinned source and adaptations: Benchmarks/manifest.json (JacobianBall).
-/
module

import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Tactic
import NormArith

open Metric
variable {E : Type*} [NormedAddCommGroup E]

-- BENCHMARK-STATEMENT
example (a z : E) (ε : ℝ) (az : a ∈ closedBall z ε) : ‖a‖ ≤ ‖z‖ + ε := by
  -- BENCHMARK-PROOF
  norm_arith
  -- BENCHMARK-END

