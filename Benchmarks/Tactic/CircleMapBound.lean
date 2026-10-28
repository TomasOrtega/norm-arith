/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Fabrizio Barroero, Christopher Hoskin
-/
/-
Standalone exact theorem from Mathlib/Analysis/SpecialFunctions/Complex/CircleMap.lean.
Pinned source and adaptations: Benchmarks/manifest.json (CircleMapBound).
-/
module

import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Tactic
import NormArith

open Complex Function Metric Real

-- BENCHMARK-STATEMENT
example (c : ℂ) (R : ℝ) (θ : ℝ) (x : ℂ) :
    ‖circleMap c R θ - x‖ ≤ |R| + dist c x := by
  -- BENCHMARK-PROOF
  have h := mem_sphere.1 (circleMap_mem_sphere' c R θ)
  norm_arith [h]
  -- BENCHMARK-END
