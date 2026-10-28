/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
/-
Standalone exact theorem from Mathlib/Analysis/Calculus/Deriv/Slope.lean.
Pinned source and adaptations: Benchmarks/manifest.json (DerivativeSlopeNorm).
-/
module

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic
import NormArith

open Filter TopologicalSpace Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : ℝ → E} {f' : E} {s : Set ℝ} {x r : ℝ}

-- BENCHMARK-STATEMENT
example (hf : HasDerivWithinAt f f' s x) (hr : ‖f'‖ < r) :
    ∀ᶠ z in 𝓝[s] x, ‖z - x‖⁻¹ * (‖f z‖ - ‖f x‖) < r := by
  -- BENCHMARK-PROOF
  apply (hf.limsup_norm_slope_le hr).mono
  intro z hz
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left ?_ (by positivity)) hz
  norm_arith
  -- BENCHMARK-END
