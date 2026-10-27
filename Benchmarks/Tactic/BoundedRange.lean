/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Mario Carneiro, Yury Kudryashov, Heather Macbeth
-/
/-
Standalone exact theorem from Mathlib/Topology/ContinuousMap/Bounded/Normed.lean.
Pinned source and adaptations: Benchmarks/manifest.json (BoundedRange).
-/
module

import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Tactic
import NormArith

variable {β γ : Type*} [SeminormedAddCommGroup β]

-- BENCHMARK-STATEMENT
example {f : γ → β} {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (x y : γ) :
    dist (f x) (f y) ≤ 2 * C := by
  -- BENCHMARK-PROOF
  norm_arith
  -- BENCHMARK-END

