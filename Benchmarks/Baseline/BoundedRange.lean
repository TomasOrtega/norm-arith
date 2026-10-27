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

variable {β γ : Type*} [SeminormedAddCommGroup β]

-- BENCHMARK-STATEMENT
example {f : γ → β} {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (x y : γ) :
    dist (f x) (f y) ≤ 2 * C := by
  -- BENCHMARK-PROOF
  calc
    dist (f x) (f y) ≤ ‖f x‖ + ‖f y‖ := dist_le_norm_add_norm _ _
    _ ≤ C + C := add_le_add (hC x) (hC y)
    _ = 2 * C := (two_mul _).symm
  -- BENCHMARK-END

