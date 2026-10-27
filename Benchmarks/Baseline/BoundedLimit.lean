/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Mario Carneiro, Yury Kudryashov, Heather Macbeth
-/
/-
Standalone extracted block from Mathlib/Topology/ContinuousMap/Bounded/Basic.lean.
Pinned source and adaptations: Benchmarks/manifest.json (BoundedLimit).
-/
module

import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Tactic

open scoped BoundedContinuousFunction
variable {α β : Type*} [TopologicalSpace α] [PseudoMetricSpace β]

-- BENCHMARK-STATEMENT
example (f : ℕ → α →ᵇ β) (F : α → β) (b : ℕ → ℝ) (C : ℝ)
    (hC : ∀ x y, dist (f 0 x) (f 0 y) ≤ C)
    (fF_bdd : ∀ x N, dist (f N x) (F x) ≤ b N) (x y : α) :
    dist (F x) (F y) ≤ C + (b 0 + b 0) := by
  -- BENCHMARK-PROOF
  calc
    dist (F x) (F y) ≤ dist (f 0 x) (f 0 y) + (dist (f 0 x) (F x) + dist (f 0 y) (F y)) :=
      dist_triangle4_left _ _ _ _
    _ ≤ C + (b 0 + b 0) := add_le_add (hC x y) (add_le_add (fF_bdd x 0) (fF_bdd y 0))
  -- BENCHMARK-END

