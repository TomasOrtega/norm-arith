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
import NormArith

open scoped BoundedContinuousFunction
variable {α β : Type*} [TopologicalSpace α] [PseudoMetricSpace β]

-- BENCHMARK-STATEMENT
example (f : ℕ → α →ᵇ β) (F : α → β) (b : ℕ → ℝ) (C : ℝ)
    (hC : ∀ x y, dist (f 0 x) (f 0 y) ≤ C)
    (fF_bdd : ∀ x N, dist (f N x) (F x) ≤ b N) (x y : α) :
    dist (F x) (F y) ≤ C + (b 0 + b 0) := by
  -- BENCHMARK-PROOF
  norm_arith [hC x y, fF_bdd x 0, fF_bdd y 0]
  -- BENCHMARK-END

