/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
/-
Standalone exact theorem from Mathlib/Topology/MetricSpace/Pseudo/Defs.lean.
Pinned source and adaptations: Benchmarks/manifest.json (MetricIntersectingBalls).
-/
module

import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic

variable {α : Type*} [PseudoMetricSpace α]
open Metric Set
variable {x y : α} {ε₁ ε₂ : ℝ}

-- BENCHMARK-STATEMENT
example (h : (closedBall x ε₁ ∩ ball y ε₂).Nonempty) : dist x y < ε₁ + ε₂ := by
  -- BENCHMARK-PROOF
  let ⟨z, hz⟩ := h
  calc
    dist x y ≤ dist z x + dist z y := dist_triangle_left _ _ _
    _ < ε₁ + ε₂ := add_lt_add_of_le_of_lt hz.1 hz.2
  -- BENCHMARK-END
