/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
/-
Standalone exact theorem from Mathlib/Topology/MetricSpace/Pseudo/Defs.lean.
Pinned source and adaptations: Benchmarks/manifest.json (MetricBallExpansion).
-/
module

import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic

variable {α : Type*} [PseudoMetricSpace α]
open Metric Set
variable {x y : α} {ε₁ ε₂ : ℝ}

-- BENCHMARK-STATEMENT
example (h : ε₁ + dist x y < ε₂) : closedBall x ε₁ ⊆ ball y ε₂ := by
  -- BENCHMARK-PROOF
  intro z hz
  calc
    dist z y ≤ dist z x + dist x y := dist_triangle _ _ _
    _ ≤ ε₁ + dist x y := by gcongr; exact hz
    _ < ε₂ := h
  -- BENCHMARK-END
