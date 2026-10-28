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
import NormArith

variable {α : Type*} [PseudoMetricSpace α]
open Metric Set
variable {x y : α} {ε₁ ε₂ : ℝ}

-- BENCHMARK-STATEMENT
example (h : (closedBall x ε₁ ∩ ball y ε₂).Nonempty) : dist x y < ε₁ + ε₂ := by
  -- BENCHMARK-PROOF
  obtain ⟨z, hz⟩ := h
  have hx : dist z x ≤ ε₁ := hz.1
  have hy : dist z y < ε₂ := hz.2
  norm_arith
  -- BENCHMARK-END
