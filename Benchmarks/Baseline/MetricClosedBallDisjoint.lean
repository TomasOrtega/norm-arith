/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
/-
Standalone exact theorem from Mathlib/Topology/MetricSpace/Pseudo/Defs.lean.
Pinned source and adaptations: Benchmarks/manifest.json (MetricClosedBallDisjoint).
-/
module

import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic

variable {α : Type*} [PseudoMetricSpace α]
open Metric Set
variable {x y : α} {δ ε : ℝ}

-- BENCHMARK-STATEMENT
example (h : δ + ε < dist x y) :
    Disjoint (closedBall x δ) (closedBall y ε) := by
  -- BENCHMARK-PROOF
  exact Set.disjoint_left.mpr fun _a ha1 ha2 =>
    h.not_ge <| (dist_triangle_left _ _ _).trans <| add_le_add ha1 ha2
  -- BENCHMARK-END
