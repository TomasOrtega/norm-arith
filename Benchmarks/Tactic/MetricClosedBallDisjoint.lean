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
import NormArith

variable {α : Type*} [PseudoMetricSpace α]
open Metric Set
variable {x y : α} {δ ε : ℝ}

-- BENCHMARK-STATEMENT
example (h : δ + ε < dist x y) :
    Disjoint (closedBall x δ) (closedBall y ε) := by
  -- BENCHMARK-PROOF
  apply Set.disjoint_left.mpr
  intro a ha1 ha2
  have ha : dist a x ≤ δ := ha1
  have hb : dist a y ≤ ε := ha2
  exact h.not_ge (by norm_arith [ha, hb])
  -- BENCHMARK-END
