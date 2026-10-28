/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
/-
Standalone exact theorem from Mathlib/Topology/MetricSpace/Bounded.lean.
Pinned source and adaptations: Benchmarks/manifest.json (MetricDiameterBound).
-/
module

import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic

open Metric Set
variable {α : Type*} [PseudoMetricSpace α] {x : α} {s : Set α}

-- BENCHMARK-STATEMENT
example {r : ℝ} (hr : 0 ≤ r) (h : s ⊆ closedBall x r) : diam s ≤ 2 * r := by
  -- BENCHMARK-PROOF
  exact diam_le_of_forall_dist_le (mul_nonneg zero_le_two hr) fun a ha b hb =>
    calc
      dist a b ≤ dist a x + dist b x := dist_triangle_right _ _ _
      _ ≤ r + r := add_le_add (h ha) (h hb)
      _ = 2 * r := by simp [mul_two, mul_comm]
  -- BENCHMARK-END
