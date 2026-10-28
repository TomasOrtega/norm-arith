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
import NormArith

open Metric Set
variable {α : Type*} [PseudoMetricSpace α] {x : α} {s : Set α}

-- BENCHMARK-STATEMENT
example {r : ℝ} (hr : 0 ≤ r) (h : s ⊆ closedBall x r) : diam s ≤ 2 * r := by
  -- BENCHMARK-PROOF
  apply diam_le_of_forall_dist_le (by positivity)
  intro a ha b hb
  have hax : dist a x ≤ r := h ha
  have hbx : dist b x ≤ r := h hb
  norm_arith
  -- BENCHMARK-END
