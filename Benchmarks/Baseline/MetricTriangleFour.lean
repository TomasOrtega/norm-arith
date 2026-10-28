/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
/-
Standalone exact theorem from Mathlib/Topology/MetricSpace/Pseudo/Defs.lean.
Pinned source and adaptations: Benchmarks/manifest.json (MetricTriangleFour).
-/
module

import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic

variable {α : Type*} [PseudoMetricSpace α]

-- BENCHMARK-STATEMENT
example (x y z w : α) : dist x w ≤ dist x y + dist y z + dist z w := by
  -- BENCHMARK-PROOF
  calc
    dist x w ≤ dist x z + dist z w := dist_triangle x z w
    _ ≤ dist x y + dist y z + dist z w := by gcongr; apply dist_triangle x y z
  -- BENCHMARK-END
