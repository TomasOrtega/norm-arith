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
import NormArith

variable {α : Type*} [PseudoMetricSpace α]

-- BENCHMARK-STATEMENT
example (x y z w : α) : dist x w ≤ dist x y + dist y z + dist z w := by
  -- BENCHMARK-PROOF
  norm_arith
  -- BENCHMARK-END
