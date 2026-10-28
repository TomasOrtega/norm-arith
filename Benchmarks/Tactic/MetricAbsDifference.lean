/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
/-
Standalone exact theorem from Mathlib/Topology/MetricSpace/Pseudo/Defs.lean.
Pinned source and adaptations: Benchmarks/manifest.json (MetricAbsDifference).
-/
module

import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic
import NormArith

variable {α : Type*} [PseudoMetricSpace α]

-- BENCHMARK-STATEMENT
example (x y z : α) : |dist x z - dist y z| ≤ dist x y := by
  -- BENCHMARK-PROOF
  rw [abs_le]
  constructor <;> norm_arith
  -- BENCHMARK-END
