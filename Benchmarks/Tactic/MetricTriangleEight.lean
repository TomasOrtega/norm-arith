/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
/-
Standalone exact theorem from Mathlib/Topology/MetricSpace/Pseudo/Defs.lean.
Pinned source and adaptations: Benchmarks/manifest.json (MetricTriangleEight).
-/
module

import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic
import NormArith

variable {α : Type*} [PseudoMetricSpace α]

-- BENCHMARK-STATEMENT
example (a b c d e f g h : α) : dist a h ≤ dist a b + dist b c + dist c d
    + dist d e + dist e f + dist f g + dist g h := by
  -- BENCHMARK-PROOF
  norm_arith
  -- BENCHMARK-END
