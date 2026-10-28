/-
Copyright (c) 2026 Hang Lu Su, Katerina Hristova. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hang Lu Su, Katerina Hristova
-/
/-
Standalone exact theorem from Mathlib/Topology/MetricSpace/GromovProduct.lean.
Pinned source and adaptations: Benchmarks/manifest.json (GromovProductBound).
-/
module

import Mathlib.Topology.MetricSpace.GromovProduct
import Mathlib.Tactic

open Metric
variable {X : Type*} [PseudoMetricSpace X]

-- BENCHMARK-STATEMENT
example (x y z : X) : gromovProduct x y z ≤ dist x y := by
  -- BENCHMARK-PROOF
  grind [gromovProduct_eq, dist_triangle x y z]
  -- BENCHMARK-END
