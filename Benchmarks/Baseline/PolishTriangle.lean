/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
/-
Standalone extracted block from Mathlib/Topology/MetricSpace/Polish.lean.
Pinned source and adaptations: Benchmarks/manifest.json (PolishTriangle).
-/
module

import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Tactic

open Metric TopologicalSpace.Opens TopologicalSpace.Opens.CompleteCopy
variable {α : Type*} [MetricSpace α] {s : TopologicalSpace.Opens α}

-- BENCHMARK-STATEMENT
example (x y z : CompleteCopy s) : dist x z ≤ dist x y + dist y z := by
  -- BENCHMARK-PROOF
  calc
    dist x z = dist x.1 z.1 + |1 / infDist x.1 sᶜ - 1 / infDist z.1 sᶜ| := rfl
    _ ≤ dist x.1 y.1 + dist y.1 z.1 + (|1 / infDist x.1 sᶜ - 1 / infDist y.1 sᶜ| +
          |1 / infDist y.1 sᶜ - 1 / infDist z.1 sᶜ|) :=
      add_le_add (dist_triangle _ _ _) (dist_triangle (1 / infDist _ _) _ _)
    _ = dist x y + dist y z := add_add_add_comm ..
  -- BENCHMARK-END

