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
import NormArith

open Metric TopologicalSpace.Opens TopologicalSpace.Opens.CompleteCopy
variable {α : Type*} [MetricSpace α] {s : TopologicalSpace.Opens α}

-- BENCHMARK-STATEMENT
example (x y z : CompleteCopy s) : dist x z ≤ dist x y + dist y z := by
  -- BENCHMARK-PROOF
  simp only [dist_eq, ← Real.dist_eq]
  norm_arith
  -- BENCHMARK-END

