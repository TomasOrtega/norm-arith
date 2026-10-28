/-
Copyright (c) 2019 Rohan Mitta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Mitta, Kevin Buzzard, Alistair Tucker, Johannes Hölzl, Yury Kudryashov
-/
/-
Standalone exact theorem from Mathlib/Topology/MetricSpace/Contracting.lean.
Pinned source and adaptations: Benchmarks/manifest.json (ContractingResidualDistance).
-/
module

import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic
import NormArith

open scoped NNReal
variable {α : Type*} [MetricSpace α] {K : ℝ≥0} {f : α → α}

-- BENCHMARK-STATEMENT
example (hf : ContractingWith K f) (x y : α) :
    dist x y ≤ (dist x (f x) + dist y (f y)) / (1 - K) := by
  -- BENCHMARK-PROOF
  suffices dist x y ≤ dist x (f x) + dist y (f y) + K * dist x y by
    rwa [le_div_iff₀ hf.one_sub_K_pos, mul_comm, _root_.sub_mul, one_mul, sub_le_iff_le_add]
  have htriangle : dist x y ≤ dist x (f x) + dist y (f y) + dist (f x) (f y) := by
    norm_arith
  linarith [hf.dist_le_mul x y]
  -- BENCHMARK-END
