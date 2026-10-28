/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
/-
Standalone exact theorem from Mathlib/Topology/MetricSpace/Gluing.lean.
Pinned source and adaptations: Benchmarks/manifest.json (MetricGluingTriangle).
-/
module

import Mathlib.Topology.MetricSpace.Gluing
import Mathlib.Tactic
import NormArith

open Metric Set
variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [Nonempty Z]

-- BENCHMARK-STATEMENT
example (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ)
    (H : ∀ p q, |dist (Φ p) (Φ q) - dist (Ψ p) (Ψ q)| ≤ 2 * ε) (x : X) (y : Y) (z : X) :
    glueDist Φ Ψ ε (.inl x) (.inl z) ≤
      glueDist Φ Ψ ε (.inl x) (.inr y) + glueDist Φ Ψ ε (.inr y) (.inl z) := by
  -- BENCHMARK-PROOF
  simp_rw [glueDist, add_add_add_comm _ ε, add_assoc]
  refine le_ciInf_add fun p => ?_
  rw [add_left_comm, add_assoc, ← two_mul]
  refine le_ciInf_add fun q => ?_
  norm_arith [(abs_le.1 (H p q)).2]
  -- BENCHMARK-END
