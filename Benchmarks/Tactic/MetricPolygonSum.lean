/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
/-
Standalone exact theorem from Mathlib/Topology/MetricSpace/Pseudo/Basic.lean.
Pinned source and adaptations: Benchmarks/manifest.json (MetricPolygonSum).
-/
module

import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic
import NormArith

variable {α : Type*} [PseudoMetricSpace α]

-- BENCHMARK-STATEMENT
example (f : ℕ → α) {m n : ℕ} (h : m ≤ n) :
    dist (f m) (f n) ≤ ∑ i ∈ Finset.Ico m n, dist (f i) (f (i + 1)) := by
  -- BENCHMARK-PROOF
  induction n, h using Nat.le_induction with
  | base => rw [Finset.Ico_self, Finset.sum_empty, dist_self]
  | succ n hle ihn =>
    rw [← Finset.insert_Ico_right_eq_Ico_add_one hle, Finset.sum_insert (by simp)]
    generalize ∑ i ∈ Finset.Ico m n, dist (f i) (f (i + 1)) = S at ihn ⊢
    norm_arith
  -- BENCHMARK-END
