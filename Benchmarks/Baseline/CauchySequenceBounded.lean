/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
/-
Standalone exact theorem from Mathlib/Topology/MetricSpace/Cauchy.lean.
Pinned source and adaptations: Benchmarks/manifest.json (CauchySequenceBounded).
-/
module

import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic

variable {α : Type*} [PseudoMetricSpace α]

-- BENCHMARK-STATEMENT
example {u : ℕ → α} (hu : CauchySeq u) : ∃ R > 0, ∀ m n, dist (u m) (u n) < R := by
  -- BENCHMARK-PROOF
  rcases Metric.cauchySeq_iff'.1 hu 1 zero_lt_one with ⟨N, hN⟩
  rsuffices ⟨R, R0, H⟩ : ∃ R > 0, ∀ n, dist (u n) (u N) < R
  · exact ⟨_, add_pos R0 R0, fun m n =>
      lt_of_le_of_lt (dist_triangle_right _ _ _) (add_lt_add (H m) (H n))⟩
  let R := Finset.sup (Finset.range N) fun n => nndist (u n) (u N)
  refine ⟨↑R + 1, add_pos_of_nonneg_of_pos R.2 zero_lt_one, fun n => ?_⟩
  rcases le_or_gt N n with h | h
  · exact lt_of_lt_of_le (hN _ h) (le_add_of_nonneg_left R.2)
  · have : _ ≤ R := Finset.le_sup (Finset.mem_range.2 h)
    exact lt_of_le_of_lt this (lt_add_of_pos_right _ zero_lt_one)
  -- BENCHMARK-END
