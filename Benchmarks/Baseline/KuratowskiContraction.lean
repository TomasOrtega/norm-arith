/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
/-
Standalone exact theorem from Mathlib/Topology/MetricSpace/Kuratowski.lean.
Pinned source and adaptations: Benchmarks/manifest.json (KuratowskiContraction).
-/
module

import Mathlib.Topology.MetricSpace.Kuratowski
import Mathlib.Tactic

open KuratowskiEmbedding
variable {α : Type*} [MetricSpace α]

-- BENCHMARK-STATEMENT
example (x : ℕ → α) (a b : α) :
    dist (embeddingOfSubset x a) (embeddingOfSubset x b) ≤ dist a b := by
  -- BENCHMARK-PROOF
  rw [dist_eq_norm]
  refine lp.norm_le_of_forall_le dist_nonneg fun n => ?_
  simp only [lp.coeFn_sub, Pi.sub_apply, embeddingOfSubset_coe]
  convert! abs_dist_sub_le a b (x n) using 2
  ring
  -- BENCHMARK-END
