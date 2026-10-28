/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Yury Kudryashov
-/
/-
Standalone exact theorem from Mathlib/Analysis/Normed/Group/AddTorsor.lean.
Pinned source and adaptations: Benchmarks/manifest.json (TorsorVAdd).
-/
module

import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Tactic
import NormArith

variable {V P : Type*} [SeminormedAddCommGroup V] [PseudoMetricSpace P]
  [NormedAddTorsor V P]

-- BENCHMARK-STATEMENT
example (v v' : V) (p p' : P) :
    dist (v +ᵥ p) (v' +ᵥ p') ≤ dist v v' + dist p p' := by
  -- BENCHMARK-PROOF
  rw [dist_eq_norm_vsub V, vadd_vsub_vadd_comm, dist_eq_norm, dist_eq_norm_vsub V]
  norm_arith
  -- BENCHMARK-END
