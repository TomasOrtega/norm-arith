/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Yury Kudryashov
-/
/-
Standalone exact theorem from Mathlib/Analysis/Normed/Group/AddTorsor.lean.
Pinned source and adaptations: Benchmarks/manifest.json (TorsorVSub).
-/
module

import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Tactic
import NormArith

variable {V P : Type*} [SeminormedAddCommGroup V] [PseudoMetricSpace P]
  [NormedAddTorsor V P]

-- BENCHMARK-STATEMENT
example (p₁ p₂ p₃ p₄ : P) :
    dist (p₁ -ᵥ p₂) (p₃ -ᵥ p₄) ≤ dist p₁ p₃ + dist p₂ p₄ := by
  -- BENCHMARK-PROOF
  rw [dist_eq_norm, vsub_sub_vsub_comm, dist_eq_norm_vsub V, dist_eq_norm_vsub V]
  norm_arith
  -- BENCHMARK-END
