/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
/-
Standalone exact theorem from Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean.
Pinned source and adaptations: Benchmarks/manifest.json (BoundedLinearAdd).
-/
module

import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Tactic

variable {𝕜 E F : Type*} [Semiring 𝕜]
  [SeminormedAddCommGroup E] [Module 𝕜 E]
  [SeminormedAddCommGroup F] [Module 𝕜 F] {f g : E → F}

-- BENCHMARK-STATEMENT
example (hf : IsBoundedLinearMap 𝕜 f) (hg : IsBoundedLinearMap 𝕜 g) :
    IsBoundedLinearMap 𝕜 fun e => f e + g e := by
  -- BENCHMARK-PROOF
  let ⟨hlf, Mf, _, hMf⟩ := hf
  let ⟨hlg, Mg, _, hMg⟩ := hg
  exact (hlf.mk' _ + hlg.mk' _).isLinear.with_bound (Mf + Mg) fun x =>
    calc
      ‖f x + g x‖ ≤ Mf * ‖x‖ + Mg * ‖x‖ := norm_add_le_of_le (hMf x) (hMg x)
      _ ≤ (Mf + Mg) * ‖x‖ := by rw [add_mul]
  -- BENCHMARK-END
