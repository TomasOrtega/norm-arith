/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
/-
Standalone exact theorem from Mathlib/Analysis/Normed/Module/Extr.lean.
Pinned source and adaptations: Benchmarks/manifest.json (SameRayMaximum).
-/
module

import Mathlib.Analysis.Normed.Module.Extr
import Mathlib.Tactic

variable {α E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
  {f : α → E} {l : Filter α} {c : α} {y : E}

-- BENCHMARK-STATEMENT
example (h : IsMaxFilter (norm ∘ f) l c) (hy : SameRay ℝ (f c) y) :
    IsMaxFilter (fun x => ‖f x + y‖) l c := by
  -- BENCHMARK-PROOF
  exact h.mono fun x hx => by dsimp at hx ⊢; grw [hy.norm_add, norm_add_le, hx]
  -- BENCHMARK-END
