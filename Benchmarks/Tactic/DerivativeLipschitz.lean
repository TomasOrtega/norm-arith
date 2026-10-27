/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
/-
Standalone extracted block from Mathlib/Analysis/Calculus/FDeriv/Basic.lean.
Pinned source and adaptations: Benchmarks/manifest.json (DerivativeLipschitz).
-/
module

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Tactic
import NormArith

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

-- BENCHMARK-STATEMENT
example (f : E → F) (f' : E →L[𝕜] F) (x₀ y : E) (C ε : ℝ)
    (hy : ‖f (x₀ + y) - f x₀ - f' y‖ ≤ ε * ‖y‖)
    (hyC : ‖f (x₀ + y) - f x₀‖ ≤ C * ‖y‖) :
    ‖f' y‖ ≤ (C + ε) * ‖y‖ := by
  -- BENCHMARK-PROOF
  norm_arith
  -- BENCHMARK-END

