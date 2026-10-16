module

import NormArith.Certificate
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

/-!
Tests of the certificate boundary, independent of the search procedure.

The examples exercise negative and fractional coefficients, a hidden linear
decomposition, and an empty certificate.  They work in seminormed spaces; no
positive-definiteness, dimension, completeness, or inner product is assumed.
-/

open scoped BigOperators
open NormArith

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

-- Negative coefficients must contribute their absolute values.
example {x y : E} (hx : ‖x‖ ≤ 2) (hy : ‖y‖ ≤ 3) :
    ‖(-2 : ℝ) • x + (1 / 2 : ℝ) • y‖ ≤ 11 / 2 := by
  have h := norm_combo_le (-2) (1 / 2) hx hy
  norm_num at h ⊢
  exact h

-- A useful decomposition need not follow the syntax of the target.
example {x y : E} (hplus : ‖x + y‖ ≤ 2) (hminus : ‖x - y‖ ≤ 4) :
    ‖x‖ ≤ 3 := by
  have hrep : x = (1 / 2 : ℝ) • (x + y) + (1 / 2 : ℝ) • (x - y) := by
    module
  have h := bound_of_eq hrep (norm_combo_le (1 / 2) (1 / 2) hplus hminus)
  norm_num at h ⊢
  exact h

-- The finite-sum certificate also handles an empty index set.
example {ι : Type*} (c : ι → ℝ) (v : ι → E) :
    ‖∑ i ∈ (∅ : Finset ι), c i • v i‖ ≤ 0 := by
  have h := bound_sum_smul (∅ : Finset ι) c
    (v := v) (b := fun _ ↦ (0 : ℝ)) (by simp)
  simpa only [Finset.sum_empty] using h

