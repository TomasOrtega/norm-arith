module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Small certificates for norm bounds

The tactic frontend searches for a useful linear decomposition.  The lemmas in
this file check its certificate using only the triangle inequality, the norm of
a real scalar multiple, and monotonicity of real arithmetic.

No nonnegativity assumption on a supplied bound is required: it follows from
the hypothesis that the bound is at least a norm.  In particular, negative
coefficients must be charged their absolute values.
-/

public section

namespace NormArith

open scoped BigOperators

variable {E : Type*} [SeminormedAddCommGroup E]

/-- The empty linear combination has norm at most zero. -/
theorem bound_zero : ‖(0 : E)‖ ≤ (0 : ℝ) := by
  simp only [norm_zero, le_refl]

/-- Combine two upper bounds with the triangle inequality. -/
theorem bound_add {x y : E} {a b : ℝ}
    (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ b) : ‖x + y‖ ≤ a + b :=
  (norm_add_le x y).trans (add_le_add hx hy)

/-- Negating a vector preserves its norm bound. -/
theorem bound_neg {x : E} {a : ℝ} (hx : ‖x‖ ≤ a) : ‖-x‖ ≤ a := by
  simpa only [norm_neg] using hx

/-- Repeated addition scales a bound without a scalar-field structure. -/
theorem bound_nsmul (n : ℕ) {x : E} {b : ℝ}
    (hx : ‖x‖ ≤ b) : ‖n • x‖ ≤ n * b :=
  (norm_nsmul_le (n := n)).trans
    (mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg n))

/-- A difference is bounded by the sum of the two supplied bounds. -/
theorem bound_sub {x y : E} {a b : ℝ}
    (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ b) : ‖x - y‖ ≤ a + b := by
  simpa only [sub_eq_add_neg] using bound_add hx (bound_neg hy)

/-- Transfer a bound along the vector equality certified by the frontend. -/
theorem bound_of_eq {x y : E} {a : ℝ}
    (hxy : x = y) (hy : ‖y‖ ≤ a) : ‖x‖ ≤ a := by
  simpa only [hxy] using hy

/-- The finite-sum form of the same certificate check. -/
theorem bound_sum {ι : Type*} (s : Finset ι) {v : ι → E} {b : ι → ℝ}
    (h : ∀ i ∈ s, ‖v i‖ ≤ b i) : ‖∑ i ∈ s, v i‖ ≤ ∑ i ∈ s, b i :=
  norm_sum_le_of_le s h

variable [NormedSpace ℝ E]

/-- Scale an upper bound by the absolute value of a real coefficient. -/
theorem bound_smul (c : ℝ) {x : E} {b : ℝ}
    (hx : ‖x‖ ≤ b) : ‖c • x‖ ≤ |c| * b := by
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left hx (abs_nonneg c)

/-- A two-term signed linear-combination certificate. -/
theorem norm_combo_le (c d : ℝ) {x y : E} {a b : ℝ}
    (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ b) :
    ‖c • x + d • y‖ ≤ |c| * a + |d| * b :=
  bound_add (bound_smul c hx) (bound_smul d hy)

/-- A finite real linear combination is bounded by its weighted norm bounds. -/
theorem bound_sum_smul {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    {v : ι → E} {b : ι → ℝ} (h : ∀ i ∈ s, ‖v i‖ ≤ b i) :
    ‖∑ i ∈ s, c i • v i‖ ≤ ∑ i ∈ s, |c i| * b i := by
  exact bound_sum s (fun i hi ↦ bound_smul (c i) (h i hi))

/-- Check a proposed linear representation and its resulting scalar bound.

Search may be implemented by arbitrary metaprogramming; its result must supply
both `hrep` and `h`.  This theorem is the mathematical certificate that connects
the finite linear representation to an upper bound on the target norm.
-/
theorem bound_linear_combination {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    {w : E} {v : ι → E} {b : ι → ℝ}
    (hrep : w = ∑ i ∈ s, c i • v i) (h : ∀ i ∈ s, ‖v i‖ ≤ b i) :
    ‖w‖ ≤ ∑ i ∈ s, |c i| * b i :=
  bound_of_eq hrep (bound_sum_smul s c h)

end NormArith
