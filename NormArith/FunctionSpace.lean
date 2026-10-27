module

public import NormArith.Analysis
public import NormArith.Parameters
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Finite function estimates

These adapters keep the measure and exponent in each expression. Real-valued
bounds require finite input norms. Hölder and interpolation include infinity.
The elliptic estimate takes the energy and Sobolev bounds as explicit premises.
-/

public section

namespace NormArith

open MeasureTheory
open scoped ENNReal NNReal

section Finite

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  {μ : Measure α} {p q r : ℝ≥0∞} {f : α → E}

theorem norm_toLp_eq_lpNorm (hf : MemLp f p μ) : ‖hf.toLp f‖ = lpNorm f p μ :=
  Lp.norm_toLp f hf

theorem finite_lp_le_iff (hf : MemLp f p μ) {A : ℝ} (hA : 0 ≤ A) :
    lpNorm f p μ ≤ A ↔ eLpNorm f p μ ≤ ENNReal.ofReal A := by
  rw [← ofReal_lpNorm hf, ENNReal.ofReal_le_ofReal_iff hA]

/-- Interpolation uses a checked Hölder triple for the scaled endpoint exponents. -/
theorem eLpNorm_interpolate {θ : ℝ} (hθ : 0 < θ) (hθ' : θ < 1)
    (hf : AEStronglyMeasurable f μ)
    [ENNReal.HolderTriple (p / ENNReal.ofReal θ) (q / ENNReal.ofReal (1 - θ)) r] :
    eLpNorm f r μ ≤ eLpNorm f p μ ^ θ * eLpNorm f q μ ^ (1 - θ) := by
  have h1 : 0 < 1 - θ := sub_pos.mpr hθ'
  have hsplit : (fun x ↦ ‖f x‖ₑ) = (‖f ·‖ₑ ^ θ) * (‖f ·‖ₑ ^ (1 - θ)) := by
    funext x
    simp only [Pi.mul_apply]
    rw [← ENNReal.rpow_add_of_nonneg θ (1 - θ) hθ.le h1.le]
    simp
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm_ennreal
    (p := p / ENNReal.ofReal θ) (q := q / ENNReal.ofReal (1 - θ)) (r := r)
    (f := fun x ↦ ‖f x‖ₑ ^ θ) (g := fun x ↦ ‖f x‖ₑ ^ (1 - θ))
    (by fun_prop) (by fun_prop)
  rw [← hsplit, eLpNorm_enorm f hf,
    eLpNorm_enorm_rpow f hf hθ, eLpNorm_enorm_rpow f hf h1,
    ENNReal.div_mul_cancel (by positivity) ENNReal.ofReal_ne_top,
    ENNReal.div_mul_cancel (by positivity) ENNReal.ofReal_ne_top] at h
  exact h

theorem finite_lp_interpolate {θ : ℝ} (hθ : 0 < θ) (hθ' : θ < 1)
    (hp : MemLp f p μ) (hq : MemLp f q μ)
    [ENNReal.HolderTriple (p / ENNReal.ofReal θ) (q / ENNReal.ofReal (1 - θ)) r] :
    lpNorm f r μ ≤ lpNorm f p μ ^ θ * lpNorm f q μ ^ (1 - θ) := by
  have h := eLpNorm_interpolate hθ hθ' hp.aestronglyMeasurable
    (p := p) (q := q) (r := r)
  have hfinite : eLpNorm f p μ ^ θ * eLpNorm f q μ ^ (1 - θ) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hθ.le hp.eLpNorm_ne_top)
      (ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.mpr hθ'.le) hq.eLpNorm_ne_top)
  simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, toReal_eLpNorm] using
    ENNReal.toReal_mono hfinite h

theorem memLp_interpolate {θ : ℝ} (hθ : 0 < θ) (hθ' : θ < 1)
    (hp : MemLp f p μ) (hq : MemLp f q μ)
    [ENNReal.HolderTriple (p / ENNReal.ofReal θ) (q / ENNReal.ofReal (1 - θ)) r] :
    MemLp f r μ := by
  refine lt_of_le_of_lt
    (eLpNorm_interpolate (p := p) (q := q) hθ hθ' hp.aestronglyMeasurable) ?_
  exact ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg hθ.le hp.eLpNorm_ne_top)
    (ENNReal.rpow_lt_top_of_nonneg (sub_nonneg.mpr hθ'.le) hq.eLpNorm_ne_top)

end Finite

section Products

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {p q r : ℝ≥0∞} {f g : α → ℝ}

theorem finite_lp_mul [ENNReal.HolderTriple p q r]
    (hf : MemLp f p μ) (hg : MemLp g q μ) :
    lpNorm (f * g) r μ ≤ lpNorm f p μ * lpNorm g q μ := by
  have h := eLpNorm_smul_le_mul_eLpNorm hf.aestronglyMeasurable hg.aestronglyMeasurable
    (p := p) (q := q) (r := r)
  simpa only [ENNReal.toReal_mul, toReal_eLpNorm, smul_eq_mul] using
    ENNReal.toReal_mono (ENNReal.mul_ne_top hf.eLpNorm_ne_top hg.eLpNorm_ne_top) h

theorem integral_mul_le_lp [ENNReal.HolderTriple p q 1]
    (hf : MemLp f p μ) (hg : MemLp g q μ) :
    |∫ x, f x * g x ∂μ| ≤ lpNorm f p μ * lpNorm g q μ := by
  calc
    |∫ x, f x * g x ∂μ| ≤ ∫ x, ‖f x * g x‖ ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x ↦ f x * g x)
    _ = lpNorm (f * g) 1 μ := (lpNorm_one_eq_integral_norm
      (hf.aestronglyMeasurable.mul hg.aestronglyMeasurable)).symm
    _ ≤ lpNorm f p μ * lpNorm g q μ := finite_lp_mul hf hg

/-- The L2/L6 endpoints give the L4 factors needed for an L2 product. -/
theorem finite_lp_two_six_product (hf2 : MemLp f 2 μ) (hf6 : MemLp f 6 μ)
    (hg2 : MemLp g 2 μ) (hg6 : MemLp g 6 μ) :
    lpNorm (f * g) 2 μ ≤
      (lpNorm f 2 μ ^ (1 / 4 : ℝ) * lpNorm f 6 μ ^ (3 / 4 : ℝ)) *
      (lpNorm g 2 μ ^ (1 / 4 : ℝ) * lpNorm g 6 μ ^ (3 / 4 : ℝ)) := by
  have hparams : ENNReal.HolderTriple
      (2 / ENNReal.ofReal (1 / 4)) (6 / ENNReal.ofReal (1 - (1 / 4))) 4 := by
    holder_arith
  let := hparams
  have hf4 := memLp_interpolate (r := 4) (by norm_num : (0 : ℝ) < 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1) hf2 hf6
  have hg4 := memLp_interpolate (r := 4) (by norm_num : (0 : ℝ) < 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1) hg2 hg6
  have hfb := finite_lp_interpolate (r := 4) (by norm_num : (0 : ℝ) < 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1) hf2 hf6
  have hgb := finite_lp_interpolate (r := 4) (by norm_num : (0 : ℝ) < 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1) hg2 hg6
  have : ENNReal.HolderTriple 4 4 2 := by holder_arith
  calc
    lpNorm (f * g) 2 μ ≤ lpNorm f 4 μ * lpNorm g 4 μ := finite_lp_mul hf4 hg4
    _ ≤ _ := by
      convert mul_le_mul hfb hgb lpNorm_nonneg (le_trans lpNorm_nonneg hfb) using 1
      norm_num

end Products

section Bilinear

variable {α E F G : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
  [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G]
  {μ : Measure α} {p q r : ℝ≥0∞} [ENNReal.HolderTriple p q r]

theorem finite_lp_bilinear (B : E →L[ℝ] F →L[ℝ] G) {f : α → E} {g : α → F}
    (hf : MemLp f p μ) (hg : MemLp g q μ) :
    lpNorm (fun x ↦ B (f x) (g x)) r μ ≤ ‖B‖ * lpNorm f p μ * lpNorm g q μ := by
  have h := eLpNorm_le_enorm_mul_eLpNorm_mul_eLpNorm B
    (p := p) (q := q) (r := r) hf.aestronglyMeasurable hg.aestronglyMeasurable
  have hfinite : ‖B‖ₑ * eLpNorm f p μ * eLpNorm g q μ ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) hf.eLpNorm_ne_top) hg.eLpNorm_ne_top
  simpa only [ENNReal.toReal_mul, toReal_eLpNorm, toReal_enorm] using
    ENNReal.toReal_mono hfinite h

end Bilinear

section Elliptic

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {u f b du : α → ℝ} {ν S : ℝ}

/-- A supplied Sobolev bound and energy inequality give uniform Lp estimates. -/
theorem elliptic_lp_estimate (hν : 0 < ν) (hS : 0 ≤ S)
    (hu : MemLp u 6 μ) (hf : MemLp f (6 / 5) μ)
    (hb : MemLp b 3 μ) (hdu : MemLp du 2 μ)
    (hsobolev : lpNorm u 6 μ ≤ S * lpNorm du 2 μ)
    (hsmall : S * lpNorm b 3 μ ≤ ν / 2)
    (henergy : ν * lpNorm du 2 μ ^ 2 ≤
      |∫ x, f x * u x ∂μ| + |∫ x, (b x * du x) * u x ∂μ|) :
    lpNorm du 2 μ ≤ 2 * S * lpNorm f (6 / 5) μ / ν ∧
    lpNorm u 6 μ ≤ 2 * S ^ 2 * lpNorm f (6 / 5) μ / ν := by
  have : ENNReal.HolderTriple (6 / 5) 6 1 := by holder_arith
  have : ENNReal.HolderTriple 3 2 (6 / 5) := by holder_arith
  have hforce := integral_mul_le_lp hf hu
  have hdrift := integral_mul_le_lp (hb.mul (r := 6 / 5) hdu) hu
  have hproduct := finite_lp_mul (r := 6 / 5) hb hdu
  have hscaled := mul_le_mul_of_nonneg_right hproduct
    (lpNorm_nonneg (f := u) (p := 6) (μ := μ))
  apply elliptic_absorb hν hS lpNorm_nonneg lpNorm_nonneg lpNorm_nonneg hsobolev hsmall
  dsimp only [Pi.mul_apply] at hdrift
  linarith

end Elliptic

section VectorElliptic

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure α} {u f : α → ℝ} {b du : α → E} {ν S : ℝ}

/-- This form also covers vector-valued drift and gradient functions. -/
theorem elliptic_lp_pairing_estimate (T : E →L[ℝ] E →L[ℝ] ℝ) (hT : ‖T‖ ≤ 1)
    (hν : 0 < ν) (hS : 0 ≤ S)
    (hu : MemLp u 6 μ) (hf : MemLp f (6 / 5) μ)
    (hb : MemLp b 3 μ) (hdu : MemLp du 2 μ)
    (hsobolev : lpNorm u 6 μ ≤ S * lpNorm du 2 μ)
    (hsmall : S * lpNorm b 3 μ ≤ ν / 2)
    (henergy : ν * lpNorm du 2 μ ^ 2 ≤
      |∫ x, f x * u x ∂μ| + |∫ x, T (b x) (du x) * u x ∂μ|) :
    lpNorm du 2 μ ≤ 2 * S * lpNorm f (6 / 5) μ / ν ∧
    lpNorm u 6 μ ≤ 2 * S ^ 2 * lpNorm f (6 / 5) μ / ν := by
  have : ENNReal.HolderTriple (6 / 5) 6 1 := by holder_arith
  have : ENNReal.HolderTriple 3 2 (6 / 5) := by holder_arith
  have hforce := integral_mul_le_lp hf hu
  have hdrift := integral_mul_le_lp (T.memLp_of_bilin (6 / 5) hb hdu) hu
  have hproduct := finite_lp_bilinear (r := 6 / 5) T hb hdu
  have hTscaled := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hT (lpNorm_nonneg (f := b) (p := 3) (μ := μ)))
    (lpNorm_nonneg (f := du) (p := 2) (μ := μ))
  simp only [one_mul] at hTscaled
  have hscaled := mul_le_mul_of_nonneg_right (hproduct.trans hTscaled)
    (lpNorm_nonneg (f := u) (p := 6) (μ := μ))
  apply elliptic_absorb hν hS lpNorm_nonneg lpNorm_nonneg lpNorm_nonneg hsobolev hsmall
  linarith

end VectorElliptic

section Mixed

variable {T X E F G : Type*} [MeasurableSpace T] [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
  [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G]
  (μ : Measure X) (ν : Measure T) {p q r a b c : ℝ≥0∞}
  [ENNReal.HolderTriple p q r] [ENNReal.HolderTriple a b c]
  [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]
  [Fact (1 ≤ a)] [Fact (1 ≤ b)]

/-- Apply spatial Hölder first and temporal Hölder second. The order is fixed. -/
theorem mixed_holder_bound (B : E →L[ℝ] F →L[ℝ] G)
    (f : Lp (Lp E p μ) a ν) (g : Lp (Lp F q μ) b ν) :
    ‖(B.holderL μ p q r).holder c f g‖ ≤ ‖B‖ * ‖f‖ * ‖g‖ := by
  apply ((B.holderL μ p q r).norm_holder_apply_apply_le (r := c) f g).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right B.norm_holderL_le (norm_nonneg f)) (norm_nonneg g)

end Mixed

attribute [analytic_rule] norm_toLp_eq_lpNorm finite_lp_two_six_product elliptic_lp_estimate
  elliptic_lp_pairing_estimate mixed_holder_bound

end NormArith

public meta section

namespace NormArith.Parameters

open Lean Meta Elab Tactic
open scoped ENNReal

private def runInterpolation (left right target : TSyntax `term) (explain : Bool) : TacticM Unit :=
  withMainContext do
    let p ← reciprocal left
    let q ← reciprocal right
    let r ← reciprocal target
    let some weight := interpolationWeight? p q r |
      throwError "the target exponent is outside the endpoint interval"
    let goal ← getMainTarget
    unless goal.isAppOf ``LE.le do throwError "expected an lpNorm upper bound"
    let args := goal.getAppArgs
    let lhs := args[args.size - 2]!
    unless lhs.isAppOf ``MeasureTheory.lpNorm do throwError "expected an lpNorm upper bound"
    let values := lhs.getAppArgs
    let f ← Term.exprToSyntax values[values.size - 3]!
    let μ ← Term.exprToSyntax values.back!
    let θ ← rationalSyntax weight
    if weight == 0 || weight == 1 then
      evalTactic (← `(tactic| norm_num))
      trace[analytic_estimate.parameters] "Endpoint weight {weight}; checked by norm_num"
      if explain then logInfo m!"Endpoint weight {weight}; checked by norm_num"
      return
    evalTactic (← `(tactic| have : ENNReal.HolderTriple
      ($left / ENNReal.ofReal $θ) ($right / ENNReal.ofReal (1 - $θ)) $target := by
        holder_arith))
    evalTactic (← `(tactic| convert NormArith.finite_lp_interpolate
      (f := $f) (μ := $μ) (p := $left) (q := $right) (r := $target)
      (θ := $θ) (by norm_num) (by norm_num) (by assumption) (by assumption)
      using 1 <;> norm_num))
    trace[analytic_estimate.parameters]
      "Interpolation weight {weight}; theorem NormArith.finite_lp_interpolate"
    if explain then
      logInfo m!"Interpolation weight {weight}; theorem NormArith.finite_lp_interpolate"

/-- Plan a weight and apply finite interpolation to the target function. -/
elab "lp_interpolate" left:term:max right:term:max target:term:max : tactic =>
  runInterpolation left right target false

/-- Show the chosen weight and emit a checked proof that can be replayed. -/
elab "lp_interpolate?" left:term:max right:term:max target:term:max : tactic =>
  NormArith.withReplay true (runInterpolation left right target true)

end NormArith.Parameters
