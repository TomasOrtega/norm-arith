module

public import NormArith.Tactic
public import NormArith.Seminorm
public import NormArith.Rules
public meta import NormArith.Facts
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public meta import Lean

/-!
# Checked analytic estimates

`analytic_estimate` combines proved norm, seminorm, operator, and scalar bounds.
It applies registered analytic theorems and checks every premise. Search has
explicit depth and application limits.

`analytic_estimate [facts]` selects its analytic premises. Local scalar
comparisons remain available. Membership, exponent, and domain assumptions must
be supplied when a theorem needs them. The tactic does not invent these facts.

`analytic_estimate?` reports the checked estimate and the selected theorem names,
then offers a proof that can be replayed without search.

This module includes Young, absorption, and finite-`Lp` bridge lemmas. More
function-space and fixed-point rules are available through optional imports.
-/

public section

namespace NormArith

open scoped ENNReal NNReal

section Scalar

/-- Young's inequality with an explicit positive absorption budget. -/
theorem young_mul (a b ε : ℝ) (hε : 0 < ε) :
    a * b ≤ ε * a ^ 2 + b ^ 2 / (4 * ε) := by
  have hpos : 0 < 4 * ε := by positivity
  have h : a * b - ε * a ^ 2 ≤ b ^ 2 / (4 * ε) := by
    apply (le_div_iff₀ hpos).2
    nlinarith [sq_nonneg (2 * ε * a - b)]
  linarith

/-- Spend half the coercive term to absorb an energy cross term. -/
theorem energy_absorb {E ν A F : ℝ} (hν : 0 < ν)
    (h : E + ν * A ^ 2 ≤ F * A) :
    E + (ν / 2) * A ^ 2 ≤ F ^ 2 / (2 * ν) := by
  have hy := young_mul A F (ν / 2) (by positivity)
  have heq : 4 * (ν / 2) = 2 * ν := by ring
  rw [heq] at hy
  nlinarith

/-- Absorb a bounded multiple of a nonnegative quantity. -/
theorem absorb {A B θ q : ℝ} (hA : 0 ≤ A) (hθ : θ ≤ q) (hq : q < 1)
    (h : A ≤ B + θ * A) : A ≤ B / (1 - q) := by
  apply (le_div_iff₀ (sub_pos.mpr hq)).2
  have hm := mul_le_mul_of_nonneg_right hθ hA
  nlinarith

theorem absorb_half {A B θ : ℝ} (hA : 0 ≤ A) (hθ : θ ≤ 1 / 2)
    (h : A ≤ B + θ * A) : A ≤ 2 * B := by
  have hm := mul_le_mul_of_nonneg_right hθ hA
  nlinarith

/-- A coupled absorption example with exact rational coefficients. -/
theorem coupled_absorb {A B F G : ℝ}
    (hA : A ≤ F + B / 4) (hB : B ≤ G + A / 2) :
    A ≤ 8 * F / 7 + 2 * G / 7 ∧ B ≤ 4 * F / 7 + 8 * G / 7 := by
  constructor <;> linarith

/-- Scalar estimate block behind a small-drift elliptic estimate.

`U` and `G` can denote function and derivative norms, `F` the forcing norm, and
`B` a coefficient norm. All analytic content is explicit in the hypotheses.
-/
theorem elliptic_absorb {ν S F B G U : ℝ}
    (hν : 0 < ν) (hS : 0 ≤ S) (hF : 0 ≤ F) (hB : 0 ≤ B) (hG : 0 ≤ G)
    (hSobolev : U ≤ S * G) (hsmall : S * B ≤ ν / 2)
    (henergy : ν * G ^ 2 ≤ F * U + B * G * U) :
    G ≤ 2 * S * F / ν ∧ U ≤ 2 * S ^ 2 * F / ν := by
  have hF' := mul_le_mul_of_nonneg_left hSobolev hF
  have hB' := mul_le_mul_of_nonneg_left hSobolev (mul_nonneg hB hG)
  have hs' := mul_le_mul_of_nonneg_right hsmall (sq_nonneg G)
  have hcoercive : (ν * G) * G ≤ (2 * S * F) * G := by nlinarith
  have hbound : G ≤ 2 * S * F / ν := by
    apply (le_div_iff₀ hν).2
    by_cases hzero : G = 0
    · subst G
      simp only [zero_mul]
      positivity
    · have hpos : 0 < G := lt_of_le_of_ne hG (Ne.symm hzero)
      have hc := (mul_le_mul_iff_left₀ hpos).mp hcoercive
      nlinarith
  refine ⟨hbound, ?_⟩
  calc
    U ≤ S * G := hSobolev
    _ ≤ S * (2 * S * F / ν) := mul_le_mul_of_nonneg_left hbound hS
    _ = 2 * S ^ 2 * F / ν := by ring

/-- The energy premise is first so template matching fixes the coefficient norm
before trying to discharge nonnegativity side conditions. -/
theorem elliptic_absorb_from_energy {ν S F B G U : ℝ}
    (henergy : ν * G ^ 2 ≤ F * U + B * G * U)
    (hSobolev : U ≤ S * G) (hsmall : S * B ≤ ν / 2)
    (hν : 0 < ν) (hS : 0 ≤ S) (hF : 0 ≤ F) (hB : 0 ≤ B) (hG : 0 ≤ G) :
    G ≤ 2 * S * F / ν ∧ U ≤ 2 * S ^ 2 * F / ν :=
  elliptic_absorb hν hS hF hB hG hSobolev hsmall henergy

end Scalar

section Operators

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [SeminormedAddCommGroup G]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G]

/-- The operator estimate, with explicit arguments for the frontend. -/
theorem linear_apply_bound (T : E →L[𝕜] F) (x : E) :
    ‖T x‖ ≤ ‖T‖ * ‖x‖ := T.le_opNorm x

/-- A bilinear application bound avoiding nested operator-norm bookkeeping. -/
theorem bilinear_apply_bound (B : E →L[𝕜] F →L[𝕜] G) (x : E) (y : F) :
    ‖B x y‖ ≤ ‖B‖ * ‖x‖ * ‖y‖ :=
  ((B x).le_opNorm y).trans
    (mul_le_mul_of_nonneg_right (B.le_opNorm x) (norm_nonneg y))

/-- A checked perturbation estimate for a continuous bilinear map. -/
theorem bilinear_sub_bound (B : E →L[𝕜] F →L[𝕜] G) (x x' : E) (y y' : F) :
    ‖B x y - B x' y'‖ ≤
      ‖B‖ * (‖x - x'‖ * ‖y‖ + ‖x'‖ * ‖y - y'‖) := by
  have heq : B x y - B x' y' = B (x - x') y + B x' (y - y') := by
    simp only [map_sub, sub_apply]
    abel
  rw [heq]
  have h₁ := bilinear_apply_bound B (x - x') y
  have h₂ := bilinear_apply_bound B x' (y - y')
  have htriangle := norm_add_le (B (x - x') y) (B x' (y - y'))
  nlinarith

end Operators

section FixedPointEstimates

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Radius `2 * A` is invariant under a small quadratic perturbation.

This is an estimate lemma, not an existence or global-uniqueness theorem.
-/
theorem quadratic_ball_bound (B : X →L[𝕜] X →L[𝕜] X) (a u : X) {A : ℝ}
    (hA : 0 ≤ A) (ha : ‖a‖ ≤ A) (hu : ‖u‖ ≤ 2 * A)
    (hsmall : 8 * ‖B‖ * A ≤ 1) : ‖a + B u u‖ ≤ 2 * A := by
  have hB := bilinear_apply_bound B u u
  have htriangle := norm_add_le a (B u u)
  have hsq : ‖u‖ * ‖u‖ ≤ (2 * A) * (2 * A) :=
    mul_self_le_mul_self (norm_nonneg u) hu
  have hscaled := mul_le_mul_of_nonneg_left hsq (norm_nonneg B)
  have hbudget := mul_le_mul_of_nonneg_right hsmall hA
  nlinarith

/-- The same radius gives a checked Lipschitz constant `1/2`. -/
theorem quadratic_contraction_bound (B : X →L[𝕜] X →L[𝕜] X) (a u v : X) {A : ℝ}
    (hu : ‖u‖ ≤ 2 * A) (hv : ‖v‖ ≤ 2 * A)
    (hsmall : 8 * ‖B‖ * A ≤ 1) :
    ‖(a + B u u) - (a + B v v)‖ ≤ (1 / 2 : ℝ) * ‖u - v‖ := by
  have hperturb := bilinear_sub_bound B u v u v
  have hsum : ‖u‖ + ‖v‖ ≤ 4 * A := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hsum (norm_nonneg B)
  have hconstant : ‖B‖ * (‖u‖ + ‖v‖) ≤ (1 / 2 : ℝ) := by nlinarith
  have hfinal := mul_le_mul_of_nonneg_right hconstant (norm_nonneg (u - v))
  simpa only [add_sub_add_left_eq_sub] using (show
    ‖B u u - B v v‖ ≤ (1 / 2 : ℝ) * ‖u - v‖ by nlinarith)

/-- Stability after a contraction estimate has been established. -/
theorem fixed_point_stability {u v a b : X}
    (h : ‖u - v‖ ≤ ‖a - b‖ + (1 / 2 : ℝ) * ‖u - v‖) :
    ‖u - v‖ ≤ 2 * ‖a - b‖ := by linarith

end FixedPointEstimates

section LpAdapters

open MeasureTheory

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  {μ : Measure α} {p : ℝ≥0∞} {f g : α → E}

/-- The finite adapter requires membership before converting back from reals. -/
theorem eLpNorm_le_of_lpNorm_le (hf : MemLp f p μ) {r : ℝ}
    (h : lpNorm f p μ ≤ r) : eLpNorm f p μ ≤ ENNReal.ofReal r := by
  rw [← ofReal_lpNorm hf]
  exact ENNReal.ofReal_le_ofReal h

/-- A finite extended-real bound can safely be transported to real arithmetic. -/
theorem lpNorm_le_of_eLpNorm_le {r : ℝ≥0}
    (h : eLpNorm f p μ ≤ (r : ℝ≥0∞)) : lpNorm f p μ ≤ (r : ℝ) := by
  have ht := ENNReal.toReal_mono ENNReal.coe_ne_top h
  simpa only [toReal_eLpNorm, ENNReal.coe_toReal] using ht

/-- A proved triangle bound for raw functions, with all membership explicit. -/
theorem finite_lp_add (hf : MemLp f p μ) (hp : 1 ≤ p) :
    lpNorm (f + g) p μ ≤ lpNorm f p μ + lpNorm g p μ := lpNorm_add_le hf hp

end LpAdapters

attribute [analytic_rule] young_mul energy_absorb elliptic_absorb_from_energy
  quadratic_ball_bound quadratic_contraction_bound eLpNorm_le_of_lpNorm_le
  lpNorm_le_of_eLpNorm_le finite_lp_add

end NormArith

public meta section

namespace NormArith.AnalyticSupport

open Lean Meta Elab Tactic

private def lastTwo? (e : Expr) : Option (Expr × Expr) :=
  let args := e.getAppArgs
  if args.size < 2 then none else some (args[args.size - 2]!, args.back!)

private def application? (input : Expr) : Option (Expr × Expr) :=
  let e := input.consumeMData
  if e.isAppOf ``DFunLike.coe then lastTwo? e else none

private structure CollectState where
  seen : Array Expr := #[]
  facts : Array Expr := #[]
  remaining : Nat := 512

private def addFact (name : Name) (args : Array Expr) : StateT CollectState MetaM Unit := do
  try
    let proof ← liftM <| mkAppM name args
    unless proof.hasMVar do modify fun s => { s with facts := s.facts.push proof }
  catch _ => pure ()

private partial def collect (input : Expr) : StateT CollectState MetaM Unit := do
  let e := input.consumeMData
  let state ← get
  if state.remaining == 0 || state.seen.contains e then return
  modify fun s => { s with seen := s.seen.push e, remaining := s.remaining - 1 }
  if e.isAppOf ``Norm.norm then
    let x := e.getAppArgs.back!
    addFact ``norm_nonneg #[x]
    let normAt (v : Expr) := mkApp e.appFn! v
    if x.isAppOf ``Neg.neg then
      let v := x.getAppArgs.back!
      addFact ``norm_neg #[v]
      collect (normAt v)
    if let some (a, b) := lastTwo? x then
      if x.isAppOf ``HAdd.hAdd then
        addFact ``norm_add_le #[a, b]
        collect (normAt a)
        collect (normAt b)
      if x.isAppOf ``HSub.hSub then
        addFact ``norm_sub_le #[a, b]
        collect (normAt a)
        collect (normAt b)
        if let some (left, y) := application? a then
          if let some (B, u) := application? left then
            if let some (right, y') := application? b then
              if let some (B', u') := application? right then
                if B == B' then addFact ``NormArith.bilinear_sub_bound #[B, u, u', y, y']
      if x.isAppOf ``HSMul.hSMul || x.isAppOf ``SMul.smul then
        addFact ``norm_smul #[a, b]
        collect (normAt b)
      if x.isAppOf ``HMul.hMul then
        addFact ``norm_mul_le #[a, b]
        collect (normAt a)
        collect (normAt b)
    if let some (T, u) := application? x then
      addFact ``NormArith.linear_apply_bound #[T, u]
      if let some (B, v) := application? T then
        addFact ``NormArith.bilinear_apply_bound #[B, v, u]
    return
  for arg in e.getAppArgs do collect arg

private def constraints (inputs : Array Expr) : MetaM (Array Expr) := do
  let (_, state) ← (inputs.forM collect).run {}
  return state.facts

private def run (hints : Option (Array (TSyntax `term))) (explain : Bool) : TacticM Unit :=
  withReplay explain <| focusAndDone <| withoutRecover do
    let originalGoal ← getMainGoal
    selectContext hints
    if (← getGoals).isEmpty then return
    let inputs ← SeminormSupport.contextInputs
    let facts ← withMainContext do
      return (← constraints inputs) ++ (← SeminormSupport.constraints inputs false)
    for proof in facts do
      if (← getGoals).isEmpty then return
      SeminormSupport.noteFact proof
    applyAnalyticRules
    if explain then
      let proof ← instantiateMVars (mkMVar originalGoal)
      let rules := analyticRules.getState (← getEnv) ++
        #[``NormArith.linear_apply_bound, ``NormArith.bilinear_apply_bound,
          ``NormArith.bilinear_sub_bound]
      let used := rules.filter fun name => (proof.find? (·.isConstOf name)).isSome
      originalGoal.withContext do
        let target ← originalGoal.getType
        let mut parameters : Array Name := #[]
        let mut premises : Array Name := #[]
        for decl in ← getLCtx do
          if decl.isImplementationDetail then continue
          let occurs := fun (e : Expr) => (e.find? (· == decl.toExpr)).isSome
          if decl.type.isConstOf ``Real && occurs target then
            parameters := parameters.push decl.userName
          if (← isProp decl.type) && occurs proof then
            premises := premises.push decl.userName
        logInfo m!"Checked estimate: {target}"
        unless parameters.isEmpty do logInfo m!"Scalar parameters: {parameters.toList}"
        unless premises.isEmpty do logInfo m!"Premises used: {premises.toList}"
      unless used.isEmpty do logInfo m!"Analytic theorems: {used.toList}"

syntax (name := analyticEstimate) "analytic_estimate" : tactic
syntax (name := analyticEstimateHints) "analytic_estimate" "[" term,* "]" : tactic
syntax (name := analyticEstimateExplain) "analytic_estimate?" : tactic
syntax (name := analyticEstimateExplainHints) "analytic_estimate?" "[" term,* "]" : tactic

elab_rules : tactic
  | `(tactic| analytic_estimate) => run none false
  | `(tactic| analytic_estimate [$hs,*]) => run (some hs.getElems) false
  | `(tactic| analytic_estimate?) => run none true
  | `(tactic| analytic_estimate? [$hs,*]) => run (some hs.getElems) true

end NormArith.AnalyticSupport
