module

public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Module
public meta import Lean
public meta import NormArith.Facts

/-!
# Arithmetic with explicit seminorms

`seminorm_arith` first tries structural seminorm bounds and scalar arithmetic.
Its fallback uses the same exact LP backend as `norm_arith`. Each real seminorm
has a separate supporting-functional block. Local vector equalities are shared.

`seminorm_arith [h₁, h₂]` selects analytic premises. Local scalar comparisons
remain available. A supplied universal comparison is specialized at observed
vectors. Distinct seminorms are never identified without a checked equality.

The frontend is deliberately bounded and incomplete. It does not synthesize
embeddings between seminorms, and failure is not a mathematical counterexample.
-/

public section

namespace NormArith

variable {𝕜 E : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

theorem seminorm_nonneg (p : Seminorm 𝕜 E) (x : E) : 0 ≤ p x :=
  apply_nonneg p x

theorem seminorm_add_le (p : Seminorm 𝕜 E) (x y : E) :
    p (x + y) ≤ p x + p y := map_add_le_add p x y

theorem seminorm_sub_le (p : Seminorm 𝕜 E) (x y : E) :
    p (x - y) ≤ p x + p y := map_sub_le_add p x y

theorem seminorm_neg_eq (p : Seminorm 𝕜 E) (x : E) : p (-x) = p x :=
  map_neg_eq_map p x

theorem seminorm_smul_eq (p : Seminorm 𝕜 E) (c : 𝕜) (x : E) :
    p (c • x) = ‖c‖ * p x := map_smul_eq_mul p c x

theorem seminorm_add_left_le (p : Seminorm 𝕜 E) (x y : E) :
    p x ≤ p (x + y) + p y := by
  simpa only [add_sub_cancel_right] using seminorm_sub_le p (x + y) y

theorem seminorm_add_right_le (p : Seminorm 𝕜 E) (x y : E) :
    p y ≤ p (x + y) + p x := by
  simpa only [add_sub_cancel_left] using seminorm_sub_le p (x + y) x

theorem seminorm_sub_left_le (p : Seminorm 𝕜 E) (x y : E) :
    p x ≤ p (x - y) + p y := by
  simpa only [sub_add_cancel] using seminorm_add_le p (x - y) y

theorem seminorm_sub_right_le (p : Seminorm 𝕜 E) (x y : E) :
    p y ≤ p (x - y) + p x := by
  have h := seminorm_sub_le p x (x - y)
  simpa only [sub_sub_cancel, add_comm] using h

theorem seminorm_sub_of_eq (p : Seminorm 𝕜 E) {x y : E} (h : x = y) :
    p (x - y) = 0 := by simp [h]

theorem seminorm_bound_zero (p : Seminorm 𝕜 E) : p 0 ≤ 0 := by simp

theorem seminorm_bound_add (p : Seminorm 𝕜 E) {x y : E} {a b : ℝ}
    (hx : p x ≤ a) (hy : p y ≤ b) : p (x + y) ≤ a + b :=
  (seminorm_add_le p x y).trans (add_le_add hx hy)

theorem seminorm_bound_smul (p : Seminorm 𝕜 E) (c : 𝕜) {x : E} {b : ℝ}
    (hx : p x ≤ b) : p (c • x) ≤ ‖c‖ * b := by
  rw [seminorm_smul_eq]
  exact mul_le_mul_of_nonneg_left hx (norm_nonneg c)

theorem seminorm_bound_of_eq (p : Seminorm 𝕜 E) {x y : E} {b : ℝ}
    (hxy : x = y) (hy : p y ≤ b) : p x ≤ b := by simpa only [hxy] using hy

end NormArith

public meta section

register_option seminorm_arith.forceLP : Bool := {
  defValue := false
  descr := "Require the compact LP backend for a seminorm estimate." }

initialize Lean.registerTraceClass `seminorm_arith.lp

namespace NormArith.SeminormSupport

open Lean Meta Elab Tactic

private def lastTwo? (e : Expr) : Option (Expr × Expr) :=
  let args := e.getAppArgs
  if args.size < 2 then none else some (args[args.size - 2]!, args.back!)

/-- Recognize bundled seminorm evaluation without unfolding the seminorm. -/
def application? (input : Expr) : MetaM (Option (Expr × Expr)) := do
  let e := input.consumeMData
  unless e.isAppOf ``DFunLike.coe do return none
  let some (p, x) := lastTwo? e | return none
  if (← whnf (← inferType p)).isAppOf ``Seminorm then return some (p, x)
  return none

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
  if let some (p, x) ← liftM <| application? e then
    addFact ``NormArith.seminorm_nonneg #[p, x]
    let evalAt (v : Expr) := mkApp e.appFn! v
    if x.isAppOf ``Neg.neg then
      let v := x.getAppArgs.back!
      addFact ``NormArith.seminorm_neg_eq #[p, v]
      collect (evalAt v)
    if let some (a, b) := lastTwo? x then
      if x.isAppOf ``HAdd.hAdd then
        for name in #[``NormArith.seminorm_add_le, ``NormArith.seminorm_add_left_le,
            ``NormArith.seminorm_add_right_le] do addFact name #[p, a, b]
        collect (evalAt a)
        collect (evalAt b)
      if x.isAppOf ``HSub.hSub then
        for name in #[``NormArith.seminorm_sub_le, ``NormArith.seminorm_sub_left_le,
            ``NormArith.seminorm_sub_right_le] do addFact name #[p, a, b]
        collect (evalAt a)
        collect (evalAt b)
      if x.isAppOf ``HSMul.hSMul || x.isAppOf ``SMul.smul then
        addFact ``NormArith.seminorm_smul_eq #[p, a, b]
        collect (evalAt b)
    return
  for arg in e.getAppArgs do collect arg

/-- Generate a bounded collection of ordinary Lean proofs. -/
def constraints (inputs : Array Expr) : MetaM (Array Expr) := do
  let (_, state) ← (inputs.forM collect).run {}
  return state.facts

/-- Add a proof and normalize its numerical coefficients. -/
def noteFact (proof : Expr) : TacticM Unit := withMainContext do
  let name ← mkFreshUserName `analytic_fact
  let (_, goal) ← (← getMainGoal).note name proof
  replaceMainGoal [goal]
  let stx := mkIdent name
  -- Full `norm_num` simplifies facts such as `0 ≤ ‖x‖` to `True`, and can
  -- similarly erase a negation identity before the scalar solver uses it.
  -- Restrict simplification to scalar norms and numerical evaluation.
  evalTactic (← `(tactic| try norm_num only [Real.norm_eq_abs] at $stx:ident))

/-- Hints are additional proved facts, not a replacement for local hypotheses. -/
def addHints (hints : Array (TSyntax `term)) : TacticM Unit := do
  for hint in hints do
    withMainContext do
      let proof ← Term.elabTermAndSynthesize hint none
      unless ← isProp (← inferType proof) do throwErrorAt hint "expected a proved proposition"
      noteFact proof

def contextInputs : TacticM (Array Expr) := withMainContext do
  let mut inputs := #[← getMainTarget]
  for decl in ← getLCtx do
    if !decl.isImplementationDetail && (← isProp decl.type) then
      inputs := inputs.push decl.type
  return inputs

private partial def observations (input : Expr) : StateT (Array Expr) MetaM Unit := do
  let e := (← liftM (zetaReduce input)).consumeMData
  if (← liftM (application? e)).isSome then
    unless (← get).contains e do modify (·.push e)
    return
  for arg in e.getAppArgs do observations arg

private def allObservations : TacticM (Array Expr) := withMainContext do
  return (← ((← contextInputs).forM observations).run #[]).2

private def contextFacts : TacticM (Array Expr) := withMainContext do
  let mut facts := #[]
  for decl in ← getLCtx do
    if !decl.isImplementationDetail && (← isProp decl.type) then
      facts := facts.push decl.toExpr
  return facts

/-- Only established inputs are used to specialize a universal bridge. -/
private def specializeBounds : TacticM Unit := withMainContext do
  let inputs ← contextFacts
  let terms ← allObservations
  let mut seen : Array Expr := #[]
  for h in inputs do
    for term in terms do
      let some (_, x) ← application? term | continue
      let type ← whnf (← inferType h)
      unless type.isForall do continue
      unless ← isDefEq type.bindingDomain! (← inferType x) do continue
      let proof := mkApp h x
      let conclusion ← inferType proof
      if conclusion.isForall || seen.contains conclusion then continue
      seen := seen.push conclusion
      noteFact proof

private def addRelations : TacticM Unit := withMainContext do
  let facts ← contextFacts
  let terms ← allObservations
  let mut families : Array Expr := #[]
  for term in terms do
    let some (p, _) ← withMainContext (application? term) | continue
    unless families.contains p do families := families.push p
  for h in facts do
    for p in families do
      let type := (← inferType h).consumeMData
      unless type.isAppOf ``Eq do continue
      let saved ← saveState
      try
        let proof ← mkAppM ``seminorm_sub_of_eq #[p, h]
        unless proof.hasMVar do noteFact proof
      catch _ => saved.restore

private def scalarComparison (type : Expr) : MetaM Bool := do
  unless type.isAppOf ``LE.le || type.isAppOf ``LT.lt || type.isAppOf ``Eq ||
      type.isAppOf ``GE.ge || type.isAppOf ``GT.gt do return false
  let some (a, _) := lastTwo? type | return false
  return ← isDefEq (← inferType a) (mkConst ``Real)

private def ratSyntax (q : Rat) : TacticM (TSyntax `term) := do
  let magnitude : TSyntax `term := ⟨Syntax.mkNumLit (toString q.num.natAbs)⟩
  let numerator ← if q.num < 0 then `(-$magnitude) else pure magnitude
  let denominator : TSyntax `term := ⟨Syntax.mkNumLit (toString q.den)⟩
  `((($numerator : ℝ) / ($denominator : ℝ)))

private def addCertificate (terms : Array Expr) (proposal : LP.Proposal) : TacticM Unit :=
  withMainContext <| Term.withoutErrToSorry do
    let some (p, target) ← application? terms[proposal.target]! |
      throwError "expected a seminorm observation"
    let pSyntax ← Term.exprToSyntax p
    let mut combination? : Option (TSyntax `term × TSyntax `term) := none
    for i in [:terms.size] do
      let c := proposal.coefficients[i]!
      if c == 0 then continue
      let some (sourceP, source) ← application? terms[i]! |
        throwError "expected a seminorm source"
      unless ← isDefEq p sourceP do throwError "certificate mixes seminorm families"
      let sourceSyntax ← Term.exprToSyntax source
      let coefficient ← ratSyntax c
      let multiple ← `($coefficient • $sourceSyntax)
      let bound ← `(seminorm_bound_smul $pSyntax $coefficient (le_refl ($pSyntax $sourceSyntax)))
      combination? ← match combination? with
        | none => pure (some (multiple, bound))
        | some (v, h) => pure (some (← `($multiple + $v),
            ← `(seminorm_bound_add $pSyntax $bound $h)))
    let (combination, bound) ← match combination? with
      | some pair => pure pair
      | none => do
        let space ← Term.exprToSyntax (← inferType target)
        pure (← `((0 : $space)), ← `(seminorm_bound_zero $pSyntax))
    let combinationExpr ← Term.elabTermAndSynthesize combination (some (← inferType target))
    let identity ← Term.elabTermAndSynthesize (← `(by module))
      (some (← mkEq target combinationExpr))
    let boundProof ← Term.elabTermAndSynthesize bound none
    noteFact (← mkAppM ``seminorm_bound_of_eq #[p, identity, boundProof])

/-- Search data is checked again with seminorm lemmas and actual vector identities. -/
private def compactLP : TacticM Unit := withMainContext do
  let terms ← allObservations
  if terms.isEmpty then throwError "no explicit seminorm observations"
  let pairs : Array (Expr × Expr) ← terms.mapM fun term => do
    let some pair ← application? term | throwError "expected a seminorm observation"
    return pair
  let mut groups := #[]
  for (p, _) in pairs do
    let mut group := #[]
    let type ← inferType p
    if type.getAppArgs[0]!.isConstOf ``Real then
      for i in [:pairs.size] do
        if ← isDefEq p pairs[i]!.1 then group := group.push i
    groups := groups.push group
  let vectorReification : StateT (Array Expr) MetaM (Array Reify.Form) :=
    pairs.mapM fun pair => Reify.linearize pair.2
  let (forms, atoms) ← vectorReification.run #[]
  let columns := forms.map (Reify.dense atoms.size)
  let facts ← (← contextFacts).filterM fun h => do scalarComparison (← inferType h)
  let target ← getMainTarget
  let reification : StateT (Array Expr) MetaM (Array LP.Row × LP.Row) := do
    let rows ← facts.mapM fun h => do Reify.lpComparison (← liftM (inferType h))
    return (rows, ← Reify.lpComparison target)
  let ((rows, goal), _) ← reification.run terms
  let mut proposals := #[]
  for negated in Reify.lpNegations goal do
    let result ← LP.propose columns groups (rows.push negated)
    trace[seminorm_arith.lp] "{result.rowCount} rows; {result.proposals.size} checked decompositions"
    proposals := proposals ++ result.proposals
  for proposal in proposals do addCertificate terms proposal
  evalTactic (← `(tactic| linarith))

private def run (hints : Option (Array (TSyntax `term))) : TacticM Unit :=
  focusAndDone <| withoutRecover do
    selectContext hints
    if (← getGoals).isEmpty then return
    let facts ← withMainContext <| constraints (← contextInputs)
    for proof in facts do
      if (← getGoals).isEmpty then return
      noteFact proof
    specializeBounds
    addRelations
    unless seminorm_arith.forceLP.get (← getOptions) do
      evalTactic (← `(tactic| try first | assumption | positivity | linarith | nlinarith))
      if (← getGoals).isEmpty then return
    compactLP

syntax (name := seminormArith) "seminorm_arith" : tactic
syntax (name := seminormArithHints) "seminorm_arith" "[" term,* "]" : tactic

elab_rules : tactic
  | `(tactic| seminorm_arith) => run none
  | `(tactic| seminorm_arith [$hs,*]) => run (some hs.getElems)

end NormArith.SeminormSupport
