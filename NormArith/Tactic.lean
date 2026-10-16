module

public import NormArith.Certificate
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public meta import Lean
public meta import NormArith.Search

/-!
# A bounded prototype for norm arithmetic

`norm_arith [h₁, ..., hₙ]` searches for a rational decomposition of the vector
in a goal `‖w‖ ≤ B`, using the vectors whose norms are bounded by the supplied
hypotheses. It checks the identity with `module`, constructs a triangle-inequality
certificate, then uses `norm_num` and `linarith` for scalar arithmetic.

`norm_arith?` additionally prints the successful vector decomposition.

This is deliberately a small, incomplete prototype. It searches subsets of at
most three of the first twelve supplied bounds, with 128 subset attempts and
16 candidate results. It does not implement Isabelle's full vertex enumeration.
-/

public meta section

namespace NormArith

open Lean Meta Elab Tactic

private abbrev Form := Array (Nat × Rat)

private def lastTwo? (e : Expr) : Option (Expr × Expr) :=
  let args := e.getAppArgs
  if args.size < 2 then none else some (args[args.size - 2]!, args.back!)

/-- Read closed rational scalar expressions without evaluating real numbers. -/
private partial def scalar? (input : Expr) : Option Rat := do
  let e := input.consumeMData
  if let .lit (.natVal n) := e then
    return (n : Rat)
  if e.isAppOf ``OfNat.ofNat then
    let .lit (.natVal n) := e.getArg! 1 | none
    return (n : Rat)
  if e.isAppOf ``Neg.neg then
    return -(← scalar? e.getAppArgs.back!)
  let (a, b) ← lastTwo? e
  if e.isAppOf ``HAdd.hAdd then return (← scalar? a) + (← scalar? b)
  if e.isAppOf ``HSub.hSub then return (← scalar? a) - (← scalar? b)
  if e.isAppOf ``HMul.hMul then return (← scalar? a) * (← scalar? b)
  if e.isAppOf ``HDiv.hDiv then
    let denominator ← scalar? b
    if denominator == 0 then none else return (← scalar? a) / denominator
  none

private def scale (c : Rat) (v : Form) : Form :=
  v.map fun (i, a) => (i, c * a)

/-- Atoms are formal expressions, not a claim of linear independence in `E`. -/
private partial def linearize (input : Expr) : StateT (Array Expr) MetaM Form := do
  let e := input.consumeMData
  if e.isAppOf ``OfNat.ofNat then
    if let .lit (.natVal 0) := e.getArg! 1 then return #[]
  if e.isAppOf ``Neg.neg then
    return scale (-1) (← linearize e.getAppArgs.back!)
  if let some (a, b) := lastTwo? e then
    if e.isAppOf ``HAdd.hAdd then
      return (← linearize a) ++ (← linearize b)
    if e.isAppOf ``HSub.hSub then
      return (← linearize a) ++ scale (-1) (← linearize b)
    if e.isAppOf ``HSMul.hSMul || e.isAppOf ``SMul.smul then
      -- Nat subtraction/division have different semantics. Only parse real scalars.
      let scalarType ← liftM (inferType a)
      if scalarType.isConstOf ``Real then
        if let some c := scalar? a then return scale c (← linearize b)
  let atoms ← get
  for i in [:atoms.size] do
    if atoms[i]! == e then return #[(i, 1)]
  set (atoms.push e)
  return #[(atoms.size, 1)]

private def dense (dimension : Nat) (form : Form) : Array Rat := Id.run do
  let mut result : Array Rat := Array.replicate dimension 0
  for (i, c) in form do
    result := result.set! i (result[i]! + c)
  return result

private def normArgument? (input : Expr) : Option Expr :=
  let e := input.consumeMData
  if e.isAppOf ``Norm.norm then some e.getAppArgs.back! else none

private structure Source where
  vector : Expr
  proof : Expr
  deriving Inhabited

private def readSource (stx : TSyntax `term) : TacticM Source := do
  let proof ← Term.elabTermAndSynthesize stx none
  let type ← instantiateMVars (← inferType proof)
  unless type.isAppOf ``LE.le do
    throwErrorAt stx "expected an upper bound of the form ‖v‖ ≤ b"
  let some (lhs, _) := lastTwo? type | throwErrorAt stx "expected a norm bound"
  let some vector := normArgument? lhs |
    throwErrorAt stx "the left side of this bound must be a norm"
  return { vector, proof }

private def ratSyntax (q : Rat) : TacticM (TSyntax `term) := do
  let magnitude : TSyntax `term := ⟨Syntax.mkNumLit (toString q.num.natAbs)⟩
  let numerator ← if q.num < 0 then `(-$magnitude) else pure magnitude
  let denominator : TSyntax `term := ⟨Syntax.mkNumLit (toString q.den)⟩
  `((($numerator : ℝ) / ($denominator : ℝ)))

private def proveCandidate (sources : Array Source) (target : Expr)
    (coefficients : Array Rat) (explain : Bool) : TacticM Unit := do
  let space ← Term.exprToSyntax (← inferType target)
  let targetStx ← Term.exprToSyntax target
  let mut combination ← `((0 : $space))
  let mut proof ← `(NormArith.bound_zero (E := $space))
  for i in [:sources.size] do
    let coefficient := coefficients[i]!
    if coefficient != 0 then
      let c ← ratSyntax coefficient
      let v ← Term.exprToSyntax sources[i]!.vector
      let h ← Term.exprToSyntax sources[i]!.proof
      combination ← `($c • $v + $combination)
      proof ← `(NormArith.bound_add (NormArith.bound_smul $c $h) $proof)
  let certificate := mkIdent (← mkFreshUserName `norm_arith_bound)
  let identity := mkIdent (← mkFreshUserName `norm_arith_identity)
  let combinationExpr ← Term.elabTermAndSynthesize combination (some (← inferType target))
  evalTactic (← `(tactic| (
    have $identity : $targetStx = $combination := by module
    have $certificate := NormArith.bound_of_eq $identity $proof
    norm_num at $certificate:ident <;> norm_num <;> linarith)))
  if explain then
    logInfo m!"norm_arith decomposition: {target} = {combinationExpr}"

private def run (hypotheses : Array (TSyntax `term)) (explain : Bool) : TacticM Unit :=
  withoutRecover <| withMainContext do
    let goal ← instantiateMVars (← getMainTarget)
    unless goal.isAppOf ``LE.le do
      throwError "norm_arith expects a goal of the form ‖w‖ ≤ B"
    let some (lhs, _) := lastTwo? goal | throwError "expected a norm inequality"
    let some target := normArgument? lhs |
      throwError "norm_arith expects a norm on the left side"
    let sources ← hypotheses.mapM readSource
    let reification : StateT (Array Expr) MetaM (Array Form × Form) := do
      let sourceForms ← sources.mapM fun (s : Source) => linearize s.vector
      let targetForm ← linearize target
      pure (sourceForms, targetForm)
    let ((sourceForms, targetForm), atoms) ← reification.run #[]
    let columns := sourceForms.map (dense atoms.size)
    let candidates := Search.decompositions columns (dense atoms.size targetForm)
    if candidates.isEmpty then
      throwError "norm_arith found no decomposition within its search limits; \
        supply relevant norm bounds first or inspect NormArith.Search.Config"
    let mut lastError : MessageData := m!"no candidate was checked"
    for candidate in candidates do
      let saved ← saveState
      try
        focusAndDone (proveCandidate sources target candidate explain)
        return
      catch error =>
        lastError := error.toMessageData
        saved.restore
    throwError "norm_arith found {candidates.size} decomposition(s), but none closed the goal; \
      their scalar bounds may be too weak, or the expression is outside this prototype's scope.\n\
      Last candidate error:\n{lastError}"

syntax (name := normArith) "norm_arith" "[" term,* "]" : tactic
syntax (name := normArithExplain) "norm_arith?" "[" term,* "]" : tactic

elab_rules : tactic
  | `(tactic| norm_arith [$hs,*]) => run hs.getElems false
  | `(tactic| norm_arith? [$hs,*]) => run hs.getElems true

end NormArith
