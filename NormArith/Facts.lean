module

public meta import NormArith.Reify
public meta import Lean.Elab.Tactic.Basic

/-! An explicit fact list keeps only its proofs and local scalar comparisons. -/

public meta section

namespace NormArith

open Lean Meta Elab Tactic Reify

private partial def plainScalar (input : Expr) : Bool := Id.run do
  let e := input.consumeMData
  if e.isFVar || (scalar? e).isSome then return true
  if e.isAppOf ``Neg.neg || e.isAppOf ``Inv.inv then
    return plainScalar e.getAppArgs.back!
  if let some (a, b) := lastTwo? e then
    if e.isAppOf ``HAdd.hAdd || e.isAppOf ``HSub.hSub || e.isAppOf ``HMul.hMul ||
        e.isAppOf ``HDiv.hDiv || e.isAppOf ``HPow.hPow then
      return plainScalar a && plainScalar b
  return false

private def scalarPremise (type : Expr) : MetaM Bool := do
  let e ← zetaReduce type
  unless e.isAppOf ``LE.le || e.isAppOf ``LT.lt || e.isAppOf ``Eq ||
      e.isAppOf ``GE.ge || e.isAppOf ``GT.gt do return false
  let some (a, b) := lastTwo? e | return false
  return (← isDefEq (← inferType a) (mkConst ``Real)) && plainScalar a && plainScalar b

/-- Copy selected proofs before clearing other assumptions from the search goal. -/
def selectContext (hints : Option (Array (TSyntax `term))) : TacticM Unit := do
  let some hints := hints | return
  let (proofs, omitted) ← withMainContext do
    let proofs ← hints.mapM fun hint => do
      let proof ← Term.elabTermAndSynthesize hint none
      unless ← isProp (← inferType proof) do
        throwErrorAt hint "expected a proved proposition"
      return proof
    let mut omitted := #[]
    for decl in ← getLCtx do
      unless ← isProp decl.type do continue
      if ← scalarPremise decl.type then continue
      if let some name ← isClass? decl.type then
        if name != ``Fact then continue
      omitted := omitted.push decl.fvarId
    return (proofs, omitted)
  for proof in proofs do
    withMainContext do
      let (_, next) ← (← getMainGoal).note (← mkFreshUserName `selected_fact) proof
      replaceMainGoal [next]
  let next ← (← getMainGoal).tryClearMany omitted
  next.withContext do
    for id in omitted do
      if (← getLCtx).contains id then
        throwError "cannot exclude a premise used by the goal or a dependent declaration"
  replaceMainGoal [next]

end NormArith
