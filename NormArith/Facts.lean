module

public meta import NormArith.Reify
public meta import Lean.Elab.Tactic.Basic

/-!
An explicit fact list keeps its proofs, local scalar comparisons, and the
structural classes listed below. Other classes can hide analytic bounds in
either Prop or Type. Select their bound projections explicitly. Selected Prop
class proofs remain local instances. Ordinary data is unchanged. Calls without
a fact list keep the full context.

`Nonempty`, `Nontrivial`, `Subsingleton`, and `Finite` are kept only on ambient
type variables. Their instances on propositions or constructed types can encode
an omitted bound.
-/

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

private def structuralClass (name : Name) (type : Expr) : MetaM Bool := do
  if #[`Subsingleton, `Nontrivial, `Nonempty, `Finite].contains name then
    let type ← whnf (← zetaReduce type)
    let some space := type.getAppArgs[0]? | return false
    return space.isFVar && (← inferType space).isSort && !(← isProp space)
  return #[`CompleteSpace, `CharZero,
    `IsScalarTower, `SMulCommClass, `IsCentralScalar, `NoZeroSMulDivisors,
    `NormSMulClass, `ContinuousSMul, `ContinuousAdd, `Module.Finite,
    `ENNReal.HolderTriple, `ENNReal.HolderConjugate,
    `Zero, `One, `Add, `Sub, `Neg, `Mul, `Div, `Inv, `SMul, `HSMul, `Pow, `HPow,
    `AddMonoid, `AddCommMonoid, `AddGroup, `AddCommGroup, `Monoid, `CommMonoid,
    `Group, `CommGroup, `Semiring, `CommSemiring, `Ring, `CommRing, `DivisionRing,
    `Field, `Module, `Algebra, `Norm, `NNNorm, `ENorm, `Dist, `NNDist, `EDist,
    `SeminormedGroup, `NormedGroup, `SeminormedAddGroup, `NormedAddGroup,
    `SeminormedAddCommGroup, `NormedAddCommGroup, `SeminormedRing, `NormedRing,
    `SeminormedCommRing, `NormedCommRing, `NormedDivisionRing, `NormedField,
    `NontriviallyNormedField, `NormedSpace, `NormedAlgebra, `Inner, `InnerProductSpace,
    `PseudoMetricSpace, `MetricSpace, `PseudoEMetricSpace, `EMetricSpace,
    `TopologicalSpace, `UniformSpace, `MeasurableSpace, `MeasureTheory.MeasureSpace,
    `RCLike, `IsRCLikeNormedField].contains name

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
      if let some name ← isClass? decl.type then
        if ← structuralClass name decl.type then continue
        omitted := omitted.push decl.fvarId
        continue
      unless ← isProp decl.type do continue
      if ← scalarPremise decl.type then continue
      omitted := omitted.push decl.fvarId
    return (proofs, omitted)
  for proof in proofs do
    withMainContext do
      let type ← inferType proof
      let binderInfo := if (← isClass? type).isSome then BinderInfo.instImplicit else .default
      let (_, next) ← (← getMainGoal).assertHypotheses #[{
        userName := ← mkFreshUserName `selected_fact
        type
        value := proof
        binderInfo }]
      replaceMainGoal [next]
  let next ← (← getMainGoal).tryClearMany omitted
  next.withContext do
    for id in omitted do
      if (← getLCtx).contains id then
        throwError "cannot exclude a premise used by the goal or a dependent declaration; select required bound projections or use the full context without a fact list (only listed structural classes are kept automatically)"
  replaceMainGoal [next]

end NormArith
