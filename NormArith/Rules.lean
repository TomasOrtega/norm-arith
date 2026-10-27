module

public import NormArith.Tactic
public import NormArith.Seminorm
public import Mathlib.Tactic.Positivity
public meta import Lean

/-!
# Bounded search with analytic theorems

A rule is a proved theorem. Search applies it to the current target and proves
every premise. Failed branches are rolled back. A repeated target is not used
as its own premise. Local and scoped attributes limit where a rule is available.
-/

public meta section

namespace NormArith

open Lean Meta Elab Tactic

initialize analyticRules : SimpleScopedEnvExtension Name (Array Name) ←
  registerSimpleScopedEnvExtension {
    initial := #[]
    addEntry := fun rules name => if rules.contains name then rules else rules.push name }

initialize registerBuiltinAttribute {
  name := `analytic_rule
  descr := "Use a proved theorem in bounded analytic estimate search."
  applicationTime := .afterCompilation
  add := fun name _ kind => do
    unless ← MetaM.run' (isProp (← getConstInfo name).type) do
      throwError "analytic_rule requires a proved proposition"
    analyticRules.add name kind }

register_option analytic_estimate.maxDepth : Nat := {
  defValue := 6
  descr := "Maximum number of analytic rules along one proof branch." }

register_option analytic_estimate.maxApplications : Nat := {
  defValue := 128
  descr := "Maximum number of attempted analytic rule applications." }

initialize registerTraceClass `analytic_estimate.rules

private def finish : TacticM Bool := do
  let saved ← saveState
  try
    evalTactic (← `(tactic| assumption))
    return true
  catch _ => saved.restore
  let target ← withMainContext do instantiateMVars (← getMainTarget)
  if target.hasExprMVar then return false
  try
    evalTactic (← `(tactic| first | positivity | norm_arith))
    if (← getUnsolvedGoals).isEmpty then return true
    saved.restore
  catch _ => saved.restore
  let hasSeminorm ← withMainContext do
    return !(← SeminormSupport.constraints (← SeminormSupport.contextInputs) false).isEmpty
  if hasSeminorm then
    try
      evalTactic (← `(tactic| seminorm_arith))
      if (← getUnsolvedGoals).isEmpty then return true
      saved.restore
    catch _ => saved.restore
  let facts ← withMainContext do
    let mut facts : Array (TSyntax `term) := #[]
    for decl in ← getLCtx do
      let type ← instantiateMVars decl.type
      unless type.isAppOf ``LE.le || type.isAppOf ``LT.lt || type.isAppOf ``Eq do continue
      let some (a, _) := Reify.lastTwo? type | continue
      unless ← isDefEq (← inferType a) (mkConst ``Real) do continue
      facts := facts.push (← Term.exprToSyntax decl.toExpr)
    return facts
  try
    evalTactic (← `(tactic| first | linarith only [$facts,*] | nlinarith only [$facts,*]))
    if (← getUnsolvedGoals).isEmpty then return true
    saved.restore
    return false
  catch _ =>
    saved.restore
    return false

private partial def search (depth : Nat) (ancestors : Array Expr)
    (rules : Array Name) : StateT Nat TacticM Bool := do
  if ← liftM finish then return true
  if depth == 0 then return false
  let target ← liftM <| withMainContext do instantiateMVars (← getMainTarget)
  if ancestors.contains target then return false
  for name in rules do
    if (← get) == 0 then return false
    modify (· - 1)
    let saved : Tactic.SavedState ← liftM (saveState : TacticM Tactic.SavedState)
    try
      liftM <| evalTactic (← `(tactic| apply $(mkIdent name):term))
      let goals ← liftM getGoals
      trace[analytic_estimate.rules] "Trying {name} with {goals.length} premises"
      let mut success := true
      for goal in goals do
        if ← goal.isAssigned then continue
        liftM <| setGoals [goal]
        if !(← search (depth - 1) (ancestors.push target) rules) then
          trace[analytic_estimate.rules] "Unmet premise: {← goal.getType}"
          success := false
          break
      if success then
        liftM <| setGoals []
        trace[analytic_estimate.rules] "Applied {name}"
        return true
      liftM saved.restore
    catch error =>
      trace[analytic_estimate.rules] "Rule {name} failed: {error.toMessageData}"
      liftM saved.restore
  return false

/-- No unproved premise enters the context used by arithmetic. -/
def applyAnalyticRules : TacticM Unit := do
  let options ← getOptions
  let rules := analyticRules.getState (← getEnv)
  let (closed, remaining) ← (search (analytic_estimate.maxDepth.get options) #[] rules).run
    (analytic_estimate.maxApplications.get options)
  unless closed do
    if remaining == 0 then
      throwError "analytic_estimate: rule application limit reached"
    throwError "analytic_estimate: no proof found; an analytic premise may be missing or the depth limit may be too small"

end NormArith
