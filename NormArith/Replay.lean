module

public meta import Lean.Meta.Tactic.TryThis
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Meta.Transform
public meta import NormArith.ReplayData

/-! Proof suggestions contain checked expression graphs. Replay does not run search. -/

public meta section

register_option norm_arith.replayText : Bool := {
  defValue := false
  descr := "Print the full replay source as well as offering it in the code action." }

namespace NormArith

open Lean Meta Elab Tactic

/-- Keep proofs independent of declarations made during tactic search. -/
private partial def inlineAuxiliaryDeclarations (original : Environment) (proof : Expr)
    (active : NameSet := {}) : CoreM Expr :=
  Core.transform proof (pre := fun e => do
    let .const name levels := e | return .continue
    if original.contains name then return .done e
    if active.contains name then
      throwError "cannot replay cyclic generated declaration {name}"
    let info ← getConstInfo name
    let some value := info.value? (allowOpaque := true)
      | throwError "cannot replay generated declaration {name}: no proof body is available"
    return .done (← inlineAuxiliaryDeclarations original
      (value.instantiateLevelParams info.levelParams levels) (active.insert name)))

/-- Save the original goal so generated local facts stay inside the proof term. -/
def withReplay (enabled : Bool) (action : TacticM Unit) : TacticM Unit := do
  if !enabled then return ← action
  let goal ← getMainGoal
  let reference ← getRef
  let saved ← saveState
  let originalEnvironment ← getEnv
  action
  let proof ← instantiateMVars (mkMVar goal)
  let proof ← inlineAuxiliaryDeclarations originalEnvironment proof
  let text ← goal.withContext <| Replay.encode proof
  let literal := Syntax.mkStrLit text
  let suggestion ← `(tactic| norm_arith_replay $literal:str)
  let completed ← saveState
  saved.restore
  try
    setGoals [goal]
    withoutRecover <| evalTactic suggestion
    unless (← getGoals).isEmpty do throwError "replay left an open goal"
  finally completed.restore
  TryThis.addSuggestion reference {
    suggestion
    messageData? := if norm_arith.replayText.get (← getOptions) then none else
      some m!"norm_arith_replay <checked proof; {text.utf8ByteSize} bytes>"
  }

end NormArith
