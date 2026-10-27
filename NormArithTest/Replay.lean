module

import NormArith.Analysis
public meta import NormArith.Replay
public meta import NormArith.ReplayData
public meta import Lean

set_option linter.unusedVariables false

open Lean Meta Elab Tactic

-- Each generated suggestion is decoded and checked before it is offered.
example {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) (a b : ℝ) (hx : ‖x + y‖ < a) (hy : ‖x - y‖ ≤ b) :
    2 * ‖x‖ < a + b := by
  set_option norm_arith.forceLP true in norm_arith? [hx, hy]

example (a b ε : ℝ) (hε : 0 < ε) : a * b ≤ ε * a ^ 2 + b ^ 2 / (4 * ε) := by
  analytic_estimate?

-- LP reconstruction can create auxiliary theorems through `abel`.
set_option maxHeartbeats 4000000 in
example {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (x y u v : E) (F G A B : ℝ)
    (hx : ‖x + y‖ ≤ F + ‖u‖ / 4)
    (hu : ‖u + v‖ ≤ G + ‖x‖ / 2)
    (hy : ‖y‖ ≤ A) (hv : ‖v‖ ≤ B) :
    7 * ‖x‖ ≤ 8 * F + 8 * A + 2 * G + 2 * B := by
  set_option norm_arith.forceLP true in norm_arith? [hx, hu, hy, hv]

example {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] (x y : E) :
    ‖x + y‖ ≤ ‖x‖ + ‖y‖ ∧ True := by
  constructor
  norm_arith?
  trivial

example {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] (x y : E) :
    ‖x + y‖ ≤ ‖x‖ + ‖y‖ := by
  let z := x + y
  have hz : ‖z‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
  norm_arith? [hz]

-- This saved graph refers to the named premise and performs no search.
example (a b : ℝ) (h : a ≤ b) : a ≤ b := by
  norm_arith_replay "[1,0,[[1,[null,\"h\"],0]]]"

example (a b : ℝ) (h : a ≤ b) : True := by
  fail_if_success
    have : a < b := by
      norm_arith_replay "[1,0,[[1,[null,\"h\"],0]]]"
  trivial

example : True := by
  fail_if_success norm_arith_replay "[1,0,[[1,[null,\"missing\"],0]]]"
  fail_if_success norm_arith_replay "[1,0,[[4,0,0]]]"
  fail_if_success norm_arith_replay "[1,0,[[0,0]]]"
  fail_if_success norm_arith_replay "[2,0,[]]"
  fail_if_success norm_arith_replay "[1,0,[[3,[null,\"sorryAx\"],[]]]]"
  trivial

-- A well-formed graph can still contain an ill-typed application.
example : True := by
  fail_if_success
    norm_arith_replay "[1,1,[[3,[[null,\"True\"],\"intro\"],[]],[4,0,0]]]"
  norm_arith_replay "[1,0,[[3,[[null,\"True\"],\"intro\"],[]]]]"

-- Shared subterms, binders, and let expressions round-trip without delaboration.
elab "check_replay_term " value:term : tactic => withMainContext do
  let proof ← Term.elabTermAndSynthesize value (some (← getMainTarget))
  let encoded ← NormArith.Replay.encode proof
  let decoded ← NormArith.Replay.decode encoded
  unless ← isDefEq (← inferType decoded) (← getMainTarget) do
    throwError "round-trip changed the proof type"
  (← getMainGoal).assign decoded
  replaceMainGoal []

example (p : Prop) (h : p) : ∀ q : Prop, q → p := by
  check_replay_term (fun q (_ : q) => h)

example (p : Prop) (h : p) : p ∧ p := by
  check_replay_term (let hp : p := h; And.intro hp hp)

example (p q : Prop) (h : p ∧ q) : p := by
  check_replay_term h.1

-- Module-local macro scopes change when a saved proof moves to another file.
elab "check_replay_hygiene " value:term : tactic => withMainContext do
  let proof ← Term.elabTermAndSynthesize value (some (← getMainTarget))
  let context ← getLCtx
  let rename (moduleName : Name) (decl : LocalDecl) : LocalDecl :=
    let base := if decl.binderInfo.isInstImplicit then `inst else decl.userName.eraseMacroScopes
    decl.setUserName (Lean.addMacroScope moduleName base (decl.index + 1))
  let capture := context.modifyLocalDecls (rename `CaptureModule)
  let replay := context.modifyLocalDecls (rename `ReplayModule)
  let instances ← getLocalInstances
  let encoded ← withLCtx capture instances <| NormArith.Replay.encode proof
  let decoded ← withLCtx replay instances <| NormArith.Replay.decode encoded
  unless ← isDefEq (← inferType decoded) (← getMainTarget) do
    throwError "changing macro scopes changed the replay type"
  (← getMainGoal).assign decoded
  replaceMainGoal []

example {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] (x : E) :
    ‖(2 : ℝ) • x‖ = 2 * ‖x‖ := by
  check_replay_hygiene (by simpa using norm_smul (2 : ℝ) x)

-- Nested helper theorems have their own universe parameter names.
elab "check_replay_auxiliaries " value:term : tactic => withMainContext do
  NormArith.withReplay true do
    let value ← Term.elabTermAndSynthesize value none
    let type ← inferType value
    let level ← getLevel type
    let inner ← mkFreshUserName `replayInner
    let outer ← mkFreshUserName `replayOuter
    let (helperType, helperProof) ← withLocalDeclD `α (.sort (.param `inner_u)) fun α =>
      withLocalDeclD `x α fun x => do
        return (← mkForallFVars #[α, x] (← mkEq x x),
          ← mkLambdaFVars #[α, x] (← mkEqRefl x))
    addDecl <| .thmDecl {
      name := inner, levelParams := [`inner_u], type := helperType, value := helperProof }
    addDecl <| .thmDecl {
      name := outer, levelParams := [`outer_u]
      type := helperType.instantiateLevelParams [`inner_u] [.param `outer_u]
      value := mkConst inner [.param `outer_u] }
    let proof := mkApp2 (mkConst outer [level]) type value
    unless ← isDefEq (← inferType proof) (← getMainTarget) do
      throwError "helper proof does not match the goal"
    (← getMainGoal).assign proof
    replaceMainGoal []

example {α : Sort u} (x : α) : x = x := by
  check_replay_auxiliaries x
