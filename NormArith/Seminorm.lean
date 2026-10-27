module

public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public meta import Lean

/-!
# Arithmetic with explicit seminorms

`seminorm_arith` adds checked nonnegativity, triangle, reverse-triangle, and
homogeneity facts for the explicit seminorm expressions occurring in the goal
and local hypotheses. It then calls exact scalar arithmetic. Several different
seminorms may occur in the same goal. They remain distinct scalar expressions.

`seminorm_arith [h₁, h₂]` adds the listed facts to the local context. Unlike the
selective fact syntax of `norm_arith`, this syntax is additive.

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

end NormArith

public meta section

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

private def run (hints : Array (TSyntax `term)) : TacticM Unit :=
  focusAndDone <| withoutRecover do
    addHints hints
    if (← getGoals).isEmpty then return
    let facts ← withMainContext <| constraints (← contextInputs)
    for proof in facts do
      if (← getGoals).isEmpty then return
      noteFact proof
    evalTactic (← `(tactic| first | assumption | positivity | linarith | nlinarith))

syntax (name := seminormArith) "seminorm_arith" : tactic
syntax (name := seminormArithHints) "seminorm_arith" "[" term,* "]" : tactic

elab_rules : tactic
  | `(tactic| seminorm_arith) => run #[]
  | `(tactic| seminorm_arith [$hs,*]) => run hs.getElems

end NormArith.SeminormSupport
