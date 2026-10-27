module

public import Mathlib.Basic.ENNReal.Holder
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Finiteness
public meta import Lean

/-!
# Exact exponent choices

The planner uses rational reciprocal exponents. Zero means the endpoint infinity.
The tactics insert a candidate and check every arithmetic condition in Lean.
They do not prove membership or measurability from exponent arithmetic.
-/

public meta section

namespace NormArith.Parameters

/-- Find the missing reciprocal exponent in Hölder's equality. -/
def holderPartner? (left target : Rat) : Option Rat :=
  let right := target - left
  if 0 ≤ left && left ≤ 1 && 0 ≤ target && target ≤ 1 && 0 ≤ right && right ≤ 1
  then some right else none

/-- Find a convex weight between two fixed reciprocal exponents. -/
def interpolationWeight? (left right target : Rat) : Option Rat :=
  if !(0 ≤ left && left ≤ 1 && 0 ≤ right && right ≤ 1 && 0 ≤ target && target ≤ 1)
  then none
  else if left == right then
    if target == left then some 1 else none
  else
    let weight := (target - right) / (left - right)
    if 0 ≤ weight && weight ≤ 1 && target == weight * left + (1 - weight) * right
    then some weight else none

end NormArith.Parameters

public meta section

namespace NormArith.Parameters

open Lean Meta Elab Tactic
open scoped ENNReal

initialize registerTraceClass `analytic_estimate.parameters

private partial def rational? : TSyntax `term → Option Rat
  | `(term| $n:num) => some n.getNat
  | `(term| ($value)) => rational? value
  | `(term| $a / $b) => do
    let denominator ← rational? b
    if denominator == 0 then none else return (← rational? a) / denominator
  | _ => none

def reciprocal (input : TSyntax `term) : TacticM Rat := do
  if let `(term| ∞) := input then return 0
  let some exponent := rational? input |
    throwErrorAt input "expected a positive rational number or infinity"
  if exponent < 1 then throwErrorAt input "expected an exponent at least one"
  return 1 / exponent

def rationalSyntax (q : Rat) : TacticM (TSyntax `term) := do
  let n := Syntax.mkNumLit q.num.natAbs.repr
  let d := Syntax.mkNumLit q.den.repr
  if q < 0 then `(-($n / $d)) else `(($n / $d))

/-- Check a concrete Hölder triple, including the infinity endpoint. -/
macro "holder_arith" : tactic => `(tactic| (
  rw [ENNReal.holderTriple_iff]
  apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)).mp
  norm_num [ENNReal.toReal_add]))

/-- Choose the missing exponent in an existential Hölder triple. -/
elab "choose_holder" left:term:max target:term:max : tactic => do
  let p ← reciprocal left
  let r ← reciprocal target
  let some q := holderPartner? p r | throwError "no admissible Hölder exponent"
  let witness ← if q == 0 then `(term| (∞ : ℝ≥0∞)) else rationalSyntax (1 / q)
  evalTactic (← `(tactic| refine ⟨$witness, ?_⟩))
  evalTactic (← `(tactic| holder_arith))
  trace[analytic_estimate.parameters]
    "Hölder partner {witness}; checked ENNReal.HolderTriple with ENNReal.toReal_eq_toReal_iff'"

/-- Choose a weight for an existential real interpolation equation. -/
elab "choose_interpolation" left:term:max right:term:max target:term:max : tactic => do
  let p ← reciprocal left
  let q ← reciprocal right
  let r ← reciprocal target
  let some weight := interpolationWeight? p q r |
    throwError "the target exponent is outside the endpoint interval"
  let witness ← rationalSyntax weight
  evalTactic (← `(tactic| refine ⟨$witness, ?_⟩))
  evalTactic (← `(tactic| norm_num))
  trace[analytic_estimate.parameters] "Interpolation weight {weight}; checked by norm_num"

end NormArith.Parameters
