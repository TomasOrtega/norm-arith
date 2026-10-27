module

public import Mathlib.Basic.Real.Basic
public meta import NormArith.LP

/-! Shared exact rational data for norm and seminorm search. -/

public meta section

namespace NormArith.Reify

open Lean Meta

abbrev Form := Array (Nat × Rat)

def lastTwo? (e : Expr) : Option (Expr × Expr) :=
  let args := e.getAppArgs
  if args.size < 2 then none else some (args[args.size - 2]!, args.back!)

/-- Read closed rational scalar expressions without evaluating real numbers. -/
partial def scalar? (input : Expr) : Option Rat := do
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

def scale (c : Rat) (v : Form) : Form :=
  v.map fun (i, a) => (i, c * a)

/-- Atoms are formal expressions, not a claim of linear independence in `E`. -/
partial def linearize (input : Expr) : StateT (Array Expr) MetaM Form := do
  let e := (← liftM (zetaReduce input)).consumeMData
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
    if atoms[i]! == e || (← liftM (isDefEq atoms[i]! e)) then return #[(i, 1)]
  set (atoms.push e)
  return #[(atoms.size, 1)]

def dense (dimension : Nat) (form : Form) : Array Rat := Id.run do
  let mut result : Array Rat := Array.replicate dimension 0
  for (i, c) in form do
    result := result.set! i (result[i]! + c)
  return result

/-- Reify affine scalar expressions for the untrusted LP search. The first
atoms are the observed norms. Opaque scalar expressions remain separate atoms;
all resulting consequences are checked again against the actual Lean terms. -/
partial def lpScalarForm (input : Expr) : StateT (Array Expr) MetaM Form := do
  let e := (← liftM (zetaReduce input)).consumeMData
  if let some q := scalar? e then return #[(0, q)]
  if e.isAppOf ``Neg.neg then
    return scale (-1) (← lpScalarForm e.getAppArgs.back!)
  if let some (a, b) := lastTwo? e then
    if e.isAppOf ``HAdd.hAdd then
      return (← lpScalarForm a) ++ (← lpScalarForm b)
    if e.isAppOf ``HSub.hSub then
      return (← lpScalarForm a) ++ scale (-1) (← lpScalarForm b)
    if e.isAppOf ``HMul.hMul then
      if let some q := scalar? a then return scale q (← lpScalarForm b)
      if let some q := scalar? b then return scale q (← lpScalarForm a)
    if e.isAppOf ``HDiv.hDiv then
      if let some q := scalar? b then
        if q != 0 then return scale (1 / q) (← lpScalarForm a)
  let atoms ← get
  for i in [:atoms.size] do
    if atoms[i]! == e || (← liftM (isDefEq atoms[i]! e)) then return #[(i + 1, 1)]
  set (atoms.push e)
  return #[(atoms.size + 1, 1)]

def lpComparison (input : Expr) : StateT (Array Expr) MetaM LP.Row := do
  let reduced ← liftM (zetaReduce input)
  -- Do not reduce `LE.le`/`LT.lt`: on concrete reals whnf unfolds the
  -- comparison into its implementation instead of retaining the relation head.
  let e := reduced.consumeMData
  let some (a, b) := lastTwo? e | throwError "norm_arith LP: expected a scalar comparison"
  let str ← if e.isAppOf ``Eq then pure Mathlib.Ineq.eq
    else if e.isAppOf ``LT.lt || e.isAppOf ``GT.gt then pure Mathlib.Ineq.lt
    else if e.isAppOf ``LE.le || e.isAppOf ``GE.ge then pure Mathlib.Ineq.le
    else throwError "norm_arith LP: unsupported comparison"
  let coefficients := (← lpScalarForm a) ++ scale (-1) (← lpScalarForm b)
  let coefficients := if e.isAppOf ``GE.ge || e.isAppOf ``GT.gt then
      scale (-1) coefficients else coefficients
  return { str, coeffs := coefficients }

/-- An equality conclusion has two refutation branches. They share all scalar
atoms and their selected hypotheses, but their certificates are searched separately. -/
def lpNegations (row : LP.Row) : Array LP.Row :=
  let opposite := row.coeffs.map fun (i, q) => (i, -q)
  if row.str == .eq then
    #[{ str := .lt, coeffs := row.coeffs }, { str := .lt, coeffs := opposite }]
  else if row.str == .lt then #[{ str := .le, coeffs := opposite }]
  else #[{ str := .lt, coeffs := opposite }]

end NormArith.Reify
