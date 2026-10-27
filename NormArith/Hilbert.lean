module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public meta import NormArith.Reify
public meta import Lean.Meta.Tactic.TryThis

/-!
# Checked quadratic estimates in real inner-product spaces

`hilbert_arith` proves rational quadratic inequalities in norms and real inner
products. It finds an exact rational sum of squares. Lean checks the resulting
identity and the sign of every weight. Search is limited to 24 vector atoms.

`hilbert_arith?` suggests a proof with the selected squares. That proof uses
`hilbert_nf` for algebraic normalization and does not run the factor search.
This module does not search over combinations of analytic hypotheses.
-/

public section

namespace NormArith.Hilbert

theorem le_of_squares {a b s : ℝ} (hs : 0 ≤ s) (h : b - a = s) : a ≤ b := by
  exact sub_nonneg.mp (h ▸ hs)

theorem eq_of_zero_difference {a b : ℝ} (h : b - a = 0) : a = b :=
  (sub_eq_zero.mp h).symm

/-- Normalize real inner products without a search procedure. -/
macro "hilbert_nf" : tactic => `(tactic| (
  simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, inner_neg_left, inner_neg_right,
    real_inner_smul_left, real_inner_smul_right, inner_zero_left, inner_zero_right,
    real_inner_comm]
  <;> ring))

end NormArith.Hilbert

public meta section

namespace NormArith.Hilbert

open Lean Meta Elab Tactic Reify

structure Square where
  weight : Rat
  row : Array Rat
  deriving Inhabited, Repr, BEq

/-- Check the full rational matrix identity and each weight. -/
def checkFactor (matrix : Array (Array Rat)) (squares : Array Square) : Bool := Id.run do
  let n := matrix.size
  if matrix.any (fun row => row.size != n) then return false
  if squares.any (fun s => s.weight < 0 || s.row.size != n) then return false
  for i in [:n] do
    for j in [:n] do
      let value := squares.foldl (fun total s => total + s.weight * s.row[i]! * s.row[j]!) 0
      if value != (matrix[i]!)[j]! then return false
  return true

/-- Exact diagonal elimination, with a checked zero-pivot case. -/
def factor (matrix : Array (Array Rat)) : Except String (Array Square) := do
  let n := matrix.size
  if n > 24 then throw "vector atom limit (24)"
  if matrix.any (fun row => row.size != n) then throw "matrix is not square"
  for i in [:n] do
    for j in [:n] do
      if (matrix[i]!)[j]! != (matrix[j]!)[i]! then throw "matrix is not symmetric"
  let mut rest := matrix
  let mut result := #[]
  for i in [:n] do
    let pivot := (rest[i]!)[i]!
    if pivot < 0 then throw "quadratic form is not positive semidefinite"
    if pivot == 0 then
      if rest[i]!.any (· != 0) then throw "zero pivot has a nonzero row"
      continue
    let row := rest[i]!.map (· / pivot)
    result := result.push { weight := pivot, row }
    rest := rest.mapIdx fun j values =>
      values.mapIdx fun k value => value - pivot * row[j]! * row[k]!
  if !checkFactor matrix result then throw "invalid quadratic factor certificate"
  return result

private abbrev Quadratic := Array (Nat × Nat × Rat)

private def scaleQuadratic (c : Rat) (q : Quadratic) : Quadratic :=
  q.map fun (i, j, a) => (i, j, c * a)

private def product (a b : Form) : Quadratic := Id.run do
  let mut terms := #[]
  for (i, x) in a do
    for (j, y) in b do
      terms := terms.push (i, j, x * y)
  return terms

private partial def quadratic (input : Expr) : StateT (Array Expr) MetaM Quadratic := do
  let e := (← liftM (zetaReduce input)).consumeMData
  if scalar? e == some 0 then return #[]
  if e.isAppOf ``Neg.neg then
    return scaleQuadratic (-1) (← quadratic e.getAppArgs.back!)
  if let some (a, b) := lastTwo? e then
    if e.isAppOf ``HAdd.hAdd then return (← quadratic a) ++ (← quadratic b)
    if e.isAppOf ``HSub.hSub then
      return (← quadratic a) ++ scaleQuadratic (-1) (← quadratic b)
    if e.isAppOf ``HMul.hMul then
      if let some c := scalar? a then return scaleQuadratic c (← quadratic b)
      if let some c := scalar? b then return scaleQuadratic c (← quadratic a)
    if e.isAppOf ``HDiv.hDiv then
      if let some c := scalar? b then
        if c != 0 then return scaleQuadratic (1 / c) (← quadratic a)
    if e.isAppOf ``HPow.hPow && scalar? b == some 2 && a.isAppOf ``Norm.norm then
      let v ← linearize a.getAppArgs.back!
      return product v v
    if e.isAppOf ``inner then
      unless (← liftM (inferType e)).isConstOf ``Real do
        throwError "hilbert_arith: expected a real inner product"
      return product (← linearize a) (← linearize b)
  throwError "hilbert_arith: expected a rational quadratic expression, found {e}"

private def symmetricMatrix (n : Nat) (terms : Quadratic) : Array (Array Rat) := Id.run do
  let mut matrix := Array.replicate n (Array.replicate n 0)
  for (i, j, value) in terms do
    let row := matrix[i]!
    matrix := matrix.set! i (row.set! j (row[j]! + value / 2))
    let row := matrix[j]!
    matrix := matrix.set! j (row.set! i (row[i]! + value / 2))
  return matrix

private def rationalTerm (q : Rat) : TacticM (TSyntax `term) := do
  let magnitude : TSyntax `term := ⟨Syntax.mkNumLit (toString q.num.natAbs)⟩
  let numerator ← if q.num < 0 then `(-$magnitude) else pure magnitude
  let denominator : TSyntax `term := ⟨Syntax.mkNumLit (toString q.den)⟩
  `((($numerator : ℝ) / ($denominator : ℝ)))

private def squareTerm (atoms : Array Expr) (s : Square) : TacticM (TSyntax `term) := do
  let mut vector : TSyntax `term ← `(0)
  for i in [:atoms.size] do
    if s.row[i]! == 0 then continue
    let atom ← PrettyPrinter.delab atoms[i]!
    let c ← rationalTerm s.row[i]!
    vector ← `($vector + $c • $atom)
  let weight ← rationalTerm s.weight
  `($weight * ‖$vector‖ ^ 2)

private def run (explain : Bool) : TacticM Unit := focusAndDone <| withoutRecover do
  let target ← withMainContext getMainTarget
  let some (a, b) := lastTwo? target |
    throwError "hilbert_arith: expected an equality or a weak inequality"
  unless target.isAppOf ``LE.le || target.isAppOf ``GE.ge || target.isAppOf ``Eq do
    throwError "hilbert_arith: expected an equality or a weak inequality"
  let (a, b) := if target.isAppOf ``GE.ge then (b, a) else (a, b)
  let (terms, atoms) ← withMainContext do
    (do return (← quadratic b) ++ scaleQuadratic (-1) (← quadratic a)).run #[]
  if atoms.size > 24 then throwError "hilbert_arith: vector atom limit (24)"
  let matrix := symmetricMatrix atoms.size terms
  let proof ← if target.isAppOf ``Eq then
      if matrix.any (fun row => row.any (· != 0)) then
        throwError "hilbert_arith: the quadratic forms are not equal"
      let rule := mkIdent ``NormArith.Hilbert.eq_of_zero_difference
      `(tactic| (apply $rule:term; hilbert_nf))
    else do
      let squares ← match factor matrix with
        | .ok result => pure result
        | .error message => throwError "hilbert_arith: {message}"
      let mut sum : TSyntax `term ← `((0 : ℝ))
      for square in squares do
        let term ← withMainContext <| squareTerm atoms square
        sum ← `($sum + $term)
      let rule := mkIdent ``NormArith.Hilbert.le_of_squares
      let parameter := mkIdent `s
      `(tactic| (apply $rule:term ($parameter:ident := $sum)
                <;> first | positivity | hilbert_nf))
  evalTactic proof
  if explain then TryThis.addSuggestion (← getRef) proof

syntax (name := hilbertArith) "hilbert_arith" : tactic
syntax (name := hilbertArithExplain) "hilbert_arith?" : tactic

elab_rules : tactic
  | `(tactic| hilbert_arith) => run false
  | `(tactic| hilbert_arith?) => run true

end NormArith.Hilbert
