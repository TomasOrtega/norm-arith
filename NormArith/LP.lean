module

public meta import Mathlib.Tactic.Linarith.Oracle.SimplexAlgorithm
public meta import NormArith.Search

/-!
# Compact linear programming for finite norm observations

This module is an untrusted search procedure. Scalar variable `i + 1` represents
the norm of vector column `i`; variable `0` is the constant one. Each real-space
block introduces one supporting functional per observed vector. The resulting
linear program has quadratic many rows, rather than enumerating decompositions.

The oracle's certificate is checked by exact arithmetic, and its auxiliary
variables are eliminated to recover ordinary rational triangle certificates.
Clients must still prove the vector identities and the final scalar consequence
in Lean. In particular, none of the supporting-functional rows are asserted as
Lean hypotheses. An oracle failure or a resource limit means unknown.
-/

public meta section

namespace NormArith.LP

open Lean Meta Mathlib Mathlib.Tactic.Linarith

/-- A rational affine expression compared with zero. Index zero denotes one. -/
structure Row where
  str : Ineq := .le
  coeffs : Array (Nat × Rat) := #[]
  deriving Inhabited, Repr

/-- Explicit formulation limits; the ambient Lean heartbeat limit also applies. -/
structure Config where
  maxNorms : Nat := 48
  maxDimension : Nat := 64
  maxRows : Nat := 6000
  maxVariables : Nat := 4096
  deriving Inhabited, Repr

/-- An ordinary decomposition, to be reconstructed with checked norm lemmas. -/
structure Proposal where
  target : Nat
  coefficients : Array Rat
  deriving Inhabited, Repr

/-- Provenance needed to eliminate an auxiliary functional block. -/
inductive Origin where
  | scalar
  | anchor (target : Nat)
  | support (target source : Nat) (positive : Bool)
  deriving Inhabited, Repr

/-- Integer rows sent to the oracle, with the positive denominator clearing factors. -/
structure Encoded where
  rows : Array Comp := #[]
  scales : Array Nat := #[]
  origins : Array Origin := #[]
  maxVar : Nat := 0
  deriving Inhabited, Repr

private def integralRow (row : Row) : Comp × Nat := Id.run do
  let mut terms : Std.TreeMap Nat Rat := ∅
  for (i, q) in row.coeffs do
    terms := terms.insert i ((terms[i]?).getD 0 + q)
  let coefficients := terms.toList.filter (fun (_, q) => q != 0)
  let denominator := coefficients.foldl (fun n (_, q) => n.lcm q.den) 1
  let integers := coefficients.reverse.map fun (i, q) =>
    (i, q.num * Int.ofNat (denominator / q.den))
  return ({ str := row.str, coeffs := integers }, denominator)

private def pushRow (encoded : Encoded) (row : Row) (origin : Origin) : Encoded :=
  let (comparison, denominator) := integralRow row
  { encoded with
    rows := encoded.rows.push comparison
    scales := encoded.scales.push denominator
    origins := encoded.origins.push origin }

/-- Build the compact support formulation.

`groups[i]` lists the observations in the same real normed space as observation
`i`. An empty group disables that functional block (for example, for an additive
group without real homogeneity). An active group must include its own target.
The frontend is responsible for choosing mathematically compatible groups;
the eventual Lean certificate checks that responsibility independently.
-/
def encode (columns : Array (Array Rat)) (groups : Array (Array Nat))
    (scalarRows : Array Row) (config : Config := {}) : Except String Encoded := do
  let count := columns.size
  if count > config.maxNorms then throw "norm observation limit"
  if groups.size != count then throw "inconsistent group dimensions"
  let dimension := (columns[0]?).map Array.size |>.getD 0
  if dimension > config.maxDimension then throw "vector dimension limit"
  if columns.any (fun column => column.size != dimension) then
    throw "inconsistent vector dimensions"
  for i in [:count] do
    let group := groups[i]!
    if group.any (fun j => j >= count) then throw "invalid source index"
    if !group.isEmpty && !group.contains i then throw "missing target in support block"
  let mut maxScalar := count
  for row in scalarRows do
    for (index, _) in row.coeffs do maxScalar := max maxScalar index
  let maxVar := maxScalar + count * dimension
  if maxVar + 1 > config.maxVariables then throw "scalar variable limit"
  let mut encoded : Encoded := { maxVar }
  -- The oracle cancels the constant coordinate too. This valid strict row lets
  -- it represent contradictions such as a positive constant bounded by zero.
  encoded := pushRow encoded { str := .lt, coeffs := #[(0, -1)] } .scalar
  for row in scalarRows do
    if row.str == .eq then
      encoded := pushRow encoded { row with str := .le } .scalar
      encoded := pushRow encoded
        { str := .le, coeffs := row.coeffs.map fun (i, q) => (i, -q) } .scalar
    else
      encoded := pushRow encoded row .scalar
  for i in [:count] do
    encoded := pushRow encoded { coeffs := #[(i + 1, -1)] } .scalar
    let group := groups[i]!
    if group.isEmpty then continue
    let functional := fun k => maxScalar + 1 + i * dimension + k
    let mut anchor : Array (Nat × Rat) := #[(i + 1, 1)]
    for k in [:dimension] do
      anchor := anchor.push (functional k, -columns[i]![k]!)
    encoded := pushRow encoded { coeffs := anchor } (.anchor i)
    for j in group do
      let mut positive : Array (Nat × Rat) := #[(j + 1, -1)]
      let mut negative : Array (Nat × Rat) := #[(j + 1, -1)]
      for k in [:dimension] do
        positive := positive.push (functional k, columns[j]![k]!)
        negative := negative.push (functional k, -columns[j]![k]!)
      encoded := pushRow encoded { coeffs := positive } (.support i j true)
      encoded := pushRow encoded { coeffs := negative } (.support i j false)
  if encoded.rows.size > config.maxRows then throw "support row limit"
  return encoded

/-- Recheck every coefficient and strictness bit of a proposed oracle certificate. -/
def checkCertificate (rows : Array Comp) (weights : Array Nat) : Bool := Id.run do
  if rows.size != weights.size then return false
  let mut sum : Linexp := []
  let mut strict := false
  for i in [:rows.size] do
    let weight := weights[i]!
    if weight == 0 then continue
    sum := sum.add (rows[i]!.coeffs.scale (Int.ofNat weight))
    if rows[i]!.str == .lt then strict := true
  return sum.isEmpty && strict

/-- Convert a valid support certificate into exact rational decompositions.

For a functional block, cancellation gives
`alpha * target = sum (betaPlus - betaMinus) * source`. When `alpha > 0`,
normalizing by `alpha` gives an ordinary triangle certificate at least as strong
as that block's scalar contribution. Blocks with `alpha = 0` contribute only
nonnegativity facts already available to the frontend.
-/
def extract (columns : Array (Array Rat)) (groups : Array (Array Nat))
    (encoded : Encoded) (weights : Array Nat) : Except String (Array Proposal) := do
  if !checkCertificate encoded.rows weights then throw "invalid LP contradiction certificate"
  if encoded.scales.size != encoded.rows.size ||
      encoded.origins.size != encoded.rows.size || groups.size != columns.size then
    throw "invalid certificate metadata"
  let mut alpha : Array Rat := Array.replicate columns.size 0
  let mut combinations : Array (Array Rat) :=
    Array.replicate columns.size (Array.replicate columns.size 0)
  for row in [:encoded.rows.size] do
    let weight : Rat := (weights[row]! * encoded.scales[row]! : Nat)
    if weight == 0 then continue
    match encoded.origins[row]! with
    | .scalar => pure ()
    | .anchor i =>
      if i >= columns.size then throw "invalid anchor index"
      alpha := alpha.set! i (alpha[i]! + weight)
    | .support i j positive =>
      if i >= columns.size || j >= columns.size then throw "invalid support index"
      let signed := if positive then weight else -weight
      let combination := combinations[i]!
      combinations := combinations.set! i (combination.set! j (combination[j]! + signed))
  let mut proposals := #[]
  for i in [:columns.size] do
    if alpha[i]! <= 0 then continue
    let coefficients := combinations[i]!.map (· / alpha[i]!)
    for j in [:columns.size] do
      if coefficients[j]! != 0 && !groups[i]!.contains j then
        throw "coefficient outside its normed-space block"
    if !Search.isDecomposition columns columns[i]! coefficients then
      throw "functional cancellation did not yield a vector identity"
    proposals := proposals.push { target := i, coefficients }
  return proposals

/-- Successful untrusted search data. The caller must construct Lean proofs. -/
structure Result where
  proposals : Array Proposal
  rowCount : Nat
  variableCount : Nat
  deriving Inhabited, Repr

/-- Run mathlib's exact simplex oracle and recover checked decomposition proposals. -/
def propose (columns : Array (Array Rat)) (groups : Array (Array Nat))
    (scalarRows : Array Row) (config : Config := {}) : MetaM Result := do
  let encoded ← match encode columns groups scalarRows config with
    | .ok encoded => pure encoded
    | .error reason => throwError "norm_arith LP: {reason}"
  let certificate ← CertificateOracle.simplexAlgorithmSparse.produceCertificate
    encoded.rows.toList encoded.maxVar
  let weights := (List.range encoded.rows.size).toArray.map fun i =>
    (certificate[i]?).getD 0
  let proposals ← match extract columns groups encoded weights with
    | .ok proposals => pure proposals
    | .error reason => throwError "norm_arith LP: {reason}"
  return { proposals, rowCount := encoded.rows.size, variableCount := encoded.maxVar + 1 }

end NormArith.LP
