module

public import Lean

/-!
# Small exact searches for linear decompositions

This module has no mathematical trust role: it proposes rational coefficients, and
the tactic proves the resulting vector identity separately. All search bounds are
explicit. A column is an array of coefficients in a shared vector basis.
-/

public section

namespace NormArith.Search

/-- Limits for the deliberately small decomposition search. -/
structure Config where
  /-- Only this many source columns are considered, in their input order. -/
  maxSources : Nat := 12
  /-- Maximum number of source columns in a searched subset. -/
  maxSupport : Nat := 3
  /-- Total number of subsets tested, including unsuccessful ones. -/
  maxSubsets : Nat := 128
  /-- Maximum number of distinct decompositions returned. -/
  maxResults : Nat := 16
  deriving Inhabited, Repr

/-- Resource limits for the finite reference enumeration. -/
structure ReferenceConfig where
  /-- Support systems examined after the full-system rank/span check. -/
  maxSubsets : Nat := 10000
  /-- Maximum number of distinct coefficient arrays retained. -/
  maxResults : Nat := 10000
  deriving Inhabited, Repr

/-- The resource that prevented a complete reference enumeration. -/
inductive ReferenceLimit where
  | subsets
  | results
  deriving Inhabited, Repr, BEq

/-- Distinguish complete results, incomplete results, and malformed input. -/
inductive ReferenceStatus where
  | complete
  | exhausted (limit : ReferenceLimit)
  | invalidDimensions
  deriving Inhabited, Repr, BEq

/-- `complete` means no independent-support proposal was omitted. -/
structure ReferenceResult where
  coefficients : Array (Array Rat) := #[]
  rank : Nat := 0
  /-- Does not include the initial full-system rank/span check. -/
  attempts : Nat := 0
  status : ReferenceStatus := .complete
  deriving Inhabited, Repr

/-- Check a proposed decomposition by exact rational arithmetic. -/
def isDecomposition (sources : Array (Array Rat)) (target coefficients : Array Rat) : Bool :=
  Id.run do
    if coefficients.size != sources.size || sources.any (fun v => v.size != target.size) then
      return false
    for row in [:target.size] do
      let mut value : Rat := 0
      for col in [:sources.size] do
        value := value + coefficients[col]! * sources[col]![row]!
      if value != target[row]! then
        return false
    return true

private structure SystemResult where
  rank : Nat
  solution? : Option (Array Rat)

/-- Solve the selected rectangular system by Gauss--Jordan elimination.

Free variables are set to zero. Inconsistent systems have no solution; dependent
columns are allowed. The solution is indexed by `selected`, not by all sources.
-/
private def solve (sources : Array (Array Rat)) (target : Array Rat)
    (selected : Array Nat) : SystemResult := Id.run do
  let width := selected.size
  let mut matrix : Array (Array Rat) := #[]
  for row in [:target.size] do
    let entries := selected.map (fun col => sources[col]![row]!)
    matrix := matrix.push (entries.push target[row]!)
  let mut pivotRow := 0
  let mut pivots : Array (Nat × Nat) := #[]
  for col in [:width] do
    let mut found : Option Nat := none
    for row in [pivotRow:matrix.size] do
      if found.isNone && matrix[row]![col]! != 0 then
        found := some row
    if let some row := found then
      let old := matrix[pivotRow]!
      matrix := matrix.set! pivotRow matrix[row]!
      matrix := matrix.set! row old
      let divisor := matrix[pivotRow]![col]!
      let normalized := matrix[pivotRow]!.map (fun x => x / divisor)
      matrix := matrix.set! pivotRow normalized
      for other in [:matrix.size] do
        if other != pivotRow then
          let factor := matrix[other]![col]!
          if factor != 0 then
            let mut reduced := matrix[other]!
            for entry in [:width + 1] do
              reduced := reduced.set! entry (reduced[entry]! - factor * normalized[entry]!)
            matrix := matrix.set! other reduced
      pivots := pivots.push (pivotRow, col)
      pivotRow := pivotRow + 1
  for row in matrix do
    if (row.take width).all (· == 0) && row[width]! != 0 then
      return { rank := pivots.size, solution? := none }
  let mut solution : Array Rat := Array.replicate width 0
  for pivot in pivots do
    solution := solution.set! pivot.2 matrix[pivot.1]![width]!
  return { rank := pivots.size, solution? := some solution }

/-- The next increasing subset of the same size, in lexicographic order. -/
private def nextSubset? (count : Nat) (selected : Array Nat) : Option (Array Nat) := Id.run do
  for offset in [:selected.size] do
    let index := selected.size - 1 - offset
    if selected[index]! + (selected.size - index) < count then
      let first := selected[index]! + 1
      let mut next := selected.set! index first
      for later in [index + 1:selected.size] do
        next := next.set! later (first + later - index)
      return some next
  return none

/-- Search for short rational linear decompositions of `target` in `sources`.

Each returned array has length `sources.size`, including zero entries for unused
sources. Subsets are tried in increasing size, then lexicographic order. Search
stops at the first exhausted budget; it is intentionally incomplete. Dimension
mismatches return no results. Every returned proposal is checked again by exact
arithmetic, but clients must still construct and check a Lean proof.
-/
def decompositions (sources : Array (Array Rat)) (target : Array Rat)
    (config : Config := {}) : Array (Array Rat) := Id.run do
  if config.maxResults == 0 || sources.any (fun v => v.size != target.size) then
    return #[]
  let zero : Array Rat := Array.replicate sources.size 0
  if target.all (· == 0) then
    return #[zero]
  let count := min sources.size config.maxSources
  let supportLimit := min count config.maxSupport
  let mut results : Array (Array Rat) := #[]
  let mut attempts := 0
  for support in [1:supportLimit + 1] do
    let mut selected? := some (List.range support).toArray
    for _ in [:config.maxSubsets] do
      if attempts >= config.maxSubsets || results.size >= config.maxResults then
        return results
      let some selected := selected? | break
      attempts := attempts + 1
      if let some solution := (solve sources target selected).solution? then
        let mut coefficients := zero
        for index in [:selected.size] do
          coefficients := coefficients.set! selected[index]! solution[index]!
        if isDecomposition sources target coefficients && !results.contains coefficients then
          results := results.push coefficients
      selected? := nextSubset? count selected
  return results

/-- Enumerate every rational decomposition with linearly independent support.

Supports are tried in increasing size, then lexicographic order, through the
column rank of `sources`. These are the signed basic solutions needed for real
absolute-convex-hull constraints. They are not a complete integer search for
arbitrary additive groups. Every proposal is checked by exact arithmetic;
clients must still construct Lean proofs.

Budget exhaustion retains sound proposals but reports an incomplete enumeration.
The zero target has only the empty-support proposal. Dimension mismatches are
reported explicitly rather than mistaken for a completed empty search.
-/
def referenceDecompositions (sources : Array (Array Rat)) (target : Array Rat)
    (config : ReferenceConfig := {}) : ReferenceResult := Id.run do
  if sources.any (fun v => v.size != target.size) then
    return { status := .invalidDimensions }
  let zero : Array Rat := Array.replicate sources.size 0
  let whole := solve sources target (List.range sources.size).toArray
  let rank := whole.rank
  if whole.solution?.isNone then
    return { rank }
  if target.all (· == 0) then
    if config.maxResults == 0 then
      return { rank, status := .exhausted .results }
    return { coefficients := #[zero], rank }
  let mut result : ReferenceResult := { rank }
  for support in [1:rank + 1] do
    let mut selected? := some (List.range support).toArray
    while let some selected := selected? do
      if result.attempts >= config.maxSubsets then
        return { result with status := .exhausted .subsets }
      result := { result with attempts := result.attempts + 1 }
      let solved := solve sources target selected
      if solved.rank == selected.size then
        if let some solution := solved.solution? then
          let mut coefficients := zero
          for index in [:selected.size] do
            coefficients := coefficients.set! selected[index]! solution[index]!
          if isDecomposition sources target coefficients && !result.coefficients.contains coefficients then
            if result.coefficients.size >= config.maxResults then
              return { result with status := .exhausted .results }
            result := { result with coefficients := result.coefficients.push coefficients }
      selected? := nextSubset? sources.size selected
  return result

end NormArith.Search
