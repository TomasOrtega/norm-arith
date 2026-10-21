module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public meta import Lean

/-!
# Checked constraints for finite metric estimates

Generate distance nonnegativity, symmetry, and triangle constraints on at most
8 observed points. This bounded extension makes no completeness claim.
-/

public meta section

namespace NormArith.Metric

open Lean Meta

private def realComparison (input : Expr) : MetaM Bool := do
  let e := input.consumeMData
  unless e.isAppOf ``LE.le || e.isAppOf ``LT.lt || e.isAppOf ``Eq ||
      e.isAppOf ``GE.ge || e.isAppOf ``GT.gt do return false
  let args := e.getAppArgs
  if args.size < 2 then return false
  return (← whnf (← inferType args[args.size - 2]!)).isConstOf ``Real

private partial def collectPoints (input : Expr) : StateT (Array Expr) MetaM Unit := do
  let e := (← liftM (zetaReduce input)).consumeMData
  if e.isAppOf ``Dist.dist then
    let args := e.getAppArgs
    for point in #[args[args.size - 2]!, args.back!] do
      if point.hasLooseBVars || point.hasMVar then continue
      let points ← get
      if points.size < 8 && !points.contains point then set (points.push point)
    return
  for arg in e.getAppArgs do collectPoints arg

def constraints (target : Expr) (inputFacts : Array Expr) : MetaM (Array Expr) := do
  unless ← realComparison target do throwError "expected a real comparison"
  let inputFacts ← inputFacts.filterM fun h => do realComparison (← inferType h)
  let points := (← (do
    collectPoints target
    for h in inputFacts do collectPoints (← inferType h)
    : StateT (Array Expr) MetaM Unit).run #[]).2
  unless !points.isEmpty do throwError "no distance expressions"
  let mut facts := inputFacts
  for i in [:points.size] do
    let a := points[i]!
    let saved ← saveState
    try
      facts := facts.push (← mkAppM ``dist_self #[a])
    catch _ => saved.restore
    for j in [i + 1:points.size] do
      let b := points[j]!
      let saved ← saveState
      try
        let nonneg ← mkAppOptM ``dist_nonneg #[some (← inferType a), none, some a, some b]
        let comm ← mkAppM ``dist_comm #[a, b]
        facts := facts ++ #[nonneg, comm]
      catch _ => saved.restore
  for i in [:points.size] do
    for j in [:points.size] do
      for k in [:points.size] do
        if i == j || j == k || i == k then continue
        let saved ← saveState
        try
          facts := facts.push (← mkAppM ``dist_triangle #[points[i]!, points[j]!, points[k]!])
        catch _ => saved.restore
  return facts

end NormArith.Metric
