module

public import NormArith.Certificate
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public meta import Lean
public meta import NormArith.Search
public meta import NormArith.Metric

/-!
# Checked norm arithmetic

`norm_arith` selects local bounds automatically. `norm_arith [facts]` controls
the norm facts while retaining local scalar comparisons. The real-space core
handles rational vector combinations and affine scalar comparisons, including
strict inequalities, equalities, and distances. Vector equalities supply checked
zero-norm constraints.

Structural bounds and a short decomposition search run first. The reference
fallback enumerates independent supports among all observed norm arguments.
Its per-target defaults allow 10000 subsets and 10000 results; exhaustion is
unknown. Every path uses the same checked vector identity and norm certificates,
then mathlib's exact `linarith` backend. `norm_arith?` reports successful search.

Integer certificates and bounded signed pairs also work in seminormed additive
groups, with weaker guarantees. The upper-bound extension accepts opaque scalar
right sides. Neither extension has the real core's completeness guarantee.

Local quantified norm bounds are specialized using observed vector terms and
checked interval or ball premises. This bounded heuristic is separate from the
quantifier-free core.

Generic metric estimates use checked distance constraints on at most 8 points.
This extension is separate from the normed-space core and its completeness claim.
-/

public meta section

namespace NormArith

open Lean Meta Elab Tactic

private abbrev Form := Array (Nat × Rat)

private def lastTwo? (e : Expr) : Option (Expr × Expr) :=
  let args := e.getAppArgs
  if args.size < 2 then none else some (args[args.size - 2]!, args.back!)

/-- Read closed rational scalar expressions without evaluating real numbers. -/
private partial def scalar? (input : Expr) : Option Rat := do
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

private def scale (c : Rat) (v : Form) : Form :=
  v.map fun (i, a) => (i, c * a)

/-- Atoms are formal expressions, not a claim of linear independence in `E`. -/
private partial def linearize (input : Expr) : StateT (Array Expr) MetaM Form := do
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

private def dense (dimension : Nat) (form : Form) : Array Rat := Id.run do
  let mut result : Array Rat := Array.replicate dimension 0
  for (i, c) in form do
    result := result.set! i (result[i]! + c)
  return result

private def normArgument? (input : Expr) : Option Expr :=
  let e := input.consumeMData
  if e.isAppOf ``Norm.norm then some e.getAppArgs.back! else none

private structure Source where
  vector : Expr
  proof : Expr
  deriving Inhabited

private def readSource (stx : TSyntax `term) : TacticM Source := do
  let proof ← Term.elabTermAndSynthesize stx none
  let type ← instantiateMVars (← inferType proof)
  unless type.isAppOf ``LE.le do
    throwErrorAt stx "expected an upper bound of the form ‖v‖ ≤ b"
  let some (lhs, _) := lastTwo? type | throwErrorAt stx "expected a norm bound"
  let some vector := normArgument? lhs |
    throwErrorAt stx "the left side of this bound must be a norm"
  return { vector, proof }

private def ratSyntax (q : Rat) : TacticM (TSyntax `term) := do
  let magnitude : TSyntax `term := ⟨Syntax.mkNumLit (toString q.num.natAbs)⟩
  let numerator ← if q.num < 0 then `(-$magnitude) else pure magnitude
  let denominator : TSyntax `term := ⟨Syntax.mkNumLit (toString q.den)⟩
  `((($numerator : ℝ) / ($denominator : ℝ)))

private def scaleSource (coefficient : Rat) (vector proof : TSyntax `term) :
    TacticM (TSyntax `term × TSyntax `term) := do
  if coefficient == 1 then return (vector, proof)
  if coefficient == -1 then return (← `(-$vector), ← `(NormArith.bound_neg $proof))
  if coefficient.den == 1 then
    let magnitude : TSyntax `term := ⟨Syntax.mkNumLit (toString coefficient.num.natAbs)⟩
    let multiple ← `(($magnitude : ℕ) • $vector)
    let bound ← `(NormArith.bound_nsmul $magnitude $proof)
    if coefficient.num < 0 then
      return (← `(-$multiple), ← `(NormArith.bound_neg $bound))
    return (multiple, bound)
  let c ← ratSyntax coefficient
  return (← `($c • $vector), ← `(NormArith.bound_smul $c $proof))

private def hasNorm (e : Expr) : Bool :=
  (e.find? fun t => t.isAppOf ``Norm.norm || t.isAppOf ``Dist.dist ||
    t.isAppOf ``NNNorm.nnnorm || t.isAppOf ``ENorm.enorm ||
    t.isAppOf ``NNDist.nndist || t.isAppOf ``EDist.edist).isSome

/-- Exclude norms that premise matching can unfold, with conservative limits. -/
private partial def hiddenNorm (input : Expr) (fuel : Nat) : StateT Nat MetaM Bool := do
  let e := (← liftM (zetaReduce input)).consumeMData
  if hasNorm e then return true
  if e.isFVar || e.isBVar || e.isSort || e.isLit then return false
  if fuel == 0 || (← get) >= 256 then return true
  modify (· + 1)
  for arg in e.getAppArgs do
    let type ← liftM (inferType arg)
    if type.isSort && type != mkSort Level.zero then continue
    if (← liftM (isClass? type)).isSome then continue
    if ← hiddenNorm arg (fuel - 1) then return true
  let operators := #[``LE.le, ``LT.lt, ``Eq, ``GE.ge, ``GT.gt, ``HAdd.hAdd,
    ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv, ``Neg.neg, ``Min.min, ``Max.max, ``OfNat.ofNat]
  if operators.any e.isAppOf then return false
  if let some unfolded ← liftM (withDefault (unfoldDefinition? e)) then
    if unfolded != e then return ← hiddenNorm unfolded (fuel - 1)
  return false

private def hasHiddenNorm (input : Expr) : MetaM Bool := do
  return (← (hiddenNorm input 8).run 0).1

private partial def scalarCore (input : Expr) : Bool := Id.run do
  let e := input.consumeMData
  if e.isAppOf ``Norm.norm || e.isAppOf ``Dist.dist then return true
  if !hasNorm e then return true
  if e.isAppOf ``Neg.neg then return scalarCore e.getAppArgs.back!
  if let some (a, b) := lastTwo? e then
    if e.isAppOf ``HAdd.hAdd || e.isAppOf ``HSub.hSub then
      return scalarCore a && scalarCore b
    if e.isAppOf ``HMul.hMul then
      return (scalar? a).isSome && scalarCore b ||
        (scalar? b).isSome && scalarCore a
    if e.isAppOf ``HDiv.hDiv then
      return (scalar? b).any (· != 0) && scalarCore a
  return false

private def realComparison (input : Expr) : MetaM Bool := do
  let e := input.consumeMData
  unless e.isAppOf ``LE.le || e.isAppOf ``LT.lt || e.isAppOf ``Eq ||
      e.isAppOf ``GE.ge || e.isAppOf ``GT.gt do return false
  let some (a, _) := lastTwo? e | return false
  return (← whnf (← inferType a)).isConstOf ``Real

private partial def normTypes (input : Expr) : StateT (Array Expr) MetaM Unit := do
  let e := input.consumeMData
  let vector? := (normArgument? e).orElse fun _ =>
    if e.isAppOf ``Dist.dist then (lastTwo? e).map Prod.fst else none
  if let some vector := vector? then
    let type ← liftM (inferType vector)
    let types ← get
    if !types.contains type then set (types.push type)
    return
  if !hasNorm e then return
  for arg in e.getAppArgs do normTypes arg

private def hasGroup (space : Expr) : MetaM Bool := do
  try
    return (← synthInstance? (← mkAppM ``SeminormedAddCommGroup #[space])).isSome
  catch _ => return false

private def hasRealSpace (space : Expr) : MetaM Bool := do
  try
    let type ← mkAppOptM ``NormedSpace #[some (mkConst ``Real), some space, none, none]
    return (← synthInstance? type).isSome
  catch _ => return false

private def hasMetricSpace (space : Expr) : MetaM Bool := do
  try
    return (← synthInstance? (← mkAppM ``PseudoMetricSpace #[space])).isSome
  catch _ => return false

private def linearComparison (input : Expr) : MetaM Bool := do
  unless ← realComparison input do return false
  let some (a, b) := lastTwo? input | return false
  return scalarCore a && scalarCore b

private def additiveComparison (input : Expr) : MetaM Bool := do
  unless ← linearComparison input do return false
  let types := (← (normTypes input).run #[]).2
  types.allM hasGroup

private partial def conjunctionTypes (input : Expr) : Array Expr :=
  let e := input.consumeMData
  if e.isAppOf ``And then
    conjunctionTypes e.getAppArgs[0]! ++ conjunctionTypes e.getAppArgs[1]!
  else #[e]

/-- Classify the recognized syntax and its actual normed-space capabilities. -/
def goalFragment (input : Expr) (extraFacts : Array Expr := #[]) : MetaM String := do
  let e := (← zetaReduce (← instantiateMVars input)).consumeMData
  unless ← realComparison e do return "outside_fragment"
  let targetTypes := (← (normTypes e).run #[]).2
  if ← linearComparison e then
    unless ← targetTypes.allM hasGroup do
      if (e.find? (·.isAppOf ``Dist.dist)).isSome && (← targetTypes.allM hasMetricSpace) then
        return "metric_extension"
      return "outside_fragment"
    let mut types := targetTypes
    let mut metricFacts := false
    let mut factTypes ← extraFacts.mapM fun h => do
      zetaReduce (← instantiateMVars (← inferType h))
    for decl in ← getLCtx do
      if !decl.isImplementationDetail then
        factTypes := factTypes.push (← zetaReduce (← instantiateMVars decl.type))
    for type in factTypes.flatMap conjunctionTypes do
      if hasNorm type && (← additiveComparison type) then
        types := (← (normTypes type).run types).2
      else if (type.find? (·.isAppOf ``Dist.dist)).isSome && (← linearComparison type) then
        if ← ((← (normTypes type).run #[]).2).allM hasMetricSpace then metricFacts := true
    if metricFacts then return "metric_extension"
    if !types.isEmpty then
      return if ← types.allM hasRealSpace then "core" else "additive_group_extension"
  if e.isAppOf ``LE.le then
    if let some (a, _) := lastTwo? e then
      let lhsTypes := (← (normTypes a).run #[]).2
      if ((normArgument? a).isSome || a.isAppOf ``Dist.dist) &&
          !lhsTypes.isEmpty && (← lhsTypes.allM hasGroup) then
        return "upper_bound_extension"
  return "outside_fragment"

/-- The complete mathematical core requires real normed-space capabilities. -/
def isCoreGoal (input : Expr) : MetaM Bool := do
  return (← goalFragment input) == "core"

/-- Census eligibility also includes the separately reported sound extensions. -/
def isEligibleGoal (input : Expr) : MetaM Bool := do
  return (← goalFragment input) != "outside_fragment"

private partial def collectNorms (input : Expr) : StateT (Array Expr) MetaM Unit := do
  let e := (← liftM (zetaReduce input)).consumeMData
  if let some v := normArgument? e then
    let v ← liftM (zetaReduce v)
    let vs ← get
    for old in vs do
      if ← liftM (isDefEq old v) then return
    set (vs.push v)
    return
  if !hasNorm e then return
  for arg in e.getAppArgs do collectNorms arg

private partial def conjuncts (h : Expr) : MetaM (Array Expr) := do
  let type := (← whnf (← zetaReduce (← instantiateMVars (← inferType h)))).consumeMData
  if type.isAppOf ``And then
    return (← conjuncts (← mkAppM ``And.left #[h])) ++
      (← conjuncts (← mkAppM ``And.right #[h]))
  return #[h]

private def selectedFacts (hypotheses : Option (Array (TSyntax `term))) :
    TacticM (Array Expr) := do
  let mut facts := #[]
  if let some hs := hypotheses then
    for h in hs do
      facts := facts ++ (← conjuncts (← Term.elabTermAndSynthesize h none))
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    for h in ← conjuncts decl.toExpr do
      let type ← zetaReduce (← instantiateMVars (← inferType h))
      if hypotheses.isNone || ((← realComparison type) && !(← hasHiddenNorm type)) then
        facts := facts.push h
  return facts

private partial def scalarOrderFacts (input : Expr) : StateT (Array Expr) MetaM (Array Expr) := do
  let e := (← liftM (zetaReduce input)).consumeMData
  let seen ← get
  if seen.contains e then return #[]
  set (seen.push e)
  let mut facts := #[]
  if let some v := normArgument? e then
    if ← liftM (hasGroup (← inferType v)) then
      facts := facts.push (← liftM (mkAppM ``norm_nonneg #[v]))
    if (← liftM (whnf (← inferType v))).isConstOf ``Real then
      facts := facts.push (← liftM (mkAppM ``Real.le_norm_self #[v]))
      let negative ← liftM (mkAppM ``Neg.neg #[v])
      let h ← liftM (mkAppM ``Real.le_norm_self #[negative])
      let eq ← liftM (mkAppM ``norm_neg #[v])
      facts := facts.push (← liftM (mkAppM ``le_of_le_of_eq #[h, eq]))
      facts := facts ++ (← scalarOrderFacts v)
    return facts
  if e.isAppOf ``Min.min || e.isAppOf ``Max.max then
    if (← liftM (whnf (← inferType e))).isConstOf ``Real then
      if let some (a, b) := lastTwo? e then
        let lemmas := if e.isAppOf ``Min.min then #[``min_le_left, ``min_le_right]
          else #[``le_max_left, ``le_max_right]
        for lemmaName in lemmas do
          facts := facts.push (← liftM (mkAppM lemmaName #[a, b]))
  for arg in e.getAppArgs do
    facts := facts ++ (← scalarOrderFacts arg)
  return facts

private def closeWith (proof : Expr) : TacticM Bool := withMainContext do
  if ← isDefEq (← inferType proof) (← getMainTarget) then
    (← getMainGoal).assign proof
    replaceMainGoal []
    return true
  return false

private def tryLinear (facts : Array Expr) : TacticM Bool := do
  let saved ← saveState
  try
    Mathlib.Tactic.Linarith.linarith true facts.toList {} (← getMainGoal)
    replaceMainGoal []
    return true
  catch _ =>
    saved.restore
    return false

private partial def vectorPatterns (input : Expr) (fuel : Nat) : Array Expr := Id.run do
  let e := input.consumeMData
  if fuel == 0 then return #[e]
  if e.isAppOf ``Neg.neg then
    return #[e] ++ vectorPatterns e.getAppArgs.back! (fuel - 1)
  if let some (a, b) := lastTwo? e then
    if e.isAppOf ``HAdd.hAdd || e.isAppOf ``HSub.hSub then
      return #[e] ++ vectorPatterns a (fuel - 1) ++ vectorPatterns b (fuel - 1)
  return #[e]

private partial def premiseProof? (target : Expr) (facts : Array Expr)
    (fuel : Nat := 4) : TacticM (Option Expr) := do
  for h in facts do
    let saved ← saveState
    if ← isDefEq (← inferType h) target then return some h
    saved.restore
  if fuel == 0 then return none
  let type := (← whnf target).consumeMData
  if type.isConstOf ``True then return some (mkConst ``True.intro)
  if type.isAppOf ``And then
    let some left ← premiseProof? type.getAppArgs[0]! facts (fuel - 1) | return none
    let some right ← premiseProof? type.getAppArgs[1]! facts (fuel - 1) | return none
    return some (← mkAppM ``And.intro #[left, right])
  if ← realComparison target then
    let saved ← saveState
    try
      let goal ← mkFreshExprSyntheticOpaqueMVar target
      let mut comparisons := #[]
      for h in facts do
        if ← realComparison (← inferType h) then comparisons := comparisons.push h
      Mathlib.Tactic.Linarith.linarith true comparisons.toList {} goal.mvarId!
      let proof ← instantiateMVars goal
      unless proof.hasMVar do return some proof
    catch _ => pure ()
    saved.restore
  return none

/-- Bounded specialization: 12 templates and binders, 32 observed vectors and
new bounds, and 128 attempts with at most 8 additive patterns per attempt. -/
private def instantiateBounds (facts : Array Expr) : TacticM (Array Expr) := do
  let vectors := (← (collectNorms (← getMainTarget)).run #[]).2
  let (_, atoms) ← (vectors.mapM linearize).run #[]
  let mut observed := vectors
  for atom in atoms do
    if !observed.contains atom then observed := observed.push atom
  observed := observed.extract 0 32
  let mut premises := facts
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    for h in ← conjuncts decl.toExpr do
      let type ← whnf (← zetaReduce (← inferType h))
      if (← isProp type) && !(← hasHiddenNorm type) && !premises.contains h then
        premises := premises.push h
  let mut result := facts
  let mut templates := 0
  let mut attempts := 0
  for h in facts do
    let type ← whnf (← inferType h)
    unless type.isForall && (← isProp type) && hasNorm type do continue
    if templates >= 12 then break
    templates := templates + 1
    for vector in observed do
      if attempts >= 128 || result.size >= facts.size + 32 then return result
      attempts := attempts + 1
      let saved ← saveState
      try
        let (args, infos, body) ← forallMetaTelescopeReducing type (some 12)
        if body.isForall then saved.restore; continue
        let patterns := ((← (collectNorms body).run #[]).2).flatMap (vectorPatterns · 8)
        let mut matched := false
        for pattern in patterns.extract 0 8 do
          let beforeMatch ← saveState
          if ← isDefEq pattern vector then matched := true; break
          beforeMatch.restore
        if !matched then saved.restore; continue
        let mut complete := true
        for k in [:args.size] do
          let arg ← instantiateMVars args[k]!
          unless arg.isMVar do continue
          let argumentType ← instantiateMVars (← inferType arg)
          let proof? ← if infos[k]! == .instImplicit && !(← hasHiddenNorm argumentType) then
              synthInstance? argumentType
            else if ← isProp argumentType then premiseProof? argumentType premises else pure none
          if let some proof := proof? then arg.mvarId!.assign proof
          else complete := false; break
        if !complete then saved.restore; continue
        let proof ← instantiateMVars (mkAppN h args)
        if proof.hasMVar then saved.restore; continue
        for bound in ← conjuncts proof do
          if result.size >= facts.size + 32 then return result
          if !result.contains bound then result := result.push bound
      catch _ => saved.restore
  return result

private def upperSources (facts : Array Expr) : TacticM (Array Source) := do
  let mut sources := #[]
  for h in facts do
    let type := (← zetaReduce (← instantiateMVars (← inferType h))).consumeMData
    if type.isAppOf ``LE.le || type.isAppOf ``LT.lt then
      if let some (a, _) := lastTwo? type then
        if let some v := normArgument? a then
          let h ← if type.isAppOf ``LT.lt then mkAppM ``le_of_lt #[h] else pure h
          sources := sources.push { vector := v, proof := h }
  return sources

private partial def structuralBound (input : Expr) (sources : Array Source) : MetaM Expr := do
  let e := (← zetaReduce input).consumeMData
  for source in sources do
    if ← isDefEq source.vector e then return source.proof
  if e.isAppOf ``Neg.neg then
    return ← mkAppM ``bound_neg #[← structuralBound e.getAppArgs.back! sources]
  if let some (a, b) := lastTwo? e then
    if e.isAppOf ``HAdd.hAdd then
      return ← mkAppM ``bound_add #[← structuralBound a sources, ← structuralBound b sources]
    if e.isAppOf ``HSub.hSub then
      return ← mkAppM ``bound_sub #[← structuralBound a sources, ← structuralBound b sources]
    if e.isAppOf ``HSMul.hSMul || e.isAppOf ``SMul.smul then
      if (← inferType a).isConstOf ``Real && (scalar? a).isSome &&
          (← hasRealSpace (← inferType b)) then
        return ← mkAppM ``bound_smul #[a, ← structuralBound b sources]
  let norm ← mkAppM ``Norm.norm #[e]
  return ← mkAppM ``le_refl #[norm]

private def addConstraint (sources : Array Source) (target : Expr)
    (coefficients : Array Rat) : TacticM Expr := do
  let space ← Term.exprToSyntax (← inferType target)
  let mut combination? : Option (TSyntax `term × TSyntax `term) := none
  for i in [:sources.size] do
    if coefficients[i]! == 0 then continue
    let v ← Term.exprToSyntax sources[i]!.vector
    let h ← Term.exprToSyntax sources[i]!.proof
    let (multiple, bound) ← scaleSource coefficients[i]! v h
    combination? ← match combination? with
      | none => pure (some (multiple, bound))
      | some (v, h) => do
        pure (some (← `($multiple + $v), ← `(NormArith.bound_add $bound $h)))
  let (combination, proof) ← match combination? with
    | some pair => pure pair
    | none => do pure (← `((0 : $space)), ← `(NormArith.bound_zero (E := $space)))
  let combinationExpr ← Term.elabTermAndSynthesize combination (some (← inferType target))
  let identity ← if ← isDefEq target combinationExpr then mkEqRefl target else do
    let tactic ← if coefficients.all (·.den == 1) then
      `(by first | (abel; done) | module) else `(by module)
    Term.elabTermEnsuringType tactic (← mkEq target combinationExpr)
  let bound ← Term.elabTermAndSynthesize proof none
  let certificate ← mkAppM ``bound_of_eq #[identity, bound]
  let userName ← mkFreshUserName `norm_arith_constraint
  let name := mkIdent userName
  let (fvar, next) ← (← getMainGoal).note userName certificate
  replaceMainGoal [next]
  if coefficients.all (fun c => c == 0 || c == 1 || c == -1) then
    return mkFVar fvar
  unless coefficients.all (fun c => c == 0 || c == 1 || c == -1) do
    evalTactic (← `(tactic| norm_num at $name:ident))
  if (← getGoals).isEmpty then return ← mkConst' ``True.intro
  withMainContext <| Term.elabTermAndSynthesize name none

private def tryUpperBound (sources : Array Source) (target : Expr)
    (comparisons : Array Expr) (explain : Bool) : TacticM Bool := do
  let reification : StateT (Array Expr) MetaM (Array Form × Form) := do
    let sourceForms ← sources.mapM fun s => linearize s.vector
    return (sourceForms, ← linearize target)
  let ((forms, targetForm), atoms) ← reification.run #[]
  let candidates := Search.decompositions (forms.map (dense atoms.size)) (dense atoms.size targetForm)
  for coefficients in candidates do
    let saved ← saveState
    try
      let proof ← addConstraint sources target coefficients
      if (← getGoals).isEmpty then return true
      if (← closeWith proof) || (← tryLinear #[proof]) ||
          (← tryLinear (comparisons.push proof)) then
        if explain then logInfo m!"norm_arith checked decomposition coefficients: {coefficients}"
        return true
      saved.restore
    catch _ => saved.restore
  return false

private def signedPairs (columns : Array (Array Rat)) (target : Array Rat) :
    Array (Array Rat) := Id.run do
  let mut results := #[]
  let mut attempts := 0
  for i in [:columns.size] do
    for j in [i + 1:columns.size] do
      for a in #[-1, 1] do
        for b in #[-1, 1] do
          if attempts >= 10000 then return results
          attempts := attempts + 1
          let coefficients := (Array.replicate columns.size 0).set! i a |>.set! j b
          if Search.isDecomposition columns target coefficients then
            results := results.push coefficients
  return results

private def tryMetric (facts : Array Expr) (explain : Bool) : TacticM Bool := do
  let saved ← saveState
  try
    withMainContext do
      let constraints ← Metric.constraints (← getMainTarget) facts
      if ← tryLinear constraints then
        if explain then logInfo "norm_arith checked metric constraints on at most 8 observed points"
        return true
      saved.restore
      return false
  catch _ =>
    saved.restore
    return false

private def run (hypotheses : Option (Array (TSyntax `term))) (explain : Bool) : TacticM Unit :=
  focusAndDone <| withoutRecover do
    let (initialFacts, fragment) ← withMainContext do
      let facts ← selectedFacts hypotheses
      let fragment ← goalFragment (← getMainTarget) facts
      if fragment == "outside_fragment" then
        throwError "norm_arith expects a real linear comparison with recognized norm or distance facts"
      pure (facts, fragment)
    if fragment == "metric_extension" && (← tryMetric initialFacts explain) then return
    evalTactic (← `(tactic| try simp only [dist_eq_norm]))
    if (← getGoals).isEmpty then return
    withMainContext do
      let normalization ← mkSimpContext (← `(tactic| simp only [dist_eq_norm,
        Metric.mem_ball, Metric.mem_closedBall, Set.mem_Icc, Set.mem_Ico,
        Set.mem_Ioc, Set.mem_Ioo])) true
      let facts ← initialFacts.mapM fun h => do
        -- Preserve scalar let names used as opaque nonlinear atoms.
        let type ← instantiateMVars (← inferType h)
        if !(← isProp type) then return h
        let (normalized, _) ← Meta.simp type normalization.ctx normalization.simprocs
        if normalized.expr == type then return h
        normalized.mkEqMP h
      let facts ← instantiateBounds facts
      let mut comparisons := #[]
      let mut scalarFacts := #[]
      for h in facts do
        let type ← zetaReduce (← instantiateMVars (← inferType h))
        if ← realComparison type then
          comparisons := comparisons.push h
          if let some (a, b) := lastTwo? type then
            if scalarCore a && scalarCore b && (← additiveComparison type) then
              scalarFacts := scalarFacts.push h
      let target ← getMainTarget
      let orderFacts := (← (do
        let mut result ← scalarOrderFacts target
        for h in comparisons do
          result := result ++ (← scalarOrderFacts (← inferType h))
        pure result : StateT (Array Expr) MetaM (Array Expr)).run #[]).1
      comparisons := comparisons ++ orderFacts
      scalarFacts := scalarFacts ++ orderFacts
      if ← tryLinear scalarFacts then return
      let sources ← upperSources comparisons
      let goal := (← getMainTarget).consumeMData
      if goal.isAppOf ``LE.le then
        if let some (a, _) := lastTwo? goal then
          if let some v := normArgument? a then
            let bound ← structuralBound v sources
            if ← closeWith bound then return
            if ← tryLinear #[bound] then return
            if ← tryUpperBound sources v comparisons explain then return
      unless ← linearComparison goal do
        throwError "norm_arith: unknown (the opaque upper-bound extension found no certificate)"
      let mut norms := (← (collectNorms goal).run #[]).2
      for h in scalarFacts do
        norms := (← (collectNorms (← zetaReduce (← inferType h))).run norms).2
      for h in facts do
        let type := (← inferType h).consumeMData
        if !type.isAppOf ``Eq then continue
        let some (a, _) := lastTwo? type | continue
        let mut relevant := false
        for v in norms do
          if ← isDefEq (← inferType a) (← inferType v) then relevant := true
        if !relevant then continue
        let saved ← saveState
        try
          let zero ← mkAppM ``norm_sub_of_eq #[h]
          scalarFacts := scalarFacts.push zero
          norms := (← (collectNorms (← inferType zero)).run norms).2
        catch _ => saved.restore
      let reification : StateT (Array Expr) MetaM (Array Form) := norms.mapM linearize
      let (forms, atoms) ← reification.run #[]
      let columns := forms.map (dense atoms.size)
      let mut certificates := scalarFacts
      for v in norms do
        certificates := certificates.push (← mkAppM ``norm_nonneg #[v])
      if ← tryLinear certificates then return
      let mut exhausted := false
      let realCore ← isCoreGoal goal
      for i in [:norms.size] do
        let space ← inferType norms[i]!
        let mut others : Array Nat := #[]
        for j in [:norms.size] do
          if j != i && (← isDefEq space (← inferType norms[j]!)) then others := others.push j
        let otherColumns := others.map (columns[·]!)
        let result := Search.referenceDecompositions otherColumns columns[i]!
        if result.status != .complete then exhausted := true
        let constraints ← others.mapM fun j => do
          let n ← mkAppM ``Norm.norm #[norms[j]!]
          return { vector := norms[j]!, proof := ← mkAppM ``le_refl #[n] : Source }
        let mut candidates := result.coefficients
        unless realCore do
          for proposal in signedPairs otherColumns columns[i]! do
            if !candidates.contains proposal then candidates := candidates.push proposal
        for coefficients in candidates do
          let saved ← saveState
          try
            let proof ← addConstraint constraints norms[i]! coefficients
            if (← getGoals).isEmpty then return
            certificates := certificates.push proof
          catch _ => saved.restore
        if ← tryLinear certificates then
          if explain then logInfo "norm_arith checked a finite family of norm constraints"
          return
      if exhausted then
        throwError "norm_arith: unknown (finite-constraint search resource limit reached)"
      throwError "norm_arith: no certificate for the recognized scalar and norm constraints; \
        the additive-group extension is incomplete"

syntax (name := normArith) "norm_arith" "[" term,* "]" : tactic
syntax (name := normArithExplain) "norm_arith?" "[" term,* "]" : tactic
syntax (name := normArithAuto) "norm_arith" : tactic
syntax (name := normArithExplainAuto) "norm_arith?" : tactic

elab_rules : tactic
  | `(tactic| norm_arith [$hs,*]) => run (some hs.getElems) false
  | `(tactic| norm_arith? [$hs,*]) => run (some hs.getElems) true
  | `(tactic| norm_arith) => run none false
  | `(tactic| norm_arith?) => run none true

end NormArith
