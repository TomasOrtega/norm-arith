import NormArith
import Lean.Elab.Frontend

/-! Semantic observations and bounded replay proposals. Source recompilation is separate. -/

open Lean Meta Elab

meta section

namespace NormArith.Census

@[extern "lean_internal_set_max_memory"]
opaque setMemoryLimit (bytes : USize) : BaseIO Unit

structure Request where
  source : String
  setup : String
  output : String
  relativePath : String
  goalHeartbeats : Nat := 200000
  goalTimeoutMs : Nat := 2000
  memoryMb : Nat := 4096
  maxAttemptsPerFile : Nat := 10000
  attempts : Bool := true
  importCycle : Bool := false
  requireLineSaving : Bool := true
  deriving FromJson

structure Observation where
  key : String
  kind : String
  syntaxKind : String
  declaration : String
  startByte : Nat
  endByte : Nat
  startLine : Nat
  startColumn : Nat
  endLine : Nat
  endColumn : Nat
  goal : String
  replacement : String
  replacementEligible : Bool
  core : Bool
  goalEligible : Bool
  fragment : String
  parentAvailable : Bool
  contextDeclarations : Nat
  bodyStartByte : Option Nat
  bodyEndByte : Option Nat
  eligibilityReason : String
  canonical : Expr

structure ObservedGoal where
  observation : Observation
  context : ContextInfo
  locals : LocalContext
  target : Expr

structure Counts where
  tacticNodes : Nat := 0
  termNodes : Nat := 0
  proofNodes : Nat := 0
  normGoals : Nat := 0
  eligible : Nat := 0
  duplicate : Nat := 0
  synthetic : Nat := 0
  unresolved : Nat := 0
  unlocatedNodes : Nat := 0
  outsideBody : Nat := 0
  errors : Nat := 0
  deriving ToJson

structure Scan where
  counts : Counts := {}
  observations : Array Observation := #[]
  seen : Std.HashSet String := {}

def emit (out : IO.FS.Handle) (fields : List (String × Json)) : IO Unit := do
  out.putStrLn (Json.mkObj fields).compress
  out.flush

def observationFields (o : Observation) : List (String × Json) := [
  ("key", toJson o.key), ("kind", toJson o.kind), ("syntax_kind", toJson o.syntaxKind),
  ("parent_declaration", toJson o.declaration),
  ("start_byte", toJson o.startByte), ("end_byte", toJson o.endByte),
  ("start_line", toJson o.startLine), ("start_column", toJson o.startColumn),
  ("end_line", toJson o.endLine), ("end_column", toJson o.endColumn),
  ("goal", toJson o.goal), ("replacement", toJson o.replacement),
  ("replacement_eligible", toJson o.replacementEligible),
  ("goal_eligible", toJson o.goalEligible),
  ("parent_available", toJson o.parentAvailable),
  ("context_declarations", toJson o.contextDeclarations),
  ("body_start_byte", toJson o.bodyStartByte), ("body_end_byte", toJson o.bodyEndByte),
  ("eligibility_reason", toJson o.eligibilityReason),
  ("fragment", toJson o.fragment)]

partial def containsNorm (e : Expr) : Bool :=
  e.isAppOf ``Norm.norm || e.isAppOf ``Dist.dist || match e with
    | .app f a => containsNorm f || containsNorm a
    | .lam _ t b _ | .forallE _ t b _ => containsNorm t || containsNorm b
    | .letE _ t v b _ => containsNorm t || containsNorm v || containsNorm b
    | .mdata _ b | .proj _ _ b => containsNorm b
    | _ => false

partial def canonicalize : Expr → Expr
  | .mdata _ e => canonicalize e
  | .app f a => .app (canonicalize f) (canonicalize a)
  | .lam _ t b i => .lam .anonymous (canonicalize t) (canonicalize b) i
  | .forallE _ t b i => .forallE .anonymous (canonicalize t) (canonicalize b) i
  | .letE _ t v b n => .letE .anonymous (canonicalize t) (canonicalize v) (canonicalize b) n
  | .proj n i e => .proj n i (canonicalize e)
  | e => e

structure BodyRange where
  startByte : Nat
  endByte : Nat

structure TacticSuffix where
  first : Syntax.Range
  stop : String.Pos.Raw

partial def tacticSuffixes (stx : Syntax) : Array TacticSuffix := Id.run do
  let mut found := #[]
  let body? := if stx.isOfKind ``Parser.Tactic.tacticSeq1Indented then stx.getArgs[0]?
    else if stx.isOfKind ``Parser.Tactic.tacticSeqBracketed then stx.getArgs[1]?
    else none
  if let some body := body? then
    if let some stop := body.getTailPos? (canonicalOnly := true) then
      for child in body.getArgs do
        if !child.isAtom then
          if let some first := child.getRange? (canonicalOnly := true) then
            if first.stop < stop then found := found.push { first, stop }
  for child in stx.getArgs do found := found ++ tacticSuffixes child
  return found

def syntaxBodyRange (stx : Syntax) : Array BodyRange :=
  match stx.getRange? (canonicalOnly := true) with
  | some range => #[{ startByte := range.start.byteIdx, endByte := range.stop.byteIdx }]
  | none => #[]

partial def equationBodies (stx : Syntax) : Array BodyRange := Id.run do
  if stx.isOfKind ``Parser.Term.matchAlt then
    return stx.getArgs.back?.map syntaxBodyRange |>.getD #[]
  let mut found := #[]
  for child in stx.getArgs do found := found ++ equationBodies child
  return found

partial def structureBodies (stx : Syntax) : Array BodyRange := Id.run do
  if stx.isOfKind ``Parser.Term.structInstFieldDef then
    return stx.getArgs.back?.map syntaxBodyRange |>.getD #[]
  if stx.isOfKind ``Parser.Term.structInstFieldEqns then return equationBodies stx
  let mut found := #[]
  for child in stx.getArgs do found := found ++ structureBodies child
  return found

partial def declarationBodies (stx : Syntax) : Array BodyRange := Id.run do
  let mut found := #[]
  if stx.isOfKind ``Parser.Command.declValSimple then
    if let some body := stx.getArgs[1]? then found := found ++ syntaxBodyRange body
  else if stx.isOfKind ``Parser.Command.declValEqns then
    found := found ++ equationBodies stx
  else if stx.isOfKind ``Parser.Command.whereStructInst then
    found := found ++ structureBodies stx
  else if stx.isOfKind ``Parser.Term.whereFinally then
    if let some tactics := stx.getArgs[1]? then found := found ++ syntaxBodyRange tactics
  else if stx.isOfKind ``Parser.Term.whereFinallySubsection then
    found := found ++ (stx.getArgs.back?.map syntaxBodyRange |>.getD #[])
  for child in stx.getArgs do found := found ++ declarationBodies child
  return found

def inspect (ctx : ContextInfo) (replayEnv : Environment) (lctx : LocalContext) (target : Expr)
    (stx : Syntax) (kind : String) (replaceable : Bool) (bodies : Array BodyRange)
    (suffixStop? : Option String.Pos.Raw := none) :
    IO (Bool × Option String × Option ObservedGoal) := do
  let declarations := lctx.foldl (init := []) fun acc decl => decl :: acc
  ctx.runMetaM lctx <| withLocalInstances declarations.reverse do
    let target ← instantiateMVars target
    unless ← isProp target do return (false, none, none)
    let fragment ← NormArith.goalFragment target
    unless containsNorm target || fragment != "outside_fragment" do return (true, none, none)
    let some range := stx.getRange? (canonicalOnly := true) |
      return (true, some "no_source_range", none)
    let .original .. := stx.getHeadInfo | return (true, some "synthetic_syntax", none)
    let range := { range with stop := suffixStop?.getD range.stop }
    if range.start >= range.stop then return (true, some "empty_source_range", none)
    let fvars := lctx.foldl (init := #[]) fun acc decl => acc.push decl.toExpr
    let closed ← mkForallFVars fvars target (usedLetOnly := false) (generalizeNondepLet := false)
    let canonical := canonicalize (← instantiateMVars closed)
    if canonical.hasMVar || canonical.hasFVar then
      throwError "unresolved_context: source-backed norm goal retains metavariables or free variables"
    let start := ctx.fileMap.toPosition range.start
    let stop := ctx.fileMap.toPosition range.stop
    let declaration := ctx.parentDecl?.map toString |>.getD ""
    let key := s!"{kind}:{range.start.byteIdx}:{range.stop.byteIdx}:{declaration}:{canonical.hash}"
    let asTerm := kind == "term" || stx.isOfKind ``Parser.Term.byTactic
    let body? := bodies.foldl (init := none) fun best candidate =>
      if candidate.startByte <= range.start.byteIdx && range.stop.byteIdx <= candidate.endByte then
        match best with
        | none => some candidate
        | some previous => if candidate.endByte - candidate.startByte < previous.endByte - previous.startByte
          then some candidate else best
      else best
    let eligibilityReason := if body?.isNone then "outside_decl_body" else
      if kind == "tactic" && stx.isAtom then "tactic_token" else
      if !replaceable then "multi_goal_tactic" else
      if fragment == "outside_fragment" then "outside_fragment" else "eligible"
    let observation := {
      key, kind, declaration, canonical
      syntaxKind := toString stx.getKind
      startByte := range.start.byteIdx, endByte := range.stop.byteIdx
      startLine := start.line, startColumn := start.column
      endLine := stop.line, endColumn := stop.column
      goal := (← ppExpr target).pretty.take 8192 |>.toString
      replacement := if asTerm then "by norm_arith" else "norm_arith"
      replacementEligible := eligibilityReason == "eligible"
      goalEligible := fragment != "outside_fragment"
      core := fragment == "core"
      fragment
      parentAvailable := ctx.parentDecl?.any replayEnv.contains
      contextDeclarations := fvars.size
      bodyStartByte := body?.map (·.startByte)
      bodyEndByte := body?.map (·.endByte)
      eligibilityReason
    }
    return (true, none, some { observation, context := { ctx with env := replayEnv }, locals := lctx, target })

def goalType (ctx : ContextInfo) (goal : MVarId) : IO (LocalContext × Expr) :=
  ctx.runMetaM {} do
    let decl ← goal.getDecl
    return (decl.lctx, ← instantiateMVars decl.type)

def recordInspection (out : IO.FS.Handle) (phase : String) (scan : IO.Ref Scan)
    (ctx : ContextInfo) (stx : Syntax)
    (result : Bool × Option String × Option ObservedGoal) : IO (Option ObservedGoal) := do
  let (proofNode, exclusion, goal?) := result
  if proofNode then scan.modify fun s => { s with counts.proofNodes := s.counts.proofNodes + 1 }
  if let some reason := exclusion then
    scan.modify fun s => { s with counts.synthetic := s.counts.synthetic + 1 }
    emit out [("type", toJson "node_exclusion"), ("phase", toJson phase),
      ("reason", toJson reason), ("syntax_kind", toJson (toString stx.getKind)),
      ("parent_declaration", toJson (ctx.parentDecl?.map toString |>.getD ""))]
  return goal?

def recordNode (out : IO.FS.Handle) (phase : String) (scan : IO.Ref Scan)
    (onGoal : ObservedGoal → IO Unit) (bodies : Array BodyRange) (suffixes : Array TacticSuffix)
    (replayEnv : Environment) (ctx : ContextInfo) (info : Info) : IO Unit := do
  match info with
  | .ofTacticInfo _ => scan.modify fun s => { s with counts.tacticNodes := s.counts.tacticNodes + 1 }
  | .ofTermInfo _ => scan.modify fun s => { s with counts.termNodes := s.counts.termNodes + 1 }
  | _ => pure ()
  if info matches .ofTacticInfo _ | .ofTermInfo _ then
    unless info.stx.getRange? (canonicalOnly := true) |>.isSome do
      scan.modify fun s => { s with counts.unlocatedNodes := s.counts.unlocatedNodes + 1 }
      return
    unless info.stx.getHeadInfo matches .original .. do
      scan.modify fun s => { s with counts.unlocatedNodes := s.counts.unlocatedNodes + 1 }
      return
  let result ← try
    match info with
    | .ofTacticInfo ti =>
      let ctx := { ctx with mctx := ti.mctxBefore }
      let mut found := #[]
      for goal in ti.goalsBefore do
        let (lctx, target) ← goalType ctx goal
        let result ← inspect ctx replayEnv lctx target ti.stx "tactic"
          (ti.goalsBefore.length == 1 && ti.goalsAfter.isEmpty) bodies
        let goal? ← recordInspection out phase scan ctx ti.stx result
        if let some goal := goal? then found := found.push goal
        if ti.goalsBefore.length == 1 then
          if let some range := ti.stx.getRange? (canonicalOnly := true) then
            for suffix in suffixes do
              if suffix.first.start == range.start && suffix.first.stop == range.stop then
                let result ← inspect ctx replayEnv lctx target ti.stx "tactic_suffix" true bodies
                  (some suffix.stop)
                let goal? ← recordInspection out phase scan ctx ti.stx result
                if let some goal := goal? then found := found.push goal
      pure found
    | .ofTermInfo ti =>
      if ti.isBinder then pure #[] else
      let target ← ti.runMetaM ctx do
        match ti.expectedType? with
          | some expected => pure expected
          | none => inferType ti.expr
      let result ← inspect ctx replayEnv ti.lctx target ti.stx "term" true bodies
      let goal? ← recordInspection out phase scan ctx ti.stx result
      pure goal?.toArray
    | _ => pure #[]
  catch error =>
    let unresolved := error.toString.contains "unresolved_context:"
    scan.modify fun s => if unresolved then
      { s with counts.unresolved := s.counts.unresolved + 1 } else
      { s with counts.errors := s.counts.errors + 1 }
    let stx := info.stx
    let range := stx.getRange? (canonicalOnly := true)
    emit out [("type", toJson (if unresolved then "node_exclusion" else "node_error")),
      ("phase", toJson phase), ("error", toJson error.toString),
      ("parent_declaration", toJson (ctx.parentDecl?.map toString |>.getD "")),
      ("syntax_kind", toJson (toString stx.getKind)),
      ("start_byte", toJson (range.map (·.start.byteIdx))),
      ("end_byte", toJson (range.map (·.stop.byteIdx)))]
    pure #[]
  for goal in result do
    let o := goal.observation
    let s ← scan.get
    if s.seen.contains o.key then
      scan.modify fun s => { s with counts.duplicate := s.counts.duplicate + 1 }
    else
      scan.modify fun s => { s with
        observations := s.observations.push o, seen := s.seen.insert o.key
        counts.normGoals := s.counts.normGoals + 1
        counts.outsideBody := s.counts.outsideBody + if o.bodyStartByte.isNone then 1 else 0
        counts.eligible := s.counts.eligible + if o.replacementEligible then 1 else 0 }
      emit out <| [("type", toJson "observation"), ("phase", toJson phase)] ++ observationFields o
      onGoal goal

def elaborate (req : Request) (setup : ModuleSetup) (input : String)
    (augmented : Bool) : IO (Lean.Elab.IncrementalState × Environment) := do
  let inputCtx := Parser.mkInputContext input req.source
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let imports := (setup.imports?.getD (HeaderSyntax.imports header)) ++
    if augmented then #[{ module := `NormArith : Import }] else #[]
  let opts := Elab.async.setIfNotSet setup.options.toOptions true
  for library in setup.dynlibs do loadDynlib library
  unsafe enableInitializersExecution
  let (env, messages) ← processHeaderCore (leakEnv := true) (HeaderSyntax.startPos header) imports
    (setup.isModule || HeaderSyntax.isModule header) opts messages inputCtx
    (plugins := setup.plugins) (mainModule := setup.name) (package? := setup.package?)
    (arts := setup.importArts) (headerStx? := some header)
  if messages.hasErrors then
    throw <| IO.userError s!"header elaboration failed: {← messages.toList.mapM (·.data.toString)}"
  let state ← IO.processCommandsIncrementally inputCtx parserState (Command.mkState env messages opts) none
  return (state, env)

def collect (out : IO.FS.Handle) (phase : String) (state : Lean.Elab.IncrementalState)
    (headerEnv : Environment)
    (onGoal : ObservedGoal → IO Unit := fun _ => pure ()) : IO Scan := do
  for message in state.commandState.messages.toList do
    if message.severity == .error then
      emit out [("type", toJson "elaboration_error"), ("phase", toJson phase),
        ("message", toJson (← message.data.toString))]
  let scan ← IO.mkRef ({} : Scan)
  let mut before := headerEnv
  let mut next := some state.initialSnap
  while let some snapshot := next do
    let preEnv := before
    let bodies := declarationBodies snapshot.stx
    let suffixes := tacticSuffixes snapshot.stx
    if let some tree := snapshot.elabSnap.infoTreeSnap.get.infoTree? then
      tree.visitM' (preNode := fun _ info _ => pure !(info matches .ofChoiceInfo _))
        (postNode := fun ctx info _ =>
          recordNode out phase scan onGoal bodies suffixes preEnv ctx info)
    before := snapshot.elabSnap.resultSnap.get.cmdState.env
    next := snapshot.nextCmdSnap?.map (·.task.get)
  emit out [("type", toJson "phase_end"), ("phase", toJson phase),
    ("errors", toJson state.commandState.messages.hasErrors), ("counts", toJson (← scan.get).counts)]
  return ← scan.get

def runTactic (ctx : ContextInfo) (lctx : LocalContext) (target : Expr)
    (heartbeats : Nat) (cancelTk : IO.CancelToken) : IO Unit := do
  let ctx := { ctx with options := ctx.options.set `maxHeartbeats heartbeats |>.setBool `debug.skipKernelTC false }
  let declarations := lctx.foldl (init := []) fun acc decl => decl :: acc
  ctx.runMetaM lctx <| withTheReader Core.Context (fun c => { c with cancelTk? := some cancelTk }) <|
      withLocalInstances declarations.reverse do
    let target ← instantiateMVars target
    let goal ← mkFreshExprMVar target .syntheticOpaque
    let tactic ← match Parser.runParserCategory (← getEnv) `tactic "norm_arith" with
      | .ok stx => pure stx
      | .error message => throwError message
    let replay : TermElabM (List MVarId) := Term.withoutErrToSorry <|
      Tactic.run goal.mvarId! <| Tactic.withoutRecover do
        Tactic.evalTactic tactic
        Term.synthesizeSyntheticMVarsNoPostponing
    let (remaining, _) ← (replay {}).run {}
    unless remaining.isEmpty do throwError "norm_arith left goals open"
    let proof ← instantiateMVars goal
    if proof.hasExprMVar || proof.hasSorry then
      let missing ← getMVars proof
      let types ← missing.toList.mapM fun id => do
        let declaration ← id.getDecl
        return s!"{id.name}: {(← ppExpr declaration.type).pretty}"
      throwError "incomplete or admitted proof (levels: {proof.hasLevelMVar}, sorry: {proof.hasSorry}); remaining: {types}"
    unless ← isDefEq (← inferType proof) target do throwError "proof type mismatch"
    if let some parent := ctx.parentDecl? then
      if proof.getUsedConstants.contains parent then throwError "proof refers to its own declaration"
    let fvars := lctx.foldl (init := (#[] : Array Expr)) fun acc decl => acc.push decl.toExpr
    let proof ← mkLambdaFVars fvars proof (usedLetOnly := true) (generalizeNondepLet := false)
    let type ← instantiateMVars (← inferType proof)
    let proof ← instantiateMVars proof
    if proof.hasMVar || type.hasMVar || proof.hasSorry then
      throwError "closed proof is incomplete or admitted (proof metavariables: {proof.hasExprMVar}, levels: {proof.hasLevelMVar}, type metavariables: {type.hasMVar}, sorry: {proof.hasSorry})"
    if let some parent := ctx.parentDecl? then
      if proof.getUsedConstants.contains parent then throwError "closed proof refers to its own declaration"
    let levels := (collectLevelParams (collectLevelParams {} type) proof).params
    addDecl <| .thmDecl {
      name := ← mkFreshUserName `census_checked
      levelParams := levels.toList, type, value := proof }

def attempt (out : IO.FS.Handle) (req : Request) (goal : ObservedGoal)
    (original : Observation) : IO Unit := do
  let started ← IO.monoNanosNow
  let done ← IO.mkRef false
  let cancelTk ← IO.CancelToken.new
  let _ ← IO.asTask (prio := .dedicated) do
    while !(← done.get) do
      if (← IO.monoNanosNow) - started >= req.goalTimeoutMs * 1000000 then
        cancelTk.set
        break
      IO.sleep 5
  let mut status := "success"
  let mut error := ""
  try
    runTactic goal.context goal.locals goal.target req.goalHeartbeats cancelTk
  catch exception =>
    status := "failed"
    error := exception.toString
  done.set true
  let elapsed := (← IO.monoNanosNow) - started
  if (← cancelTk.isSet) || elapsed >= req.goalTimeoutMs * 1000000 then
    status := "goal_timeout"
  else if error.contains "maximum number of heartbeats" then
    status := "heartbeat_limit"
  emit out <| [("type", toJson "attempt"), ("status", toJson status),
    ("elapsed_ms", toJson (elapsed / 1000000)),
    ("kernel_checked", toJson (status == "success")), ("error", toJson error),
    ("context_match", toJson true), ("original_fragment", toJson original.fragment),
    ("augmented_fragment", toJson goal.observation.fragment)] ++ observationFields original

def skipAttempt (out : IO.FS.Handle) (o : Observation) (status : String) : IO Unit :=
  emit out <| [("type", toJson "attempt"), ("status", toJson status),
    ("kernel_checked", toJson false)] ++ observationFields o

def censusFile (out : IO.FS.Handle) (req : Request) (setup : ModuleSetup)
    (input : String) : IO Unit := do
  emit out [("type", toJson "file_start"), ("path", toJson req.relativePath)]
  let (original, originalErrors) ← do
    let (state, headerEnv) ← elaborate req setup input false
    pure ((← collect out "original" state headerEnv), state.commandState.messages.hasErrors)
  let eligible := original.observations.filter (·.replacementEligible)
  let promising := eligible.filter fun o => !req.requireLineSaving || o.startLine != o.endLine
  let mut status := "complete"
  if originalErrors then
    status := "original_elaboration_failed"
    for o in eligible do skipAttempt out o status
  else if !req.attempts then
    for o in eligible do skipAttempt out o "extract_only"
  else
    for o in eligible do
      if req.requireLineSaving && o.startLine == o.endLine then
        skipAttempt out o "no_line_saving_untried"
    if req.importCycle then
      for o in promising do skipAttempt out o "import_cycle"
    else if !promising.isEmpty then try
      let (state, headerEnv) ← elaborate req setup input true
      if state.commandState.messages.hasErrors then
        let _ ← collect out "augmented" state headerEnv
        status := "augmented_elaboration_failed"
        for o in promising do skipAttempt out o status
      else
        let byKey := original.observations.foldl (init := ({} : Std.HashMap String Observation))
          fun map o => map.insert o.key o
        let matched ← IO.mkRef ({} : Std.HashSet String)
        let attempted ← IO.mkRef 0
        let augmented ← collect out "augmented" state headerEnv fun goal => do
          let o := goal.observation
          unless o.replacementEligible do return
          let some original := byKey[o.key]? | return
          unless original.replacementEligible && original.canonical == o.canonical do return
          if req.requireLineSaving && original.startLine == original.endLine then return
          matched.modify (·.insert o.key)
          if (← attempted.get) >= req.maxAttemptsPerFile then
            skipAttempt out original "file_attempt_budget"
          else
            attempted.modify (· + 1)
            attempt out req goal original
        if augmented.counts.errors > 0 then status := "partial_extraction"
        for o in promising do
          unless (← matched.get).contains o.key do skipAttempt out o "context_unmatched"
    catch error =>
      status := "augmented_exception"
      emit out [("type", toJson "phase_error"), ("phase", toJson "augmented"),
        ("error", toJson error.toString)]
      for o in promising do skipAttempt out o status
  if original.counts.errors > 0 then status := "partial_extraction"
  emit out [("type", toJson "file_end"), ("status", toJson status),
    ("path", toJson req.relativePath), ("counts", toJson original.counts)]

end NormArith.Census

unsafe def main (args : List String) : IO UInt32 := do
  let [requestPath] := args | IO.eprintln "usage: norm_arith_census REQUEST.json"; return 2
  try
    let request ← IO.FS.readFile requestPath
    let req ← IO.ofExcept <| Json.parse request >>= fromJson? (α := NormArith.Census.Request)
    let setup ← ModuleSetup.load req.setup
    initSearchPath (← findSysroot)
    enableInitializersExecution
    NormArith.Census.setMemoryLimit (req.memoryMb.toUSize * 1024 * 1024)
    let input ← IO.FS.readFile req.source
    IO.FS.withFile req.output .write fun out => do
      NormArith.Census.censusFile out req setup input
    return 0
  catch error =>
    IO.eprintln error.toString
    return 1
