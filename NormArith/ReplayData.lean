module

public meta import Lean.Meta.Check
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Data.Json

/-!
# Exact proof graphs

Replay data contains expressions, not tactic programs. Each graph edge points to
an earlier node. Local facts use names without macro scopes and occurrence
numbers. The kernel checks the decoded proof. No arithmetic or analytic search
is used.
-/

public meta section

namespace NormArith.Replay

open Lean Meta Elab Tactic

private def encodeName : Name → Json
  | .anonymous => .null
  | .str p s => .arr #[encodeName p, toJson s]
  | .num p n => .arr #[encodeName p, toJson n]

private partial def decodeName (j : Json) : Except String Name := do
  if j.isNull then return .anonymous
  let #[p, part] ← j.getArr? | throw "invalid replay name"
  let p ← decodeName p
  match part with
  | .str s => return .str p s
  | _ => return .num p (← part.getNat?)

private partial def encodeLevel : Level → Json
  | .zero => toJson (0 : Nat)
  | .succ l => .arr #[toJson (1 : Nat), encodeLevel l]
  | .max a b => .arr #[toJson (2 : Nat), encodeLevel a, encodeLevel b]
  | .imax a b => .arr #[toJson (3 : Nat), encodeLevel a, encodeLevel b]
  | .param n => .arr #[toJson (4 : Nat), encodeName n]
  | .mvar _ => .null

private partial def decodeLevel (j : Json) : Except String Level := do
  if j == toJson (0 : Nat) then return .zero
  match ← j.getArr? with
  | #[tag, a] =>
    match ← tag.getNat? with
    | 1 => return .succ (← decodeLevel a)
    | 4 => return .param (← decodeName a)
    | _ => throw "invalid replay universe"
  | #[tag, a, b] =>
    match ← tag.getNat? with
    | 2 => return .max (← decodeLevel a) (← decodeLevel b)
    | 3 => return .imax (← decodeLevel a) (← decodeLevel b)
    | _ => throw "invalid replay universe"
  | _ => throw "invalid replay universe"

private def encodeBinder : BinderInfo → Nat
  | .default => 0
  | .implicit => 1
  | .strictImplicit => 2
  | .instImplicit => 3

private def decodeBinder (n : Nat) : Except String BinderInfo :=
  match n with
  | 0 => .ok .default
  | 1 => .ok .implicit
  | 2 => .ok .strictImplicit
  | 3 => .ok .instImplicit
  | _ => .error "invalid replay binder"

private structure EncodeState where
  nodes : Array Json := #[]
  indices : Std.HashMap Expr Nat := {}

private partial def encodeExpr (input : Expr) : StateT EncodeState MetaM Nat := do
  let e := input.consumeMData
  if let some i := (← get).indices[e]? then return i
  let node ← match e with
    | .bvar i => pure <| Json.arr #[toJson (0 : Nat), toJson i]
    | .fvar id => do
      let decl ← liftM <| id.getDecl
      let name := decl.userName.eraseMacroScopes
      let mut occurrence := 0
      let context ← liftM (getLCtx : MetaM LocalContext)
      for other in context do
        if other.fvarId == id then break
        if other.userName.eraseMacroScopes == name then occurrence := occurrence + 1
      pure <| Json.arr #[toJson (1 : Nat), encodeName name, toJson occurrence]
    | .sort u => pure <| Json.arr #[toJson (2 : Nat), encodeLevel u]
    | .const n us => pure <| Json.arr #[toJson (3 : Nat), encodeName n,
        Json.arr (us.toArray.map encodeLevel)]
    | .app f a => do
      pure <| Json.arr #[toJson (4 : Nat), toJson (← encodeExpr f), toJson (← encodeExpr a)]
    | .lam n t b bi => do
      pure <| Json.arr #[toJson (5 : Nat), encodeName n, toJson (← encodeExpr t),
        toJson (← encodeExpr b), toJson (encodeBinder bi)]
    | .forallE n t b bi => do
      pure <| Json.arr #[toJson (6 : Nat), encodeName n, toJson (← encodeExpr t),
        toJson (← encodeExpr b), toJson (encodeBinder bi)]
    | .letE n t v b nd => do
      pure <| Json.arr #[toJson (7 : Nat), encodeName n, toJson (← encodeExpr t),
        toJson (← encodeExpr v), toJson (← encodeExpr b), toJson nd]
    | .lit (.natVal n) => pure <| Json.arr #[toJson (8 : Nat), toJson n]
    | .lit (.strVal s) => pure <| Json.arr #[toJson (9 : Nat), toJson s]
    | .proj n i a => do
      pure <| Json.arr #[toJson (10 : Nat), encodeName n, toJson i, toJson (← encodeExpr a)]
    | _ => throwError "replay cannot contain unresolved metavariables"
  let i := (← get).nodes.size
  modify fun s => { nodes := s.nodes.push node, indices := s.indices.insert e i }
  return i

/-- Store the full proof with shared subexpressions. -/
def encode (proof : Expr) : MetaM String := do
  let proof ← instantiateMVars proof
  if proof.hasMVar then throwError "replay cannot contain unresolved metavariables"
  let (root, state) ← (encodeExpr proof).run {}
  return (Json.arr #[toJson (1 : Nat), toJson root, Json.arr state.nodes]).compress

private def readValue (result : Except String α) : MetaM α :=
  match result with
  | .ok value => pure value
  | .error reason => throwError "invalid replay: {reason}"

private def reference (nodes : Array Expr) (j : Json) : MetaM Expr := do
  let i ← readValue j.getNat?
  let some e := nodes[i]? | throwError "invalid replay: forward or missing graph reference"
  return e

private def localReference (name : Name) (occurrence : Nat) : MetaM Expr := do
  let mut found := 0
  for decl in ← getLCtx do
    if decl.userName.eraseMacroScopes != name then continue
    if found == occurrence then return decl.toExpr
    found := found + 1
  throwError "stale replay: local premise {name} is missing"

/-- Decode the graph and ask the kernel to check the resulting proof. -/
def decode (text : String) : MetaM Expr := do
  let json ← readValue (Json.parse text)
  let #[version, root, data] ← readValue json.getArr? | throwError "invalid replay header"
  unless (← readValue version.getNat?) == 1 do throwError "unsupported replay version"
  let data ← readValue data.getArr?
  let mut nodes : Array Expr := #[]
  for node in data do
    let fields ← readValue node.getArr?
    let some tag := fields[0]? | throwError "empty replay node"
    let tag ← readValue tag.getNat?
    let expr ← match tag, fields with
      | 0, #[_, i] => pure <| mkBVar (← readValue i.getNat?)
      | 1, #[_, n, i] => localReference (← readValue (decodeName n)) (← readValue i.getNat?)
      | 2, #[_, u] => pure <| mkSort (← readValue (decodeLevel u))
      | 3, #[_, n, us] => do
        let name ← readValue (decodeName n)
        if name == ``sorryAx then throwError "replay cannot contain sorry"
        let levels ← (← readValue us.getArr?).toList.mapM fun u => readValue (decodeLevel u)
        pure <| mkConst name levels
      | 4, #[_, f, a] => pure <| mkApp (← reference nodes f) (← reference nodes a)
      | 5, #[_, n, t, b, bi] => do
        pure (mkLambda (← readValue (decodeName n))
          (← readValue (decodeBinder (← readValue bi.getNat?)))
          (← reference nodes t) (← reference nodes b))
      | 6, #[_, n, t, b, bi] => do
        pure (mkForall (← readValue (decodeName n))
          (← readValue (decodeBinder (← readValue bi.getNat?)))
          (← reference nodes t) (← reference nodes b))
      | 7, #[_, n, t, v, b, nd] => do
        pure (mkLet (← readValue (decodeName n))
          (← reference nodes t) (← reference nodes v) (← reference nodes b)
          (← readValue (fromJson? nd)))
      | 8, #[_, n] => pure <| mkNatLit (← readValue n.getNat?)
      | 9, #[_, s] => pure <| mkStrLit (← readValue s.getStr?)
      | 10, #[_, n, i, a] => do
        pure (mkProj (← readValue (decodeName n))
          (← readValue i.getNat?) (← reference nodes a))
      | _, _ => throwError "invalid replay node"
    nodes := nodes.push expr
  let proof ← reference nodes root
  if proof.hasLooseBVars then throwError "invalid replay: unbound variable"
  let context ← instantiateLCtxMVars (← getLCtx)
  withLCtx context (← getLocalInstances) <| checkWithKernel proof
  return proof

elab "norm_arith_replay" data:str : tactic => withMainContext do
  let proof ← decode data.getString
  unless ← isDefEq (← inferType proof) (← getMainTarget) do
    throwError "stale replay: proof has type {← inferType proof}, expected {← getMainTarget}"
  (← getMainGoal).assign proof
  replaceMainGoal []

end NormArith.Replay
