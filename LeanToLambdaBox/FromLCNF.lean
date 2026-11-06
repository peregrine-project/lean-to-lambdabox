import LeanToLambdaBox.Erasure

/-!
A second eraser, which reads Lean's compiler IR instead of kernel terms. `#erase_lcnf` translates
the LCNF that the compiler stored for a declaration and its dependencies, at the base or mono phase.

Base phase is the default: it is close to the output of `#erase`, and with `nat := .peano` it needs
no primitives. Mono phase adds the compiler's specialization, and it has rewritten matches on `Nat`
into arithmetic, so it needs machine `Nat`.

LCNF is in A-normal form with named variables, so the translation is direct:

| LCNF | λ□ |
|---|---|
| `let x := v; k` | `tLetIn x ⟦v⟧ ⟦k⟧` |
| `fun f ps := b; k`, `jp j ps := b; k` | `tLetIn f (λ ps. ⟦b⟧) ⟦k⟧` |
| `jmp j args`, `f args` | application |
| `cases x` | `tCase x`, with a default alternative copied to each constructor it stands for |
| `return x` | `x` |
| `unreach`, `erased`, type arguments | `□` |

A join point without parameters takes a dummy `□` argument, as `tLetIn` evaluates its value.

The call graph between declarations decides what becomes a fixpoint: each strongly connected
component is one `tFix`, because the compiler's auxiliary declarations can be mutually recursive
without being in one Lean `mutual` block.

This mode trusts Lean's compiler up to the phase it reads, including its `csimp` replacements.

A definition without compiled code, such as one tagged `@[extern]` or one the compiler implements
natively, is erased from its kernel value as `#erase` does, under the same `extern` policy, at the
base phase only. The mono phase represents some types differently from kernel terms (`Decidable` as
`Bool`, a structure with one relevant field as that field), so there such a definition is an axiom.
-/

open Lean
open Lean.Compiler.LCNF

namespace Erasure.FromLCNF

/-- Keep the name if it is ASCII graphic, as in `fvar_to_name`. -/
def binder (n : Name) : BinderName :=
  let s := n.toString
  if s.all (fun c => decide (33 <= c.toNat ∧ c.toNat < 127)) then .named s else .anon

def fetchDecl (phase : Phase) (n : Name) : CoreM (Option (Decl .pure)) :=
  match phase with
  | .base => getBaseDecl? n
  | .mono => getMonoDecl? n
  | .impure => throwError "#erase_lcnf reads the base or mono phase"

/-- The result of `Sort u`-valued telescopes: whether the inductive may live in `Prop`. -/
def mayBeProp (ind : InductiveVal) : Bool :=
  (go ind.type).normalize.isNeverZero == false
where
  go : Expr → Level
    | .forallE _ _ b _ => go b
    | .sort u => u
    | _ => .succ .zero

/-! ## The call graph -/

mutual
  partial def letValueDeps (machine : Bool) (env : Environment) : LetValue .pure → NameSet → NameSet
    | .const n _ _ _, acc =>
      match env.find? n with
      | some (.ctorInfo _) => if machine && n == ``Nat.succ then acc.insert ``Nat.add else acc
      | _ => acc.insert n
    | _, acc => acc

  partial def codeDeps (machine : Bool) (env : Environment) : Code .pure → NameSet → NameSet
    | .let d k, acc => codeDeps machine env k (letValueDeps machine env d.value acc)
    | .fun d k _, acc | .jp d k, acc => codeDeps machine env k (codeDeps machine env d.value acc)
    | .cases c, acc =>
      let acc :=
        if !machine then acc
        else if c.typeName == ``Nat then (acc.insert ``Nat.beq).insert ``Nat.sub
        else if c.typeName == ``Int then ((acc.insert ``Nat.ble).insert ``Int.neg).insert ``Nat.add
        else acc
      c.alts.foldl (init := acc) fun acc alt =>
        match alt with
        | .alt _ _ code _ | .default code => codeDeps machine env code acc
        | _ => acc
    | _, acc => acc
end

structure Node where
  /-- `none` for a declaration without compiled code, which becomes an axiom. -/
  decl : Option (Decl .pure)
  deps : Array Name

/-- The declarations reachable from `root`. -/
partial def gatherGraph (phase : Phase) (machine : Bool) (root : Name)
    : CoreM (Std.HashMap Name Node) := do
  let env ← getEnv
  let rec go (n : Name) (g : Std.HashMap Name Node) : CoreM (Std.HashMap Name Node) := do
    if g.contains n then return g
    let decl? ← fetchDecl phase n
    let node : Node ← match decl? with
      | some d =>
        match d.value with
        | .code c => pure { decl := some d, deps := (codeDeps machine env c {}).toArray }
        | .extern _ => pure { decl := none, deps := #[] }
      | none => pure { decl := none, deps := #[] }
    node.deps.foldlM (init := g.insert n node) fun g m => go m g
  go root {}

structure TarjanState where
  next : Nat := 0
  index : Std.HashMap Name Nat := {}
  low : Std.HashMap Name Nat := {}
  stack : List Name := []
  onStack : Std.HashSet Name := {}
  /-- The components found so far, latest first; each comes after those it depends on. -/
  comps : List (List Name) := []

/-- The strongly connected components of the graph, dependencies first. -/
partial def components (g : Std.HashMap Name Node) (root : Name) : List (List Name) :=
  let rec visit (n : Name) (s : TarjanState) : TarjanState := Id.run do
    let mut s := { s with
      next := s.next + 1, index := s.index.insert n s.next, low := s.low.insert n s.next,
      stack := n :: s.stack, onStack := s.onStack.insert n }
    for m in (g[n]?.map (·.deps)).getD #[] do
      if !s.index.contains m then
        s := visit m s
        s := { s with low := s.low.insert n (min s.low[n]! s.low[m]!) }
      else if s.onStack.contains m then
        s := { s with low := s.low.insert n (min s.low[n]! s.index[m]!) }
    if s.low[n]! == s.index[n]! then
      let (comp, rest) := s.stack.splitAt (s.stack.idxOf n + 1)
      s := { s with
        stack := rest, comps := comp :: s.comps,
        onStack := comp.foldl Std.HashSet.erase s.onStack }
    return s
  (visit root {}).comps.reverse

/-! ## Terms -/

def argTerm : Arg .pure → LBTerm
  | .fvar x => .fvar x
  | _ => .box

def mkApps (f : LBTerm) (args : Array LBTerm) : LBTerm := args.foldl .app f

def lambdas (params : Array (Param .pure)) (body : LBTerm) : LBTerm :=
  params.foldr (fun p b => .lambda (binder p.binderName) (abstract p.fvarId b)) body

def knOf (fix : Std.HashMap Name FVarId) (n : Name) : EraseM LBTerm := do
  if let some x := fix[n]? then return .fvar x
  match (← get).constants[n]? with
  | some kn => return .const kn
  | none => throwError "#erase_lcnf: {n} has no translation yet"

def primInt (n : Nat) : EraseM LBTerm := do
  if n <= BitVec.intMax 63 then
    return .prim ⟨.primInt, n⟩
  throwError "Nat literal {n} not representable as a 63-bit signed integer."

def natLit (n : Nat) : EraseM LBTerm := do
  match (← read).config.nat with
  | .machine => primInt n
  | .peano =>
    let (indid, _) ← register_inductive (← getConstInfoInduct ``Nat)
    return n.fold (init := .construct indid 0 []) fun _ _ t => .app (.construct indid 1 []) t

/-- A constructor application. The arguments include the parameters, as in `#erase`. -/
def ctorTerm (fix : Std.HashMap Name FVarId) (info : ConstructorVal) (args : Array LBTerm)
    : EraseM LBTerm := do
  let (indid, masks) ← register_inductive (← getConstInfoInduct info.induct)
  if isExtern (← getEnv) info.name && (← read).config.extern == .preferAxiom then
    return mkApps (.const (toKername info.name)) args
  if (← read).config.nat matches .machine then
    if info.name == ``Nat.zero then return ← primInt 0
    if info.name == ``Nat.succ then
      return .app (.app (← knOf fix ``Nat.add) args[0]!) (← primInt 1)
  let params := args[:info.numParams].toArray
  let fields := args[info.numParams:info.numParams + info.numFields].toArray
  let extra := args[info.numParams + info.numFields:].toArray
  return mkApps (.construct indid info.cidx []) (params ++ filter masks[info.cidx]! fields ++ extra)

mutual
  partial def letValueTerm (fix : Std.HashMap Name FVarId) : LetValue .pure → EraseM LBTerm
    | .lit (.nat n) => natLit n
    | .lit (.str _) => do
      -- λ□ here has no strings, and the standard library's panic messages reach most programs.
      logWarning "#erase_lcnf: a string literal is erased to □"
      return .box
    | .lit _ => throwError "#erase_lcnf: only Nat and string literals are supported"
    | .erased => return .box
    | .proj s i x _ => do
      let ind ← getConstInfoInduct s
      let (indid, masks) ← register_inductive ind
      let fieldIdx := masks[0]![:i].toArray.count .keep
      return .proj { indType := indid, paramCount := ind.numParams, fieldIdx } (.fvar x)
    | .const n _ args _ => do
      let args := args.map argTerm
      match (← getEnv).find? n with
      | some (.ctorInfo info) => ctorTerm fix info args
      | _ => return mkApps (← knOf fix n) args
    | .fvar f args => return mkApps (.fvar f) (args.map argTerm)
    | _ => throwError "#erase_lcnf: impure value in pure code"

  partial def funTerm (fix : Std.HashMap Name FVarId) (d : FunDecl .pure) (k : Code .pure)
      : EraseM LBTerm := do
    let body ← codeTerm fix d.value
    -- A join point without parameters must not run when it is bound.
    let value := if d.params.isEmpty then .lambda .anon body else lambdas d.params body
    return .letIn (binder d.binderName) value (abstract d.fvarId (← codeTerm fix k))

  partial def codeTerm (fix : Std.HashMap Name FVarId) : Code .pure → EraseM LBTerm
    | .let d k => do
      return .letIn (binder d.binderName) (← letValueTerm fix d.value)
        (abstract d.fvarId (← codeTerm fix k))
    | .fun d k _ | .jp d k => funTerm fix d k
    | .jmp j args =>
      return if args.isEmpty then .app (.fvar j) .box else mkApps (.fvar j) (args.map argTerm)
    | .cases c => casesTerm fix c
    | .return x => return .fvar x
    | .unreach _ => return .box
    | _ => throwError "#erase_lcnf: impure code"

  /-- The alternative of a constructor, with its parameters; `[]` for the default alternative. -/
  partial def altFor (c : Cases .pure) (ctor : Name) : Option (Array (Param .pure) × Code .pure) :=
    c.alts.findSome? fun alt =>
      match alt with
      | .alt n ps code _ => if n == ctor then some (ps, code) else none
      | _ => none
    |>.orElse fun _ => c.alts.findSome? fun alt =>
      match alt with
      | .default code => some (#[], code)
      | _ => none

  /-- A branch that binds `field` to the value of `val` around the alternative. -/
  partial def withValue (fix : Std.HashMap Name FVarId) (alt : Option (Array (Param .pure) × Code .pure))
      (val : LBTerm) : EraseM LBTerm := do
    match alt with
    | some (#[p], code) =>
      return .letIn (binder p.binderName) val (abstract p.fvarId (← codeTerm fix code))
    | some (_, code) => codeTerm fix code
    | none => return .box

  partial def casesTerm (fix : Std.HashMap Name FVarId) (c : Cases .pure) : EraseM LBTerm := do
    let ind ← getConstInfoInduct c.typeName
    let d : LBTerm := .fvar c.discr
    let machine := (← read).config.nat matches .machine
    let boolId := do return (← register_inductive (← getConstInfoInduct ``Bool)).1
    if machine && c.typeName == ``Nat then
      let zero ← withValue fix (altFor c ``Nat.zero) .box
      let sub1 := .app (.app (← knOf fix ``Nat.sub) d) (← primInt 1)
      let succ ← withValue fix (altFor c ``Nat.succ) sub1
      let cond := .app (.app (← knOf fix ``Nat.beq) d) (← primInt 0)
      return .case ((← boolId), 0) cond [([], succ), ([], zero)]
    if machine && c.typeName == ``Int then
      let ofNat ← withValue fix (altFor c ``Int.ofNat) d
      let succ := .app (.app (← knOf fix ``Nat.add) d) (← primInt 1)
      let negSucc ← withValue fix (altFor c ``Int.negSucc) (.app (← knOf fix ``Int.neg) succ)
      let cond := .app (.app (← knOf fix ``Nat.ble) (← primInt 0)) d
      return .case ((← boolId), 0) cond [([], negSucc), ([], ofNat)]
    /- As in `#erase`: a `case` on □ reduces only on a propositional inductive, and one declaration
    of `PUnit` serves every level. So the only constructor of a type that may be a Prop is reduced
    here, giving □ to each field. -/
    if mayBeProp ind && ind.numCtors == 1 then
      return ← match altFor c ind.ctors[0]! with
        | some (ps, code) => do
          let body ← codeTerm fix code
          return ps.foldr (fun p b => .letIn .anon .box (abstract p.fvarId b)) body
        | none => pure .box
    let (indid, masks) ← register_inductive ind
    let mut branches := #[]
    for ctor in ind.ctors, mask in masks do
      let kept := mask.count .keep
      let branch ← match altFor c ctor with
        | none => pure (List.replicate kept BinderName.anon, LBTerm.box)
        | some (ps, code) => do
          if ps.isEmpty then
            pure (List.replicate kept BinderName.anon, ← codeTerm fix code)
          else
            -- An erased field stays out of the binders, and its variable is □.
            let body ← codeTerm fix code
            let body := (ps.zip mask).foldr (init := body) fun (p, r) b =>
              if r == .erase then .letIn .anon .box (abstract p.fvarId b) else b
            let bound := filter mask ps
            let body := bound.toList.reverse.zipIdx.foldl (init := body) fun b (p, i) =>
              toBvar p.fvarId i b
            pure (bound.toList.map (binder ·.binderName), body)
      branches := branches.push branch
    return .case (indid, ind.numParams) d branches.toList
end

/-! ## Declarations -/

def declBody (fix : Std.HashMap Name FVarId) (d : Decl .pure) : EraseM LBTerm := do
  match d.value with
  | .code c => return lambdas d.params (← codeTerm fix c)
  | .extern _ => throwError "#erase_lcnf: {d.name} has no code"

def addComponent (phase : Phase) (g : Std.HashMap Name Node) (comp : List Name) : EraseM Unit := do
  let isRec := match comp with
    | [n] => (g[n]?.map (·.deps.contains n)).getD false
    | _ => true
  match comp with
  | [n] =>
    if (← get).constants.contains n then return
    match (g[n]?.bind (·.decl)) with
    | none =>
      -- A constructor marked `@[extern]` is added by `register_inductive`.
      -- A definition without compiled code, such as `Nat.add`, which the compiler implements
      -- natively, is erased from its kernel value as `#erase` does, under the same `extern` policy.
      -- Not at the mono phase: there the callers expect mono's types, e.g. a `Bool` where the
      -- kernel value of `Nat.decEq` builds a `Decidable`.
      if phase matches .base && ((← getEnv).find? n).any (·.hasValue (allowOpaque := true)) then
        discard <| Erasure.erase.get_constant_kername n
      else
        logInfo s!"No compiled code for {n}, emitting axiom."
        addAxiom n
    | some d =>
      if !isRec then
        let t ← declBody {} d
        let kn := toKername n
        modify fun s => { s with
          constants := s.constants.insert n kn,
          gdecls := s.gdecls.cons (kn, .constantDecl ⟨some t⟩) }
        return
      addFix [n]
  | _ => addFix comp
where
  addFix (names : List Name) : EraseM Unit := do
    let ids ← names.mapM fun _ => mkFreshFVarId
    let fix := Std.HashMap.ofList (names.zip ids)
    let defs : List (@FixDef LBTerm) ← names.mapM fun n => do
      let some d := g[n]?.bind (·.decl)
        | throwError "#erase_lcnf: {n} is recursive but has no code"
      if d.params.isEmpty then
        throwError "#erase_lcnf: {n} is recursive without parameters"
      let mut body ← declBody fix d
      for (x, i) in ids.reverse.zipIdx do
        body := toBvar x i body
      return { name := .named n.toString, body }
    for (n, i) in names.zipIdx do
      let kn := toKername n
      modify fun s => { s with
        constants := s.constants.insert n kn,
        gdecls := s.gdecls.cons (kn, .constantDecl ⟨some (.fix defs i)⟩) }

def eraseDecl (name : Name) (phase : Phase) (cfg : ErasureConfig) : CoreM Program := do
  let machine := cfg.nat matches .machine
  let g ← gatherGraph phase machine name
  let (t, s) ← Erasure.run (do
      for comp in components g name do
        addComponent phase g comp
      knOf {} name) cfg
  return .untyped s.gdecls (some t)

/-! ## The command -/

syntax (name := eraselcnfstx) "#erase_lcnf" (&" mono")? ppSpace term (ppSpace "config" term)?
  (ppSpace "to" ppSpace str)? (ppSpace "mli" ppSpace str)? : command

@[command_elab eraselcnfstx]
def eraseLcnfElab : Elab.Command.CommandElab
  | `(command| #erase_lcnf $[mono%$mono?]? $t:term $[config $cfg?:term]? $[to $path?:str]? $[mli $mli?:str]?) =>
    Elab.Command.liftTermElabM do
      let e ← Elab.Term.elabTerm t (expectedType? := .none)
      Elab.Term.synthesizeSyntheticMVarsNoPostponing
      let e ← Lean.instantiateMVars e
      let cfg : ErasureConfig ← match cfg? with
        | .none => pure {}
        | .some cfg => unsafe Elab.Term.evalTerm ErasureConfig (.const ``Erasure.ErasureConfig []) cfg
      -- LCNF exists for declarations: an arbitrary term becomes one.
      let e ← if e.isConst then pure e else Meta.mkAuxDefinitionFor (← mkFreshUserName `_erase_target) e
      let .const name _ := e.getAppFn
        | throwError "#erase_lcnf: the term has free variables"
      let phase : Phase := if mono?.isSome then .mono else .base
      let p ← eraseDecl name phase cfg
      let s := p |> Serialize.to_sexpr |>.toString
      -- The compiler has already inlined what it would inline, so the attribute file is empty.
      let c : AttributesConfig :=
        { inlinings := [], constRemappings := [], indRemappings := [], cstrReorders := [], customAttributes := [] }
      match path? with
      | .some path =>
        IO.FS.writeFile path.getString s
        IO.FS.writeFile (path.getString ++ ".inlinings") (c |> Serialize.to_sexpr |>.toString)
      | .none => logInfo s
      if let some mliPath := mli? then
        IO.FS.writeFile mliPath.getString (← gen_mli (← Meta.inferType e))
  | _ => Elab.throwUnsupportedSyntax

end Erasure.FromLCNF
