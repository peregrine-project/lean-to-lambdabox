import Lean
/-!
Blueprint checker: the Lean side of `blueprint/scripts/audit.py`.

Run with `lake env` of the package whose environment resolves every import (`env_dir` of
`blueprint/audit.toml`, the proof package `proof/`), after `lake build` of the targets listed there:

    cd proof && lake env lean --run ../blueprint/CheckDecls.lean check   <names-file>            <module>...
    cd proof && lake env lean --run ../blueprint/CheckDecls.lean measure <names-file> <out.json> <module>...

`<module>...` are the modules to import (the environment the blueprint is checked against).

* `check` prints every name of `<names-file>` (one per line, such as the `lean_decls` file that
  `leanblueprint web` writes) that the environment does not contain, and exits with status 1 if
  there is one. It replaces `lake exe checkdecls`, which would need a `checkdecls` dependency in
  the root `lakefile.toml`.
* `measure` writes a JSON object with three fields:
  - `names`: for each name of `<names-file>`: whether it exists, its module, line and kind, the axioms
    it depends on (the closure over the constants its type, value and constructors use, as
    `#print axioms` follows them), whether they equal what `Lean.collectAxioms` (`#print axioms`)
    computes (for an inductive, together with its constructors: `leanAxioms`), and its sorry
    sources: the declarations of that closure whose own type or value
    uses `sorryAx`; axioms and sorry sources come with their module and line;
  - `census`: every declaration of the inherited modules (prefix `$BP_INHERITED_PREFIX`, default
    `Lean4Lean`) and of the shipping modules (prefix `$BP_SHIPPING_PREFIX`, default
    `LeanToLambdaBox`) that is an `axiom` or whose own type or value uses `sorryAx`;
  - `shipping`: every user-facing declaration of the shipping modules, with its kind (`partial def`
    for a `partial` definition, which is an opaque constant for the kernel) and the head constant
    of its result type (to spot the monadic code: `MetaM`, `CoreM`, `EraseM`, ...);
  - `covered`: every user-facing declaration of the verification modules (prefix
    `$BP_COVER_PREFIX`, default `EraseProof`) that has a source position (auxiliary declarations
    that Lean generates, such as `below`, `brecOn`, `ctorIdx`, have none), with its module, line
    and kind: the declarations that the blueprint's nodes must cite.
-/
open Lean

/-- The constants that `ci` uses directly, as `#print axioms` (`Lean.CollectAxioms`) follows them:
its type, its value (definitions, theorems, opaques) and its constructors (inductives). -/
def directDeps (ci : ConstantInfo) : Array Name :=
  let t := ci.type.getUsedConstants
  match ci with
  | .defnInfo v => t ++ v.value.getUsedConstants
  | .thmInfo v => t ++ v.value.getUsedConstants
  | .opaqueInfo v => t ++ v.value.getUsedConstants
  | .inductInfo v => t ++ v.ctors.toArray
  | _ => t

/-- Whether the type or value of `ci` itself uses `sorryAx`. -/
def usesSorryDirectly (ci : ConstantInfo) : Bool :=
  (directDeps ci).contains ``sorryAx

def moduleOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some idx => toString (env.header.moduleNames[idx.toNat]!)
  | none => ""

def lineOf (env : Environment) (n : Name) : Option Nat :=
  (declRangeExt.find? env n (level := .server)).map (·.range.pos.line)

/-- `partial def f` is compiled to an opaque constant `f`, whose compiled code is the unsafe
`f._unsafe_rec`; the kernel cannot unfold `f`. -/
def isPartial (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.opaqueInfo _) => env.contains (Compiler.mkUnsafeRecName n)
  | _ => false

def kindOf (env : Environment) (n : Name) : String :=
  match env.find? n with
  | none => "missing"
  | some ci =>
    let base := match ci with
      | .axiomInfo _ => "axiom"
      | .defnInfo _ => "def"
      | .thmInfo _ => "theorem"
      | .opaqueInfo _ =>
        if isPartial env n then "partial def"
        else if (Compiler.getImplementedBy? env n).isSome then "opaque, implemented_by"
        else "opaque"
      | .quotInfo _ => "quot"
      | .inductInfo _ => if isStructure env n then "structure" else "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
    if ci.isUnsafe then "unsafe " ++ base else base

/-- The head constant of the type after its leading Π-binders, e.g. `Lean.Meta.MetaM`. -/
def resultHead (ty : Expr) : String :=
  match ty.getForallBody.getAppFn with
  | .const c _ => toString c
  | .sort _ => "Sort"
  | _ => ""

/-- Axioms and sorry sources in the closure of `root` (breadth-first, memoising direct deps). -/
def closure (env : Environment) (cache : IO.Ref (Std.HashMap Name (Array Name))) (root : Name) :
    IO (Array Name × Array Name) := do
  let mut seen : Std.HashSet Name := {}
  let mut todo : Array Name := #[root]
  let mut axioms : Array Name := #[]
  let mut sorries : Array Name := #[]
  while h : todo.size > 0 do
    let c := todo.back
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    let some ci := env.find? c | continue
    if let .axiomInfo _ := ci then axioms := axioms.push c
    let deps ← match (← cache.get)[c]? with
      | some d => pure d
      | none => do
        let d := directDeps ci
        cache.modify (·.insert c d)
        pure d
    if deps.contains ``sorryAx then sorries := sorries.push c
    for d in deps do
      unless seen.contains d do todo := todo.push d
  return (axioms.qsort (·.toString < ·.toString), sorries.qsort (·.toString < ·.toString))

instance : MonadEnv (StateM Environment) where
  getEnv := get
  modifyEnv := modify

/-- The axioms of `n` as `#print axioms` computes them (`Lean.collectAxioms`), to cross-check
`closure`; for an inductive, the union with `#print axioms` of its constructors. For an imported
declaration `#print axioms` reads the axioms its module stored when it was compiled; the module
computes them with one cache for all its declarations, and a declaration visited inside the
cycle between an inductive and its constructors is cached before the cycle closes. So the stored
axioms of an inductive can miss those that only its constructors reach
(`EraseProof.AtomSpine`: none, while `EraseProof.AtomSpine.const` gives `propext`). -/
def leanAxioms (env : Environment) (n : Name) : Array Name :=
  let get (c : Name) : Array Name := (collectAxioms c : StateM Environment (Array Name)).run' env
  let own := get n
  let all := match env.find? n with
    | some (.inductInfo v) =>
      v.ctors.foldl (fun (acc : Array Name) c => acc ++ (get c).filter (fun a => !acc.contains a)) own
    | _ => own
  all.qsort (·.toString < ·.toString)

def jsonNames (env : Environment) (ns : Array Name) : Json :=
  Json.arr <| ns.map fun n => Json.mkObj [("name", toString n), ("module", moduleOf env n),
    ("line", match lineOf env n with | some l => toJson l | none => Json.null)]

/-- Whether `s` is `pre` followed by one or more digits: the names Lean numbers (`eq_1`,
`match_2`, `proof_3`). -/
def isNumbered (pre s : String) : Bool :=
  s.startsWith pre && s.length > pre.length && (s.drop pre.length).all Char.isDigit

/-- A declaration a user wrote (not a constructor, recursor, projection, matcher or other
auxiliary declaration that Lean generates, such as the equation lemmas `f.eq_1`, `f.eq_def`,
`f.eq_unfold`). A user name that only starts with `eq_`, such as `eq_of_beq`, is user-facing. -/
def isUserFacing (env : Environment) (n : Name) (ci : ConstantInfo) : Bool :=
  let s := n.getString!
  !n.isInternalDetail && !isPrivateName n && !isAuxRecursor env n && !isNoConfusion env n &&
  !env.isProjectionFn n && !Meta.isMatcherCore env n &&
  !(match ci with | .ctorInfo _ | .recInfo _ => true | _ => false) &&
  !(s.endsWith "_unsafe_rec") &&
  !(["sizeOf_spec", "injEq", "inj", "eq_def", "eq_unfold"].contains s) &&
  !isNumbered "eq_" s && !isNumbered "match_" s && !isNumbered "proof_" s

unsafe def importEnv (mods : List String) : IO Environment := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  importModules (mods.toArray.map fun m => { module := m.toName }) {} (loadExts := true)

def readNames (file : String) : IO (Array String) := do
  return (← IO.FS.lines file).filterMap fun l =>
    let s := l.trimAscii.toString
    if s.isEmpty || s.startsWith "#" then none else some s

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | "check" :: file :: mods@(_ :: _) =>
    let env ← importEnv mods
    let names ← readNames file
    let missing := names.filter fun s => !env.contains s.toName
    for s in missing do IO.println s!"{s} is missing."
    IO.println s!"checked {names.size} declarations, {missing.size} missing"
    return if missing.isEmpty then 0 else 1
  | "measure" :: file :: out :: mods@(_ :: _) =>
    let env ← importEnv mods
    let names ← readNames file
    let cache ← IO.mkRef ({} : Std.HashMap Name (Array Name))
    let mut entries : Array (String × Json) := #[]
    for s in names do
      let n := s.toName
      if env.contains n then
        let (axs, srcs) ← closure env cache n
        let lax := leanAxioms env n
        entries := entries.push (s, Json.mkObj [("exists", true), ("module", moduleOf env n),
          ("axioms_agree", toJson (lax.map toString == axs.map toString)),
          ("lean_axioms", toJson (lax.map toString)),
          ("line", match lineOf env n with | some l => toJson l | none => Json.null),
          ("kind", kindOf env n), ("axioms", jsonNames env axs),
          ("sorry_sources", jsonNames env srcs)])
      else
        entries := entries.push (s, Json.mkObj [("exists", false)])
    let mut census : Array Json := #[]
    let mut shipping : Array Json := #[]
    let mut covered : Array Json := #[]
    let inh := (← IO.getEnv "BP_INHERITED_PREFIX").getD "Lean4Lean"
    let ship := (← IO.getEnv "BP_SHIPPING_PREFIX").getD "LeanToLambdaBox"
    let cover := (← IO.getEnv "BP_COVER_PREFIX").getD "EraseProof"
    let pkgOf (m : String) : String :=
      if m.startsWith inh then "inherited" else if m.startsWith ship then "shipping"
      else if m.startsWith cover then "covered" else ""
    let consts := (env.constants.fold (init := #[]) fun acc n ci =>
      let m := moduleOf env n
      if (pkgOf m).isEmpty then acc else acc.push (n, ci, m)).qsort
      (·.1.toString < ·.1.toString)
    for (n, ci, m) in consts do
      let pkg := pkgOf m
      let isAx := match ci with | .axiomInfo _ => true | _ => false
      if isAx || usesSorryDirectly ci then
        census := census.push <| Json.mkObj [("package", pkg), ("name", toString n),
          ("module", m), ("kind", kindOf env n), ("axiom", isAx), ("sorry", usesSorryDirectly ci),
          ("line", match lineOf env n with | some l => toJson l | none => Json.null)]
      if pkg == "shipping" && isUserFacing env n ci then
        shipping := shipping.push <| Json.mkObj [("name", toString n), ("module", m),
          ("kind", kindOf env n), ("result", resultHead ci.type),
          ("line", match lineOf env n with | some l => toJson l | none => Json.null)]
      if pkg == "covered" && isUserFacing env n ci && (lineOf env n).isSome then
        covered := covered.push <| Json.mkObj [("name", toString n), ("module", m),
          ("kind", kindOf env n),
          ("line", match lineOf env n with | some l => toJson l | none => Json.null)]
    let j := Json.mkObj [("modules", toJson mods), ("names", Json.mkObj (entries.toList)),
      ("census", Json.arr census), ("shipping", Json.arr shipping), ("covered", Json.arr covered)]
    IO.FS.writeFile out (j.pretty ++ "\n")
    IO.println s!"measured {names.size} names; census {census.size}; shipping {shipping.size}; covered {covered.size}"
    return 0
  | _ =>
    IO.eprintln "usage: lake env lean --run blueprint/CheckDecls.lean (check <names> | measure <names> <out.json>) <module>..."
    return 2
