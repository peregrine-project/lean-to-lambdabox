import LeanToLambdaBox

/-!
`Erasure.erasePure view cfg decls e` runs the traversal of `#erase` (`Erasure.visitExpr`) with the
pure backend `PureM` over the declarations `decls` (register entry S-20). `#erase` calls it on the
programs in the fragment (S-21). The test checks:
- the operations of the instance `Backend PureM`: `declInfo?` is `findConst?`, `unsafeRecBase?` is
  always `none`, `prepare` returns its term, no constant is an instance, `log` does nothing,
  `instantiate1` is lean4lean's `Expr.instantiate1'` (by `rfl`); every constructor field is kept,
  and a missing constant and fuel exhaustion are errors of the pure path;
- at this backend the traversal's recursion test `name_occurs` is `nameOccurs` (by `rfl`), and the
  test of `visitMutual` is `isRecursiveDecl`;
- `isRecursiveDecl` and `axiomatized` on declarations of the elaboration environment;
- `#erase_pure t [config c] to "f"`, defined below, which elaborates `t` and `c` as `#erase` does
  and writes the output of `collectDeps` and `erasePure` in the format of `#erase`, next to
  `#erase` on the same programs, which are in the fragment, so that `#erase` writes the same
  output: a Church-style application (`nv1`), unsafe recursion (`ufOne`: a fixpoint), a
  `@[macro_inline]` function, whose call the pure path keeps (`useM`), an `@[extern]` definition
  under both `extern` settings (`useExt`, `useExtL`), a proof whose proposition is one only
  through an `@[irreducible]` alias, which the pure path erases (`pidHR`);
- errors: a constant missing from the declarations, an ill-typed application (the oracle's
  `failed`), and too little fuel.
-/

-- peregrine: validate nv1.pure.ast
-- peregrine: eval nv1.pure.ast --anf=false
-- peregrine: validate ufOne.pure.ast
-- peregrine: eval ufOne.pure.ast --anf=false
-- peregrine: validate useM.pure.ast
-- peregrine: validate useExtL.pure.ast
-- peregrine: validate pidHR.pure.ast

open Lean Elab Command Erasure

/-- An error of the pure path as text. -/
def showErr : EraseError → String
  | .outOfFragment w => s!"outOfFragment {w}"
  | .nameCollision a b => s!"nameCollision {a} {b}"
  | .fuel s => s!"fuel {s}"
  | .failed m => s!"failed {m}"

/-- A result of the pure path as text: its error, or `ok`. -/
def showRes {α} : Except EraseError α → String
  | .ok _ => "ok"
  | .error e => showErr e

/-- `#erase_pure t [config c] to "f"`: elaborate `t` and `c` as `#erase` does, compute
`collectDeps` over the elaboration environment and run `erasePure` on its declarations; write the
program to `f` and its attributes to `f.inlinings` as `#erase` does, or log the error. -/
syntax (name := erasePureCmd) "#erase_pure " term (" config " term)? " to " str : command

@[command_elab erasePureCmd]
def erasePureElab : CommandElab
  | `(command| #erase_pure $t:term $[config $cfg?:term]? to $path:str) => liftTermElabM do
    let e ← Term.elabTerm t (expectedType? := none)
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let cfg : ErasureConfig ← match cfg? with
      | none => pure {}
      | some c => unsafe Term.evalTerm ErasureConfig (.const ``ErasureConfig []) c
    let view := EnvView.ofEnvironment (← getEnv)
    match collectDeps view e >>= fun decls => erasePure view cfg decls e with
    | .ok (p, inls) =>
      IO.FS.writeFile path.getString (p |> Serialize.to_sexpr |>.toString)
      let c : AttributesConfig :=
        { inlinings := inls, constRemappings := [], indRemappings := [], cstrReorders := [],
          customAttributes := [] }
      IO.FS.writeFile (path.getString ++ ".inlinings") (c |> Serialize.to_sexpr |>.toString)
    | .error err => logInfo s!"pure path: {showErr err}"
  | _ => throwUnsupportedSyntax

/-! ## The operations of the pure backend -/

theorem declInfo?_eq (n : Name) : Backend.declInfo? (m := PureM) n = PureM.findConst? n := rfl
theorem findConst?_eq (n : Name) : Backend.findConst? (m := PureM) n = PureM.findConst? n := rfl
theorem unsafeRecBase?_eq (n : Name) : Backend.unsafeRecBase? (m := PureM) n = none := rfl
theorem remove_unsafe_rec_eq (n : Name) : remove_unsafe_rec (m := PureM) n = n := rfl
theorem prepare_eq (cfg : ErasureConfig) (e : Expr) : Backend.prepare (m := PureM) cfg e = pure e :=
  rfl
theorem isInstance_eq (n : Name) : Backend.isInstance (m := PureM) n = pure false := rfl
theorem log_eq (s : String) : Backend.log (m := PureM) s = pure () := rfl
theorem instantiate1_eq (b a : Expr) : Backend.instantiate1 (m := PureM) b a = b.instantiate1' a :=
  rfl
theorem isErasable_eq (lctx : LocalContext) (ls : List Local) (e : Expr) :
    Backend.isErasable (m := PureM) lctx ls e = PureM.isErasable ls e := rfl

/-! ## The recursion test -/

set_option smartUnfolding false in
/-- At the pure backend, the traversal's `name_occurs` compares names exactly: it is `nameOccurs`,
by unfolding both definitions. -/
theorem name_occurs_eq : ∀ n e, name_occurs (m := PureM) n e = nameOccurs n e := fun _ _ => rfl

/-- The same, as functions. -/
theorem name_occurs_fun : @name_occurs PureM _ = nameOccurs := by
  delta name_occurs nameOccurs; rfl

/-- `visitMutual` erases `ci` as a fixpoint exactly when `isRecursiveDecl ci` (its test
`nonrecursive := single_decl && !name_occurs name value`, at the pure backend, where
`declInfo? name` finds `ci`). -/
theorem visitMutual_test (ci : ConstantInfo) :
    (!(ci.all.length == 1 && !name_occurs (m := PureM) ci.name (ci.value! (allowOpaque := true)))) =
      isRecursiveDecl ci := by
  rw [name_occurs_eq, isRecursiveDecl, bne]
  cases ci.all.length == 1 <;> cases nameOccurs ci.name (ci.value! (allowOpaque := true)) <;> rfl

/-! ## Programs -/

namespace PB
axiom A : Type
def CN := (A → A) → A → A
def one : CN := fun s z => s z

universe u
def CNu : Type (u+1) := (α : Type u) → (α → α) → α → α
def oneU : CNu.{u} := fun _ s z => s z
/-- A recursive constant: `uf n = n`. -/
unsafe def uf (n : CNu.{0}) : CNu.{0} := (fun _ => n) (fun (x : CNu.{0}) => uf x)

/-- `mfirst a b = a`, inlined by the `Meta` path before erasure. -/
@[macro_inline] def mfirst (a _b : CN) : CN := a
def useM : CN := mfirst one one

/-- An `@[extern]` definition. -/
@[extern "pb_ext"] def ext (x : A) : A := x
def useExt : A → A := fun x => ext x

def IProp : Type := Prop
axiom R : IProp
axiom hR : R
def pid {α : Sort u} (a : α) : α := a
/--
warning: Definition `pidHR` is a proposition; use `theorem` instead of `def`

Note: This linter can be disabled with `set_option linter.defProp false`
-/
#guard_msgs in
def pidHR : R := pid hR
attribute [irreducible] IProp
end PB

/-- info: ["PB.one: false", "PB.oneU: false", "PB.uf: true", "PB.ext: false"] -/
#guard_msgs in
#eval show CoreM _ from do
  let env ← getEnv
  return [``PB.one, ``PB.oneU, ``PB.uf, ``PB.ext].map fun n =>
    s!"{n}: {isRecursiveDecl (env.find? n).get!}"

/-- info: ["PB.one: false false", "PB.ext: true false", "PB.useExt: false false"] -/
#guard_msgs in
#eval show CoreM _ from do
  let env ← getEnv
  let v := EnvView.ofEnvironment env
  return [``PB.one, ``PB.ext, ``PB.useExt].map fun n =>
    let ci := (env.find? n).get!
    s!"{n}: {axiomatized v {} ci} {axiomatized v { extern := .preferLogical } ci}"

#erase_pure PB.one (fun a : PB.A => a) to "nv1.pure.ast"
/--
warning: failed to translate PB.A into ML type, emitting unit instead.
---
warning: failed to translate PB.A into ML type, emitting unit instead.
---
info: val main: unit -> unit
-/
#guard_msgs in
#erase PB.one (fun a : PB.A => a) to "nv1.ast"

#erase_pure PB.uf PB.oneU.{0} to "ufOne.pure.ast"
#guard_msgs (drop warning, drop info) in
#erase PB.uf PB.oneU.{0} to "ufOne.ast"

#erase_pure PB.useM to "useM.pure.ast"
#guard_msgs (drop warning, drop info) in
#erase PB.useM to "useM.ast"

#erase_pure PB.useExt to "useExt.pure.ast"
#erase_pure PB.useExt config { extern := .preferLogical } to "useExtL.pure.ast"

#erase_pure PB.pidHR to "pidHR.pure.ast"
/--
warning: failed to translate PB.R into ML type, emitting unit instead.
---
info: val main: unit
-/
#guard_msgs in
#erase PB.pidHR to "pidHR.ast"

/-! ## Errors -/

/-- A constructor field's relevance as text. -/
def showRel : ConstructorArgRelevance → String
  | .keep => "keep"
  | .erase => "erase"

/-- A view with nothing in it. -/
def emptyView : EnvView := ⟨fun _ => none, fun _ => false, fun _ => none⟩

def AE : Expr := .const `A []
def decls : List ConstantInfo :=
  [.axiomInfo { name := `a, levelParams := [], type := AE, isUnsafe := false },
   .axiomInfo { name := `A, levelParams := [], type := .sort (.succ .zero), isUnsafe := false }]

/-- info: ["outOfFragment unknown constant", "failed not a function", "ok", "fuel visitApp"] -/
#guard_msgs in
#eval [showRes (erasePure emptyView {} [] (.const `a [])),
  showRes (erasePure emptyView {} decls (.app (.const `a []) (.const `a []))),
  showRes (erasePure emptyView {} decls (.const `a [])),
  showRes ((visitExpr (m := PureM) 1 (.const `a [])).runPure {} { «config» := {} } ⟨decls, emptyView⟩ {})]

/-- Run an action of `PureM` over `decls`. -/
def runP {α} (x : PureM α) : Except EraseError (α × PureState) := (x.run ⟨decls, emptyView⟩).run {}

/-- A constructor with two fields. -/
def ctor2 : ConstructorVal :=
  { name := `c, levelParams := [], type := AE, induct := `I, cidx := 0, numParams := 0,
    numFields := 2, isUnsafe := false }

/-- info: ["outOfFragment unknown constant x", "fuel site", "ok [keep, keep]"] -/
#guard_msgs in
#eval [showRes (runP (Backend.unknownConstant (m := PureM) (α := Unit) `x)),
  showRes (runP (Backend.outOfFuel (m := PureM) (α := Unit) "site")),
  match runP (Backend.argMask (m := PureM) {} ctor2) with
  | .ok (mask, _) => s!"ok {mask.toList.map showRel}"
  | .error e => showErr e]
