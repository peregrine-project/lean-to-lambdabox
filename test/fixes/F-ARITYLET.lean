/-
Regression test for F-ARITYLET.

`Erasure.arityResultSort` is MetaRocq's `destArity`
(`../metarocq/pcuic/theories/PCUICAst.v:486-490`), which walks `tProd` **and `tLetIn`**;
`Erasure.isPropositionalArity` is `Sort.is_propositional` of the sort it ends at, and since
F-PROP that is what `register_inductive` emits as `OneInductiveBody.propositional`. The walk
used to stop at `.letE` and `.mdata`, where the kernel's own walks go through, so a `Prop`
whose declared arity carries a `let` was emitted non-propositional — and an elimination of it
shipped **stuck**, exactly the failure F-PROP repaired for every other `Prop`:
`peregrine eval` answered `Case: <15> branch not found`, measured on this file's own
`letTest` against the pre-fix build.

Three shapes are checked through the emitted flag, and two of them end to end:

* `FooLet : (let _x := Nat; Prop)` — the shape the finding measured. Elaborates, and
  `InductiveVal.type` keeps the `letE`.
* `FooParam (a : Nat) : (let _x := Nat; Prop)` — a parameter before the `let`, so the walk has
  to cross a `.forallE` *and* a `.letE`. A parameter is not a field, so the single constructor
  still binds nothing and F-ACC's guard admits the elimination.
* `FooMData` — an inductive whose declared type is `.mdata … (.sort .zero)`, added through
  `Lean.addDecl`, which accepts it. It has no `casesOn`, so only its emitted flag is read.

The fourth shape is the residual, pinned here so that the decision is not silently reversed:
at `def MyArity := Prop`, `inductive FooAlias : MyArity`, whose `InductiveVal.type` is
`.const MyArity []`, the walk still answers `none`. Seeing through that would take `whnf`, and
a reducing walk would emit a flag the model does not support — lean4lean's `TrExprS` is not
transparent at `.const`, so `vResultSort` of the translated type is `none` there and
`ErasureSpec.propositionalInd_of_arity`, the direction of MetaRocq's equation that is proved
and spent, would become false. `.letE` and `.mdata` are exactly the arms where `TrExprS` *is*
transparent (`../lean4lean/Lean4Lean/Verify/Typing/Expr.lean:164-170`).
-/
import LeanToLambdaBox.Erasure

open Lean Erasure

namespace FArityLet

/-- The finding's own shape: a `Prop` whose declared arity carries a `let`. -/
inductive FooLet : (let _x := Nat; Prop) where | mk : FooLet

/-- A parameter before the `let`, so the walk crosses a `.forallE` and a `.letE`. -/
inductive FooParam (a : Nat) : (let _x := Nat; Prop) where | mk : FooParam a

/-- The residual: an arity behind a definitional alias, which only a *reducing* walk would
see through. Deliberately still unflagged — see the file header. -/
def MyArity := Prop
inductive FooAlias : MyArity where | mk : FooAlias

/-- An elimination of the `let`-arity `Prop` into data. `FooLet.mk` binds no field, so the
downstream collapse (`remove_match_on_box`, `EOptimizePropDiscr.v:48`) boxes nothing and the
program must evaluate to 5. -/
def letData (h : FooLet) : Nat := FooLet.casesOn (motive := fun _ => Nat) h 5

def letTest : Nat := letData FooLet.mk

def paramData (h : FooParam 7) : Nat := FooParam.casesOn (motive := fun _ => Nat) h 4

def paramTest : Nat := paramData FooParam.mk

def cfg : ErasureConfig := { extern := .preferLogical, nat := .peano, csimp := false }

/-- The `propositional` flag `register_inductive` emits for `n`, read out of the registry a run
that registers it alone produces. Reads the emitted flag, not `isPropositionalArity` directly,
so the test covers the field `Basic.lean` no longer defaults. -/
def emittedFlag (n : Name) : CoreM String := do
  let .inductInfo iv ← getConstInfo n | return "NOT AN INDUCTIVE"
  let (_, s) ← run (register_inductive iv) cfg
  let flag? := s.gdecls.findSome? fun e =>
    match e.2 with
    | .inductiveDecl mib => (mib.bodies.find? (·.name == toString n)).map (·.propositional)
    | _ => none
  return match flag? with | some b => toString b | none => "NOT REGISTERED"

/-- Erase `name` and report the `propositional` flag of every inductive body it emits, writing
the program into `FIXES_AST_DIR` so that `scripts/fixes.sh` runs it through `peregrine`. -/
def check (label : String) (name : Name) : CoreM Unit := do
  let (p, _) ← erase (.const name []) cfg
  let .untyped gdecls _ := p
  let flags := gdecls.flatMap fun e =>
    match e.2 with
    | .constantDecl _ => []
    | .inductiveDecl body => body.bodies.map fun b => (b.name, b.propositional)
  IO.println s!"F-ARITYLET {label}: {flags.mergeSort (fun a b => a.1 <= b.1)}"
  if let some dir ← IO.getEnv "FIXES_AST_DIR" then
    IO.FS.writeFile s!"{dir}/{label}.ast" (Serialize.to_sexpr p).toString

#eval show CoreM Unit from do
  IO.println s!"F-ARITYLET let arity FooLet: {← emittedFlag ``FooLet}"
  IO.println s!"F-ARITYLET param+let arity FooParam: {← emittedFlag ``FooParam}"
  IO.println s!"F-ARITYLET alias arity FooAlias (unflagged by design): {← emittedFlag ``FooAlias}"
  check "let-prop" ``letTest
  check "param-prop" ``paramTest

-- An `.mdata`-headed arity, which the kernel accepts and every kernel walk sees through. It
-- has no `casesOn`, so only the emitted flag is read.
#eval show CoreM Unit from do
  let n := `FArityLet.FooMData
  Lean.addDecl <| .inductDecl [] 0
    [{ name := n, type := .mdata (KVMap.empty.insert `test (.ofBool true)) (.sort .zero),
       ctors := [{ name := n ++ `mk, type := .const n [] }] }] false
  IO.println s!"F-ARITYLET mdata arity FooMData: {← emittedFlag n}"

end FArityLet
