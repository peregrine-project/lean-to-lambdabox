import LeanToLambdaBox

/-!
The pure backend declares an inductive `propositional` iff its sort is `Prop`, as the `Meta` path
does: its `isPropFormerType` is the oracle's `Pure.isPropFormerType` (weak-head reduction with the
kernel's δ, then the sort `Sort 0`). The test checks:
- `Pure.isPropFormerType` and `Meta.isPropFormerType` on the types of `And`, `Eq`, `True`, `Acc`,
  `Idx` (a Prop inductive with an informative index field), `PP` (whose sort is `Prop` only after
  unfolding `MyProp`), and of `PUnit`, `Nat`, `Idx'` (not in `Prop`): the answers agree;
- `register_inductive` at the pure backend declares `And`, `Idx` and `PP` propositional, and `PUnit`
  and `Nat` not; it writes the declarations to `registered.ast`, which peregrine validates;
- `indexFields`, the index positions of constructor fields that `visitCases` substitutes on both
  paths: `Idx.mk`'s field `b` is the second index, `Acc.intro`'s `x` the first, `And.intro` has
  none.
-/

-- peregrine: validate registered.ast

open Lean Elab Command Erasure

namespace PIP
inductive B | f | t
inductive Idx : B → B → Prop | mk (b : B) : Idx .f b
inductive Idx' : B → Type | mk (b : B) : Idx' b
def MyProp : Type := Prop
inductive PP : B → MyProp | mk : PP .t
end PIP

/-- The declarations of the environment, as the pure backend reads them. -/
def allDecls : CoreM (List ConstantInfo) :=
  return (← getEnv).constants.fold (fun acc _ ci => ci :: acc) []

def names : List Name :=
  [``And, ``Eq, ``True, ``Acc, ``PIP.Idx, ``PIP.PP, ``PUnit, ``Nat, ``PIP.Idx']

/-- `(name, pure answer, Meta answer)` for the type of each inductive of `names`. -/
def answers : CoreM (List (Name × String × Bool)) := do
  let decls ← allDecls
  names.mapM fun n => do
    let ty := (← getConstInfo n).type
    let p := match Pure.isPropFormerType ⟨decls⟩ oracleFuel [] ty with
      | .ok b => toString b
      | .error _ => "error"
    return (n, p, ← runMetaM {} (Meta.isPropFormerType ty))

/--
info: [(`And, "true", true), (`Eq, "true", true), (`True, "true", true), (`Acc, "true", true), (`PIP.Idx, "true", true),
  (`PIP.PP, "true", true), (`PUnit, "false", false), (`Nat, "false", false), (`PIP.Idx', "false", false)]
-/
#guard_msgs in
#eval answers

/-- `(inductive, propositional)` of the bodies `register_inductive` declares at the pure backend;
the declarations are written to `registered.ast` as a program without a main term. -/
def registered (ns : List Name) : CoreM (List (String × Bool)) := do
  let decls ← allDecls
  let x : EraseT PureM Unit := ns.forM fun n => do
    let .inductInfo iv ← getConst (m := PureM) n | unreachable!
    discard <| register_inductive (m := PureM) iv
  match x.runPure {} { «config» := {} } ⟨decls, EnvView.ofEnvironment (← getEnv)⟩ {} with
  | .ok ((_, s), _) =>
    IO.FS.writeFile "registered.ast" (ASTType.untyped s.gdecls none |> Serialize.to_sexpr |>.toString)
    return s.gdecls.reverse.flatMap fun
      | (_, .inductiveDecl mb) => mb.bodies.map fun b => (b.name, b.propositional)
      | _ => []
  | .error _ => throwError "pure path error"

/--
info: [("And", true), ("PIP.Idx", true), ("PIP.PP", true), ("PUnit", false), ("Nat", false)]
-/
#guard_msgs in
#eval registered [``And, ``PIP.Idx, ``PIP.PP, ``PUnit, ``Nat]

/-- `indexFields` of a constructor. -/
def idxFieldsOf (c : Name) : CoreM (List (Option Nat)) := do
  let .ctorInfo cv ← getConstInfo c | throwError "not a constructor"
  return indexFields cv.numParams cv.type

/-- info: [[some 1], [some 0, none], [none, none]] -/
#guard_msgs in
#eval [``PIP.Idx.mk, ``Acc.intro, ``And.intro].mapM idxFieldsOf
