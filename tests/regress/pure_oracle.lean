import LeanToLambdaBox

/-!
`Erasure.Pure.isErasable cx fuel ls e` decides, over the list of declarations `cx.decls` and the
traversal's locals `ls`, whether `e` is erasable: it infers the type of `e`, and answers "erasable"
when that type is an arity or its sort is always zero. Every reduction it makes unfolds every
definition, `@[irreducible]` ones included (the kernel's δ); when its fuel runs out it fails with
`fuel` (register entry S-19). `Erasure.PureM` is the monad of the backend that runs the traversal
with this oracle, on the programs that `#erase` sends to the pure path (S-21). The test checks:
- by kernel evaluation (`decide`) at `Erasure.oracleFuel`, on environments built by hand:
  - `hq A a`, an ill-typed spine of the proof `hq : Q` whose proposition
    `Q := ∀ P : Prop, P → P` is a definition, is kept;
  - the proof `hq.{v} : P.{v}` of `P.{v} : Sort v` is kept at the level parameter `v` and erased at
    level `0`;
  - through the aliases `IProp := Prop` and `Endo := A → A`, the oracle types and keeps
    `fun (_ : R) (x : A) => x` and `fI a`, and erases `R : IProp` and `hR : R`;
- with too little fuel it fails with `fuel` instead of answering, and with enough fuel it answers;
- the operations of `PureM` (`findConst?`, `freshFVarId`, `instantiate1`, `isErasable`,
  `casesInfo?`, `ctorArity?`) and `EraseT.runPure`, on small inputs;
- over the declarations that `collectDeps` collects from the elaboration environment, where
  `IProp` is `@[irreducible]`, the oracle erases `R`, `hR` and `pidHR := pid hR` and keeps
  `pid.{1}`; `#erase`, which takes the pure path on `pidHR`, erases it to `□` (`pidHR.ast`).
-/

-- peregrine: validate pidHR.ast

open Lean Erasure

/-- The error class of a result of the oracle, for kernel evaluation. -/
def errKind : Except EraseError Bool → Option Nat
  | .ok _ => none
  | .error (.outOfFragment _) => some 0
  | .error (.nameCollision _ _) => some 1
  | .error (.fuel _) => some 2
  | .error (.failed _) => some 3

/-- A readable form of a result of the oracle. -/
def show' : Except EraseError Bool → String
  | .ok b => s!"ok {b}"
  | .error (.outOfFragment w) => s!"outOfFragment {w}"
  | .error (.nameCollision a b) => s!"nameCollision {a} {b}"
  | .error (.fuel s) => s!"fuel {s}"
  | .error (.failed m) => s!"failed {m}"

/-! ## A proof whose proposition is a definition

Environment, newest first: `hq : Q`, `Q : Prop := ∀ P : Prop, P → P`, `a : A`, `A : Type`. -/

namespace DefHead
def ty0E : Expr := .sort .zero
def ty1E : Expr := .sort (.succ .zero)
def AE : Expr := .const `A []
def A_val : AxiomVal := { name := `A, levelParams := [], type := ty1E, isUnsafe := false }
def a_val : AxiomVal := { name := `a, levelParams := [], type := AE, isUnsafe := false }
def Q_val : DefinitionVal :=
  { name := `Q, levelParams := [], type := ty0E,
    value := .forallE `P ty0E (.forallE `h (.bvar 0) (.bvar 1) .default) .default,
    hints := .abbrev, safety := .safe, all := [`Q] }
def hq_val : AxiomVal := { name := `hq, levelParams := [], type := .const `Q [], isUnsafe := false }
def decls : List ConstantInfo :=
  [.axiomInfo hq_val, .defnInfo Q_val, .axiomInfo a_val, .axiomInfo A_val]
def cx : Pure.Ctx := ⟨decls⟩
/-- `hq A a`: `Q` unfolds to a Π, so `hq` can be applied, here to arguments of the wrong types. -/
def e0 : Expr := .app (.app (.const `hq []) AE) (.const `a [])

theorem kept : (Pure.isErasable cx oracleFuel [] e0).toOption = some false := by
  decide
end DefHead

/-! ## A proof whose propositionality depends on its level parameter

Environment, newest first: `hq.{v} : P.{v}`, `P.{v} : Sort v`. -/

namespace LevelDep
def P_val : AxiomVal :=
  { name := `P, levelParams := [`v], type := .sort (.param `v), isUnsafe := false }
def hq_val : AxiomVal :=
  { name := `hq, levelParams := [`v], type := .const `P [.param `v], isUnsafe := false }
def decls : List ConstantInfo := [.axiomInfo hq_val, .axiomInfo P_val]
def cx : Pure.Ctx := ⟨decls⟩

theorem kept_at_param_erased_at_zero :
    (Pure.isErasable cx oracleFuel [] (.const `hq [.param `v])).toOption = some false ∧
    (Pure.isErasable cx oracleFuel [] (.const `hq [.zero])).toOption = some true := by
  decide
end LevelDep

/-! ## Aliases of a sort and of a Π

Environment, newest first: `a : A`, `fI : Endo`, `Endo : Type := A → A`, `hR : R`, `R : IProp`,
`IProp : Type := Prop`, `A : Type`. -/

namespace IrrAlias
def ty1E : Expr := .sort (.succ .zero)
def AE : Expr := .const `A []
def A_val : AxiomVal := { name := `A, levelParams := [], type := ty1E, isUnsafe := false }
def IProp_val : DefinitionVal :=
  { name := `IProp, levelParams := [], type := ty1E, value := .sort .zero, hints := .abbrev,
    safety := .safe, all := [`IProp] }
def R_val : AxiomVal :=
  { name := `R, levelParams := [], type := .const `IProp [], isUnsafe := false }
def hR_val : AxiomVal := { name := `hR, levelParams := [], type := .const `R [], isUnsafe := false }
def Endo_val : DefinitionVal :=
  { name := `Endo, levelParams := [], type := ty1E, value := .forallE `x AE AE .default,
    hints := .abbrev, safety := .safe, all := [`Endo] }
def fI_val : AxiomVal :=
  { name := `fI, levelParams := [], type := .const `Endo [], isUnsafe := false }
def a_val : AxiomVal := { name := `a, levelParams := [], type := AE, isUnsafe := false }
def decls : List ConstantInfo :=
  [.axiomInfo a_val, .axiomInfo fI_val, .defnInfo Endo_val, .axiomInfo hR_val, .axiomInfo R_val,
   .defnInfo IProp_val, .axiomInfo A_val]
def cx : Pure.Ctx := ⟨decls⟩
/-- `fun (_ : R) (x : A) => x`. -/
def guardE : Expr := .lam `h (.const `R []) (.lam `x AE (.bvar 0) .default) .default
/-- `fI a`. -/
def appE : Expr := .app (.const `fI []) (.const `a [])
def RE : Expr := .const `R []
def hRE : Expr := .const `hR []

theorem kernel_delta :
    (Pure.isErasable cx oracleFuel [] guardE).toOption = some false ∧
    (Pure.isErasable cx oracleFuel [] appE).toOption = some false ∧
    (Pure.isErasable cx oracleFuel [] RE).toOption = some true ∧
    (Pure.isErasable cx oracleFuel [] hRE).toOption = some true := by
  decide

/-! ## Fuel -/

/-- One unit of fuel types no application: the oracle fails with `fuel`, and enough fuel gives the
answer. -/
theorem fuel_error :
    errKind (Pure.isErasable cx 1 [] appE) = some 2 ∧
    errKind (Pure.isErasable cx 0 [] hRE) = some 2 ∧
    errKind (Pure.isErasable cx 8 [] appE) = none := by
  decide

/-- info: ["fuel inferType", "fuel inferType", "ok false"] -/
#guard_msgs in
#eval [show' (Pure.isErasable cx 1 [] appE), show' (Pure.isErasable cx 0 [] hRE),
  show' (Pure.isErasable cx 8 [] appE)]
end IrrAlias

/-! ## The operations of `PureM` -/

namespace Ops
/-- Run a `PureM` action over the declarations `decls` from the counter `n`. -/
def runP {α} (decls : List ConstantInfo) (n : Nat) (x : PureM α) :
    Except EraseError (α × PureState) :=
  (x.run ⟨decls, ⟨findConst decls, fun _ => false, fun _ => none⟩⟩).run { next := n }

theorem findConst?_hq :
    (runP DefHead.decls 0 (PureM.findConst? `hq)).toOption.map (·.1.map (·.name)) =
      some (some `hq) ∧
    (runP DefHead.decls 0 (PureM.findConst? `B)).toOption.map (·.1.isSome) = some false := by
  decide

theorem noCases : (runP [] 0 (PureM.casesInfo? `x)).toOption.map (·.1.isSome) = some false ∧
    (runP [] 0 (PureM.ctorArity? `x)).toOption.map (·.1) = some none := by
  decide

theorem instantiate1_bvar : PureM.instantiate1 (.bvar 0) (.const `a []) = .const `a [] := rfl

/-- `PureM.isErasable` gives the oracle's answer at `oracleFuel`, and fails with its error. -/
theorem isErasable_run :
    (runP DefHead.decls 0 (PureM.isErasable [] DefHead.e0)).toOption.map (·.1) = some false ∧
    (runP LevelDep.decls 0 (PureM.isErasable [] (.const `hq [.zero]))).toOption.map (·.1) =
      some true ∧
    (match runP DefHead.decls 0 (PureM.isErasable [] (.fvar ⟨`x⟩)) with
      | .error (.outOfFragment _) => true
      | _ => false) = true := by
  decide

/-- A local whose type is `A → A` in scope, and a `let`-bound local whose value is `A`. -/
def locals : List Local :=
  [⟨⟨`y⟩, `y, .sort (.succ .zero), some DefHead.AE⟩,
   ⟨⟨`f⟩, `f, .forallE `x DefHead.AE DefHead.AE .default, none⟩]

/-- The oracle types the traversal's locals from their list: `f a` is kept, and `y`, a local
definition of a type, is erased. -/
theorem isErasable_locals :
    (runP DefHead.decls 0
      (PureM.isErasable locals (.app (.fvar ⟨`f⟩) (.const `a [])))).toOption.map (·.1) =
      some false ∧
    (runP DefHead.decls 0 (PureM.isErasable locals (.fvar ⟨`y⟩))).toOption.map (·.1) =
      some true := by
  decide

/-- Two fresh free variables. -/
def twoFresh : PureM (List FVarId) := return [← PureM.freshFVarId, ← PureM.freshFVarId]

/-- info: "ok ([_pure.3, _pure.4], 5)" -/
#guard_msgs in
#eval match runP [] 3 twoFresh with
  | .ok (xs, s) => s!"ok ({xs.map FVarId.name}, {s.next})"
  | .error _ => "error"

/-- A traversal action at the pure backend: it reads the traversal's locals, takes a fresh free
variable from the backend and registers an axiom in the traversal's state. -/
def act : EraseT PureM (Nat × FVarId) := do
  let tc ← readThe TravCtx
  let x ← (PureM.freshFVarId : PureM FVarId)
  modifyThe ErasureState fun s => { s with inlinings := [toKername `k] }
  return (tc.locals.length, x)

/-- info: "ok (2, _pure.7, 1, 8)" -/
#guard_msgs in
#eval match act.runPure {} { locals := locals, «config» := {} } ⟨[], ⟨fun _ => none, fun _ => false,
    fun _ => none⟩⟩ { next := 7 } with
  | .ok (((n, x), st), ps) => s!"ok ({n}, {x.name}, {st.inlinings.length}, {ps.next})"
  | .error _ => "error"
end Ops

/-! ## The elaboration environment, and `#erase` -/

namespace Irr
def IProp : Type := Prop
axiom R : IProp
axiom hR : R
universe u
def pid {α : Sort u} (a : α) : α := a
/--
warning: Definition `pidHR` is a proposition; use `theorem` instead of `def`

Note: This linter can be disabled with `set_option linter.defProp false`
-/
#guard_msgs in
def pidHR : R := pid hR
attribute [irreducible] IProp
end Irr

/-- info: ["R: ok true", "hR: ok true", "pidHR: ok true", "pid: ok false"] -/
#guard_msgs in
#eval show MetaM (List String) from do
  let .ok decls := collectDeps (EnvView.ofEnvironment (← getEnv)) (.const ``Irr.pidHR [])
    | return ["collectDeps failed"]
  let cx : Pure.Ctx := ⟨decls⟩
  return [s!"R: {show' (Pure.isErasable cx oracleFuel [] (.const ``Irr.R []))}",
    s!"hR: {show' (Pure.isErasable cx oracleFuel [] (.const ``Irr.hR []))}",
    s!"pidHR: {show' (Pure.isErasable cx oracleFuel [] (.const ``Irr.pidHR []))}",
    s!"pid: {show' (Pure.isErasable cx oracleFuel [] (.const ``Irr.pid [.succ .zero]))}"]

/--
warning: failed to translate Irr.R into ML type, emitting unit instead.
---
info: val main: unit
-/
#guard_msgs in
#erase Irr.pidHR to "pidHR.ast"
