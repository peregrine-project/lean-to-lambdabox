import LeanToLambdaBox

/-!
`Erasure.collectDeps view cfg e` gives the declarations that `e` depends on as the pure traversal
reads them, read through the view `view`, or says why `e` lies outside the fragment (register
entries S-18, S-29); `#erase` routes on it (S-21):
- on the program `one (fun a : A => a)` (`axiom A : Type`, `def CN := (A → A) → A → A`,
  `def one : CN := fun s z => s z`), over a view built by hand, it gives `[A, CN, one]` by kernel
  evaluation (`decide`), and the same names over the elaboration environment;
- over the elaboration environment (`EnvView.ofEnvironment`): a constant using an `unsafe` block is
  `outOfFragment`; `@pid` at a universe metavariable is `outOfFragment`; a closure with two
  colliding kernames and a literal (under `nat := .machine`) is `outOfFragment`, not
  `nameCollision`; an in-fragment closure with two colliding kernames is `nameCollision`;
- over views built by hand, by `decide`: the closure of `B := A`; the collision-first and the
  in-fragment collision programs, as above; a constant the view does not have is `outOfFragment`;
  a view that answers with a declaration of another name is `failed`;
- over the elaboration environment, programs with inductive types: `B.neg B.f` (a canonical
  `casesOn`: the closure has `B.casesOn` and `B.rec`, not what the value of `B.casesOn` reads),
  `Eq.casesOn` on `Eq.refl` and on the theorem `hEq` (whose value is not read) are in the
  fragment; so are a literal under `nat := .peano`, a projection, a mention of `Unit`, a mutual
  block and a root-level inductive with the kername of its block; outside it are a literal and
  `Nat.zero` under `nat := .machine`, a recursor in a definition and alone, a `partial def`, an
  `implemented_by` target, a `casesOn` with an index field, a `casesOn` on `PUnit`, and any
  inductive under `remove_irrel_constr_args`; two blocks with one block name, and a block whose
  name is the kername of a definition, are `nameCollision`.
The output of `#erase` on the program `one (fun a : A => a)` is pinned (`nv1.ast`).
-/

-- peregrine: validate nv1.ast
-- peregrine: eval nv1.ast --anf=false

open Lean Erasure

/-- A readable form of a result of `collectDeps`. -/
def show' (r : Except EraseError (List ConstantInfo)) : String :=
  match r with
  | .ok ds => s!"ok {ds.map (·.name)}"
  | .error (.outOfFragment w) => s!"outOfFragment {w}"
  | .error (.nameCollision a b) => s!"nameCollision {a} {b}"
  | .error (.fuel s) => s!"fuel {s}"
  | .error (.failed m) => s!"failed {m}"

/-- The error class of a result of `collectDeps`, for kernel evaluation. -/
def errKind : Except EraseError (List ConstantInfo) → Option Nat
  | .ok _ => none
  | .error (.outOfFragment _) => some 0
  | .error (.nameCollision _ _) => some 1
  | .error (.fuel _) => some 2
  | .error (.failed _) => some 3

/-! ## The program `one (fun a : A => a)` -/

namespace NV1src
axiom A : Type
def CN : Type := (A → A) → A → A
def one : CN := fun s z => s z
end NV1src

namespace NV1
def A : Expr := .const `A []
def arrow (t u : Expr) : Expr := .forallE `a t u .default
def A_val : AxiomVal :=
  { name := `A, levelParams := [], type := .sort (.succ .zero), isUnsafe := false }
def CN_val : DefinitionVal :=
  { name := `CN, levelParams := [], type := .sort (.succ .zero),
    value := arrow (arrow A A) (arrow A A), hints := .abbrev, safety := .safe, all := [`CN] }
def one_val : DefinitionVal :=
  { name := `one, levelParams := [], type := .const `CN [],
    value := .lam `s (arrow A A) (.lam `z A (.app (.bvar 1) (.bvar 0)) .default) .default,
    hints := .abbrev, safety := .safe, all := [`one] }
def decls : List ConstantInfo := [.axiomInfo A_val, .defnInfo CN_val, .defnInfo one_val]
def view : EnvView := ⟨findConst decls, fun _ => false, fun _ => none, fun _ => none⟩
def e : Expr := .app (.const `one []) (.lam `a A (.bvar 0) .default)

theorem collect : (collectDeps view {} e).toOption.map (·.map (·.name)) = some [`A, `CN, `one] := by
  decide
end NV1

/-- info: "ok [NV1src.A, NV1src.CN, NV1src.one]" -/
#guard_msgs in
#eval show MetaM String from do
  let v := EnvView.ofEnvironment (← getEnv)
  return show' (collectDeps v {}
    (.app (.const ``NV1src.one []) (.lam `a (.const ``NV1src.A []) (.bvar 0) .default)))

/-! ## Blocks, universe metavariables and kername collisions, over the elaboration environment -/

namespace D3src
axiom A : Type
def CN : Type := (A → A) → A → A
def one : CN := fun s z => s z
mutual
unsafe def ua (n : CN) : CN := ub n
unsafe def ub (n : CN) : CN := ua n
end
unsafe def useU : CN := ua one
universe u
def pid {α : Sort u} (a : α) : α := a
def a_u32b : CN := (fun (_ : Nat) => one) 0
def «a b» : CN := (fun (_ : CN) => one) a_u32b
def c_u32d : CN := one
def «c d» : CN := (fun (_ : CN) => one) c_u32d
end D3src

/--
info: ["useU: outOfFragment unsafe or partial D3src.useU", "pid.?u: outOfFragment level metavariable",
  "«a b»: outOfFragment Nat literal under nat := .machine", "«c d»: nameCollision D3src.c_u32d D3src.«c d»"]
-/
#guard_msgs in
#eval show MetaM (List String) from do
  let v := EnvView.ofEnvironment (← getEnv)
  return [s!"useU: {show' (collectDeps v {} (.const ``D3src.useU []))}",
    "pid.?u: " ++ show' (collectDeps v {} (.const ``D3src.pid [.mvar ⟨`u⟩])),
    s!"«a b»: {show' (collectDeps v {} (.const ``D3src.«a b» []))}",
    s!"«c d»: {show' (collectDeps v {} (.const ``D3src.«c d» []))}"]

/-! ## Kernel evaluation over views built by hand -/

namespace D3k
def A_val : AxiomVal :=
  { name := `A, levelParams := [], type := .sort (.succ .zero), isUnsafe := false }
def B_val : DefinitionVal :=
  { name := `B, levelParams := [], type := .sort (.succ .zero), value := .const `A [],
    hints := .abbrev, safety := .safe, all := [`B] }
def decls : List ConstantInfo := [.defnInfo B_val, .axiomInfo A_val]
def view : EnvView := ⟨fun n => decls.find? (·.name == n), fun _ => false, fun _ => none, fun _ => none⟩

theorem collect_B :
    (collectDeps view {} (.const `B [])).toOption.map (·.map (·.name)) = some [`A, `B] := by decide

/-- A definition of type `Type` without universe parameters. -/
def defn (n : Name) (v : Expr) : ConstantInfo := .defnInfo
  { name := n, levelParams := [], type := .sort (.succ .zero), value := v,
    hints := .abbrev, safety := .safe, all := [n] }

/-- `«a b»` and `a_u32b` have the same kername, and the value of `a_u32b` has a literal; `«c d»`
and `c_u32d` have the same kername, and no literal. -/
def cdecls : List ConstantInfo :=
  [.axiomInfo A_val,
   defn `a_u32b (.app (.lam `x (.const `A []) (.const `A []) .default) (.lit (.natVal 0))),
   defn (.str .anonymous "a b") (.const `a_u32b []),
   defn `c_u32d (.const `A []),
   defn (.str .anonymous "c d") (.const `c_u32d [])]
def cview : EnvView := ⟨findConst cdecls, fun _ => false, fun _ => none, fun _ => none⟩

theorem collisionFirst_outOfFragment :
    errKind (collectDeps cview {} (.const (.str .anonymous "a b") [])) = some 0 := by decide
theorem collision : errKind (collectDeps cview {} (.const (.str .anonymous "c d") [])) = some 1 := by
  decide
theorem unknown_outOfFragment : errKind (collectDeps cview {} (.const `B [])) = some 0 := by decide

/-- A view whose `find? a` is the declaration `b`. -/
def badView : EnvView :=
  ⟨fun n => if n == `a then some (.axiomInfo { A_val with name := `b }) else none,
    fun _ => false, fun _ => none, fun _ => none⟩
theorem badView_failed : errKind (collectDeps badView {} (.const `a [])) = some 3 := by decide
end D3k

/-! ## Inductive types, constructors, `casesOn`, literals and the exclusions -/

namespace F
inductive B | f | t
def B.neg (b : B) : B := B.casesOn (motive := fun _ => B) b B.t B.f
theorem hEq : B.t = B.t := rfl
structure P2 where
  a : B
  b : B
def isZero (n : Nat) : B := Nat.casesOn (motive := fun _ => B) n B.t (fun _ => B.f)
noncomputable def recNeg (b : B) : B := B.rec (motive := fun _ => B) B.t B.f b
instance : Inhabited B := ⟨B.f⟩
partial def spin (b : B) : B := spin b
def fastNeg (b : B) : B := b
@[implemented_by fastNeg] def slowNeg (b : B) : B := b
inductive Ix : B → B → Type | mk (b : B) : Ix B.f b
def ixVal (b : B) (x : Ix B.f b) : B := Ix.casesOn (motive := fun _ _ _ => B) x (fun c => c)
def unitArg (_ : Unit) : B := B.t
def unitCase (u : PUnit.{1}) : B := PUnit.casesOn (motive := fun _ => B) u B.t
mutual
inductive M1 | m (n : M2)
inductive M2 | z | s (m : M1)
end
def mz : M2 := M2.z
end F
inductive «F.Q» | q
def F.Q.q' : «F.Q» := .q
namespace F
inductive Q | q
def useQs : «F.Q» → Q := fun _ => .q
end F
def F_u46B : F.B := .t
def useBlk : F.B := F.B.neg F_u46B
inductive RB | x
def RB.y : RB := .x

/-- A closure's names, or the error. -/
def names (cfg : ErasureConfig) (e : Expr) : MetaM String := do
  return show' (collectDeps (EnvView.ofEnvironment (← getEnv)) cfg e)

/--
info: ["B.neg B.f: ok [F.B.rec, F.B.casesOn, F.B.t, F.B.f, F.B, F.B.neg]",
  "Eq.casesOn on Eq.refl: ok [F.B.t, F.B.f, F.B, Eq.refl, Eq, Eq.rec, Eq.casesOn]",
  "Eq.casesOn on hEq: ok [F.hEq, F.B.t, F.B.f, F.B, Eq.refl, Eq, Eq.rec, Eq.casesOn]"]
-/
#guard_msgs in
#eval show MetaM (List String) from do
  let B := mkConst ``F.B
  let tB := mkConst ``F.B.t
  let motE := .lam `a B (.lam `h (mkAppN (mkConst ``Eq [1]) #[B, tB, .bvar 0]) (.forallE `y B B .default) .default) .default
  let idB := .lam `y B (.bvar 0) .default
  return [s!"B.neg B.f: {← names {} (.app (mkConst ``F.B.neg) (mkConst ``F.B.f))}",
    s!"Eq.casesOn on Eq.refl: {← names {} (mkAppN (mkConst ``Eq.casesOn [1, 1])
      #[B, tB, motE, tB, mkAppN (mkConst ``Eq.refl [1]) #[B, tB], idB])}",
    s!"Eq.casesOn on hEq: {← names {} (mkAppN (mkConst ``Eq.casesOn [1, 1])
      #[B, tB, motE, tB, mkConst ``F.hEq, idB])}"]

/--
info: ["isZero 2, peano: ok", "isZero 2, machine: outOfFragment Nat literal under nat := .machine",
  "isZero Nat.zero, machine: outOfFragment Nat.zero under nat := .machine", "P2.mk projection: ok",
  "recNeg: outOfFragment recursor F.B.rec", "B.rec: outOfFragment recursor F.B.rec",
  "spin: outOfFragment partial definition F.spin", "slowNeg: outOfFragment F.slowNeg has an implemented_by target",
  "ixVal: outOfFragment F.Ix.casesOn on a constructor with an index field", "unitArg (): ok",
  "unitCase: outOfFragment cases or projection on PUnit, whose sort may be Prop or not", "mz: ok",
  "B.neg, remove_irrel_constr_args: outOfFragment inductive F.B under remove_irrel_constr_args",
  "F.Q.q', useQs: nameCollision F.Q «F.Q»", "useBlk: nameCollision F.B F_u46B", "RB.y: ok"]
-/
#guard_msgs in
#eval show MetaM (List String) from do
  let short (s : String) := if s.startsWith "ok" then "ok" else s
  let peano : ErasureConfig := { nat := .peano }
  return [s!"isZero 2, peano: {short (← names peano (.app (mkConst ``F.isZero) (mkNatLit 2)))}",
    s!"isZero 2, machine: {← names {} (.app (mkConst ``F.isZero) (mkNatLit 2))}",
    s!"isZero Nat.zero, machine: {← names {} (.app (mkConst ``F.isZero) (mkConst ``Nat.zero))}",
    s!"P2.mk projection: {short (← names {} (.proj ``F.P2 1
      (mkAppN (mkConst ``F.P2.mk) #[mkConst ``F.B.f, mkConst ``F.B.t])))}",
    s!"recNeg: {← names {} (.app (mkConst ``F.recNeg) (mkConst ``F.B.f))}",
    s!"B.rec: {← names {} (mkConst ``F.B.rec [1])}",
    s!"spin: {← names {} (.app (mkConst ``F.spin) (mkConst ``F.B.f))}",
    s!"slowNeg: {← names {} (.app (mkConst ``F.slowNeg) (mkConst ``F.B.f))}",
    s!"ixVal: {← names {} (mkConst ``F.ixVal)}",
    s!"unitArg (): {short (← names {} (.app (mkConst ``F.unitArg) (mkConst ``Unit.unit)))}",
    s!"unitCase: {← names {} (mkConst ``F.unitCase)}",
    s!"mz: {short (← names {} (mkConst ``F.mz))}",
    s!"B.neg, remove_irrel_constr_args: {← names { remove_irrel_constr_args := true }
      (.app (mkConst ``F.B.neg) (mkConst ``F.B.f))}",
    s!"F.Q.q', useQs: {← names {} (.app (mkConst ``F.useQs) (mkConst ``F.Q.q'))}",
    s!"useBlk: {← names {} (mkConst ``useBlk)}",
    s!"RB.y: {short (← names {} (mkConst ``RB.y))}"]

/-! ## The program `one (fun a : A => a)`, erased -/

/--
warning: failed to translate NV1src.A into ML type, emitting unit instead.
---
warning: failed to translate NV1src.A into ML type, emitting unit instead.
---
info: val main: unit -> unit
-/
#guard_msgs in
#erase NV1src.one (fun a : NV1src.A => a) to "nv1.ast"
