import LeanToLambdaBox

/-!
`Erasure.collectDeps view e` gives the declarations that `e` depends on through types, values and
block members, read through the view `view`, or says why `e` lies outside the fragment without
inductive types, literals, projections and metavariables (register entry S-18). `#erase` does not
call it:
- on the program `one (fun a : A => a)` (`axiom A : Type`, `def CN := (A → A) → A → A`,
  `def one : CN := fun s z => s z`), over a view built by hand, it gives `[A, CN, one]` by kernel
  evaluation (`decide`), and the same names over the elaboration environment;
- over the elaboration environment (`EnvView.ofEnvironment`): a two-member `unsafe` block is closed
  under its members; `@pid` at a universe metavariable is `outOfFragment`; a closure with two
  colliding kernames and a literal is `outOfFragment`, not `nameCollision`; an in-fragment closure
  with two colliding kernames is `nameCollision`;
- over views built by hand, by `decide`: the closure of `B := A`; the collision-first and the
  in-fragment collision programs, as above; a constant the view does not have is `outOfFragment`;
  a view that answers with a declaration of another name is `failed`.
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
def view : EnvView := ⟨findConst decls, fun _ => false, fun _ => none⟩
def e : Expr := .app (.const `one []) (.lam `a A (.bvar 0) .default)

theorem collect : (collectDeps view e).toOption.map (·.map (·.name)) = some [`A, `CN, `one] := by
  decide
end NV1

/-- info: "ok [NV1src.A, NV1src.CN, NV1src.one]" -/
#guard_msgs in
#eval show MetaM String from do
  let v := EnvView.ofEnvironment (← getEnv)
  return show' (collectDeps v
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
info: ["useU: ok [D3src.one, D3src.ub, D3src.ua, D3src.A, D3src.CN, D3src.useU]", "pid.?u: outOfFragment level metavariable",
  "«a b»: outOfFragment literal", "«c d»: nameCollision D3src.c_u32d D3src.«c d»"]
-/
#guard_msgs in
#eval show MetaM (List String) from do
  let v := EnvView.ofEnvironment (← getEnv)
  return [s!"useU: {show' (collectDeps v (.const ``D3src.useU []))}",
    "pid.?u: " ++ show' (collectDeps v (.const ``D3src.pid [.mvar ⟨`u⟩])),
    s!"«a b»: {show' (collectDeps v (.const ``D3src.«a b» []))}",
    s!"«c d»: {show' (collectDeps v (.const ``D3src.«c d» []))}"]

/-! ## Kernel evaluation over views built by hand -/

namespace D3k
def A_val : AxiomVal :=
  { name := `A, levelParams := [], type := .sort (.succ .zero), isUnsafe := false }
def B_val : DefinitionVal :=
  { name := `B, levelParams := [], type := .sort (.succ .zero), value := .const `A [],
    hints := .abbrev, safety := .safe, all := [`B] }
def decls : List ConstantInfo := [.defnInfo B_val, .axiomInfo A_val]
def view : EnvView := ⟨fun n => decls.find? (·.name == n), fun _ => false, fun _ => none⟩

theorem collect_B :
    (collectDeps view (.const `B [])).toOption.map (·.map (·.name)) = some [`A, `B] := by decide

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
def cview : EnvView := ⟨findConst cdecls, fun _ => false, fun _ => none⟩

theorem collisionFirst_outOfFragment :
    errKind (collectDeps cview (.const (.str .anonymous "a b") [])) = some 0 := by decide
theorem collision : errKind (collectDeps cview (.const (.str .anonymous "c d") [])) = some 1 := by
  decide
theorem unknown_outOfFragment : errKind (collectDeps cview (.const `B [])) = some 0 := by decide

/-- A view whose `find? a` is the declaration `b`. -/
def badView : EnvView :=
  ⟨fun n => if n == `a then some (.axiomInfo { A_val with name := `b }) else none,
    fun _ => false, fun _ => none⟩
theorem badView_failed : errKind (collectDeps badView (.const `a [])) = some 3 := by decide
end D3k

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
