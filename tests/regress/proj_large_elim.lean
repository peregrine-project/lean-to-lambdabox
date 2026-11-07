import LeanToLambdaBox

/-!
The pure oracle `Erasure.Pure.inferType` types a projection `proj S i s` only if `S` is
large-eliminating, which it reads from the recursor: `S.rec` has a universe parameter more than `S`
(register entry S-36). For that, the closure that `collectDeps` computes contains the recursor of
each inductive with one constructor. The test checks:
- on `Ex3 : Prop` with the constructor `intro (w : Prop) (h : (fun _ : Prop => True) w)` and
  `axiom a : Ex3`, added to the kernel directly (the elaborator would β-reduce the field's type):
  `Ex3` is not large-eliminating, Lean's kernel rejects `proj Ex3 1 a` (`h` depends on `w`, which
  is not a proof), and the oracle, over the closure of `proj Ex3 1 a`, which contains `Ex3.rec`,
  answers the error `projection of an inductive that is not large-eliminating`;
- on `E4 : Prop` with the constructor `intro (w : Nat) (h : True)` (an `inductive`, so Lean
  declares no projections) and `axiom a4 : E4`: the kernel accepts `proj E4 1 a4`, a proof
  field that does not depend on `w`, and the oracle answers the same error;
- over the closures of their programs, the oracle types the projections `(P.mk B.t B.f).2` of a
  structure `P` (type `B`) and `(And.intro True.intro True.intro).1` of the `Prop` structure `And`
  (type `True`), and the closures contain `P.rec` and `And.rec`;
- `useSnd := P.b (P.mk B.t B.f)`, whose closure contains the projection `self.2` in the value of
  `P.b`, takes the pure path, and its `#erase` output is pinned (`useSnd.ast`), which peregrine
  evaluates to `B.f`.
-/

-- peregrine: validate useSnd.ast
-- peregrine: eval useSnd.ast

open Lean Erasure

run_cmd Lean.Elab.Command.liftCoreM do
  let ex : Expr := .const `PLE.Ex3 []
  let hT : Expr := .app (.lam `x (.sort 0) (.const ``True []) .default) (.bvar 0)
  let ctorTy : Expr := .forallE `w (.sort 0) (.forallE `h hT ex .default) .default
  let ctor : Constructor := { name := `PLE.Ex3.intro, type := ctorTy }
  let ind : InductiveType := { name := `PLE.Ex3, type := .sort 0, ctors := [ctor] }
  addDecl (.inductDecl [] 0 [ind] false)
  addDecl (.axiomDecl { name := `PLE.a, levelParams := [], type := ex, isUnsafe := false })

namespace PLE
inductive E4 : Prop where
  | intro (w : Nat) (h : True)
axiom a4 : E4
inductive B where
  | t | f
structure P where
  a : B
  b : B
def useSnd : B := P.b (P.mk B.t B.f)
end PLE

/-- Whether the kernel accepts a definition of type `ty` and value `e`. -/
def kernel (ty e : Expr) : CoreM Unit := do
  let dv : DefinitionVal :=
    { name := `PLE.probe, levelParams := [], type := ty, value := e, hints := .opaque, safety := .safe }
  match (← getEnv).addDeclCore 0 512 (.defnDecl dv) none with
  | .ok _ => logInfo "kernel accepts"
  | .error _ => logInfo "kernel rejects"

/-- The oracle's type of `e` over the closure of `e`, and whether the closure contains `r`, under
`nat := .peano`. -/
def oracle (e : Expr) (r : Name) : CoreM Unit := do
  match collectDeps (EnvView.ofEnvironment (← getEnv)) { nat := .peano } e with
  | .error err => logInfo s!"collectDeps error ({err.describe})"
  | .ok ds =>
    let has := (findConst ds r).isSome
    match Pure.inferType ⟨ds⟩ oracleFuel [] [] e with
    | .ok t => logInfo m!"ok {t}; {r} in the closure: {has}"
    | .error err => logInfo s!"error ({err.describe}); {r} in the closure: {has}"

/-- info: kernel rejects -/
#guard_msgs in
#eval kernel (.const ``True []) (.proj `PLE.Ex3 1 (.const `PLE.a []))
/--
info: error (projection of an inductive that is not large-eliminating); PLE.Ex3.rec in the closure: true
-/
#guard_msgs in
#eval oracle (.proj `PLE.Ex3 1 (.const `PLE.a [])) `PLE.Ex3.rec

/-- info: kernel accepts -/
#guard_msgs in
#eval kernel (.const ``True []) (.proj ``PLE.E4 1 (.const ``PLE.a4 []))
/--
info: error (projection of an inductive that is not large-eliminating); PLE.E4.rec in the closure: true
-/
#guard_msgs in
#eval oracle (.proj ``PLE.E4 1 (.const ``PLE.a4 [])) ``PLE.E4.rec

/-- info: ok PLE.B; PLE.P.rec in the closure: true -/
#guard_msgs in
#eval oracle (.proj ``PLE.P 1 (mkApp2 (.const ``PLE.P.mk []) (.const ``PLE.B.t [])
  (.const ``PLE.B.f []))) ``PLE.P.rec
/-- info: ok True; And.rec in the closure: true -/
#guard_msgs in
#eval oracle (.proj ``And 0 (mkApp4 (.const ``And.intro []) (.const ``True [])
  (.const ``True []) (.const ``True.intro []) (.const ``True.intro []))) ``And.rec

/-- info: viaPure ok -/
#guard_msgs in
#eval show CoreM Unit from do
  match route (EnvView.ofEnvironment (← getEnv)) {} (.const ``PLE.useSnd []) with
  | .viaPure (.ok _) => logInfo "viaPure ok"
  | .viaPure (.error err) => logInfo s!"viaPure error ({err.describe})"
  | .viaMeta => logInfo "viaMeta"

#guard_msgs (drop warning, drop info) in
#erase PLE.useSnd to "useSnd.ast"
