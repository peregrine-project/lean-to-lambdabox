import LeanToLambdaBox

/-!
`Erasure.collectDeps` excludes an inductive whose declared type is not syntactically an arity
`Π x₁…xₙ, Sort u` (`arityShape`), such as a type that reaches its sort only by unfolding an alias
(register entry S-35). Lean's kernel accepts such declarations, and the default elaborator keeps
the alias as the declared type. The pure path reads an inductive's sort from the syntactic arity
of its type; the `Meta` path reduces it. The test checks, under `nat := .peano`, that the
following programs are outside the fragment with the reason `inductive … whose type is not an
arity`, and route to the `Meta` path:
- `t := PU.casesOn.{1, 0} (motive := fun _ => Nat) PU.mk 5`, with `def S.{u} := Sort u` and
  `inductive PU.{u} : S.{u} | mk` (declared with `bootstrap.inductiveCheckResultingUniverse`
  off): `PU.{0}` is a proposition with one constructor, at a sort that may be zero;
- `useFoo := Foo.mk` with `def T1 := Type` and `inductive Foo : T1 | mk`;
- `usePT := PT.casesOn (motive := fun _ => Nat) PT.mk 3` with `def PAlias := Prop` and
  `inductive PT : PAlias | mk`;
- `useG := G.mk` with `def F := Nat → Type` and `inductive G : F | mk : G 0` (the `Π` itself is
  behind the alias).
The `#erase` output of `t` on the `Meta` path is pinned (`t.ast`): the `Meta` path reduces the
`casesOn` to its alternative `5`, which peregrine evaluates.
-/

-- peregrine: validate t.ast
-- peregrine: eval t.ast --anf=false

open Lean Erasure

namespace AT
def S.{u} := Sort u
set_option bootstrap.inductiveCheckResultingUniverse false in
inductive PU.{u} : S.{u} where
  | mk : PU
def t : Nat := PU.casesOn.{1, 0} (motive := fun _ => Nat) PU.mk 5
def T1 := Type
inductive Foo : T1 where
  | mk : Foo
def useFoo : Foo := Foo.mk
def PAlias := Prop
inductive PT : PAlias where
  | mk : PT
def usePT : Nat := PT.casesOn (motive := fun _ => Nat) PT.mk 3
def F := Nat → Type
inductive G : F where
  | mk : G 0
def useG : G 0 := G.mk
end AT

/-- The fragment test and the route of the constant `n` under `nat := .peano`. -/
def check (n : Name) : CoreM Unit := do
  let view := EnvView.ofEnvironment (← getEnv)
  let cfg : ErasureConfig := { nat := .peano }
  let r := match collectDeps view cfg (.const n []) with
    | .ok _ => "in the fragment"
    | .error err => err.describe
  let rt := match route view cfg (.const n []) with
    | .viaPure (.ok _) => "viaPure ok"
    | .viaPure (.error err) => s!"viaPure error ({err.describe})"
    | .viaMeta => "viaMeta"
  logInfo s!"{r}; {rt}"

/-- info: outside the fragment: inductive AT.PU whose type is not an arity; viaMeta -/
#guard_msgs in
#eval check ``AT.t
/-- info: outside the fragment: inductive AT.Foo whose type is not an arity; viaMeta -/
#guard_msgs in
#eval check ``AT.useFoo
/-- info: outside the fragment: inductive AT.PT whose type is not an arity; viaMeta -/
#guard_msgs in
#eval check ``AT.usePT
/-- info: outside the fragment: inductive AT.G whose type is not an arity; viaMeta -/
#guard_msgs in
#eval check ``AT.useG

#guard_msgs (drop warning, drop info) in
#erase AT.t config {nat := .peano} to "t.ast"
