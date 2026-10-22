import LeanToLambdaBox

/-!
The traversal's reader context `Erasure.TravCtx` holds its binders twice, as a `LocalContext` and as
a list of `Erasure.Local`s, and λ□ binder names come from the list (register entry S-17):
- `withLocalDecl` and `withLocalDef` push the binder onto both, innermost first in the list, with
  its value for a `let`;
- `binderNameOf` keeps an ASCII graphic user name and makes any other anonymous; `fixDefName` names
  the fixpoint definition of a constant;
- `#erase` of programs with a binder at every place where the traversal introduces one is pinned:
  a λ with an ASCII and a non-ASCII name, a `let`, a constructor η-expanded to its arity, a
  `casesOn` alternative that is not a λ and one that is, a sparse `casesOn` whose discriminant the
  traversal let-binds (`discr`), a `Nat` match in machine mode (`n`), and a recursive definition
  (its fixpoint definition's name). A binder missing from the list would make the traversal panic,
  and this test fails on a panic.
-/

-- peregrine: validate all.ast
-- peregrine: eval all.ast

open Lean Erasure

/-- info: [BinderName.named "x", BinderName.anon, BinderName.named "a.b", BinderName.anon] -/
#guard_msgs in
#eval [binderNameOf `x, binderNameOf `α₁, binderNameOf `a.b, binderNameOf (.mkSimple "a b")]

/-- info: BinderName.named "Loc.step" -/
#guard_msgs in
#eval fixDefName `Loc.step

/-- info: [(`b, true, some `b), (`a, false, some `a)] -/
#guard_msgs in
#eval show CoreM (List (Name × Bool × Option Name)) from do
  let (r, _) ← Erasure.run (m := CoreM) (withLocalDecl `a (.const ``Nat []) .default fun x =>
      withLocalDef `b (.const ``Nat []) (.fvar x) false fun _ => do
        let tc ← read
        return tc.locals.map fun l =>
          (l.userName, l.value?.isSome, (tc.lctx.find? l.fvarId).map (·.userName))) {}
  return r

namespace Loc

inductive T where
  | a
  | b (n : Nat)
  | c (m k : Nat)

def g (x : Nat) : Nat := x + 1

/-- A λ with an ASCII and a non-ASCII binder, a `let`, an η-expanded constructor (`T.b`), and a
`casesOn` with an alternative that is not a λ (`g`) and one that is. -/
def names (a : Nat) (α₁ : Nat) (t : T) : List T × Nat :=
  let s := a + α₁
  (List.map T.b [s], @T.casesOn (fun _ => Nat) t 0 g (fun m k => m + k))

/-- Recursive; matches on `Nat` and, with a wildcard, on its own recursive call. -/
def step : Nat → T
  | 0 => .a
  | n + 1 =>
    match step n with
    | .b k => .b (k + 1)
    | _ => .c n n

/-- `(1 + 2) + (3 + 4) + 1 = 11`. -/
def all : Nat :=
  match names 1 2 (.c 3 4), step 2 with
  | ([.b s], v), .c m _ => s + v + m
  | _, _ => 0

#guard all = 11

end Loc

#erase Loc.names to "names.ast"
#erase Loc.step to "step.ast"
#erase Loc.all config {nat := .peano, extern := .preferLogical} to "all.ast"
