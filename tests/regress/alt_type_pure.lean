import LeanToLambdaBox

/-!
An alternative whose type is a function type only after unfolding (register entry S-31): the
traversal reduces the type with the backend's `whnf`, which the pure backend computes with the
oracle (`Pure.whnf`: head β, ζ, the kernel's δ and ι). The test checks, for programs in the
fragment:
- `aliasT`, whose alternative `first` has the type `Fn2`, an alias of `B → B → B`, and `famT`,
  whose alternative `idB` has the type `Fam B`, which β-reduces to `B → B`: both take the pure path,
  and the pure and the `Meta` paths give the same program; `#erase` writes them to `alias.ast` and
  `fam.ast`, which peregrine evaluates to `B.t`;
- `selT`, whose alternative's type `Sel true` reaches `B → B` only through `Bool.rec` (ι, register
  entry S-43): it takes the pure path as well, with the program of the `Meta` path; `#erase` writes
  it to `sel.ast`, which peregrine evaluates to `B.t`. Without the recursor ι-rule, the pure path
  stops with the error "expected a function type, got `Bool.rec …`".
-/

-- peregrine: validate alias.ast
-- peregrine: eval alias.ast
-- peregrine: validate fam.ast
-- peregrine: eval fam.ast
-- peregrine: validate sel.ast
-- peregrine: eval sel.ast

open Lean Erasure

namespace ATP
inductive B | f | t
abbrev Fn2 := B → B → B
def first : Fn2 := fun a _ => a
def aliasT : B := Prod.casesOn (motive := fun _ => B) (B.t, B.f) first
def Fam (α : Type) : Type := α → α
def idB : Fam B := fun b => b
def famT : B := Option.casesOn (motive := fun _ => B) (some B.t) B.f idB
def Sel (b : Bool) : Type := Bool.casesOn (motive := fun _ => Type) b B (B → B)
def idS : Sel true := fun b => b
def selT : B := Option.casesOn (motive := fun _ => B) (some B.t) B.f idS
end ATP

/-- The route of the constant `n` under `nat := .peano`, and whether its pure output equals the
`Meta` path's; of an error, the text before the term it names. -/
def check (n : Name) : CoreM Unit := do
  let e : Expr := .const n []
  let cfg : ErasureConfig := { nat := .peano }
  let view := EnvView.ofEnvironment (← getEnv)
  match route view cfg e with
  | .viaPure (.ok (p, _)) =>
    let (q, _) ← erase e cfg
    logInfo s!"viaPure ok; pure = Meta: \
      {(Serialize.to_sexpr p).toString == (Serialize.to_sexpr q).toString}"
  | .viaPure (.error err) => logInfo s!"viaPure error ({err.describe.takeWhile (· != ',')})"
  | .viaMeta => logInfo "viaMeta"

/-- info: viaPure ok; pure = Meta: true -/
#guard_msgs in
#eval check ``ATP.aliasT
/-- info: viaPure ok; pure = Meta: true -/
#guard_msgs in
#eval check ``ATP.famT
/-- info: viaPure ok; pure = Meta: true -/
#guard_msgs in
#eval check ``ATP.selT

#guard_msgs (drop warning, drop info) in
#erase ATP.aliasT config {nat := .peano} to "alias.ast"
#guard_msgs (drop warning, drop info) in
#erase ATP.famT config {nat := .peano} to "fam.ast"
#guard_msgs (drop warning, drop info) in
#erase ATP.selT config {nat := .peano} to "sel.ast"
