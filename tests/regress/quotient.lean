import LeanToLambdaBox

/-!
Quotients are erased as the code generator erases them (register entry S-38): a quotient is
represented by its elements, so `Quot.mk α r a` is erased to `a` and `Quot.lift α r β f h q` to
`f q`, η-expanded when under-applied and applied to the arguments beyond the sixth when
over-applied; `Quot` is a type and `Quot.ind` a proof, both erased to □. The fragment test admits
quotients (register entry S-39).

The test checks, under `nat := .peano`, over the declarations that `collectDeps` collects, the
oracle's answers on the quotient constants, that the five programs below take the pure path, and
`#erase` writes them:
- `useLift`: `Quot.lift` applied to its six arguments, on `Quot.mk`;
- `usePart`: `liftNeg`, a `Quot.lift` applied to four arguments (η-expanded), applied to `Quot.mk`;
- `useOver`: `Quot.lift` into a function type, applied to a seventh argument;
- `useQuotient`: `Quotient.lift` and `Quotient.mk` on a `Setoid` instance (definitions whose
  values apply `Quot.lift` and `Quot.mk`);
- `indPf`: a proof by `Quot.ind`, stated as a definition so that the closure reads its value;
  it is erased to □, which peregrine evaluates to □ (printed `(FIX 0)`).
peregrine evaluates the first four to `QT.B.t`, `QT.B.f`, `QT.B.t` and `QT.B.f`.
`useLift.meta.ast` is the output of the `Meta` path (`remove_irrel_constr_args` puts the program
outside the fragment), which is the same term. Before the fragment test admits quotients,
`collectDeps` excludes the five programs (`quotient …`), so the oracle checks fail and the
programs take the `Meta` path.
-/

-- peregrine: validate useLift.ast
-- peregrine: eval useLift.ast
-- peregrine: validate usePart.ast
-- peregrine: eval usePart.ast
-- peregrine: validate useOver.ast
-- peregrine: eval useOver.ast
-- peregrine: validate useQuotient.ast
-- peregrine: eval useQuotient.ast
-- peregrine: validate indPf.ast
-- peregrine: eval indPf.ast --anf=false
-- peregrine: validate useLift.meta.ast
-- peregrine: eval useLift.meta.ast

open Lean Erasure
set_option linter.defProp false

namespace QT
inductive B | f | t

def neg : B → B
  | .f => .t
  | .t => .f

/-- Equality as the relation, so that the respect proofs need no recursor. -/
def r (a b : B) : Prop := a = b

def useLift : B := Quot.lift (fun b : B => b) (fun _ _ e => e) (Quot.mk r B.t)

def liftNeg : Quot r → B := Quot.lift neg (fun _ _ e => congrArg neg e)
def usePart : B := liftNeg (Quot.mk r B.t)

def useOver : B :=
  Quot.lift (fun b _ => b) (fun _ _ e => congrArg (fun (x : B) (_ : B) => x) e) (Quot.mk r B.t) B.f

instance setoid : Setoid B := ⟨Eq, ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩⟩
def useQuotient : B := Quotient.lift neg (fun _ _ e => congrArg neg e) (Quotient.mk setoid B.t)

/-- A definition, not a theorem, so that the closure reads its value. -/
def indPf (q : Quot r) : True := Quot.ind (β := fun _ => True) (fun _ => trivial) q
end QT

/-- The oracle's answer on `e` over the closure of the constant `n`, under `nat := .peano`. -/
def oracle (n : Name) (e : Expr) : CoreM Unit := do
  match collectDeps (EnvView.ofEnvironment (← getEnv)) { nat := .peano } (.const n []) with
  | .error err => logInfo s!"collectDeps error ({err.describe})"
  | .ok ds => match Pure.isErasable ⟨ds⟩ oracleFuel [] e with
    | .ok b => logInfo s!"ok {b}"
    | .error err => logInfo s!"error ({err.describe})"

/-- The route of the constant `n` under `nat := .peano`. -/
def check (n : Name) : CoreM Unit := do
  let view := EnvView.ofEnvironment (← getEnv)
  match route view { nat := .peano } (.const n []) with
  | .viaPure (.ok _) => logInfo "viaPure ok"
  | .viaPure (.error err) => logInfo s!"viaPure error ({err.describe})"
  | .viaMeta => logInfo "viaMeta"

/-- `Quot.{1} QT.B QT.r`, `@Quot.mk.{1} QT.B QT.r` and `@Quot.ind.{1} QT.B QT.r`. -/
def quotB : Expr := mkApp2 (.const ``Quot [1]) (.const ``QT.B []) (.const ``QT.r [])
def mkB : Expr := mkApp2 (.const ``Quot.mk [1]) (.const ``QT.B []) (.const ``QT.r [])
def indB : Expr := mkApp2 (.const ``Quot.ind [1]) (.const ``QT.B []) (.const ``QT.r [])

/-- info: ok true -/
#guard_msgs in
#eval oracle ``QT.usePart quotB
/-- info: ok true -/
#guard_msgs in
#eval oracle ``QT.indPf indB
/-- info: ok false -/
#guard_msgs in
#eval oracle ``QT.usePart (.app mkB (.const ``QT.B.t []))
/-- info: ok false -/
#guard_msgs in
#eval oracle ``QT.usePart (.const ``QT.liftNeg [])

/-- info: viaPure ok -/
#guard_msgs in
#eval check ``QT.useLift
/-- info: viaPure ok -/
#guard_msgs in
#eval check ``QT.usePart
/-- info: viaPure ok -/
#guard_msgs in
#eval check ``QT.useOver
/-- info: viaPure ok -/
#guard_msgs in
#eval check ``QT.useQuotient
/-- info: viaPure ok -/
#guard_msgs in
#eval check ``QT.indPf

#guard_msgs (drop warning, drop info) in
#erase QT.useLift config {nat := .peano} to "useLift.ast"
#guard_msgs (drop warning, drop info) in
#erase QT.usePart config {nat := .peano} to "usePart.ast"
#guard_msgs (drop warning, drop info) in
#erase QT.useOver config {nat := .peano} to "useOver.ast"
#guard_msgs (drop warning, drop info) in
#erase QT.useQuotient config {nat := .peano} to "useQuotient.ast"
#guard_msgs (drop warning, drop info) in
#erase QT.indPf config {nat := .peano} to "indPf.ast"
#guard_msgs (drop warning, drop info) in
#erase QT.useLift config {nat := .peano, remove_irrel_constr_args := true} to "useLift.meta.ast"
