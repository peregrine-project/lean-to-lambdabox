import LeanToLambdaBox

/-!
Quotients are erased as the code generator erases them (register entry S-38): a quotient is
represented by its elements, so `Quot.mk α r a` is erased to `a` and `Quot.lift α r β f h q` to
`f q`, η-expanded when under-applied and applied to the arguments beyond the sixth when
over-applied; `Quot` is a type and `Quot.ind` a proof, both erased to □.

The fragment test excludes quotients, so, under `nat := .peano`, the five programs below take the
`Meta` path (`outside the fragment: quotient …`, the first quotient constant the closure meets),
and `#erase` writes them:
- `useLift`: `Quot.lift` applied to its six arguments, on `Quot.mk`;
- `usePart`: `liftNeg`, a `Quot.lift` applied to four arguments (η-expanded), applied to `Quot.mk`;
- `useOver`: `Quot.lift` into a function type, applied to a seventh argument;
- `useQuotient`: `Quotient.lift` and `Quotient.mk` on a `Setoid` instance (definitions whose
  values apply `Quot.lift` and `Quot.mk`);
- `indPf`: a proof by `Quot.ind`, erased to □, which peregrine evaluates to □ (printed `(FIX 0)`).
peregrine evaluates the first four to `QT.B.t`, `QT.B.f`, `QT.B.t` and `QT.B.f`. Before this
change the `Meta` path emits `Quot.lift` and `Quot.mk` as axioms; peregrine validates these
outputs but does not evaluate them (`Axioms found`).
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

def indPf (q : Quot r) : True := Quot.ind (β := fun _ => True) (fun _ => trivial) q
end QT

/-- The fragment test's verdict on the constant `n` under `nat := .peano`. -/
def check (n : Name) : CoreM Unit := do
  match collectDeps (EnvView.ofEnvironment (← getEnv)) { nat := .peano } (.const n []) with
  | .ok _ => logInfo "in the fragment"
  | .error err => logInfo err.describe

/-- info: outside the fragment: quotient Quot.lift -/
#guard_msgs in
#eval check ``QT.useLift
/-- info: outside the fragment: quotient Quot -/
#guard_msgs in
#eval check ``QT.usePart
/-- info: outside the fragment: quotient Quot.lift -/
#guard_msgs in
#eval check ``QT.useOver
/-- info: outside the fragment: quotient Quot -/
#guard_msgs in
#eval check ``QT.useQuotient
/-- info: outside the fragment: quotient Quot -/
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
