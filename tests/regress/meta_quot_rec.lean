import LeanToLambdaBox

/-!
Quotients (register entry S-38) and recursors (S-40) on the `Meta` path. Each program below has
a Nat literal, which the fragment test excludes under the default configuration
(`nat := .machine`), so `#erase` takes the `Meta` path; under `nat := .peano` the same programs are
in the fragment. The test checks both routes and pins the `Meta` path's output:
- `useLift`: `Quot.lift` applied to its six arguments, on `Quot.mk`, erased to `f a`;
- `usePart`: `liftId`, a `Quot.lift` applied to four arguments (η-expanded), applied to `Quot.mk`;
- `useOver`: `Quot.lift` into a function type, applied to a seventh argument;
- `useQuotient`: `Quotient.lift` and `Quotient.mk` on a `Setoid` instance;
- `useRec`: `Tr.rec` on a binary tree with a Nat field, which negates the induction hypothesis of
  the right subtree, erased to a fixpoint over a `case`.
peregrine evaluates the first four to 7 and `useRec` to `MQR.B.t`.
-/

-- peregrine: validate useLift.ast
-- peregrine: eval useLift.ast
-- peregrine: validate usePart.ast
-- peregrine: eval usePart.ast
-- peregrine: validate useOver.ast
-- peregrine: eval useOver.ast
-- peregrine: validate useQuotient.ast
-- peregrine: eval useQuotient.ast
-- peregrine: validate useRec.ast
-- peregrine: eval useRec.ast

open Lean Erasure
set_option linter.defProp false

namespace MQR
inductive B | f | t

def neg : B → B
  | .f => .t
  | .t => .f

def r (a b : Nat) : Prop := a = b

def useLift : Nat := Quot.lift (fun n : Nat => n) (fun _ _ e => e) (Quot.mk r 7)

def liftId : Quot r → Nat := Quot.lift (fun n => n) (fun _ _ e => e)
def usePart : Nat := liftId (Quot.mk r 7)

def useOver : Nat :=
  Quot.lift (fun n (_ : Nat) => n) (fun _ _ e => congrArg (fun (x : Nat) (_ : Nat) => x) e)
    (Quot.mk r 7) 8

instance setoid : Setoid Nat := ⟨Eq, ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩⟩
def useQuotient : Nat := Quotient.lift (fun n : Nat => n) (fun _ _ e => e) (Quotient.mk setoid 7)

inductive Tr | leaf | node : Nat → Tr → Tr → Tr

noncomputable def parity (t : Tr) : B := Tr.rec (motive := fun _ => B) B.t (fun _ _ _ _ ih => neg ih) t
noncomputable def useRec : B := parity (.node 7 .leaf (.node 8 .leaf .leaf))
end MQR

/-- The route of the constant `n` under `cfg`, with the fragment test's verdict on the `Meta`
path. -/
def check (cfg : ErasureConfig) (n : Name) : CoreM Unit := do
  let view := EnvView.ofEnvironment (← getEnv)
  match route view cfg (.const n []) with
  | .viaPure (.ok _) => logInfo "pure path"
  | .viaPure (.error err) => logInfo s!"pure path, error: {err.describe}"
  | .viaMeta => match collectDeps view cfg (.const n []) with
    | .error err => logInfo s!"Meta path ({err.describe})"
    | .ok _ => logInfo "Meta path"

/-- info: Meta path (outside the fragment: Nat literal under nat := .machine) -/
#guard_msgs in #eval check {} ``MQR.useLift
/-- info: Meta path (outside the fragment: Nat literal under nat := .machine) -/
#guard_msgs in #eval check {} ``MQR.usePart
/-- info: Meta path (outside the fragment: Nat literal under nat := .machine) -/
#guard_msgs in #eval check {} ``MQR.useOver
/-- info: Meta path (outside the fragment: Nat literal under nat := .machine) -/
#guard_msgs in #eval check {} ``MQR.useQuotient
/-- info: Meta path (outside the fragment: Nat literal under nat := .machine) -/
#guard_msgs in #eval check {} ``MQR.useRec
/-- info: pure path -/
#guard_msgs in #eval check {nat := .peano} ``MQR.useLift
/-- info: pure path -/
#guard_msgs in #eval check {nat := .peano} ``MQR.usePart
/-- info: pure path -/
#guard_msgs in #eval check {nat := .peano} ``MQR.useOver
/-- info: pure path -/
#guard_msgs in #eval check {nat := .peano} ``MQR.useQuotient
/-- info: pure path -/
#guard_msgs in #eval check {nat := .peano} ``MQR.useRec

#guard_msgs (drop warning, drop info) in
#erase MQR.useLift to "useLift.ast"
#guard_msgs (drop warning, drop info) in
#erase MQR.usePart to "usePart.ast"
#guard_msgs (drop warning, drop info) in
#erase MQR.useOver to "useOver.ast"
#guard_msgs (drop warning, drop info) in
#erase MQR.useQuotient to "useQuotient.ast"
#guard_msgs (drop warning, drop info) in
#erase MQR.useRec to "useRec.ast"
