import LeanToLambdaBox

/-!
An application of a recursor `T.rec` is erased to a λ□ fixpoint over a `case` (register entry
S-40): the minor premises are let-bound, and the fixpoint of the recursor's block, one function per
member taking the indices and the major premise, is applied to the indices and the major premise;
each alternative applies its minor premise to the constructor's fields and to an induction
hypothesis `λ ys. rec □… (f ys)` for each recursive field `f`. A recursor whose application is a
proof is erased to □.

The fragment test admits recursors (register entry S-41), except those that the eraser keeps
as constants, so, under `nat := .peano`, the programs below take the pure path, and `#erase`
writes them:
- `useNat`: `double 3`, where `double` is `Nat.rec` without its major premise (η-expanded), with
  `csimp := false` (with `csimp`, the code generator's `Nat.rec = Nat.recCompiled` replaces it);
- `useList`: the length of a list by `List.rec`, whose induction hypothesis is used;
- `useVec`: the last element of a vector by `Vec.rec`, on an indexed family;
- `useMutual`: `Od.rec` on the mutual block `Ev`/`Od`, whose fixpoint has two functions;
- `useCast`: a cast `h ▸ b` (`Eq.rec`, a `Prop` inductive with a data motive), and `useAnd`:
  `And.rec` into data; the major premise is a proof, erased to □, so the fixpoint reduces its
  `case` itself;
- `useOver`: `Bool.rec` into a function type, applied to an argument beyond its major premise;
- `propRec`: a proof by `Nat.rec` with a `Prop` motive, erased to □ (printed `(FIX 0)`);
- `useNatMachine`: `useNat` under `nat := .machine`, where `Nat.rec` stays an axiom, since the
  values of `Nat` are primitive integers (peregrine reads no output with them, R-1).
peregrine evaluates them to 6, 3, `RT.B.t`, `RT.B.t`, `RT.B.t`, `RT.B.t`, `RT.B.f` and □.
The test also pins `useList` on the `Meta` path (`useList.meta.ast`, under
`remove_irrel_constr_args`, which the fragment excludes), which equals the pure path's output, and
checks that the fragment test excludes `useAcc`, which applies `Acc.rec` (a `Prop` inductive with
a field that is an index), which the eraser keeps as a constant, so that `#erase` writes it
(`useAcc.ast`) with the axiom `Acc.rec` on the `Meta` path.
-/

-- peregrine: validate useNat.ast
-- peregrine: eval useNat.ast
-- peregrine: validate useList.ast
-- peregrine: eval useList.ast
-- peregrine: validate useVec.ast
-- peregrine: eval useVec.ast
-- peregrine: validate useMutual.ast
-- peregrine: eval useMutual.ast
-- peregrine: validate useCast.ast
-- peregrine: eval useCast.ast
-- peregrine: validate useAnd.ast
-- peregrine: eval useAnd.ast
-- peregrine: validate useOver.ast
-- peregrine: eval useOver.ast
-- peregrine: validate propRec.ast
-- peregrine: eval propRec.ast --anf=false
-- peregrine: validate useList.meta.ast
-- peregrine: eval useList.meta.ast
-- peregrine: validate useAcc.ast

open Lean Erasure
set_option linter.defProp false

namespace RT
inductive B | f | t

def neg : B → B
  | .f => .t
  | .t => .f

noncomputable def double : Nat → Nat := Nat.rec (motive := fun _ => Nat) 0 (fun _ ih => ih.succ.succ)
noncomputable def useNat : Nat := double 3

noncomputable def len {α : Type} (l : List α) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => ih.succ) l
noncomputable def useList : Nat := len [B.t, B.f, B.t]

inductive Vec (α : Type) : Nat → Type
  | nil : Vec α 0
  | cons {n : Nat} : α → Vec α n → Vec α n.succ

noncomputable def vlast {n : Nat} (v : Vec B n) : B :=
  Vec.rec (motive := fun _ _ => B) B.f (fun a _ ih => match ih with | .f => a | .t => .t) v
noncomputable def useVec : B := vlast (.cons B.t (.cons B.f .nil))

mutual
inductive Ev | zero | succ : Od → Ev
inductive Od | succ : Ev → Od
end

noncomputable def odNeg (o : Od) : B :=
  Od.rec (motive_1 := fun _ => B) (motive_2 := fun _ => B) B.f (fun _ ih => neg ih)
    (fun _ ih => neg ih) o
noncomputable def useMutual : B := odNeg (.succ (.succ (.succ .zero)))

def cast (h : B = B) (b : B) : B := h ▸ b
def useCast : B := cast rfl B.t

noncomputable def andData (h : True ∧ True) : B := And.rec (motive := fun _ => B) (fun _ _ => B.t) h
noncomputable def useAnd : B := andData ⟨trivial, trivial⟩

noncomputable def useOver : B := Bool.rec (motive := fun _ => B → B) id neg true B.t

def propRec (n : Nat) : True := Nat.rec (motive := fun _ => True) trivial (fun _ ih => ih) n

noncomputable def accVal {n : Nat} (h : Acc (· < ·) n) : Nat :=
  Acc.rec (motive := fun _ _ => Nat) (fun k _ _ => k) h
noncomputable def useAcc : Nat := accVal (Acc.intro 0 fun m h => absurd h (Nat.not_lt_zero m))
end RT

/-- The fragment test's verdict on the constant `n` under `nat := .peano`. -/
def check (n : Name) : CoreM Unit := do
  match collectDeps (EnvView.ofEnvironment (← getEnv)) { nat := .peano } (.const n []) with
  | .ok _ => logInfo "in the fragment"
  | .error err => logInfo err.describe

/-- info: in the fragment -/
#guard_msgs in
#eval check ``RT.useNat
/-- info: in the fragment -/
#guard_msgs in
#eval check ``RT.useList
/-- info: in the fragment -/
#guard_msgs in
#eval check ``RT.useVec
/-- info: in the fragment -/
#guard_msgs in
#eval check ``RT.useMutual
/-- info: in the fragment -/
#guard_msgs in
#eval check ``RT.useCast
/-- info: in the fragment -/
#guard_msgs in
#eval check ``RT.useAnd
/-- info: in the fragment -/
#guard_msgs in
#eval check ``RT.useOver
/-- info: in the fragment -/
#guard_msgs in
#eval check ``RT.propRec
/-- info: outside the fragment: recursor Acc.rec, which the eraser keeps as a constant -/
#guard_msgs in
#eval check ``RT.useAcc

/-- The route of the constant `n` under `nat := .peano`. -/
def route? (n : Name) : CoreM Unit := do
  match route (EnvView.ofEnvironment (← getEnv)) { nat := .peano } (.const n []) with
  | .viaPure (.ok _) => logInfo "pure path"
  | .viaPure (.error err) => logInfo s!"pure path, error: {err.describe}"
  | .viaMeta => logInfo "Meta path"

/-- info: pure path -/
#guard_msgs in
#eval route? ``RT.useNat
/-- info: pure path -/
#guard_msgs in
#eval route? ``RT.useList
/-- info: pure path -/
#guard_msgs in
#eval route? ``RT.useVec
/-- info: pure path -/
#guard_msgs in
#eval route? ``RT.useMutual
/-- info: pure path -/
#guard_msgs in
#eval route? ``RT.useCast
/-- info: pure path -/
#guard_msgs in
#eval route? ``RT.useAnd
/-- info: pure path -/
#guard_msgs in
#eval route? ``RT.useOver
/-- info: pure path -/
#guard_msgs in
#eval route? ``RT.propRec
/-- info: Meta path -/
#guard_msgs in
#eval route? ``RT.useAcc

#guard_msgs (drop warning, drop info) in
#erase RT.useNat config {nat := .peano, csimp := false} to "useNat.ast"
#guard_msgs (drop warning, drop info) in
#erase RT.useList config {nat := .peano} to "useList.ast"
#guard_msgs (drop warning, drop info) in
#erase RT.useVec config {nat := .peano} to "useVec.ast"
#guard_msgs (drop warning, drop info) in
#erase RT.useMutual config {nat := .peano} to "useMutual.ast"
#guard_msgs (drop warning, drop info) in
#erase RT.useCast config {nat := .peano} to "useCast.ast"
#guard_msgs (drop warning, drop info) in
#erase RT.useAnd config {nat := .peano} to "useAnd.ast"
#guard_msgs (drop warning, drop info) in
#erase RT.useOver config {nat := .peano} to "useOver.ast"
#guard_msgs (drop warning, drop info) in
#erase RT.propRec config {nat := .peano} to "propRec.ast"
#guard_msgs (drop warning, drop info) in
#erase RT.useNat config {csimp := false} to "useNatMachine.ast"
#guard_msgs (drop warning, drop info) in
#erase RT.useList config {nat := .peano, remove_irrel_constr_args := true} to "useList.meta.ast"
#guard_msgs (drop warning, drop info) in
#erase RT.useAcc config {nat := .peano} to "useAcc.ast"
