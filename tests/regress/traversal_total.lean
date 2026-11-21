import LeanToLambdaBox

/-!
The erasure traversal is a family of total functions, generic over its backend (register entry
S-16):
- the equations of `Erasure.visitExpr`, `Erasure.visitAppArgs` and `Erasure.visitMutual` hold by
  their definitions, for every backend;
- `toBvar` is total and shifts the level under each binder: a λ, the body of a let, a case
  alternative (by its number of binders), the definitions of a fixpoint (by their number);
- with too little fuel the traversal stops with the backend's error, and with enough fuel it gives
  the term that `#erase` gives (`#erase` runs it with `Erasure.travFuel`);
- `#erase` of a program that goes through every function of the traversal is pinned: `all.ast`
  under Peano naturals, which peregrine evaluates to 10, and `go.ast` under the default
  configuration.
-/

-- peregrine: validate all.ast
-- peregrine: eval all.ast

open Lean Erasure

section
variable {m : Type → Type} [Monad m] [Backend m]

example (e : Expr) :
    visitExpr (m := m) 0 e = (Backend.outOfFuel (m := m) "visitExpr" : EraseT m LBTerm) := by
  rw [visitExpr]

example (n : Nat) (x : FVarId) :
    visitExpr (m := m) (n + 1) (.fvar x) =
      (do
        if (← Backend.isErasable (m := m) (← read).lctx (← read).locals (.fvar x)) then
          return .box
        pure (.fvar x) : EraseT m LBTerm) := by
  rw [visitExpr]

example (n : Nat) (f : LBTerm) (args : Array Expr) :
    visitAppArgs (m := m) (n + 1) f args =
      args.foldlM (fun e arg => do return LBTerm.app e (← visitExpr n arg)) f := by
  rw [visitAppArgs]

example (c : Name) :
    visitMutual (m := m) 0 c = (Backend.outOfFuel (m := m) "visitMutual" : EraseT m Unit) := by
  rw [visitMutual]
end

section
private def x : FVarId := ⟨`x⟩
private def y : FVarId := ⟨`y⟩
private def ind : InductiveId := { mutualBlockName := rootKername "T", idx := 0 }

example : toBvar x 0 (.lambda .anon (.app (.fvar x) (.fvar y))) =
    .lambda .anon (.app (.bvar 1) (.fvar y)) := rfl
example : toBvar x 0 (.letIn .anon (.fvar x) (.fvar x)) = .letIn .anon (.bvar 0) (.bvar 1) := rfl
example : toBvar x 2 (.case (ind, 0) (.fvar x) [([.anon, .anon], .fvar x), ([], .fvar x)]) =
    .case (ind, 0) (.bvar 2) [([.anon, .anon], .bvar 4), ([], .bvar 2)] := rfl
example : toBvar x 0 (.fix [⟨.anon, .fvar x, 0⟩, ⟨.anon, .construct ind 0 [.fvar x, .box], 0⟩] 1) =
    .fix [⟨.anon, .bvar 2, 0⟩, ⟨.anon, .construct ind 0 [.bvar 2, .box], 0⟩] 1 := rfl
end

/-- `fun (x : Nat) => x`: `visitExpr` needs fuel 1 for the λ, 1 for `visitLambda` and 1 for the body. -/
def idNat : Expr := .lam `x (.const ``Nat []) (.bvar 0) .default

/-- error: erasure: recursion bound reached in visitExpr -/
#guard_msgs in
#eval show CoreM Unit from do
  let _ ← Erasure.run (visitExpr 2 idNat) {}

/-- info: LBTerm.lambda (BinderName.named "x") (LBTerm.bvar 0) -/
#guard_msgs in
#eval show CoreM LBTerm from do
  let (t, _) ← Erasure.run (visitExpr 3 idNat) {}
  return t

#guard travFuel = 2 ^ 32

namespace Trav

structure Pt where
  x : Nat
  y : Nat

inductive T where
  | a
  | b (n : Nat)

mutual
def ev : Nat → Bool
  | 0 => true
  | n + 1 => od n
def od : Nat → Bool
  | 0 => false
  | n + 1 => ev n
end

/-- A let of a literal, a projection, a match, an η-expanded constructor and mutual recursion. -/
def go (p : Pt) (t : T) : Nat :=
  let k := 2
  match t with
  | .a => p.x + k
  | .b n => if ev n then n else (List.map T.b [n]).length + k

/-- `3 + 4 + 3 = 10`. -/
def all : Nat := go ⟨1, 2⟩ .a + go ⟨0, 0⟩ (.b 4) + go ⟨0, 0⟩ (.b 3)

#guard all = 10

end Trav

#erase Trav.all config {nat := .peano, extern := .preferLogical} to "all.ast"
#erase Trav.go to "go.ast"
