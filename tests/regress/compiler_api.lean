import LeanToLambdaBox

/-!
Erasure steps that rely on Lean APIs whose form changes between Lean releases:
- the projections of a structure are declared with its inductive type (`Pt` in `ptSum.ast`);
- an ASCII binder name is kept and a non-ASCII one (`α₁`) becomes anonymous (`names.ast`);
- a `@[csimp]` replacement is applied when `csimp` is on, the default (`useSlow.ast` refers to
  `fast`), and not when it is off (`useSlow.nocsimp.ast` refers to `slow`).
-/

-- peregrine: validate ptSum.ast
-- peregrine: validate names.ast
-- peregrine: validate useSlow.ast

namespace Api

inductive N | z | s (n : N)

structure Pt where
  x : N
  y : N

def ptSum (p : Pt) : N := .s (.s p.y)
#erase ptSum to "ptSum.ast"

def names (a : N) (α₁ : N) : Pt := ⟨a, α₁⟩
#erase names to "names.ast"

def slow (n : N) : N := n
def fast (n : N) : N := n
@[csimp] theorem slow_eq_fast : @slow = @fast := rfl

def useSlow (n : N) : N := slow n
#erase useSlow to "useSlow.ast"
#erase useSlow config {csimp := false} to "useSlow.nocsimp.ast"

end Api
