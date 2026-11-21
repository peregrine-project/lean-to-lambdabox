import LeanToLambdaBox

/-!
Erasure steps that rely on Lean APIs whose form changes between Lean releases:
- the projections of a structure are declared with its inductive type (`Pt` in `ptSum.ast`);
- an ASCII binder name is kept and a non-ASCII one (`α₁`) becomes anonymous (`names.ast`);
- a `@[csimp]` replacement is applied when `csimp` is on, the default (`useSlow.ast` refers to
  `fast`), and not when it is off (`useSlow.nocsimp.ast` refers to `slow`);
- a `@[csimp]` replacement that is `@[macro_inline]` is inlined (`useSlowIf.ast` has no constant
  `fastIf`), as `Bool.and` is replaced by `Bool.Internal.and` since Lean v4.35.
`csimp` and `macro_inline` are steps of the `Meta` path only, so `useSlow` and `useSlowIf` are
`unsafe`, which puts them outside the fragment of the pure path (register entry S-29).
-/

-- peregrine: validate ptSum.ast
-- peregrine: validate names.ast
-- peregrine: validate useSlow.ast
-- peregrine: validate useSlowIf.ast

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

unsafe def useSlow (n : N) : N := slow n
#erase useSlow to "useSlow.ast"
#erase useSlow config {csimp := false} to "useSlow.nocsimp.ast"

def slowIf (b : Bool) (x y : N) : N := match b with | true => x | false => y
@[macro_inline] def fastIf (b : Bool) (x y : N) : N := match b with | true => x | false => y
@[csimp] theorem slowIf_eq_fastIf : @slowIf = @fastIf := rfl

unsafe def useSlowIf (b : Bool) (n : N) : N := slowIf b n .z
#erase useSlowIf to "useSlowIf.ast"

end Api
