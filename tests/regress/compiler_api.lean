import LeanToLambdaBox

/-!
The eraser code that calls Lean APIs whose form differs between Lean v4.22 and v4.33 (register
entry S-12), each on an input that exercises it:
- `register_inductive`: the projections of a structure (`Pt`);
- `fvar_to_name`: an ASCII binder name is kept, a non-ASCII one (`α₁`) becomes anonymous;
- `csimpReplaceConstants`: `List.foldr` is replaced by `List.foldrTR` when `csimp` is on (the
  default), and kept when it is off;
- `Erasure.visitCases`: the alternatives of `Nat.casesOn` and `Int.casesOn` in machine mode, and of
  the `casesOn` of a user inductive.
Every match covers all constructors and has no wildcard.
-/

-- peregrine: validate all.ast
-- peregrine: eval all.ast

structure Pt where
  x : Nat
  y : Nat

def ptSum (p : Pt) : Nat := p.x + p.y
#erase ptSum to "ptSum.ast" mli "ptSum.mli"

def names (a : Nat) (α₁ : Nat) : Nat := a + α₁
#erase names to "names.ast"

def sumFoldr (l : List Nat) : Nat := l.foldr (· + ·) 0
#erase sumFoldr to "sumFoldr.ast"
#erase sumFoldr config {csimp := false} to "sumFoldr.nocsimp.ast"

def natCase : Nat → Nat
  | 0 => 3
  | n + 1 => n
#erase natCase to "natCase.ast" mli "natCase.mli"

def intCase : Int → Nat
  | .ofNat n => n
  | .negSucc n => n + 5
#erase intCase to "intCase.ast" mli "intCase.mli"

inductive Tri where
  | a
  | b (n : Nat)
  | c (m k : Nat)

def triVal : Tri → Nat
  | .a => 1
  | .b n => n
  | .c m k => m + k
#erase triVal to "triVal.ast"

/-- `2 + 3 + 7 + 5 + 4 = 21`; `sumFoldr` is left out, as `List.foldrTR` reaches the axiom `False.rec`. -/
def all : Nat :=
  ptSum ⟨1, 1⟩ + natCase 0 + intCase (.negSucc 2) + triVal (.c 2 3) + names 1 3
#erase all config {nat := .peano, extern := .preferLogical} to "all.ast"
