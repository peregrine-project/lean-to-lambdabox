import LeanToLambdaBox

/-!
Types and proofs behind an `@[irreducible]` definition. The kernel ignores reducibility, so `IProp`
is `Prop`, `Endo` is `B → B` and `MyType` is `Type`, and the eraser must see through them:
- `hR` and `pidHR` are proofs of `R : IProp` and are erased to □;
- `negI .f` applies a function whose type is `Endo`;
- `lamHR .f` is a proof of `R` whose type is a proposition only through `IProp`;
- `mkT` is a type whose type is `MyType`, and is erased to □.
Peregrine evaluates `check.ast` to `B.t`. Without the fix, `#erase` kept `hR` and `pidHR` as
axioms, on which Peregrine's evaluator stops, kept `mkT` as code, and failed on `negI .f`
(`function expected`) and on `lamHR .f` (`type expected`).
-/

-- peregrine: validate check.ast
-- peregrine: eval check.ast

namespace Irr

inductive B | f | t

def neg : B → B
  | .f => .t
  | .t => .f

def IProp : Type := Prop
axiom R : IProp
axiom hR : R
def guardR (_ : R) (b : B) : B := b
universe u
def pid {α : Sort u} (a : α) : α := a
set_option linter.defProp false in
def pidHR : R := pid hR
theorem lamHR : B → R := fun _ => hR

def Endo : Type := B → B
def negI : Endo := neg
def useFI : B := negI .f

attribute [irreducible] IProp Endo

-- Lean's compiler does not see through `IProp` either, so these are `noncomputable`.
noncomputable def useGuard : B := guardR hR .t
noncomputable def usePid : B := guardR pidHR .t
noncomputable def useLamHR : B := guardR (lamHR .f) .t

@[irreducible] def MyType : Type 1 := Type
noncomputable def mkT : MyType := by unfold MyType; exact B
def useT (_ : MyType) : B := .t

noncomputable def check : B :=
  match useFI, useGuard, usePid, useLamHR, useT mkT with
  | .t, .t, .t, .t, .t => .t
  | _, _, _, _, _ => .f

end Irr

#erase Irr.check to "check.ast"
