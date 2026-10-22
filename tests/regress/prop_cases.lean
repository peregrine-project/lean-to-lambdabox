import LeanToLambdaBox

/-!
A `casesOn` with a data motive on a proof: `And`, `Eq` and `True` have subsingleton elimination, so
Lean allows it. The proof is erased to □, and a λ□ `case` on □ reduces to its only branch, with □
for the fields, only if the inductive is declared `propositional`. `PUnit.{u} : Sort u` is a proof
at level 0 (`viaPUnit`, and `viaPoly` called at level 0), but its one λ□ declaration serves every
level and is not `propositional`. So the eraser emits no `case` on an inductive whose sort may be
`Prop`: it gives the alternative □ for each field, as the λ□ `case` on □ would. A field of such a
constructor that is not a proof is an index of its type (`Idx.mk`'s `b`); the eraser passes the
alternative the `casesOn`'s index argument for it instead (`viaIdx`). Peregrine evaluates
`check.ast` to `B.t`, meaning that every function returns Lean's value; with a `case` on □ of
`PUnit` it fails with "branch not found", and without the index argument `viaIdx` returns □.
-/

-- peregrine: validate check.ast
-- peregrine: eval check.ast

namespace PropCases

inductive B | f | t

def viaAnd (h : True ∧ True) : B := And.casesOn (motive := fun _ => B) h (fun _ _ => .t)
def viaEq (h : B.t = B.t) : B := Eq.casesOn (motive := fun _ _ => B) h .t
def viaTrue (h : True) : B := True.casesOn (motive := fun _ => B) h .t
/-- The same through a matcher. -/
def viaMatch (h : True ∧ True) : B := match h with | ⟨_, _⟩ => .t
inductive Idx : B → B → Prop | mk (b : B) : Idx .f b
def viaIdx (h : Idx .f .t) : B := Idx.casesOn (motive := fun _ _ _ => B) h (fun b => b)
def viaPUnit : B := @PUnit.casesOn.{1, 0} (fun _ => B) PUnit.unit .t
def viaPoly.{u} (x : PUnit.{u}) : B := PUnit.casesOn (motive := fun _ => B) x .t

def check : B :=
  match viaAnd ⟨trivial, trivial⟩, viaEq rfl, viaTrue trivial, viaMatch ⟨trivial, trivial⟩,
      viaIdx (.mk .t), viaPUnit, viaPoly.{0} .unit with
  | .t, .t, .t, .t, .t, .t, .t => .t
  | _, _, _, _, _, _, _ => .f

end PropCases

#erase PropCases.check to "check.ast"
