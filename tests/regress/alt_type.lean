import LeanToLambdaBox

/-!
A `casesOn` alternative whose type is a function type only after unfolding: an alias of a function
type (`viaAlias`), or a type family that computes to one (`viaFamily`). The eraser reduces the type
to weak head normal form to find the alternative's binders. Peregrine evaluates `check.ast` to
`B.t`, meaning that every function returns Lean's value; without the reduction, the eraser panicked
and emitted the alternative as □ with no binders, and the λ□ `case` was stuck.
-/

-- peregrine: validate check.ast
-- peregrine: eval check.ast

namespace AltType

inductive B | f | t

abbrev Fn2 := B → B → B
def first : Fn2 := fun a _ => a
def viaAlias (p : B × B) : B := Prod.casesOn (motive := fun _ => B) p first

def Sel : Bool → Type
  | true => B → B
  | false => B
def idB : Sel true := fun b => b
def viaFamily (o : Option B) : B := Option.casesOn (motive := fun _ => B) o .f idB

def check : B :=
  match viaAlias (.t, .f), viaFamily (some .t) with
  | .t, .t => .t
  | _, _ => .f

end AltType

#erase AltType.check to "check.ast"
