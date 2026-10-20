import LeanToLambdaBox

/-!
Smoke test: the README example under the default configuration, and a closed recursive program
under Peano naturals with logical `@[extern]` definitions, which peregrine can evaluate.
-/

-- peregrine: validate readme.ast --attributes=readme.ast.inlinings
-- peregrine: validate fact3.ast --attributes=fact3.ast.inlinings
-- peregrine: eval fact3.ast

def val_at_false (f : Bool → Nat) : Nat := f .false
#erase val_at_false to "readme.ast" mli "readme.mli"

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n
#erase (fact 3) config {nat := .peano, extern := .preferLogical} to "fact3.ast"
