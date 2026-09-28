import LeanToLambdaBox

/-!
`ErasureConfig.auto_inline_typeclass_dispatch` (register entry S-2, claim C2). It is off by default,
so `default.*` and `off.*` are equal. Turned on, the program `on.ast` is still equal to `default.ast`,
and `on.ast.inlinings` also lists the instance and projection chain of `+` and of the literal `1`.
Under Peano naturals (`default3`, `on3`: equal up to hygienic binder names), peregrine evaluates the
program to 3 with either inlinings file.
-/

-- peregrine: validate on3.ast --attributes=on3.ast.inlinings
-- peregrine: eval default3.ast --attributes=default3.ast.inlinings
-- peregrine: eval on3.ast --attributes=on3.ast.inlinings

def addOne (n : Nat) : Nat := n + 1

#erase addOne to "default.ast"
#erase addOne config {auto_inline_typeclass_dispatch := false} to "off.ast"
#erase addOne config {auto_inline_typeclass_dispatch := true} to "on.ast"

#erase (addOne 2) config {nat := .peano, extern := .preferLogical} to "default3.ast"
#erase (addOne 2) config {nat := .peano, extern := .preferLogical, auto_inline_typeclass_dispatch := true} to "on3.ast"
