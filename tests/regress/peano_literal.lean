import LeanToLambdaBox

/-!
`Nat` literals with `nat := .peano`. A literal up to `Erasure.peanoMaxLiteral` becomes that many
`Nat.succ` applications: peregrine evaluates `small.ast` to 3. A larger literal is an error that
names the literal and the declaration it occurs in, here a dependency of the erased term; before
this check, the eraser recursed once per unit and Lean crashed with a stack overflow on literals
such as the bound 1114112 in `Char.ofNat`, a dependency of `List.getD`. `hugeIfZero` takes the
`Meta` path (its closure has the recursive `Nat.beq`), `huge` the pure path, whose errors `#erase`
reports after "erasure failed:".
-/

-- peregrine: validate small.ast
-- peregrine: eval small.ast

namespace PeanoLiteral

def small : Nat := 3

def huge : Nat := 18446744073709551616
def hugeIfZero (n : Nat) : Nat := if n = 0 then huge else n

end PeanoLiteral

#erase PeanoLiteral.small config {nat := .peano} to "small.ast"

/--
error: #erase: the Nat literal 18446744073709551616 in PeanoLiteral.huge exceeds 65536, the largest literal that `nat := .peano` erases to `Nat.succ` applications
-/
#guard_msgs (error, drop info) in
#erase PeanoLiteral.hugeIfZero 1 config {nat := .peano} to "huge.ast"

/--
error: erasure failed: #erase: the Nat literal 18446744073709551616 in PeanoLiteral.huge exceeds 65536, the largest literal that `nat := .peano` erases to `Nat.succ` applications
-/
#guard_msgs (error, drop info) in
#erase PeanoLiteral.huge config {nat := .peano} to "huge.ast"
