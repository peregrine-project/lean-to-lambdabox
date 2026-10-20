import LeanToLambdaBox

/-!
`ErasureConfig.auto_inline_typeclass_dispatch` considers only non-recursive definitions
(register entry S-9). A recursive definition is erased to a fixpoint and is never marked, even when
it is an instance: `depthInst` is not marked. A non-recursive instance whose method calls a
recursive function contains a reference to that function, not a fixpoint: `instSum` is marked.

Under Peano naturals, peregrine evaluates `useBoth 2` to 6.
-/

-- peregrine: validate useBoth2.ast --attributes=useBoth2.ast.inlinings
-- peregrine: eval useBoth2.ast --attributes=useBoth2.ast.inlinings

class Depth (n : Nat) where val : Nat

def depthInst : (n : Nat) → Depth n
  | 0 => ⟨0⟩
  | n+1 => ⟨(depthInst n).val + 1⟩

attribute [instance] depthInst

def sumTo : Nat → Nat
  | 0 => 0
  | n+1 => (n+1) + sumTo n

class Tbl where get : Nat → Nat

instance instSum : Tbl := ⟨fun i => sumTo i⟩

def useBoth (n : Nat) : Nat := Depth.val (n := 3) + Tbl.get n

#erase useBoth config {auto_inline_typeclass_dispatch := true} to "useBoth.ast"
#erase (useBoth 2) config {nat := .peano, extern := .preferLogical, auto_inline_typeclass_dispatch := true} to "useBoth2.ast"
