import LeanToLambdaBox

/-!
`ErasureConfig.auto_inline_typeclass_dispatch` does not mark a constant tagged `@[noinline]`
(register entry S-10). The instance `instNo` and the alias `addNo` carry the attribute and are not
marked; `instYes` and `addYes`, the same without it, are marked.

Under Peano naturals, peregrine evaluates `useAll 2` to 8.
-/

-- peregrine: validate useAll2.ast --attributes=useAll2.ast.inlinings
-- peregrine: eval useAll2.ast --attributes=useAll2.ast.inlinings

class OpNo where op : Nat → Nat
class OpYes where op : Nat → Nat

@[noinline] instance instNo : OpNo := ⟨fun n => n.succ⟩
instance instYes : OpYes := ⟨fun n => n.succ⟩

@[noinline] def addNo : Nat → Nat → Nat := Nat.add
def addYes : Nat → Nat → Nat := Nat.add

def useAll (n : Nat) : Nat := addNo (OpNo.op n) (addYes (OpYes.op n) n)

#erase useAll config {auto_inline_typeclass_dispatch := true} to "useAll.ast"
#erase (useAll 2) config {nat := .peano, extern := .preferLogical, auto_inline_typeclass_dispatch := true} to "useAll2.ast"
