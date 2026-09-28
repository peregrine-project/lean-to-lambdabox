import LeanToLambdaBox

/-!
The definitions that `ErasureConfig.auto_inline_typeclass_dispatch` considers besides instances:
those whose erased body, after its leading λs, is a constant, a projection, or a constructor of index
0 applied to nothing (`LBTerm.isTrivialAlias`; register entry S-11). Marked: the alias `addAlias`,
the constant function `kfun`, the projection function `P.b`, and `falseDef`. Not marked: `trueDef`
(index 1), `noneDef` (a constructor applied to its type parameter) and `pVal` (a structure literal:
a constructor applied to its fields).

Under Peano naturals, peregrine evaluates `useAll 2` to 10.
-/

-- peregrine: validate useAll2.ast --attributes=useAll2.ast.inlinings
-- peregrine: eval useAll2.ast --attributes=useAll2.ast.inlinings

structure P where
  a : Nat
  b : Nat

def pVal : P := ⟨Nat.zero, Nat.succ Nat.zero⟩
def falseDef : Bool := false
def trueDef : Bool := true
def noneDef : Option Nat := none
def seven : Nat := 7
def kfun (_ : Nat) : Nat := seven
def addAlias : Nat → Nat → Nat := Nat.add

def useAll (n : Nat) : Nat :=
  addAlias (pVal.b + kfun n) (if falseDef || trueDef then noneDef.getD n else 0)

#erase useAll config {auto_inline_typeclass_dispatch := true} to "useAll.ast"
#erase (useAll 2) config {nat := .peano, extern := .preferLogical, auto_inline_typeclass_dispatch := true} to "useAll2.ast"
