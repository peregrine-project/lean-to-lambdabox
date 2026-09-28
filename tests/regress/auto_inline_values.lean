import LeanToLambdaBox

/-!
`ErasureConfig.auto_inline_typeclass_dispatch` marks a constant only if its erased body is a value
(register entry S-8). Inlining a body that computes would compute it again at every use, while the
constant is computed once.

- `instSlow` is a constructor applied to a computation, and `instLet` computes before building its
  dictionary: neither is marked.
- `instLam` computes only under a λ: it is marked.

Under Peano naturals, peregrine evaluates `useAll 2` to 25.
-/

-- peregrine: validate useAll2.ast --attributes=useAll2.ast.inlinings
-- peregrine: eval useAll2.ast --attributes=useAll2.ast.inlinings

def slowSum : Nat → Nat
  | 0 => 0
  | n+1 => (n+1) + slowSum n

class Tbl where get : Nat → Nat

instance instSlow : Inhabited Nat := ⟨slowSum 4⟩
instance instLet : Tbl := let s := slowSum 4; ⟨Nat.add s⟩
instance instLam : Tbl := ⟨fun i => slowSum i⟩

def useAll (n : Nat) : Nat :=
  instSlow.default + Tbl.get (self := instLet) n + Tbl.get (self := instLam) n

#erase useAll config {auto_inline_typeclass_dispatch := true} to "useAll.ast"
#erase (useAll 2) config {nat := .peano, extern := .preferLogical, auto_inline_typeclass_dispatch := true} to "useAll2.ast"
