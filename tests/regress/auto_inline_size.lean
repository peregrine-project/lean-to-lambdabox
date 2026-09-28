import LeanToLambdaBox

/-!
`ErasureConfig.auto_inline_typeclass_dispatch` marks a constant only if its body, with the marked
constants inlined into it, has at most `Erasure.autoInlineMaxSize` nodes (register entry S-7).

- `instMonadSt`, the `Monad` instance of a state monad, is a large dictionary: it is not marked.
- `i0` to `i3` form a chain of instances, each calling the method of the previous one twice. Every
  body has at most 12 nodes, but each step more than doubles the inlined size: `i0` and `i1` are
  marked, `i2` is not, and `i3`, which then refers to `i2` without inlining it, is marked.

Under Peano naturals, peregrine evaluates `chain 2` to 10 and `(twice 3).1` to 7.
-/

-- peregrine: validate chain2.ast --attributes=chain2.ast.inlinings
-- peregrine: eval chain2.ast --attributes=chain2.ast.inlinings
-- peregrine: validate twice3.ast --attributes=twice3.ast.inlinings
-- peregrine: eval twice3.ast --attributes=twice3.ast.inlinings

def St (σ α : Type) := σ → α × σ

instance instMonadSt : Monad (St σ) where
  pure a := fun s => (a, s)
  bind m f := fun s => let (a, s') := m s; f a s'

def tick : St Nat Nat := fun s => (s, s + 1)

def twice : St Nat Nat := do
  let a ← tick
  let b ← tick
  pure (a + b)

class C0 where f : Nat → Nat
class C1 where f : Nat → Nat
class C2 where f : Nat → Nat
class C3 where f : Nat → Nat

instance i0 : C0 := ⟨fun n => n.succ⟩
instance i1 : C1 := ⟨fun n => C0.f (C0.f n)⟩
instance i2 : C2 := ⟨fun n => C1.f (C1.f n)⟩
instance i3 : C3 := ⟨fun n => C2.f (C2.f n)⟩

def chain (n : Nat) : Nat := C3.f n

#erase twice config {auto_inline_typeclass_dispatch := true} to "twice.ast"
#erase chain config {auto_inline_typeclass_dispatch := true} to "chain.ast"

#erase (twice 3).1 config {nat := .peano, extern := .preferLogical, auto_inline_typeclass_dispatch := true} to "twice3.ast"
#erase (chain 2) config {nat := .peano, extern := .preferLogical, auto_inline_typeclass_dispatch := true} to "chain2.ast"
