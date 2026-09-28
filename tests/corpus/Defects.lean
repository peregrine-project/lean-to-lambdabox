import LeanToLambdaBox

/-!
Corpus examples that reproduce defects listed under "Reported, not fixed" in
`doc/SHIPPING-CHANGES.md`. Each block names its register entry. The emitted files record the
current behaviour, so a fix shows up in a corpus diff.
-/

namespace Defects

/-! R-1: machine-mode literals are printed as quoted strings, `(primInt "7")`. -/
def seven : Nat := 7
#erase seven to "primint.ast"

/-! R-2: string atoms are not escaped. -/
def «ns"q».f (n : Nat) : Nat := n
#erase («ns"q».f 1) config {nat := .peano, extern := .preferLogical} to "quote_modpath.ast"

inductive «Q"T» where | «m"k»
def useQ : «Q"T» → Nat | .«m"k» => 0
#erase (useQ .«m"k») config {nat := .peano, extern := .preferLogical} to "quote_inductive.ast"

/-! R-3: two distinct names map to the same kername. -/
def colA.«a b» : Nat := 1
def colA.a_u32b : Nat := 2
#erase (colA.«a b» + colA.a_u32b) config {nat := .peano, extern := .preferLogical} to "collide.ast"

/-! R-4: unsupported literals panic and are erased to `□`. -/
#erase "abc" to "strlit.ast"
#erase (5000000000000000000 : Nat) to "biglit.ast"

/-! R-5: an alternative whose type is a Π only after unfolding gets a branch with no binders. -/
def MyFun := Nat → Nat
def g : MyFun := fun x => x
def viaCases (n : Nat) : Nat := @Nat.casesOn (fun _ => Nat) n 0 g
#erase (viaCases 3) config {nat := .peano, extern := .preferLogical} to "nonsyn_pi.ast"

/-! R-7: a match on a proof of a large-eliminating Prop inductive (here `And`). -/
def andElim (p q : Prop) (h : p ∧ q) : Nat := match h with | ⟨_, _⟩ => 7
#erase (andElim True True ⟨trivial, trivial⟩) config {nat := .peano, extern := .preferLogical} to "and_elim.ast"

/-! R-8: an informative field that is also an index of a large-eliminating Prop inductive. -/
inductive Foo : Nat → Nat → Prop where
  | mk (n : Nat) : Foo 0 n
noncomputable def getN (m : Nat) (h : Foo 0 m) : Nat := Foo.casesOn (motive := fun _ _ _ => Nat) h (fun n => n)
#erase (getN 1 (Foo.mk 1)) config {nat := .peano, extern := .preferLogical} to "index_field.ast"

/-! R-9: recursors become axioms (`Eq.rec` for a cast, recursor axioms under well-founded recursion). -/
def castTo (α : Type) (h : α = Nat) (x : α) : Nat := h ▸ x
#erase (castTo Nat rfl 3) config {nat := .peano, extern := .preferLogical} to "eq_cast.ast"

def log2 (n : Nat) : Nat := if n < 2 then 0 else 1 + log2 (n / 2)
termination_by n
decreasing_by omega
#erase (log2 8) config {nat := .peano, extern := .preferLogical} to "wf_rec.ast"

/-! R-10: a projection out of a recursive structure, which gets no projection declarations. -/
structure RS where
  val : Nat
  kids : List RS
def rsVal (r : RS) : Nat := r.val
#erase (rsVal ⟨3, []⟩) config {nat := .peano, extern := .preferLogical} to "rec_struct_proj.ast"

/-! R-12: `@[inline]` on a member of a mutual block is not recorded in the `.inlinings` file. -/
mutual
@[inline] def fooI (n : Nat) : Nat := match n with | 0 => 0 | n + 1 => barI n
def barI (n : Nat) : Nat := match n with | 0 => 1 | n + 1 => fooI n
end
#erase fooI to "mutual_inline.ast"

/-! R-13: `@[implemented_by]` is ignored: `#eval fastId 2` gives 2, the erased program gives 3. -/
def slowId (n : Nat) : Nat := n
@[implemented_by slowId] def fastId (n : Nat) : Nat := n + 1
#erase (fastId 2) config {nat := .peano, extern := .preferLogical} to "implemented_by.ast"

/-! R-14: a type hidden behind an irreducible alias is not erased. -/
@[irreducible] def MyType : Type 1 := Type
noncomputable def mkT : MyType := by unfold MyType; exact Nat
def useT (_x : MyType) : Nat := 3
#erase (useT mkT) config {nat := .peano, extern := .preferLogical} to "irreducible_alias.ast"

/-! R-17: the `.mli` signature falls back to `unit` for an unsupported result type. -/
inductive MyNat where
  | z
  | s (n : MyNat)
def toMy : Nat → MyNat
  | 0 => .z
  | n + 1 => .s (toMy n)
#erase toMy to "mli_fallback.ast" mli "mli_fallback.mli"

end Defects
