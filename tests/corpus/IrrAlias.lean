import LeanToLambdaBox

/-!
Corpus examples inside the verification scope whose types are proposition sorts or Π-types only
through an `@[irreducible]` alias (the cross-check's probe programs `useFI`, `useLamHR`, `pidHR`).
Each program is erased under `{nat := .peano}` to `<name>.peano.ast` and under the default
configuration to `<name>.default.ast`.
-/

namespace Irr

def CNat : Type 1 := ∀ α : Type, (α → α) → α → α
def two : CNat := fun _ s z => s (s z)
def succ (n : CNat) : CNat := fun α s z => s (n α s z)
def six : CNat := fun _ s z => s (s (s (s (s (s z)))))

def IProp : Type := Prop
axiom R : IProp
axiom hR : R
def guardR (_ : R) (n : CNat) : CNat := n
/-- A function type behind an alias that becomes irreducible below. -/
def EndoC : Type 1 := CNat → CNat
def fI : EndoC := succ
def useFI : CNat := fI two
universe u
def pid {α : Sort u} (a : α) : α := a
/-- `hR` passed by value to a polymorphic identity at `Sort 0` (no binder typed by `R`). -/
def pidHR : R := pid hR
/-- A function returning a proof of `R`; its type `CNat → R` is a proposition only through
`IProp`. -/
theorem lamHR : CNat → R := fun _ => hR
attribute [irreducible] IProp EndoC
/-- `lamHR two` passed to `guardR`. -/
noncomputable def useLamHR : CNat := guardR (lamHR two) six

end Irr

-- `#erase` fails on `useFI` and `useLamHR` (R-14): the `Meta` type inference behind the eraser's
-- erasability test does not unfold the `@[irreducible]` aliases. `#guard_msgs` pins the error;
-- no file is written.
/--
error: function expected
  Irr.fI Irr.two
-/
#guard_msgs (error) in
#erase Irr.useFI config {nat := .peano} to "useFI.peano.ast"
/--
error: function expected
  Irr.fI Irr.two
-/
#guard_msgs (error) in
#erase Irr.useFI to "useFI.default.ast"
/--
error: type expected
  Irr.R
-/
#guard_msgs (error) in
#erase Irr.useLamHR config {nat := .peano} to "useLamHR.peano.ast"
/--
error: type expected
  Irr.R
-/
#guard_msgs (error) in
#erase Irr.useLamHR to "useLamHR.default.ast"
#erase Irr.pidHR config {nat := .peano} to "pidHR.peano.ast"
#erase Irr.pidHR to "pidHR.default.ast"
