import LeanToLambdaBox

/-!
Corpus near-miss programs, OUTSIDE the verification scope, for contrast with
`Examples.lean`. Each one adds exactly one excluded feature to a Church-numeral program: a Nat
literal, a structure projection, a match, structural recursion, a quotient, a `partial def`, an
unassigned metavariable, a universe metavariable. Each program is erased under `{nat := .peano}` to
`<name>.peano.ast` and under the default configuration to `<name>.default.ast`; the readouts
(`NM_R_*`) under `{nat := .peano}` only.
-/

namespace NM

universe u

def CNat : Type 1 := ∀ α : Type, (α → α) → α → α
def two : CNat := fun _ s z => s (s z)
def three : CNat := fun _ s z => s (s (s z))
def pid {α : Sort u} (a : α) : α := a

/-- OUT: a Nat literal. -/
def natLit : Nat := 3

/-- OUT: a structure projection (`Pair.fst` is defined by `Expr.proj`). -/
structure Pair (α β : Type 1) where
  fst : α
  snd : β
def pairFst : CNat := (Pair.mk two three).fst

/-- OUT: a match (compiled to a matcher over `Nat.casesOn`). -/
def isZeroNat : Nat → Bool
  | .zero => true
  | .succ _ => false
def matchEx : Bool := isZeroNat (Nat.succ Nat.zero)

/-- OUT: structural recursion on `Nat` (`Nat.rec`/`brecOn`). -/
def church : Nat → CNat
  | .zero => fun _ _ z => z
  | .succ n => fun α s z => s (church n α s z)
def church3 : CNat := church (Nat.succ (Nat.succ (Nat.succ Nat.zero)))

/-- OUT: a quotient (`Quot.mk`, `Quot.lift`; `Quot.lift`'s type mentions `Eq`). -/
def quotEx : CNat :=
  Quot.lift (fun n : CNat => n) (fun _ _ (h : False) => h.elim) (Quot.mk (fun _ _ => False) two)

/-- OUT: a `partial def` (needs an `Inhabited` instance, a structure). -/
instance : Inhabited CNat := ⟨two⟩
partial def spin (n : CNat) : CNat := spin n
def spinEx : CNat := spin two

end NM

#erase NM.natLit config {nat := .peano} to "NM_natLit.peano.ast"
#erase NM.natLit to "NM_natLit.default.ast"
#erase NM.pairFst config {nat := .peano} to "NM_pairFst.peano.ast"
#erase NM.pairFst to "NM_pairFst.default.ast"
#erase (NM.pairFst Nat Nat.succ Nat.zero) config {nat := .peano} to "NM_R_pairFst.peano.ast"
#erase NM.matchEx config {nat := .peano} to "NM_matchEx.peano.ast"
#erase NM.matchEx to "NM_matchEx.default.ast"
#erase NM.church3 config {nat := .peano} to "NM_church3.peano.ast"
#erase NM.church3 to "NM_church3.default.ast"
#erase (NM.church3 Nat Nat.succ Nat.zero) config {nat := .peano} to "NM_R_church3.peano.ast"
#erase NM.quotEx config {nat := .peano} to "NM_quotEx.peano.ast"
#erase NM.quotEx to "NM_quotEx.default.ast"
#erase NM.spinEx config {nat := .peano} to "NM_spinEx.peano.ast"
#erase NM.spinEx to "NM_spinEx.default.ast"
-- OUT: an unassigned metavariable in the erased term. `#erase` fails and writes no file;
-- `#guard_msgs` pins the error up to the metavariable's unique id, which depends on what the file
-- elaborates before it.
/-- error: unknown metavariable -/
#guard_msgs (error, substring := true) in
#erase (_ : NM.CNat) config {nat := .peano} to "NM_mvar.peano.ast"
/-- error: unknown metavariable -/
#guard_msgs (error, substring := true) in
#erase (_ : NM.CNat) to "NM_mvar.default.ast"
-- OUT: a universe metavariable in the erased term (`@NM.pid.{?u}`).
#erase @NM.pid config {nat := .peano} to "NM_levelMVar.peano.ast"
#erase @NM.pid to "NM_levelMVar.default.ast"

