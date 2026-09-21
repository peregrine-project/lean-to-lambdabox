/-
Regression test for F-ACC.

A λbox `case` on a propositional inductive is collapsed downstream — MetaRocq's
`remove_match_on_box` and `eval_iota_sing` — by substituting `□` for *every* binder of the single
alternative. Lean, unlike Rocq, admits large elimination for a `Prop` whose non-proof fields are
recovered from the result indices: `Acc.intro`'s `x : α` is such a field, and `Acc.casesOn` does
bind it, so collapsing that elimination boxes data and computes a wrong program. `visitCases`
therefore refuses a propositional inductive one of whose constructor fields is not a proof.

The refusal is keyed on the shape and not on a name, so the test checks both halves: `Acc` and a
user-declared inductive of the same shape are refused, while `And`, `Eq` and `Iff` eliminations —
whose fields are all proofs, and which collapse soundly — are still erased.
-/
import LeanToLambdaBox.Erasure

open Lean Erasure

-- Every declaration of a test lives in its own namespace, so that the suite's files share the
-- root namespace without colliding.
namespace FAcc

/-- The `Acc`-shaped elimination: the alternative returns `x`, the field of `Acc.intro` that is
data rather than a proof. Boxing it loses the value. -/
def accData {α : Type} {r : α → α → Prop} {a : α} (h : Acc r a) : α :=
  Acc.casesOn (motive := fun _ _ => α) h (fun x _ => x)

def accTest (h : Acc (fun a b : Nat => a < b) 7) : Nat := accData h

/-- The same shape under another name, so that the refusal is visibly not keyed on `Acc`. -/
inductive Reach (r : Nat → Nat → Prop) : Nat → Prop where
  | intro (x : Nat) (h : ∀ y, r y x → Reach r y) : Reach r x

def reachData (r : Nat → Nat → Prop) (n : Nat) (h : Reach r n) : Nat :=
  Reach.casesOn (motive := fun _ _ => Nat) h (fun x _ => x)

def reachTest (h : Reach (fun a b => a < b) 7) : Nat := reachData _ 7 h

/-- A propositional inductive whose fields are all proofs: the collapse boxes nothing but proofs,
so the guard must accept it. -/
def andData (p q : Prop) (h : p ∧ q) : Nat :=
  And.casesOn (motive := fun _ => Nat) h (fun _ _ => 5)

def andTest : Nat := andData True True ⟨trivial, trivial⟩

/-- The same for `Iff`, and for `Eq`, whose constructor has no field at all. -/
def iffData (p q : Prop) (h : p ↔ q) : Nat :=
  Iff.casesOn (motive := fun _ => Nat) h (fun _ _ => 6)

def iffTest : Nat := iffData True True ⟨fun h => h, fun h => h⟩

def eqData (n : Nat) (h : n = 7) : Nat :=
  Eq.casesOn (motive := fun _ _ => Nat) h 7

def eqTest : Nat := eqData 7 rfl

/-- Erase `name` and report whether `visitCases` refused it. -/
def check (label : String) (name : Name) : MetaM Unit := do
  try
    let (p, _) ← erase (.const name []) { extern := .preferLogical, nat := .peano, csimp := false }
    let .untyped gdecls _ := p
    IO.println s!"F-ACC {label}: accepted declarations={gdecls.length}"
  catch e =>
    -- Normalized to one line, as in the other refusal tests of this suite.
    let msg := (← e.toMessageData.toString).replace "\n" " "
    IO.println s!"F-ACC {label}: refused : {msg}"

#eval show MetaM Unit from do
  check "acc" ``accTest
  check "reach" ``reachTest
  check "and" ``andTest
  check "iff" ``iffTest
  check "eq" ``eqTest

end FAcc
