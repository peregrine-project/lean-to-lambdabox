/-
Regression test for F-EQREC.

A recursor has no compiler value, so `Erasure.visitMutual` used to emit every recursor it reached
as a constant as a body-less axiom — `Fannkuch` ships one, `((MPdot (MPfile ()) "Eq") "rec")`, and
applies it. `peregrine validate` accepts such a file and `peregrine eval` refuses to compile it
("Axioms found, use Extract Constant to realize them"); the benchmarks only run because they hand
peregrine an `.attr` realizer the frontend does not emit.

Rocq has no primitive `Eq.rec` either: `eq_rect` is an ordinary constant whose body is a `match` on
a propositional singleton, which `remove_match_on_box` collapses. `Erasure.recursorRealizer`
synthesizes exactly that body, keyed on the shape the `RecursorVal` and its inductive report and
never on the constant's name.

The test erases three programs that reach a recursor as a constant — `Eq.rec` through `cast`/`▸`,
`And.rec` whose minor takes two proof fields, and `False.rec` whose inductive has no constructor —
and prints the body-less constants each emits and the shape of the synthesized body. Nothing may be
left body-less. With `FIXES_AST_DIR` set the programs are written there, so `scripts/fixes.sh` runs
them through `peregrine validate` and `peregrine eval`, which is what checks that the synthesized
`case` reduces to the minor rather than sticking.
-/
import LeanToLambdaBox.Erasure

open Lean Erasure

-- Every declaration of a test lives in its own namespace, so that the suite's files share the
-- root namespace without colliding.
namespace FEqrec

/-- `cast` and `▸` both leave an `Eq.rec` behind. The erased program applies it to a boxed proof
and must give back the data argument: `3 + 6`. -/
def castTest : Nat :=
  let h : (Nat × Nat) = (Nat × Nat) := rfl
  (cast h (3, 4)).1 + (h ▸ (5, 6)).2

/-- `And.rec` reached as a constant. `And.intro`'s two fields are proofs, so the realizer hands the
minor two `□`; the program must evaluate to 4. -/
def andTest : Nat := And.rec (motive := fun _ => Nat) (fun _ _ => 4) (And.intro trivial trivial)

/-- `False.rec`, whose inductive has no constructor: the body is a `case` with no alternative. The
branch that reaches it needs a proof of `False` and is never taken, but the constant is emitted all
the same, so a program carrying it must still validate and evaluate — here to 2. -/
def deadTest : Nat :=
  let pred : (n : Nat) → n ≠ 0 → Nat := fun n h =>
    match n with
    | 0 => absurd rfl h
    | k + 1 => k
  pred 3 (by decide)

/-- A compact shape of a λbox term: enough to pin a realizer, short enough to read. -/
partial def shape : LBTerm → String
  | .box => "box"
  | .bvar i => s!"bvar {i}"
  | .lambda _ b => s!"λ.{shape b}"
  | .app f a => s!"({shape f} {shape a})"
  | .const kn => s!"const {kn.id}"
  | .construct _ i _ => s!"ctor {i}"
  | .case _ d alts =>
    let alts := ", ".intercalate (alts.map fun (bs, b) => s!"{bs.length}|{shape b}")
    s!"case {shape d} [{alts}]"
  | _ => "?"

/-- Erase `name`, report the body-less constants it emits and the shape of `rec`'s body. -/
def check (label : String) (name rec : Name) : MetaM Unit := do
  let (p, _) ← erase (.const name []) { extern := .preferLogical, nat := .peano, csimp := false }
  let .untyped gdecls _ := p
  let bodyless := gdecls.filterMap fun (kn, d) =>
    match d with | .constantDecl ⟨.none⟩ => some kn.id | _ => none
  let body := gdecls.findSome? fun (k, d) =>
    match d with
    | .constantDecl ⟨.some t⟩ => if k = toKername rec then some (shape t) else none
    | _ => none
  IO.println s!"F-EQREC {label}: bodyless={bodyless} {rec}={body}"
  if let some dir ← IO.getEnv "FIXES_AST_DIR" then
    IO.FS.writeFile s!"{dir}/{label}.ast" (Serialize.to_sexpr p).toString

#eval show MetaM Unit from do
  check "cast" ``castTest ``Eq.rec
  check "and" ``andTest ``And.rec
  check "dead" ``deadTest ``False.rec

end FEqrec
