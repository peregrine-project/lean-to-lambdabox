/-
Regression test for F-QUOT.

Lean's four quotient primitives have no value, so `Erasure.visitMutual` used to take them down the
body-less-axiom arm: a program using `Quot.mk`/`Quot.lift` erased to one that applies two axioms,
which `peregrine eval` refuses to compile ("Axioms found, use Extract Constant to realize them").
A quotient has no runtime representation beyond its representative, so both are realizable in λbox:
`Quot.mk` is the identity on it and `Quot.lift` applies the lifted function to it.

The test erases a `Quot.lift` program and prints the body-less constants it emits together with the
shape of the realizer registered for each quotient primitive. Nothing may be left body-less, and
the two realizers must be written at the arities the kernel fixes (`Quot.mk` 3, `Quot.lift` 6).
With `FIXES_AST_DIR` set the program is written there, so `scripts/fixes.sh` runs it through
`peregrine validate` and `peregrine eval` — which is what checks that the realizers reduce.
-/
import LeanToLambdaBox.Erasure

open Lean Erasure

-- Every declaration of a test lives in its own namespace, so that the suite's files share the
-- root namespace without colliding.
namespace FQuot

/-- The quotient of `Nat` by equality, on which every function is liftable. -/
def NatQ : Type := Quot (α := Nat) Eq

def mk (n : Nat) : NatQ := Quot.mk Eq n

def double (q : NatQ) : Nat := Quot.lift (fun n => n + n) (fun _ _ h => by subst h; rfl) q

/-- `Quot.lift f h (Quot.mk r a)` must compute `f a`, here `3 + 3`. -/
def quotTest : Nat := double (mk 3)

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

#eval show MetaM Unit from do
  let (p, _) ← erase (.const ``quotTest []) { extern := .preferLogical, nat := .peano, csimp := false }
  let .untyped gdecls _ := p
  let bodyless := gdecls.filterMap fun (kn, d) =>
    match d with | .constantDecl ⟨.none⟩ => some kn.id | _ => none
  IO.println s!"F-QUOT quot: bodyless={bodyless}"
  for n in [``Quot.mk, ``Quot.lift] do
    let kn := toKername n
    let body := gdecls.findSome? fun (k, d) =>
      match d with | .constantDecl ⟨.some t⟩ => if k = kn then some (shape t) else none | _ => none
    IO.println s!"F-QUOT {n}: {body}"
  if let some dir ← IO.getEnv "FIXES_AST_DIR" then
    IO.FS.writeFile s!"{dir}/quot.ast" (Serialize.to_sexpr p).toString

end FQuot
