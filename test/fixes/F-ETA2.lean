/-
Regression test for F-ETA2 (first half: the η path misplaces the supplied prefix).

`visitCtorEtaGo`/`visitCasesEtaGo` saturate an under-applied constructor or eliminator by
pushing fresh variables onto the argument array and erasing the whole application at the
bottom of the loop, *inside* the binders they opened. The arguments the call site had already
supplied therefore ended up under those binders, where weak evaluation re-runs them on every
application of the expansion: the source evaluates the prefix once, `λ x⃗. C a⃗ x⃗` evaluates it
once per application. λ□ is pure, so the value is unchanged — what the placement costs is the
work, unboundedly so for a prefix that is expensive to recompute.

The two programs below each apply such an expansion twice, with `slowSum 12` (a real
computation, not a value) as the misplaced argument: `consSlow` is `@List.cons Nat (slowSum 12)`,
two of `List.cons`'s three arguments, and `elimSlow` is `Nat.casesOn` at a motive, the major
premise `slowSum 12` and the zero alternative, one short of its four.

The test reports, for each emitted body, the spine of binder nodes above its first real node
and the binder depth of every reference to `slowSum`. The prefix is bound once outside the
η binders exactly when the spine starts with the `let`s and the depths are all `0`
(before the fix: `spine=[λ, app]`/`[λ, case]`, `slowSum-depths=[1]`).

With `FIXES_AST_DIR` set both programs are written there; `scripts/fixes.sh` runs them through
`peregrine validate` and `peregrine eval`, which is what checks that the let-bound programs are
well-formed and still compute 3 and 3.
-/
import LeanToLambdaBox.Erasure

open Lean Erasure

namespace FEta2

/-- An effect-free argument that is expensive to recompute: a naive unary sum, 78 additions. -/
def slowSum : Nat → Nat
  | 0 => 0
  | n + 1 => n + 1 + slowSum n

/-- An under-applied constructor: `@List.cons Nat (slowSum 12)`, supplying 2 of 3 arguments. -/
def consSlow : List Nat → List Nat := List.cons (slowSum 12)

/-- Two applications of the expansion; the answer does not depend on the misplaced argument,
so that the evaluation check reads the fix and not the sum. -/
def consTest : Nat := (consSlow []).length + (consSlow [7]).length

/-- An under-applied eliminator: `Nat.casesOn` at a motive, the major premise `slowSum 12` and
the zero alternative, one short of its four arguments. -/
def elimSlow : (Nat → Nat) → Nat := Nat.casesOn (motive := fun _ => Nat) (slowSum 12) 0

def elimTest : Nat := elimSlow (fun _ => 1) + elimSlow (fun _ => 2)

/-- The binder nodes above the first node that is neither a `lambda` nor a `letIn`, and that
node's kind. -/
partial def spine : LBTerm → List String
  | .lambda _ b => "λ" :: spine b
  | .letIn _ _ b => "let" :: spine b
  | .box => ["box"]
  | .bvar _ => ["bvar"]
  | .fvar _ => ["fvar"]
  | .app .. => ["app"]
  | .const _ => ["const"]
  | .construct .. => ["construct"]
  | .case .. => ["case"]
  | .proj .. => ["proj"]
  | .fix .. => ["fix"]
  | .prim _ => ["prim"]

/-- The binder depth of every reference to the constant named `id`. -/
partial def constDepths (id : String) (depth : Nat) : LBTerm → List Nat
  | .const kn => if kn.id == id then [depth] else []
  | .lambda _ b => constDepths id (depth + 1) b
  | .letIn _ v b => constDepths id depth v ++ constDepths id (depth + 1) b
  | .app a b => constDepths id depth a ++ constDepths id depth b
  | .construct _ _ args => args.flatMap (constDepths id depth)
  | .case _ d alts =>
    constDepths id depth d ++ alts.flatMap (fun a => constDepths id (depth + a.1.length) a.2)
  | .proj _ e => constDepths id depth e
  | .fix defs _ => defs.flatMap (fun d => constDepths id (depth + defs.length) d.body)
  | .box | .bvar _ | .fvar _ | .prim _ => []

/-- Erase `top`, report the spine and the `slowSum` depths of the body emitted for `defName`,
and write the program to `$FIXES_AST_DIR/<label>.ast` when that directory is set. -/
def check (label : String) (defName : String) (top : Name) : MetaM Unit := do
  let (p, _) ← erase (.const top []) { extern := .preferLogical, nat := .peano, csimp := false }
  let .untyped gdecls _ := p
  for (kn, d) in gdecls do
    if kn.id == defName then
      match d with
      | .constantDecl ⟨.some t⟩ =>
        IO.println s!"F-ETA2 {label}: spine={spine t} slowSum-depths={constDepths "slowSum" 0 t}"
      | _ => IO.println s!"F-ETA2 {label}: {defName} has no body"
  if let some dir ← IO.getEnv "FIXES_AST_DIR" then
    IO.FS.writeFile s!"{dir}/{label}.ast" (Serialize.to_sexpr p).toString

#eval show MetaM Unit from do
  check "cons" "consSlow" ``consTest
  check "elim" "elimSlow" ``elimTest

end FEta2
