/-
Regression test for F-PROP.

`OneInductiveBody.propositional` is MetaRocq's `ind_propositional`, and
`erases_mutual_inductive_body` (`Extract.v:276`) states it as an *equality* with
`isPropositionalArity` of the source declaration's arity — so a hard-wired `false` is as wrong as a
hard-wired `true`. It is also load-bearing: `remove_match_on_box` (`EOptimizePropDiscr.v:48`) and
`eval_iota_sing` (`EWcbvEval.v:162`) both key on it, so with the flag false an elimination of a
`Prop` — whose discriminee erases to `□` — is **stuck**, in peregrine's evaluator as in the
verified pipeline.

The test erases a `Prop` elimination (`And`, `Eq`) and an ordinary data program, and prints the
flag of every inductive each one emits. The eliminations must come out flagged, `Nat`/`Bool`/`List`
and the rest must not, and with `FIXES_AST_DIR` set the emitted programs are written there so that
`scripts/fixes.sh` runs them through `peregrine validate` and `peregrine eval` — which is what
checks that the flagged `case` reduces rather than sticking.
-/
import LeanToLambdaBox.Erasure

open Lean Erasure

-- Every declaration of a test lives in its own namespace, so that the suite's files share the
-- root namespace without colliding.
namespace FProp

/-- An elimination of `And` into data. Both fields of `And.intro` are proofs, so the downstream
collapse boxes only proofs and the program `peregrine eval` sees must evaluate to 5. -/
def andData (p q : Prop) (h : p ∧ q) : Nat :=
  And.casesOn (motive := fun _ => Nat) h (fun _ _ => 5)

def andTest : Nat := andData True True ⟨trivial, trivial⟩

/-- The same for `Eq`, whose constructor has no field at all. -/
def eqData (n : Nat) (h : n = 7) : Nat :=
  Eq.casesOn (motive := fun _ _ => Nat) h 3

def eqTest : Nat := eqData 7 rfl

/-- An ordinary data program: every inductive it emits must stay unflagged. -/
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => n + 1 + sumTo n

def dataTest : Nat := (List.range 3).length + sumTo 0

/-- Erase `name` and report the `propositional` flag of every inductive body it emits. -/
def check (label : String) (name : Name) : MetaM Unit := do
  let (p, _) ← erase (.const name []) { extern := .preferLogical, nat := .peano, csimp := false }
  let .untyped gdecls _ := p
  let flags := gdecls.flatMap fun (_, d) =>
    match d with
    | .constantDecl _ => []
    | .inductiveDecl body => body.bodies.map fun b => (b.name, b.propositional)
  IO.println s!"F-PROP {label}: {flags.mergeSort (fun a b => a.1 <= b.1)}"
  if let some dir ← IO.getEnv "FIXES_AST_DIR" then
    IO.FS.writeFile s!"{dir}/{label}.ast" (Serialize.to_sexpr p).toString

#eval show MetaM Unit from do
  check "prop-and" ``andTest
  check "prop-eq" ``eqTest
  check "data" ``dataTest

end FProp
