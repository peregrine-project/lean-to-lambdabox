/-
Regression test for F-SPARSE.

Lean compiles a `match` that examines some constructors and leaves the rest to a catch-all to a
*sparse* `casesOn` auxiliary. `Erasure.visitCases` used to look the inductive up under the
auxiliary's name prefix — the enclosing function, not the inductive — panic, and emit a box for the
whole elimination, so the run still exited 0 and wrote a program computing the wrong value.

The test erases two such programs and prints, for each, the shape of every `case` node of the
emitted program: the binder count of each alternative, and how many nodes disagree with the
constructors of the inductive they eliminate. A λbox `case` has one alternative per constructor, in
constructor order, binding that constructor's fields, so `bad-case-arities` must be 0 and the
elimination must be present rather than boxed away.

With `FIXES_AST_DIR` set the two programs are also written there; `scripts/fixes.sh` runs them
through `peregrine validate` and `peregrine eval`, which is what checks the value they compute.
-/
import LeanToLambdaBox.Erasure

open Lean Erasure

-- Every declaration of a test lives in its own namespace, so that the suite's files share the
-- root namespace without colliding.
namespace FSparse

inductive Shape where
  | dot
  | seg (a : Nat)
  | tri (a b c : Nat)

/-- `Shape.dot` is covered and the catch-all of `pick._sparseCasesOn_1` stands for `Shape.seg` and
`Shape.tri`, whose expanded alternatives bind one and three fields. Its body is the variable `k`,
bound outside the match, so the alternatives also exercise the claim that a body moved under those
binders keeps its variables. -/
def pick (k : Nat) (s : Shape) : Nat :=
  match s with
  | .dot => 0
  | _ => k

def pickTest : Nat := pick 5 (.tri 7 8 9)

/-- A three-way list match inside a recursive function: the shape of the `Quicksort` benchmark,
where the finding was measured. -/
def qsPartition (pivot : Nat) (l : List Nat) : List Nat × List Nat :=
  match l with
  | [] => ([], [])
  | x :: xs =>
    let (lo, hi) := qsPartition pivot xs
    if x < pivot then (x :: lo, hi) else (lo, x :: hi)

def qsFuel (fuel : Nat) (l : List Nat) : List Nat :=
  match fuel with
  | 0 => l
  | fuel' + 1 =>
    match l with
    | [] => []
    | [x] => [x]
    | pivot :: rest =>
      let (lo, hi) := qsPartition pivot rest
      qsFuel fuel' lo ++ [pivot] ++ qsFuel fuel' hi

def qsSorted : List Nat → Bool
  | [] => true
  | [_] => true
  | x :: y :: rest => x <= y && qsSorted (y :: rest)

/-- Sorting `[3, 1, 2]` and digesting the result, so that `peregrine eval` sees the value and not
just the shape of the list: 3 when the three elements come back sorted, 0 otherwise. -/
def qsTest : Nat :=
  let l := qsFuel 9 [3, 1, 2]
  if qsSorted l then l.length else 0

/-- The λbox arity of every constructor of every inductive declared in `gdecls`, keyed by the
printed `InductiveId` that `case` nodes carry. -/
def ctorArities (gdecls : GlobalDeclarations) : List (String × List Nat) :=
  gdecls.flatMap fun (kn, d) =>
    match d with
    | .constantDecl _ => []
    | .inductiveDecl body =>
      body.bodies.zipIdx.map fun (b, idx) =>
        ((repr ({ mutualBlockName := kn, idx } : InductiveId)).pretty, b.ctors.map (·.nargs))

/-- Every `case` node of the term: the printed id of the inductive it eliminates, paired with the
binder count of each of its alternatives. -/
partial def caseShapes : LBTerm → List (String × List Nat)
  | .case (indid, _) discr alts =>
    ((repr indid).pretty, alts.map (·.1.length))
      :: (caseShapes discr ++ alts.flatMap (fun (_, b) => caseShapes b))
  | .lambda _ b => caseShapes b
  | .letIn _ v b => caseShapes v ++ caseShapes b
  | .app a b => caseShapes a ++ caseShapes b
  | .construct _ _ args => args.flatMap caseShapes
  | .proj _ e => caseShapes e
  | .fix defs _ => defs.flatMap (fun d => caseShapes d.body)
  | .box | .bvar _ | .fvar _ | .const _ | .prim _ => []

/-- Erase `name`, report the `case` shapes of the emitted program, and write it to
`$FIXES_AST_DIR/<label>.ast` when that directory is set. `full` also prints the shapes themselves,
which is readable only for a small program. -/
def check (label : String) (name : Name) (full : Bool) : MetaM Unit := do
  let (p, _) ← erase (.const name []) { extern := .preferLogical, nat := .peano, csimp := false }
  let .untyped gdecls term := p
  let arities := ctorArities gdecls
  let bodies := gdecls.filterMap fun (_, d) =>
    match d with | .constantDecl ⟨.some t⟩ => some t | _ => none
  let shapes := (bodies ++ term.toList).flatMap caseShapes
  let bad := shapes.filter fun (k, ns) => arities.lookup k != some ns
  let shown := if full then s!"case-shapes={shapes.map (·.2)} " else ""
  IO.println s!"F-SPARSE {label}: {shown}bad-case-arities={bad.length}"
  for (k, ns) in bad do
    IO.println s!"F-SPARSE   {k}: alternatives {ns}, constructors {arities.lookup k}"
  if let some dir ← IO.getEnv "FIXES_AST_DIR" then
    IO.FS.writeFile s!"{dir}/{label}.ast" (Serialize.to_sexpr p).toString

#eval show MetaM Unit from do
  check "pick" ``pickTest (full := true)
  check "quicksort" ``qsTest (full := false)

end FSparse
