/-
Regression test for F-ETA (every emitted recursive body is a bare unapplied `.fix`).

`visitMutual` registered the body of a recursive declaration as `.fix defs i`. Such a body
runs — λ□ treats an unapplied fixpoint as a value and unfolds it on application — but it
falsifies `EEtaExpandedFix.expanded` (`metarocq/erasure/theories/EEtaExpandedFix.v:46-54`),
which admits a `.fix` only under an argument spine longer than the selected member's
principal argument index. That predicate is the declared precondition of
`guarded_to_unguarded_fix`, the first pass of peregrine's verified untyped pipeline, and
nothing downstream checks it: peregrine's own discharge is `Admitted` and `validate` does
not look.

The test erases one singly recursive and one mutually recursive program and reports, for
each, the shape of the registered body and the number of `expanded` violations in the whole
emitted environment — the fixpoint clause above, the λ-headedness of every member body, and
the self-reference clause (a de Bruijn reference to a member carries at least
`principalArgIdx + 1` arguments), checked with MetaRocq's own context discipline.

Before the fix: `sumTo=fix#0`, `isEven=fix#0`, `isOdd=fix#1`, and one violation per
registered fixpoint. After: the bodies are `λ.app(fix#i,bvar0)` and no violations remain.

With `FIXES_AST_DIR` set both programs are written there; `scripts/fixes.sh` runs them
through `peregrine validate` and `peregrine eval`, which is what checks that the wrapped
bodies are well-formed and still compute 6 and `Bool.true`.
-/
import LeanToLambdaBox.Erasure

open Lean Erasure

namespace FEta

/-- A singly recursive definition: its body is registered as a one-member fixpoint. -/
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => n + 1 + sumTo n

def sumTest : Nat := sumTo 3

-- A two-member block, so that the wrapper is exercised at both fixpoint indices.
mutual
  def isEven : Nat → Bool
    | 0 => true
    | n + 1 => isOdd n
  def isOdd : Nat → Bool
    | 0 => false
    | n + 1 => isEven n
end

def parityTest : Bool := isEven 4

/-- The outer shape of a term, down to the first node that is none of `lambda`/`app`/`fix`. -/
partial def shape : LBTerm → String
  | .lambda _ b => s!"λ.{shape b}"
  | .app f a => s!"app({shape f},{shape a})"
  | .fix _ i => s!"fix#{i}"
  | .bvar n => s!"bvar{n}"
  | _ => "_"

/-- The violations of the fixpoint clauses of `EEtaExpandedFix.expanded` in `t`.
`Γ` is MetaRocq's context — the number of arguments demanded at each bound variable, `0` at
an ordinary binder and `principalArgIdx + 1` at a fixpoint member, innermost first — and
`nargs` is the length of the argument spine the term sits under. -/
partial def violations (Γ : List Nat) (nargs : Nat) : LBTerm → List String
  | .app f a => violations Γ (nargs + 1) f ++ violations Γ 0 a
  | .bvar n =>
    match Γ[n]? with
    | some m => if m ≤ nargs then [] else [s!"self-reference under {nargs} of {m} arguments"]
    | none => []
  | .lambda _ b => violations (0 :: Γ) 0 b
  | .letIn _ v b => violations Γ 0 v ++ violations (0 :: Γ) 0 b
  | .case _ d alts =>
    violations Γ 0 d ++
      alts.flatMap (fun (ns, b) => violations (List.replicate ns.length 0 ++ Γ) 0 b)
  | .proj _ e => violations Γ 0 e
  | .construct _ _ args => args.flatMap (violations Γ 0)
  | .fix defs i =>
    let Γ' := defs.reverse.map (fun d => d.principalArgIdx + 1) ++ Γ
    let spine := match defs[i]? with
      | some d => if d.principalArgIdx < nargs then [] else [s!"fixpoint under {nargs} arguments"]
      | none => ["fixpoint selects no member"]
    let headed := defs.filterMap (fun d =>
      match d.body with | .lambda .. => none | _ => some "member body is not λ-headed")
    spine ++ headed ++ defs.flatMap (fun d => violations Γ' 0 d.body)
  | .box | .fvar _ | .const _ | .prim _ => []

/-- Erase `top`, report the shape of the body registered for each name in `names` and the
number of `expanded` violations over the whole emitted environment, and write the program to
`$FIXES_AST_DIR/<label>.ast` when that directory is set. -/
def check (label : String) (names : List String) (top : Name) : MetaM Unit := do
  let (p, _) ← erase (.const top []) { extern := .preferLogical, nat := .peano, csimp := false }
  let .untyped gdecls _ := p
  let bodies := gdecls.filterMap (fun (kn, d) =>
    match d with | .constantDecl ⟨.some t⟩ => some (kn.id, t) | _ => none)
  for n in names do
    for (id, t) in bodies do
      if id == n then IO.println s!"F-ETA {label}: {n}={shape t}"
  let bare := bodies.countP (fun (_, t) => match t with | .fix .. => true | _ => false)
  let viol := bodies.flatMap (fun (_, t) => violations [] 0 t)
  IO.println s!"F-ETA {label}: bare-fix-bodies={bare} expanded-violations={viol.length}"
  if let some dir ← IO.getEnv "FIXES_AST_DIR" then
    IO.FS.writeFile s!"{dir}/{label}.ast" (Serialize.to_sexpr p).toString

#eval show MetaM Unit from do
  check "sum" ["sumTo"] ``sumTest
  check "parity" ["isEven", "isOdd"] ``parityTest

end FEta
