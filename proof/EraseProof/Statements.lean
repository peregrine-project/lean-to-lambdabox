import EraseProof.Spec

/-!
# The statements

The statements of the four theorems whose statements `proof/spec.pin` pins (check C12b), each as a
definition of type `Prop`: the final theorem `erase_correct`, the relation-level simulation
`erases_correct`, the correctness of the pure traversal `erasePure_erases`, and the lower bound
`collectDeps_ok_of` of the final theorem's fragment hypothesis. Check C12 (`proof/tools/Report.lean`)
compares the type of each theorem, once it is proved, with its statement here (kernel
definitional equality).

The theorems are about the logical definitions of the shipping functions `Erasure.collectDeps`,
`Erasure.erasePure` and `Erasure.eraseEntry`. What `#erase` runs is their compiled code, and it
then prints the program and writes the `.inlinings` file; Lean's compiler and runtime, the printer
and the command's elaboration code are trusted, as `doc/DIVERGENCES.md` ("Trust base") lists.
-/

open Lean Erasure
open Metalean (Defeq)

namespace EraseProof

/-- The statement of `erases_correct`, the relation-level simulation: an erasure, with erased
dependencies, of a typed source term that evaluates, evaluates in λ□ to an erasure of the source
value. The inductive blocks of the evaluation environment have distinct λ□ names
(`BlockNamesInj`) and syntactic arities as types (`ArityTypes`), as the fragment test checks on the
closure. Reference: `erases_correct` (`MR E/ErasureCorrectness.v:51`); MC §7.3, Thm 7.3. -/
def erases_correct_statement : Prop :=
  ∀ {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P : List ConstantInfo}
    {σ : EvalEnv} {lps : List Name} {lenv : GlobalDeclarations} {e : Expr} {tb : LBTerm} {v : Expr},
    ProgEnv P ζ E B → Metalean.EnvWF E → SubEnv σ.decls P → KernameInj σ.decls →
    BlockNamesInj σ.decls → ArityTypes σ.decls → LenvClosed lenv →
    ∀ {t : Metalean.Expr ζ lps.length 0},
      TrM E B lps .nil [] e t → (∃ T, E[.nil] ⊢ t : T) →
      Erases E B lps σ .nil [] e tb → ErasesDeps E B σ lenv tb → SrcEval σ e v →
      ∃ vb, Erases E B lps σ .nil [] v vb ∧ LBEval defaultFlags lenv tb vb

/-- The statement of `collectDeps_ok_of`, a lower bound of the fragment test: a typed program whose
read closure is inside the fragment (`ReadClosed`, `PhaseIDecl`, `PlainExpr`, recursors read only in
the shape `RecInFragment` admits (`RecShaped`), no name collision, within the fuel) is accepted by
`Erasure.collectDeps`. It covers the recursors and, under `structural := .kernel`, the structural
recursion that the fragment admits. It shows that the hypothesis `hfrag` of
`erase_correct_statement` does not make the theorem empty. Reference: none (DV-26). -/
def collectDeps_ok_of_statement : Prop :=
  ∀ {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P decls : List ConstantInfo}
    {lps : List Name} {e : Expr} {t : Metalean.Expr ζ lps.length 0} {view : EnvView}
    {cfg : ErasureConfig},
    ProgEnv P ζ E B → ViewAgrees view P → TrM E B lps .nil [] e t → (∃ T, E[.nil] ⊢ t : T) →
    cfg.remove_irrel_constr_args = false → SubEnv decls P → ReadClosed decls e →
    (∀ ci ∈ decls, PhaseIDecl view cfg decls ci) →
    (PlainExpr cfg e ∧ ∀ ci ∈ decls, ∀ x, ReadExpr decls ci x → PlainExpr cfg x) →
    (RecShaped cfg decls e ∧ ∀ ci ∈ decls, ∀ x, ReadExpr decls ci x → RecShaped cfg decls x) →
    KernameInj decls → BlockNamesInj decls → decls.length ≤ collectFuel →
    ∃ decls', collectDeps view cfg e = .ok decls'

/-- The statement of `erasePure_erases`: the output of the pure traversal on the closure that the
fragment test returns is an erasure of the input with erased dependencies, in a closed λ□
environment. Reference: `erase_correct`, its erasure part (`MR E/ErasureFunctionProperties.v:172`,
`MR E/ErasureFunction.v:1309`). -/
def erasePure_erases_statement : Prop :=
  ∀ {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P decls : List ConstantInfo}
    {lps : List Name} {e : Expr} {view : EnvView} {cfg : ErasureConfig} {p : Program}
    {inl : List Kername},
    ProgEnv P ζ E B → Metalean.EnvWF E → ViewAgrees view P →
    ∀ {t : Metalean.Expr ζ lps.length 0},
      TrM E B lps .nil [] e t → (∃ T, E[.nil] ⊢ t : T) →
      collectDeps view cfg e = .ok decls → erasePure view cfg decls e = .ok (p, inl) →
      ∃ lenv tb, p = .untyped lenv (some tb) ∧
        Erases E B lps (evalEnvOf view cfg decls) .nil [] e tb ∧
        ErasesDeps E B (evalEnvOf view cfg decls) lenv tb ∧ LenvClosed lenv

/-- The statement of `erase_correct`, the final theorem: partial correctness of `#erase` on the
fragment. If the program `P` is the Lean form of a well-formed Metalean environment (`henv`, `hwf`),
the view `#erase` reads agrees with `P` (`hview`), the input `e` is the Lean form of a closed, typed
Metalean term `t` (`he`, `hty`), the fragment test accepts `e` (`hfrag`), the entry point behind
`#erase` returns the program `p` (`hrun`) and `e` evaluates to `v` (`hev`), then `p` is an untyped
λ□ program whose main term evaluates in λ□ (at `default_wcbv_flags`) to an erasure of `v`, and `v`
is the Lean form of a term definitionally equal to `t` at each of its types (subject reduction:
the source evaluation is Metalean conversion). Reference: `erase_correct`
(`MR E/ErasureFunctionProperties.v:657`), with subject reduction (`MR P/PCUICSR.v`,
`subject_reduction_eval`); MC §7.3–7.4.

Scope.
* `ProgEnv P ζ E B` asks every declaration of `P` to be the Lean form of a Metalean declaration,
  and `ViewAgrees view P` asks the view `#erase` reads to agree with `P` on the names of `P`. For
  `P` the whole environment of a Lean file (all of `EnvView.ofEnvironment`, which contains `Init`)
  the premises are unsatisfiable, since `Init` contains declarations that Metalean cannot express
  (`unsafe` definitions, and nested inductives such as `Lean.Syntax`). An application takes for
  `P` the program's dependency closure, a list of declarations closed under the constants their
  types and values mention, and a view that agrees with it on those names: the view of the
  closure alone, as the non-vacuity instance `EraseProof.Test.NV1` uses (six declarations), or
  the view of the whole environment that `#erase` builds.
* The result is partial correctness: it assumes that the source evaluates (`hev`). Metalean
  proves neither canonicity nor normalization, and the call-by-value relation `SrcEval` is tied to
  Metalean only through definitional equality (the last conjunct), so nothing here shows that a
  typed program evaluates.
* Programs defined by well-founded recursion are excluded. The fragment test rejects them (their
  definitions have a compiled `_unsafe_rec` companion), and the theorem could say nothing about
  them anyway: their recursion reduces only through the accessibility proof, and proofs are opaque
  in Metalean (theorems have no δ, DV-24), so the source does not evaluate them and `hev` never
  holds.
* The fragment has no recursive definitions. By default the fragment test rejects structural
  recursion as well (every recursive definition has a compiled `_unsafe_rec` companion, `Nat.add`
  and `Nat.beq` included), so `Nat` arithmetic of `Init` is outside it. Under
  `structural := .kernel` it admits a definition by structural recursion
  (`Erasure.isStructuralRecursive`): its kernel definition is not recursive, it recurses through
  `T.brecOn`, whose value is the first projection of a `T.rec` into the pairs of a value and its
  table of recursive calls `T.below`, and the eraser erases it as any definition. A mutual
  structural block (definitions that share `all`) is not the Lean form of Metalean definitions
  (`ProgEnv.defn`), and the source semantics has no recursor ι on a Nat literal, so the theorem
  says nothing about either.
  Programs recurse through recursors: the
  test admits `T.rec` of a single inductive without indices that eliminates into every sort, whose
  induction hypotheses take no arguments and are about the last fields of their constructor
  (`RecInFragment`), and other recursors only as the companions of `casesOn` that the traversal does
  not read. Nat literals are in the fragment only under `nat := .peano`; under the default
  `nat := .machine` the test rejects them, with `Nat.zero`, `Nat.succ` and `Nat.casesOn`.
* The fragment admits programs on which the source evaluation is stuck where λ□ evaluation is not
  necessarily: they use opaques with a value (no δ, DV-10; the eraser emits the value), axioms of
  data type, `@[extern]` definitions under the default `extern := .preferAxiom` (no δ, DV-12), or
  `casesOn` on a lemma of an inductive with proof fields (DV-24). A source evaluation that needs
  to unfold such a constant or to match on such a lemma is stuck, so `hev` does not
  hold and the theorem says nothing about the program, although the emitted λ□ program may
  compute a value: `Ex.opaqueEx` of `tests/corpus/Examples.lean`, the successor of
  `opaque opaqueTwo : CNat := two`, is in the fragment, and its source evaluation is stuck at
  `opaqueTwo` while λ□ unfolds the emitted value. -/
def erase_correct_statement : Prop :=
  ∀ {P decls : List ConstantInfo} {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ}
    {view : EnvView} {cfg : ErasureConfig} {lps : List Name}
    {e v : Expr} {t : Metalean.Expr ζ lps.length 0}
    {p : Program} {inl : List Kername},
    (henv  : ProgEnv P ζ E B) →
    (hwf   : Metalean.EnvWF E) →
    (hview : ViewAgrees view P) →
    (he    : TrM E B lps .nil [] e t) →
    (hty   : ∃ T, E[.nil] ⊢ t : T) →
    (hfrag : collectDeps view cfg e = .ok decls) →
    (hrun  : eraseEntry view cfg e = pure (p, inl)) →
    (hev   : SrcEval (evalEnvOf view cfg P) e v) →
    ∃ lenv tb vb, p = .untyped lenv (some tb) ∧
      Erases E B lps (evalEnvOf view cfg P) .nil [] v vb ∧
      LBEval defaultFlags lenv tb vb ∧
      ∀ T, E[.nil] ⊢ t : T → ∃ t', TrM E B lps .nil [] v t' ∧ E[.nil] ⊢ t ≡ t' : T

end EraseProof
