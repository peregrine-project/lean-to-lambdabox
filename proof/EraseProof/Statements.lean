import EraseProof.Spec

/-!
# The statements

The statements whose definitions `proof/spec.pin` pins (check C12b), each a sorry-free definition
of type `Prop`: the final theorem `erase_correct`, the relation-level simulation `erases_correct`,
the correctness of the pure traversal `erasePure_erases`, the meaning of the source evaluation in
con-leche's model `srcEval_sound`, the lower bound `collectDeps_ok_of` of the fragment hypothesis,
the first-order corollary `erase_correct_firstorder`; and the lemmas on which the final theorem's
hypotheses rest: that `Sound` has content (`sound_nonvacuous`), that a proof certificate means a
proof (`clCert_proof_pt`), that the marking is a function of the input (`markOf_det`) defined
wherever the traversal runs (`markOf_exists`), and that the closure is part of the program
(`collectDeps_sub`). Check C12 (`proof/tools/Report.lean`) compares the type of each theorem, once it
is proved, with its statement here. Layout as `ML-V Statements.lean`; every con-leche premise
stands where that file has a Metalean typing premise.

The theorems are about the logical definitions of the shipping functions `Erasure.collectDeps`,
`Erasure.erasePure` and `Erasure.eraseEntry`, and they read the shipping oracle
`Erasure.Pure.isErasable` through `MarkOf`. Lean's compiler, the printer and the command's
elaboration code are trusted.
-/

open Lean Erasure

namespace EraseProof

/-- The statement of `erases_correct`, the relation-level simulation: an erasure, with erased
dependencies, of a marked source term that evaluates, evaluates in λ□ to an erasure of the source
value. No typing premise and no certificate (`noCert`): con-leche (`env`) occurs only through the
run-time certificates of `SrcEval`, which the simulation does not read. The closure facts are
those the fragment test checks (`KernameInj`, `BlockNamesInj`: DV-14; `ArityTypes`: DV-32), and
the shape facts con-leche's frontend and `DeclsOf?` check of an accepted program (`CtorsListed`,
`NatShaped`, `NatCtors`, `RecsShaped`). Port
of `ML-V Statements.lean:29`. Reference: `erases_correct` (`MR E/ErasureCorrectness.v:51`), whose
`wf_ext Σ` and typing premises have no counterpart (DV-32); MC §7.3, Thm 7.3. -/
def erases_correct_statement : Prop :=
  ∀ {env : ConLeche.Env} {σ : EvalEnv} {lenv : GlobalDeclarations} {ê v : Expr} {tb : LBTerm},
    KernameInj σ.decls → BlockNamesInj σ.decls → ArityTypes σ.decls → CtorsListed σ.decls →
    NatShaped σ → NatCtors σ → RecsShaped σ.decls → LenvClosed lenv → Erases noCert σ [] ê tb →
    ErasesDeps noCert σ lenv tb → SrcEval env σ ê v →
    ∃ vb, Erases noCert σ [] v vb ∧ LBEval defaultFlags lenv tb vb

/-- The statement of `collectDeps_ok_of`, a lower bound of the fragment test: a program that
con-leche accepts, with an input con-leche types, whose read closure is inside the fragment, is
accepted by `Erasure.collectDeps`. It shows that the hypothesis `hfrag` of `erase_correct_statement`
does not make the theorem empty. Port of `ML-V Statements.lean:47`, with `ConLecheAccepts` and
`CLTyped` where that file has Metalean's environment and typing. Reference: none (DV-26). -/
def collectDeps_ok_of_statement : Prop :=
  ∀ {P decls : List ConstantInfo} {env : ConLeche.Env} {e : Expr} {view : EnvView}
    {cfg : ErasureConfig},
    ConLecheAccepts P env → ViewAgrees view P → CLTyped env e →
    cfg.remove_irrel_constr_args = false → SubEnv decls P → ReadClosed decls e →
    (∀ ci ∈ decls, PhaseIDecl view cfg decls ci) →
    (PlainExpr cfg e ∧ ∀ ci ∈ decls, ∀ x, ReadExpr decls ci x → PlainExpr cfg x) →
    (RecShaped cfg decls e ∧ ∀ ci ∈ decls, ∀ x, ReadExpr decls ci x → RecShaped cfg decls x) →
    PreRead view cfg decls →
    KernameInj decls → BlockNamesInj decls → decls.length ≤ collectFuel →
    ∃ decls', collectDeps view cfg e = .ok decls'

/-- The statement of `erasePure_erases`: on the closure the fragment test returns, part of a
program con-leche accepts (`ConLecheAccepts`, `SubEnv`: so every value mentions only earlier
declarations and the inductive blocks are consistent), if no declaration the traversal erases by
its value has a compiled pre-definition and every value of the closure that the traversal erases
has a marking (`ValuesMarkedOf`), the output of the pure traversal is an erasure of the
marking of the input (`MarkOf`, the traversal's own decisions), with erased dependencies, in a
closed λ□ environment. No typing premise on the input and no certificate (`noCert`): the `□`
decisions are the marks. Port of `ML-V Statements.lean:65`, with con-leche's acceptance where that
file has Metalean's environment. Reference: `erases_erase` (`MR E/ErasureFunction.v:1228`) and
`erase_global_erases_deps` (`MR E/ErasureFunctionProperties.v:172`); DV-32, DV-35. -/
def erasePure_erases_statement : Prop :=
  ∀ {P decls : List ConstantInfo} {env : ConLeche.Env} {e ê : Expr} {view : EnvView}
    {cfg : ErasureConfig} {p : Program} {inl : List Kername},
    ConLecheAccepts P env → SubEnv decls P → NoPreDefs view cfg decls →
    collectDeps view cfg e = .ok decls → erasePure view cfg decls e = .ok (p, inl) →
    ValuesMarkedOf decls cfg → MarkOf decls cfg [] e ê →
    ∃ lenv tb, p = .untyped lenv (some tb) ∧
      Erases noCert (evalEnvOf view cfg decls) [] ê tb ∧
      ErasesDeps noCert (evalEnvOf view cfg decls) lenv tb ∧ LenvClosed lenv

/-- The statement of `srcEval_sound`: the marked source evaluation preserves meaning in every
con-leche model of the accepted program: if the closure `decls` is part of the program (`SubEnv`: the
values δ unfolds are those con-leche checked), `e` is typed by con-leche and carries no mark key
(`NoMarkKeys`), the closure `decls` carries none (`NoMarkKeysDecls`; the program con-leche accepts
is clean), `ê` is a marking of it and `ê` evaluates to `v` in the closure (DV-41), then `unmark v` has a con-leche form that denotes what `e` denotes wherever
that is not the proof point (`Sound`). Proved from con-leche's model (`checkDeclsPure_sound_of`,
the claims of `checkSoundAtP5`) and the run-time certificates of `SrcEval`. Reference: none
(subject reduction, `MR P/PCUICSR.v`, has no con-leche counterpart; DV-34). -/
def srcEval_sound_statement.{w} : Prop :=
  ∀ {P decls : List ConstantInfo} {env : ConLeche.Env} {view : EnvView} {cfg : ErasureConfig}
    {e ê v : Expr},
    ConLecheAccepts P env → SubEnv decls P → CLTyped env e → NoMarkKeys e = true →
    NoMarkKeysDecls decls = true → MarkOf decls cfg [] e ê →
    SrcEval env (evalEnvOf view cfg decls) ê v → Sound.{w} env e v

/-- The statement of `erase_correct`, the final theorem: partial correctness of `#erase` on the
fragment, against con-leche. If con-leche's pure fold accepts the program `P` with environment
`env` (`hacc`; `P`'s Lean records are consistent as Lean's kernel generates them, `DeclsOf?`),
con-leche types the input `e` (`hty`), `e` carries no mark key in its metadata (`hclean`: the marks'
anonymous key, which elaboration never writes), the view `#erase` reads agrees with `P` and the compiled
pre-definitions it holds for `P`'s declarations name only constants of `P` (`hview`), the fragment
test accepts `e` with the closure `decls` (`hfrag`), no declaration of the
closure that the traversal erases by its value has a compiled pre-definition (`hnopre`), the entry
point behind `#erase` returns the program `p` (`hrun`), `ê` is `e` with the eraser's erasability
decisions marked on it (`hmark`), con-leche types `ê` and a marking of the value of every constant
of the closure whose value the traversal erases (`ErasedValue`), and certifies each of their
marks, as a proof or a type former in the context of its enclosing binders, the discriminant of
each reduced `casesOn` as a proof (`hcert`), and
`ê` evaluates to `v` in the closure, as `#erase` computes it (`hev`, DV-41), then `p` is an untyped λ□
program whose main term is an erasure of `ê`, and whose environment holds erasures of its
dependencies, both over the closure, with every `□` of a mark, and the discriminant of every
reduced `casesOn`, con-leche-certified; the main term evaluates in λ□ (at
`default_wcbv_flags`) to an erasure of `v`; and `v` means what `e` means in every con-leche model
of `env` (`Sound`). Reference: `erase_correct` (`MR E/ErasureFunctionProperties.v:657`), with
subject reduction (`MR P/PCUICSR.v`) replaced by `Sound`; MC §7.3–7.4.

Scope.
* The theorem does not prove that the eraser's erasure decisions are irrelevant to the
  computation: the source semantics evaluates the marked term, in which an erased subterm is a
  frozen value (DV-32). If the eraser erases a subterm the computation needs, the marked
  evaluation is stuck or `hcert` fails, and the theorem says nothing about that program.
* Every `□` of the emitted program that the relation pairs with a mark stands for a subterm that
  con-leche types as a proof (it then denotes the proof point, `clCert_proof_pt_statement`) or as
  a type former (a syntactic verdict of the checker, with no model content) in its context, the
  context's binder domains checked by typing the marked term as a whole (`hcert`, `CLTypedAt`,
  `CLCert`). The `□` placeholders of a reduced `casesOn` stand for the fields of a discriminant
  con-leche types as a proof. The other `□`s of the emitted program are justified by declaration
  conditions and the fragment test: the direct-mode placeholders of a recursor's fixpoint rest on
  `RecFixOf`'s declaration condition (a `Prop` inductive or no fields) and on the fragment test,
  which admits only recursors without indices and with large elimination
  (`recShapeInFragment`, `recStaysConstant`). A `□` of the λ□ value under a binder is a certified mark with evaluated values
  substituted, which con-leche does not check again; a `□` the value's evaluation forms (the
  placeholders `markErase (proj I j d)` of `SrcEval.casesFrozen`, `frozenApp`) is justified by the
  step's `CLProofTerm` (resp. `CLErasable`).
* The λ□ inductive declarations are related only in their parameter count, constructor counts and
  arities, and `propositional` (`ErasesInd`); their names, `kelim` and projection lists
  (`projs`) are output metadata that no theorem relates.
* `hev` evaluates in the closure (`evalEnvOf view cfg decls`), and the erasure relation of the
  conclusion (`Erases`, `ErasesDeps`, with the markings `ErasesDecl` reads) is over the closure
  too: δ unfolds only declarations the eraser reads, marked over them, as the eraser marks them.
  The closure is part of `P` (`collectDeps_sub_statement`), so con-leche's acceptance of `P`
  applies to it; MetaRocq evaluates in the whole global environment (DV-3, DV-41).
* The marks are the shipping oracle's (`Erasure.Pure.isErasable`, read through `MarkOf`), which is
  not verified; `hcert` checks each of its answers on this program: on the input, and on the value
  of every constant of the closure that the traversal erases (`ErasedValue`: not a theorem, not a
  recognized `casesOn`), also one whose body the emitted environment does not hold. A program on
  which the oracle has no marking of such a value, or con-leche does not certify one, is outside
  the theorem (DV-37).
* The source evaluation carries con-leche's run-time certificates (`CLOk`, `CLErasable`,
  `CLProofTerm`, `IotaNoCertAt`, `FrozenFieldsCert`, DV-33): a rule that forms a redex or a data
  value from evaluated parts asks con-leche to type it, and a `casesOn` step asks that con-leche's
  ι step fires on its major premise without a certificate, or, on a proof with fields, with the
  certificate it checks.
* `Sound` is conditional on the input's meaning not being the proof point, and it is not type
  preservation (DV-34).
* Partial correctness: `hev` is assumed; con-leche proves no normalisation (DV-17).
* Out of the fragment: user axioms (con-leche declines them, DV-36), structural recursion through
  compiled pre-definitions, which is the default `structural := .unsafeRec` (`hnopre`, DV-35;
  under `structural := .kernel` it is in), well-founded recursion, `partial`, `unsafe` and
  `implemented_by` code, mutual definitions, nested inductives, `nat := .machine`, strings,
  `remove_irrel_constr_args` (DV-26). -/
def erase_correct_statement.{w} : Prop :=
  ∀ {P decls : List ConstantInfo} {env : ConLeche.Env} {view : EnvView} {cfg : ErasureConfig}
    {e ê v : Expr} {p : Program} {inl : List Kername},
    (hacc   : ConLecheAccepts P env) →
    (hty    : CLTyped env e) →
    (hclean : NoMarkKeys e = true) →
    (hview  : ViewAgrees view P) →
    (hfrag  : collectDeps view cfg e = .ok decls) →
    (hnopre : NoPreDefs view cfg decls) →
    (hrun   : eraseEntry view cfg e = pure (p, inl)) →
    (hmark  : MarkOf decls cfg [] e ê) →
    (hcert  : ProgCert env decls cfg ê) →
    (hev    : SrcEval env (evalEnvOf view cfg decls) ê v) →
    ∃ lenv tb vb, p = .untyped lenv (some tb) ∧
      Erases (CLCert env) (evalEnvOf view cfg decls) [] ê tb ∧
      ErasesDeps (CLCert env) (evalEnvOf view cfg decls) lenv tb ∧
      Erases noCert (evalEnvOf view cfg decls) [] v vb ∧
      LBEval defaultFlags lenv tb vb ∧
      Sound.{w} env e v

/-- The statement of `erase_correct_firstorder`: under the hypotheses of `erase_correct` other
than `hcert`, with a marking of every value of the closure that the traversal erases (`hvals`, the
part of `hcert` that is not a con-leche check; `erasePure_erases_statement` takes it) and the
closure `decls` free of mark keys (`hcleanD`), if the value `v` is first-order (a constructor
tree with frozen and literal leaves), the main term of the emitted program evaluates in λ□ to its
structural erasure `foErase` (frozen leaves ↦ `□`, literals ↦ Peano numerals), con-leche types
`v`, every leaf erased to `□` is a subterm that con-leche types as a proof or a type former, and
`v` means what `e` means in every con-leche model of `env` (`Sound`). Port of
`ML-V FirstOrder.lean:132`. Reference:
`erase_correct_strong` (`MR E/ErasureFunctionProperties.v:2269`); DV-27, DV-34. -/
def erase_correct_firstorder_statement.{w} : Prop :=
  ∀ {P decls : List ConstantInfo} {env : ConLeche.Env} {view : EnvView} {cfg : ErasureConfig}
    {e ê v : Expr} {p : Program} {inl : List Kername},
    (hacc   : ConLecheAccepts P env) →
    (hty    : CLTyped env e) →
    (hclean : NoMarkKeys e = true) →
    (hcleanD : NoMarkKeysDecls decls = true) →
    (hview  : ViewAgrees view P) →
    (hfrag  : collectDeps view cfg e = .ok decls) →
    (hnopre : NoPreDefs view cfg decls) →
    (hrun   : eraseEntry view cfg e = pure (p, inl)) →
    (hmark  : MarkOf decls cfg [] e ê) →
    (hvals  : ValuesMarkedOf decls cfg) →
    (hev    : SrcEval env (evalEnvOf view cfg decls) ê v) →
    (hfo    : FirstOrderValue (evalEnvOf view cfg decls) v) →
    ∃ lenv tb, p = .untyped lenv (some tb) ∧
      LBEval defaultFlags lenv tb (foErase (evalEnvOf view cfg decls) v []) ∧
      CLTyped env v ∧ (∀ s, FrozenLeaf v s → CLErasable env s) ∧ Sound.{w} env e v

/-- The statement of `sound_nonvacuous`: `Sound`'s antecedent has content. If con-leche accepts
`P` and types an application of `e` to closed arguments with a type whose whnf is a sort
(`CLStrictType`: its members are types, never the proof point), then in every model `e` has a
reading that is not the proof point (the proof point applied is the proof point,
`CL ConLeche/SetTheory/Derive/Graphs.lean:79 app_pt`). A data-typed input is not covered (DV-34).
Reference: none (DV-34). -/
def sound_nonvacuous_statement.{w} : Prop :=
  ∀ {P : List ConstantInfo} {env : ConLeche.Env} {e : Expr} {as : List Expr}
    {c c₁ T W : ConLeche.Expr} {F : Nat},
    ConLecheAccepts P env → toCL? e = some c → toCL? (mkAppN e as.toArray) = some c₁ →
    ConLeche.inferTypeCore .verified false env F 0 c₁ = .ok T →
    ConLeche.whnf .verified false env F 0 T = .ok W → CLStrictType W →
    ∀ (V : Type w) [ConLeche.SetTheory V] (m : ConLeche.Model.EnvModelM V env)
      (φ : ConLeche.LevelParam → Nat) (ρ : ConLeche.BVarIdx → V),
      ∃ X, ConLeche.Denotes (ConLeche.Model.Model.ofEnvModelM m).cval env φ ρ c X ∧
        X ≠ ConLeche.SetTheory.pt

/-- The statement of `clCert_proof_pt`: the proof verdict of `CLCert` means a proof. If con-leche
accepts `P`, types the closed telescope `c` of a marked subterm under its binders, and the opened
subterm's type is a proposition (`CLProof`), then in every model `c` denotes the proof point: the
subterm denotes the proof point under every valuation of its binders that satisfies their
domains (a λ whose body is the point on its whole domain is the point,
`CL ConLeche/Denotes.lean:146`, `CL ConLeche/SetModel/Ops.lean:264 lamV`; a `let` is read at its
value). From `InferClaim` (`CL ConLeche/Model/Claims.lean:112`) on the subterm and on its type, `WhnfClaim` (`:70`) on the
type's type, `IsTy.ne_pt` (`CL ConLeche/SetTheory/Derive/TypeU.lean:98`) and
`eq_pt_of_mem_univZero` (`CL ConLeche/SetTheory/Derive/Pt.lean:125`). The type-former verdict has
no such statement: it is a typing fact of the checker (DV-32). Reference: none. -/
def clCert_proof_pt_statement.{w} : Prop :=
  ∀ {P : List ConstantInfo} {env : ConLeche.Env} {Γ : List CtxBinder} {s : Expr}
    {c c' T₀ T : ConLeche.Expr} {d : Nat},
    ConLecheAccepts P env → toCL? (lamTele Γ s) = some c →
    ConLeche.inferTypeCore .verified false env ConLeche.checkFuel 0 c = .ok T₀ →
    openLams 0 Γ.length c = some (d, c') →
    ConLeche.inferTypeCore .verified false env ConLeche.checkFuel d c' = .ok T →
    CLProof env ConLeche.checkFuel d T →
    ∀ (V : Type w) [ConLeche.SetTheory V] (m : ConLeche.Model.EnvModelM V env)
      (φ : ConLeche.LevelParam → Nat) (ρ : ConLeche.BVarIdx → V) (X : V),
      ConLeche.Denotes (ConLeche.Model.Model.ofEnvModelM m).cval env φ ρ c X →
        X = ConLeche.SetTheory.pt

/-- The statement of `markOf_det`: the marking is a function of the term, the closure, the
configuration and the locals, for a closure whose types and values mention no free variable
(`ClosedDecls`; the oracle's answers then do not depend on the names of the fresh variables), for
a closed input at no locals (every binder's domain is then in scope, so the fresh variable a
binder rule picks cannot occur in it). Reference: none (DV-32). -/
def markOf_det_statement : Prop :=
  ∀ {decls : List ConstantInfo} {cfg : ErasureConfig} {e ê ê' : Expr},
    ClosedDecls decls = true → FVarsIn (fun _ => False) e → MarkOf decls cfg [] e ê →
    MarkOf decls cfg [] e ê' → ê = ê'

/-- The statement of `markOf_exists`: wherever the pure traversal erases the input, the input has a
marking, so the hypothesis `hmark` of `erase_correct_statement` follows from `hfrag` and `hrun`,
for a closed closure (`ClosedDecls`) that is part of a program con-leche accepts (`ConLecheAccepts`,
`SubEnv`: so every constructor sits at its index in its inductive's constructor list, whose names
are distinct, as the traversal's masks and alternatives read them) and an input without mark keys
(`NoMarkKeys`). Reference: none (DV-32). -/
def markOf_exists_statement : Prop :=
  ∀ {P decls : List ConstantInfo} {env : ConLeche.Env} {e : Expr} {view : EnvView}
    {cfg : ErasureConfig} {p : Program} {inl : List Kername},
    ConLecheAccepts P env → SubEnv decls P → ClosedDecls decls = true → NoMarkKeys e = true →
    collectDeps view cfg e = .ok decls → erasePure view cfg decls e = .ok (p, inl) →
    ∃ ê, MarkOf decls cfg [] e ê

/-- The statement of `collectDeps_sub`: the closure the fragment test returns is part of the
program con-leche accepted. Every constant the fragment test reads is read from a type or a value
con-leche checked, from a Lean record field that `DeclsOf?` checks (a constructor's `induct`, a
type's `all` and `ctors`, the `T.rec` of a member), or from a compiled pre-definition, whose
constants `ViewAgrees` puts in `P`. Reference: `erase_global_deps` keeps a sub-environment
(`MR E/ErasureFunction.v:1602`); DV-3. -/
def collectDeps_sub_statement : Prop :=
  ∀ {P decls : List ConstantInfo} {env : ConLeche.Env} {e : Expr} {view : EnvView}
    {cfg : ErasureConfig},
    ConLecheAccepts P env → ViewAgrees view P → CLTyped env e →
    collectDeps view cfg e = .ok decls → NoPreDefs view cfg decls → SubEnv decls P

end EraseProof
