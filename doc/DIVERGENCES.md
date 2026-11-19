# Divergence register

This register lists every place where the verification code on the `cl/verification` branch
(`proof/`, library `EraseProof`), or the statements it proves, diverge from the references —
Letouzey, "A New Extraction for Coq" (TYPES 2002), and Sozeau et al., "Correct and Complete Type
Checking and Certified Erasure for Coq, in Coq" (J. ACM 2025), including its MetaRocq sources at
commit `4b201296` (branch 9.1). The verification follows these references as closely as the
differences between Lean's kernel, as con-leche (`github.com/leanprover/con-leche`, commit
`d88e04e9b`) checks it, and Rocq/PCUIC/MetaRocq allow; every place it does not, for any reason, is
recorded here. Entries land with the artifact that diverges.

Each entry has an id `DV-<n>` and exactly these fields:

- **Our artifact:** file and declaration on the `cl/verification` branch that carries the
  divergence.
- **Reference artifact:** the paper section/figure/theorem and the MetaRocq `file:identifier` it
  corresponds to.
- **What differs:** the concrete difference between our artifact and the reference artifact.
- **Why it is forced:** the concrete reason the divergence is necessary — a difference between
  Lean's kernel and CIC, a gap in what con-leche provides, a scope boundary of the verified
  fragment, or similar. This field must name a real constraint; "it was simpler" or "we chose to"
  is not a forcing reason.
- **What was considered instead:** the alternative(s) that would have kept the divergence from
  existing, and why each was rejected.

An entry without a forcing reason is a defect, not a divergence: it must be removed and the
statement or definition restated to match the reference instead. Differences of representation
alone (a judgment in `Prop` where MetaRocq's lives in `Type`, explicit flags, bundled helpers) get
no entry.

The ids 1 to 31 are those of the register of the Metalean development of this repository (#16),
which continues the register of the lean4lean experiment; the shipping sources and the ported
definitions cite them. Only the ids that this branch or the shipping sources cite appear here. An
id whose divergence does not arise against con-leche keeps an entry that says so ("Not applicable
on this branch"), so that no citation is left without an entry. The ids from 32 on are new.

## Trust base

What the statements and the checks rely on without proof:

- Lean's kernel at the pinned toolchain (`lean-toolchain`), and the axioms `propext`,
  `Classical.choice` and `Quot.sound`: every declaration of the library stays within them (checks
  C3 to C5), and its modules are replayed through the kernel (check `replay`, `leanchecker`). The
  replay covers the library's modules `EraseProof.*` and the shipping code's `LeanToLambdaBox.*`;
  the compiled `.olean` files of con-leche that they import are trusted as built.
- con-leche at the pinned revision (`d88e04e9b`, `lake-manifest.json`, pinned in `proof/spec.pin`):
  its checker, run as a function on the program's records (`EraseProof.ConLecheAccepts`,
  `EraseProof.CLTyped`, `EraseProof.CLCert`), and its set-theoretic model, which the statements
  quantify over (`EraseProof.Sound`). A `SetTheory` model is a hypothesis of the statements, never an
  axiom: con-leche instantiates it only from an inaccessibility hypothesis that this development does
  not use.
- The shipping oracle `Erasure.Pure.isErasable`, which defines the marks (`EraseProof.MarkOf`,
  DV-32), and the helpers through which the statements are defined. `proof/spec.pin` holds a SHA-256
  digest of each statement definition and of every definition of the library, of the shipping code
  or of con-leche that the statements reach (check C12b). The three functions under verification,
  `Erasure.collectDeps`, `Erasure.erasePure` and `Erasure.eraseEntry`, are pinned by name only.
- Lean's compiler and runtime for the shipping code. The theorems are about the logical
  definitions of the three functions; `#erase` runs their compiled code. What `#erase` does around
  `Erasure.eraseEntry` (the elaboration of the input and of the `config` term, the printer that
  writes the program as an S-expression, the `.inlinings` file, the `.mli` signature) is not
  covered.

## Entries

### DV-1

- **Our artifact:** `proof/EraseProof/Spec.lean`: `EraseProof.toCL?` (with `EraseProof.Level.toCL`
  and `EraseProof.Name.toCL`) reads a Lean `Expr` as a con-leche `Expr`, and `EraseProof.CLTyped`
  (hypothesis `hty` of `EraseProof.erase_correct_statement`) asks con-leche's full-grade inference
  to accept the reading of the input; `EraseProof.SrcEval` and `EraseProof.Erases` evaluate and
  erase Lean terms.
- **Reference artifact:** PCUIC's weak call-by-value evaluation `eval`
  (`pcuic/theories/PCUICWcbvEval.v:231`; MC §5.6) and the erasure relation `erases`
  (`erasure/theories/Extract.v:88`; MC §7.3, Fig. 18), both on PCUIC terms, the syntax PCUIC's
  typing judges; the premise `welltyped` (`pcuic/theories/PCUICTyping.v:355`) of
  `erases_correct` (`erasure/theories/ErasureCorrectness.v:51`); Letouzey §3.1 (CIC terms).
- **What differs:** the syntax that evaluates and the syntax that is typed differ. con-leche's `Expr`
  has no binder names or infos, no metavariables and no metadata; `EraseProof.toCL?` drops binder
  names, binder infos and `mdata` (every mark is therefore transparent to it), keeps `let` and
  projections, and is `none` on a free variable, a metavariable and a level metavariable, as
  con-leche reads a stored Lean `Expr`
  (CL ConLeche/Frontend/Olean/Spec.lean:162 exprNode). The hypothesis `hty` is a run of con-leche's
  inference on that reading at some fuel, in place of `welltyped Σ [] t`; there is no typing
  judgement on Lean terms and no relation between the two syntaxes, only the function `toCL?`. A
  projection, a `let` and a literal are evaluated and erased on the Lean term and read by the same
  function.
- **Why it is forced:** con-leche has no syntactic typing judgement (its theory is a set model,
  `EraseProof.Sound`, DV-34): the only typing it offers is the run of its checker on its own
  `Expr`, so a premise on a Lean term can only go through a reading function. The reading has to
  be a function, with con-leche's own drops, for a statement to mention it; the eraser consumes
  Lean `Expr`s.
- **What was considered instead:** con-leche's frontend `parseExportD` on an export of the program,
  which is IO code (outside the hygiene allow list of check C6) and not a function of the program's
  records; a typing relation on Lean `Expr`, which no development of this repository provides.

### DV-2

- **Our artifact:** `proof/EraseProof/Spec.lean`, `EraseProof.toCL?`, whose cases for literals and
  projections stand where the translation rules of earlier developments stood.
- **Reference artifact:** MetaRocq's translation of Template terms into PCUIC terms, `trans`
  (`template-pcuic/theories/TemplateToPCUIC.v:63`; MC §9).
- **What differs:** Not applicable on this branch. There is no translation relation between two
  syntaxes (DV-1): `EraseProof.toCL?` reads Nat literals, strings and projections directly, as
  con-leche's frontend does.
- **Why it is forced:** not applicable: the gap that the id recorded in the lean4lean experiment
  (no rule for literals and projections in the bridge) does not exist.
- **What was considered instead:** dropping the id, which would leave the citations of the earlier
  registers without an entry.

### DV-3

- **Our artifact:** `proof/EraseProof/Spec.lean`: `EraseProof.DeclsOf?` (with
  `EraseProof.declOf?`, `EraseProof.blockOf?` and `EraseProof.blockShapeOK`) reads the program's
  declarations, a newest-first list of Lean `ConstantInfo`s, as con-leche's input;
  `EraseProof.ViewAgrees`; `EraseProof.SubEnv`, and the evaluation environment `EraseProof.EvalEnv`
  (`EraseProof.evalEnvOf`), over the whole program in the conclusions of
  `EraseProof.erase_correct_statement` and over the dependency closure in its hypothesis `hev`
  (DV-41) and in `EraseProof.erasePure_erases_statement`; `EraseProof.collectDeps_sub_statement`.
- **Reference artifact:** the well-formed global environment `wf_ext`
  (`pcuic/theories/PCUICTyping.v:507`; MC §3.6), whose declarations are a newest-first list
  searched by `lookup_env` (`common/theories/Environment.v:483`); MetaRocq's `erase_correct`
  (`erasure/theories/ErasureFunctionProperties.v:657`) evaluates the erased term over the erasure
  of the dependency closure `erase_global_deps` (`erasure/theories/ErasureFunction.v:1602`).
- **What differs:** the environment is a list of Lean records, and `DeclsOf?` turns it into
  con-leche's declarations only if the records agree with one another as Lean's kernel generates
  them: names are distinct; no type or value carries a mark key (DV-39); unsafe and partial
  constants are left out as lean4export leaves them out
  (CL ConLeche/Frontend/Olean/Reads.lean:18 CKindF.skipped); each inductive block passes the
  record checks of con-leche's frontend (CL ConLeche/Frontend/ExportC.lean:241 validateIndF: one
  parameter count, constructor positions, field counts, recursor counts) and the checks of the
  fields the traversal reads and con-leche does not (each type's `all` and `numIndices`, the head
  of each constructor's result type, `isRec`, the recursors being exactly the `T.rec` of the
  block's members, `EraseProof.blockShapeOK`). The erasure relation of the conclusions (`EvalEnv`)
  ranges over the whole program, and the source evaluation (DV-41) and the λ□ dependencies over the
  closure the fragment test returns, which is a sub-environment of the program
  (`EraseProof.collectDeps_sub_statement`: the constants it reads come from a type or a value
  con-leche checked, from a record field `DeclsOf?` checks, or from a compiled pre-definition, whose
  constants `ViewAgrees` puts in the program). `ViewAgrees` also requires that the compiled pre-definitions the view holds for the program's
  declarations name only constants of the program.
- **Why it is forced:** the eraser reads Lean records through `Erasure.EnvView`, and con-leche
  checks its own `Declaration`s without the Lean fields (`induct`, `all`, `cidx`, `isRec`, the
  recursor list) that the traversal reads: a record con-leche accepts may still disagree with
  another record the traversal reads, so the agreement is a check of the reading. The relation of
  the conclusions and the λ□ dependencies range over different sets because a λ□ constant is found by its kername
  (DV-14), and kernames are injective only where `Erasure.collectDeps` checks it, on the closure;
  the λ□ environment the eraser emits holds the closure only. The view is outside what con-leche
  checks.
- **What was considered instead:** con-leche's frontend on an export of the program, which is IO
  code (check C6) and not a function of the records; reading the records without checks, under
  which `collectDeps_sub_statement` is false on records con-leche does not read; one environment
  for acceptance and evaluation, which fails for programs whose names collide outside the closure.

### DV-4

- **Our artifact:** `proof/EraseProof/Spec.lean`, `EraseProof.CLErasable` and `EraseProof.CLFormer`,
  where earlier developments had `IsErasable` with `IsArity`.
- **Reference artifact:** `isErasable` (`erasure/theories/Extract.v:18`; MC §7.3, Fig. 18), with
  `isArity` (`pcuic/theories/PCUICTyping.v:29`) and `Sort.is_propositional`
  (`common/theories/Universes.v:1528`).
- **What differs:** Not applicable on this branch. There is no declaration `IsErasable` or
  `IsArity`: erasability of a mark is the verdict of con-leche's checker (`EraseProof.CLErasable`,
  `EraseProof.CLCert`, DV-32, DV-37), whose proof verdict compares the sort of the type with zero
  under every level valuation (CL ConLeche/Kernel/Level.lean:201 isAlwaysZero). The shipping
  oracle's structural test (`Erasure.Pure.alwaysZero`, `LeanToLambdaBox/Erasure/Pure.lean:190`),
  which cites this id, approximates `Prop` as `isErasable` does; Lean has no `SProp`.
- **Why it is forced:** not applicable: the entry exists for the citation of the shipping code.
- **What was considered instead:** dropping the id, which would leave the shipping citation without
  an entry.

### DV-7

- **Our artifact:** `proof/EraseProof/Spec.lean`, `EraseProof.NoPreDefs`, which excludes the
  programs whose declarations the traversal erases through a compiled pre-definition (DV-35).
- **Reference artifact:** PCUIC's fixpoints `tFix`, `eval_fix`
  (`pcuic/theories/PCUICWcbvEval.v:273`) and `erases_tFix` (`erasure/theories/Extract.v:122`).
- **What differs:** Not applicable on this branch. The source semantics has no rule for a recursive
  definition (no unfolding through a pre-definition, no fix variable in the erasure relation); a
  recursor is evaluated by `EraseProof.SrcEval.recIota` and erased to a fixpoint of its own (DV-30),
  and a structural definition under `structural := .kernel` recurses through its kernel value. The
  shipping function `nameOccurs` (`LeanToLambdaBox/Erasure/Pure.lean:428`), which
  cites this id, treats Lean's environment-level recursion through the `_unsafe_rec` companion,
  which `EraseProof.NoPreDefs` leaves out of the final theorem.
- **Why it is forced:** not applicable: the entry exists for the citation of the shipping code; the
  exclusion itself is DV-35.
- **What was considered instead:** dropping the id, which would leave the shipping citations without
  an entry.

### DV-10

- **Our artifact:** `proof/EraseProof/Spec.lean`, `EraseProof.EvalEnv.unfold?`: the source semantics
  unfolds definitions only; an opaque constant has no δ rule.
- **Reference artifact:** `eval_delta` (`pcuic/theories/PCUICWcbvEval.v:247`; MC §5.6), which
  unfolds every constant whose declaration has a body.
- **What differs:** a Lean `opaque` declaration has a value, and the eraser emits it as the body of
  its λ□ constant, but `EraseProof.EvalEnv.unfold?` does not unfold it: evaluation is stuck where
  λ□ evaluation unfolds.
- **Why it is forced:** con-leche checks the value of an opaque against its type and stores the
  constant as an axiom, without the value (CL ConLeche/Kernel/Checker.lean:89 checkOpaqueVal), so
  its model of the environment relates the constant to no unfolding: the meaning claim `Sound`
  would be false for a step that replaces the constant by its value.
- **What was considered instead:** unfolding opaques as `eval_delta` does, under which evaluation
  does not preserve the meaning of the input in every model of the environment.

### DV-11

- **Our artifact:** `proof/EraseProof/Spec.lean`: `EraseProof.EvalEnv.isAtom` with
  `EraseProof.EvidentZero`, `EraseProof.DeltaFree`, `EraseProof.EvidentProp` and
  `EraseProof.IsThm`, the rule `EraseProof.SrcEval.constAtom`; and the premise
  `σ.isAtom c = false` of `EraseProof.Erases.const`: atoms erase only to `□`.
- **Reference artifact:** PCUIC's atoms `atom` (`pcuic/theories/PCUICWcbvEval.v:51`), which
  contain the inductive types `tInd`, and `eval_atom` (`pcuic/theories/PCUICWcbvEval.v:331`); a
  constant without a body has no rule. `erases_tConst` (`erasure/theories/Extract.v:104`) relates
  every constant to its `tConst`; `tInd` erases only to `□` (`erases_box`,
  `erasure/theories/Extract.v:140`).
- **What differs:** a constant without a δ rule (an axiom, an opaque, a theorem, an inductive type)
  is a value when its declared type is evidently an arity (`Erasure.arityShape`), evidently a
  proposition (`EraseProof.EvidentProp`), or it is a theorem; the spines it heads are values.
  Every other constant without a δ rule is stuck.
- **Why it is forced:** Lean's inductive types are constants, where PCUIC has the term `tInd`; and
  lemmas passed as arguments (theorems have no δ here, DV-24) must be values, or the theorem is
  vacuous for every program that passes one. Atomhood is decided on declared types so that an
  atom's erasure, `□`, does not depend on the occurrence.
- **What was considered instead:** every δ-free constant a value: an axiom `n : Nat` would then be a
  value whose erasure, a λ□ constant without a body, is not a λ□ value (and con-leche declines such
  an axiom, DV-36); no δ-free constant a value, under which programs that pass lemmas never
  evaluate.

### DV-12

- **Our artifact:** `proof/EraseProof/Spec.lean`: `EraseProof.EvalEnv` with its field
  `axiomatized`, `EraseProof.EvalEnv.unfold?`, `EraseProof.evalEnvOf` (the shipping test
  `Erasure.axiomatized`), and the remapped branch of `EraseProof.ErasesDecl`.
- **Reference artifact:** `eval` (`pcuic/theories/PCUICWcbvEval.v:231`), whose `eval_delta` unfolds
  a constant exactly when it has a body, and `erases_constant_body`
  (`erasure/theories/Extract.v:264`).
- **What differs:** a definition that the configuration remaps to foreign code (`@[extern]` under
  `extern := .preferAxiom`) has a Lean value but no δ rule, and `EraseProof.ErasesDecl` relates it
  to a λ□ declaration without a body, a pair `erases_constant_body` excludes. The source leaves the
  constant stuck. `EraseProof.NoPreDefs` exempts such a declaration (the traversal gives it no
  body), so a remapped recursive definition is not excluded by DV-35.
- **Why it is forced:** the eraser emits such a declaration as a λ□ axiom so that it is linked
  with its foreign implementation; neither con-leche nor λ□ models that implementation, so the
  source can only leave the constant stuck, as λ□ leaves the axiom.
- **What was considered instead:** excluding programs that mention a remapped constant, which
  also excludes programs that never evaluate it.

### DV-13

- **Our artifact:** `proof/EraseProof/Spec.lean`: `EraseProof.Fresh`, `EraseProof.absFV` and the
  rule `EraseProof.Erases.fvar`: the eraser's free variables, kept in the marking and related to
  themselves in λ□; `proof/EraseProof/Target.lean`, `EraseProof.hasFVar` and
  `EraseProof.LenvClosed`: no body of the λ□ environment has a free variable.
- **Reference artifact:** PCUIC's de Bruijn contexts and MetaRocq's `erase`
  (`erasure/theories/ErasureFunction.v:989`), which works on de Bruijn indices; `closed_env`
  (`erasure/theories/EGlobalEnv.v:181`).
- **What differs:** the shipping traversal is locally nameless: it opens binders with free
  variables and closes them with `abstract` before a body is stored. `EraseProof.MarkOf` opens each
  binder with a fresh free variable and closes it again, the erasure relation has a rule for free
  variables, and the closedness of the λ□ environment includes the absence of free variables. The
  input and the declarations have none (`toCL?` is `none` on a free variable, DV-1;
  `EraseProof.ClosedDecls`).
- **Why it is forced:** the theorem is about the shipping traversal, which uses Lean's locally
  nameless `Expr` interface (`LeanToLambdaBox/Erasure/Pure.lean`); its intermediate states contain
  free variables, which the induction over the traversal must relate.
- **What was considered instead:** a relation on closed terms only, under which no intermediate
  state of the traversal is related.

### DV-14

- **Our artifact:** `proof/EraseProof/Spec.lean`: the rule `EraseProof.ErasesDeps.const`, indexed
  by the source constant `c` and finding its λ□ declaration at `toKername c`;
  `EraseProof.KernameInj` and `EraseProof.BlockNamesInj`, hypotheses of
  `EraseProof.erases_correct_statement`; `EraseProof.BlockNamesInj`, a hypothesis of
  `EraseProof.collectDeps_ok_of_statement`.
- **Reference artifact:** `erases_deps_tConst` (`erasure/theories/Extract.v:324`; MC §7.4), where
  the PCUIC and the λ□ declaration are found at the same kername.
- **What differs:** a Lean constant and its λ□ constant have different names (`toKername`), and two
  Lean names may have the same kername, so the rule names the source declaration it uses, and the
  simulation assumes that kernames are distinct on the evaluation environment and that no two λ□
  declarations of the closure share a name (`BlockNamesInj`).
- **Why it is forced:** `toKername` (`LeanToLambdaBox/Basic.lean`) is not injective; the fragment
  test rejects closures with two constants or two λ□ blocks of one kername
  (`Erasure.findCollision`, `Erasure.findBlockCollision`), so the hypotheses hold on what the
  eraser erases.
- **What was considered instead:** an injective name mangling, a shipping change that alters the
  output for every name with special characters, which the theorem does not need.

### DV-16

- **Our artifact:** `proof/EraseProof/Target.lean`: `EraseProof.LBEval` with `EraseProof.lbAtom`,
  `EraseProof.csubst`, `EraseProof.closedn`, `EraseProof.hasFVar` and `EraseProof.LenvClosed`, on
  the shipping AST `LBTerm` (`LeanToLambdaBox/Basic.lean`); `proof/EraseProof/Spec.lean`,
  `EraseProof.ErasesDeps` on the same terms.
- **Reference artifact:** MetaRocq's λ□ evaluation `eval` (`erasure/theories/EWcbvEval.v:119`) on
  `term` (`erasure/theories/EAst.v:29`), with `atom` (`erasure/theories/EWcbvEval.v:36`), `csubst`
  (`erasure/theories/ECSubst.v:14`), `closedn` (`erasure/theories/ELiftSubst.v:90`) and
  `closed_env` (`erasure/theories/EGlobalEnv.v:181`); `erases_deps`
  (`erasure/theories/Extract.v:306`); MC §7.1.
- **What differs:** `LBTerm` has no `tVar`, `tEvar`, `tCoFix`, `tLazy` or `tForce`, and its only
  primitive values are 63-bit integers, so `EraseProof.LBEval` has no cofixpoint or `force` rule;
  it has a constructor `fvar` (DV-13), with no evaluation rule. `EraseProof.ErasesDeps` has no rule
  for primitive values, which the fragment does not produce (DV-26).
- **Why it is forced:** the theorem is about the eraser's output, an `LBTerm`, the λ□ that
  peregrine reads; the missing terms cannot occur in it.
- **What was considered instead:** extending `LBTerm`, a shipping change no output needs; a
  separate transcription of `term`, which every statement would reach through a translation.

### DV-17

- **Our artifact:** `proof/EraseProof/Statements.lean`: `EraseProof.erase_correct_statement`
  assumes a run of `Erasure.eraseEntry` that returns a program (`hrun`) and an evaluation of the
  source (`hev`); `EraseProof.collectDeps_ok_of_statement` bounds the closure by the fragment
  test's fuel (`decls.length ≤ collectFuel`). The shipping oracle, fragment test and traversal are
  fuelled (`Erasure.oracleFuel`, `Erasure.collectFuel`, `Erasure.travFuel`); `EraseProof.CLTyped`
  asks con-leche's inference to accept at some fuel.
- **Reference artifact:** MetaRocq's `is_erasableb` (`erasure/theories/ErasureFunction.v:894`)
  and `erase` (`erasure/theories/ErasureFunction.v:989`; MC §7.2), total under the hypothesis
  `NormalizationIn` (`pcuic/theories/PCUICSN.v:44`); `erases_erase`
  (`erasure/theories/ErasureFunction.v:1228`) and `erase_correct`
  (`erasure/theories/ErasureFunctionProperties.v:657`), which hold for every input.
- **What differs:** the final theorem is partial correctness: it says nothing about a run that
  fails (out of fuel, for example, an error of `#erase` and never an output) and nothing about a
  source term that does not evaluate. No statement has a normalization hypothesis.
- **Why it is forced:** con-leche proves no normalization: its theory is a set model, in which a
  term denotes a set, and its checker is fuelled, so a total oracle by well-founded recursion
  cannot be defined from its results, and a normalization hypothesis would stand in for a theorem
  con-leche does not have. For the same reason `EraseProof.SrcEval` is tied to con-leche only
  through run-time certificates and the meaning claim `EraseProof.Sound`, and nothing shows that a
  typed program evaluates.
- **What was considered instead:** a normalization hypothesis as MetaRocq's `NormalizationIn`,
  which would assume what con-leche does not prove.

### DV-23

- **Our artifact:** `proof/EraseProof/Spec.lean`: `EraseProof.markEta` and the rules
  `EraseProof.MarkEta.intro` and `EraseProof.MarkAlt.intro` of the marking, which write each
  η-expansion the traversal performs (`withAppEtaToMinArity`, `lambdaMonocularOrIntro`) on the
  source term as an `eta`-marked λ; the rules `EraseProof.SrcEval.etaLam` and
  `EraseProof.SrcEval.etaBeta` (an `eta`-marked λ is a value and is applied as a λ);
  `EraseProof.Erases.etaLam` and `EraseProof.ErasesAlt.etaLam`; `EraseProof.unmark`, which
  η-contracts the `eta` marks (`EraseProof.etaContract`).
- **Reference artifact:** PCUIC's `eval` evaluates the arguments of an application eagerly
  (`eval_app_cong`, `pcuic/theories/PCUICWcbvEval.v:311`; `eval_construct`,
  `pcuic/theories/PCUICWcbvEval.v:303`); MetaRocq η-expands constructors in λ□ by a separate pass
  (`isEtaExp`, `erasure/theories/EEtaExpanded.v:61`).
- **What differs:** an under-applied constructor, `casesOn`, quotient or recursor spine is
  η-expanded in the marked input, one `eta`-marked λ per missing argument, and the expansion is the
  term that evaluates and is erased: its λ keeps the arguments as they are, and the erasure relates
  it to a λ□ λ. No evaluation rule expands a spine and no erasure rule expands one.
- **Why it is forced:** the eraser η-expands such spines, and the λ□ value of the expansion is a
  closure whose arguments are not evaluated; with eager evaluation of the unexpanded spine the
  source value has an evaluated argument where the λ□ value has the unevaluated one, and the final
  theorem is false (on `P2.mk ((fun x => x) B.t)`). The expansion is written on the source term
  because con-leche gives meaning to a term only once its checker has typed it: `ProgCert` types the
  marked input as a whole (`EraseProof.CLTypedAt`, so that the domain of each introduced binder is
  checked against the argument position it fills), and `unmark` η-contracts only `eta` marks, so
  that `Sound` compares the value with the unexpanded input.
- **What was considered instead:** PCUIC's eager evaluation, under which the final theorem is false
  on under-applied constructors; an evaluation rule that expands a short spine, which has no mark
  for `ProgCert` to certify and no η-contraction for `unmark` to undo; an η-expansion pass on the
  source before evaluation, which is not what the eraser runs.

### DV-24

- **Our artifact:** `proof/EraseProof/Spec.lean`: `EraseProof.EvalEnv.unfold?` (no δ for
  theorems), `EraseProof.IsThm` in `EraseProof.EvalEnv.isAtom` (theorems are atoms), and the rules
  `EraseProof.SrcEval.projFrozen` and `EraseProof.SrcEval.casesFrozen`, which handle the proofs the
  traversal erases (frozen, DV-32).
- **Reference artifact:** `eval_delta` (`pcuic/theories/PCUICWcbvEval.v:247`), which unfolds a
  lemma like any constant with a body; λ□'s `eval_iota_sing` (`erasure/theories/EWcbvEval.v:162`)
  and `eval_proj_prop` (`erasure/theories/EWcbvEval.v:238`), which reduce a `case` or a projection
  on a proof erased to `□`.
- **What differs:** theorems are not unfolded, so a proof is a frozen term (when the traversal
  erases it) or an atom spine, never a constructor. A projection of a `Prop` structure out of a
  frozen proof is frozen (`projFrozen`), and a `casesOn` that the traversal reduces at erasure time
  continues with its alternative at frozen projections of its discriminant (`casesFrozen`, DV-25). A
  `casesOn` on a lemma of an inductive with proof fields that the traversal does not reduce does not
  evaluate, nor does a recursor on a lemma (`True.rec`, `And.rec` or `PUnit.rec.{_, 0}` applied to
  a theorem): `EraseProof.SrcEval.recIota` needs a constructor value as its major premise (DV-30),
  while λ□ reduces the erased fixpoint's `case` on `□`. Programs defined by well-founded recursion,
  whose recursion reduces only through a proof of accessibility, do not evaluate either: the final
  theorem holds vacuously for all of these, and the fragment test excludes the last (DV-26).
- **Why it is forced:** con-leche stores a theorem by its statement alone, without its value
  (CL ConLeche/Kernel/Checker.lean:59 checkThmVal): its model has no unfolding of a theorem, and
  the value of a theorem typically uses recursors and tactics that nothing here evaluates.
- **What was considered instead:** δ for theorems, which has no counterpart in con-leche's
  environment; a recursor rule on a lemma, which covers only recursors of a field-less `Prop`
  constructor (`True.rec`; `And.rec` on a lemma stays stuck as `And.casesOn` does) and needs its own
  run-time certificate.

### DV-25

- **Our artifact:** `proof/EraseProof/Spec.lean`: `EraseProof.EvalEnv.casesOn?` (the shipping
  recognizer `Erasure.casesInfo?`), the rules `EraseProof.SrcEval.casesIota`,
  `EraseProof.SrcEval.casesLitZero`, `EraseProof.SrcEval.casesLitSucc` and
  `EraseProof.SrcEval.casesFrozen`; the marks `EraseProof.markReduced` and
  `EraseProof.MarkSat.casesReduced`; the rules `EraseProof.Erases.cases` and
  `EraseProof.Erases.casesReduced`.
- **Reference artifact:** PCUIC's `tCase`, a term, with `eval_iota`
  (`pcuic/theories/PCUICWcbvEval.v:253`); `erases_tCase` (`erasure/theories/Extract.v:109`); λ□'s
  `eval_iota_sing` (`erasure/theories/EWcbvEval.v:162`).
- **What differs:** Lean has no case term: `T.casesOn` is a definition through the recursor
  `T.rec`. The source treats a recognized `casesOn` as primitive, without δ, reducing on the
  constructor its major evaluates to; it does not unfold it to the recursor, which has a rule of
  its own (`EraseProof.SrcEval.recIota`, DV-30). A `casesOn` on a one-constructor inductive whose
  sort may be `Prop` is reduced by the traversal at erasure time: the discriminant is marked
  `reduced`, it is not evaluated, con-leche certifies it as a proof (`EraseProof.CLErasable` in
  `casesFrozen`, `EraseProof.CLCert` in `casesReduced`), and the erased alternative is applied to
  `□` for each field, the reduction `eval_iota_sing` makes at run time. The fragment test admits it
  only on an inductive written in `Prop` (`Erasure.eliminatedUndecided`), whose fields are proofs.
- **Why it is forced:** the eraser translates recognized `casesOn` spines to λ□ `case` and never
  unfolds them (`LeanToLambdaBox/Erasure.lean`); a recursor it erases to a λ□ fixpoint of its own
  (DV-30), not to a `case`. The reduced form is what the eraser emits when the discriminant's
  sort may be `Prop`, since λ□ marks a whole block as propositional or not; without a typing, the
  premise that the discriminant is a proof is a certificate of con-leche's checker.
- **What was considered instead:** δ-unfolding `casesOn` to `T.rec` and evaluating the recursor,
  which has no counterpart in the eraser's output.

### DV-26

- **Our artifact:** `proof/EraseProof/Statements.lean`: the hypothesis `hfrag` of
  `EraseProof.erase_correct_statement`, that the shipping fragment test `Erasure.collectDeps`
  accepts the input; and `EraseProof.collectDeps_ok_of_statement`, a sufficient condition for it
  (`EraseProof.ReadClosed`, `EraseProof.PhaseIDecl`, `EraseProof.PlainExpr`,
  `EraseProof.RecShaped`, `EraseProof.PreRead`, `EraseProof.KernameInj`,
  `EraseProof.BlockNamesInj`), which covers the recursors and the structural recursion that the
  test admits.
- **Reference artifact:** MetaRocq's `erase_correct`
  (`erasure/theories/ErasureFunctionProperties.v:657`), which holds for every well-typed term.
- **What differs:** the final theorem covers the inputs the fragment test accepts and con-leche
  accepts. The fragment test's exclusion classes: recursors that a read expression names other than
  those of a single inductive without indices that eliminates into every sort and whose induction
  hypotheses take no arguments and are about the last fields (`EraseProof.RecInFragment`;
  `Erasure.recShapeInFragment`), and those the eraser keeps as constants
  (`Erasure.recStaysConstant`); recursive definitions (every definition with a compiled
  `_unsafe_rec` companion except one that `Erasure.isStructuralRecursive` recognizes, a syntactic
  test for a `T.brecOn` in its value; definitions by well-founded recursion and `partial`
  definitions are out); definitions, theorems and opaques of mutual blocks, `partial`, `unsafe` and
  `implemented_by` constants, nested inductives, string literals, Nat literals and Nat or Int
  constructors under `nat := .machine`, `casesOn` on a constructor with an index field, eliminations
  of an inductive whose sort may be both `Prop` and not `Prop`, `remove_irrel_constr_args`,
  metavariables. The hypotheses of the final theorem add the classes that con-leche or the source
  semantics leaves out: user axioms (DV-36), declarations of `Nat.div` and `Nat.mod` (DV-38), and
  structural recursion through compiled pre-definitions, the default `structural := .unsafeRec`
  (DV-35).
- **Why it is forced:** `#erase` sends an input outside the fragment to the `Meta` path
  (`Erasure.route`, `LeanToLambdaBox/Erasure/Entry.lean:331-335`), `CoreM` code about which
  nothing is proved, and some of the excluded constructs have no con-leche counterpart (`unsafe`
  and `partial` constants). Typed inputs outside the fragment exist, so the hypothesis cannot be
  derived from typing as in the lean4lean experiment.
- **What was considered instead:** deriving the hypothesis from `hacc`, `hview` and `hty`, which is
  false on typed programs that use a mutual recursor; leaving the fragment unstated, which makes it
  impossible to tell how much the hypothesis excludes, which
  `EraseProof.collectDeps_ok_of_statement` states.

### DV-27

- **Our artifact:** `proof/EraseProof/Spec.lean`: `EraseProof.FirstOrderValue`, the values on which
  `EraseProof.erase_correct_firstorder_statement` determines the λ□ value, their structural erasure
  `EraseProof.foErase` (with `EraseProof.peanoLB`), and `EraseProof.FrozenLeaf`.
- **Reference artifact:** `firstorder_value` (`pcuic/theories/PCUICFirstorder.v:115`), with the
  first-order inductives of `firstorder_con` (`pcuic/theories/PCUICFirstorder.v:52`), and
  `erase_correct_strong` (`erasure/theories/ErasureFunctionProperties.v:2269`).
- **What differs:** MetaRocq's first-order value is a typed constructor application of an inductive
  that is not propositional, every argument (parameters included) a first-order value, and its
  first-order inductives have neither type parameters nor proof fields. Ours is syntactic: a tree of
  saturated constructor applications whose leaves are frozen terms (`markErase`, erased to `□`:
  type parameters and proof fields the traversal erased) and Nat literals (erased to Peano
  numerals). The conclusion compares with the structural erasure, which keeps parameters (DV-23),
  instead of the erasure function's output, and adds that con-leche types the value
  (`EraseProof.CLTyped`) and certifies every frozen leaf (`EraseProof.CLErasable`).
- **Why it is forced:** a Lean inductive in `Sort u` is universe-polymorphic over `Prop`, and there
  is no typing from which to read whether a constructor application is a proof: the marks are the
  eraser's decision, so a leaf erased to `□` is a mark, and a constructor node is unmarked and
  erases to a λ□ constructor. λ□ keeps parameters in constructor applications (DV-23), and Lean's
  data inductives take type parameters (`Prod`, `Option`, `List`) and its structures proof fields
  (`Subtype`, `Fin`), so MetaRocq's notion would leave only monomorphic inductives without proofs;
  there is no erasure function on the relation's side to compare with.
- **What was considered instead:** MetaRocq's notion exactly (all arguments first-order, the
  inductive not propositional), which excludes every value with a type parameter; comparing with
  `Erasure.erasePure`'s output, which reads the configuration and the view instead of the value
  alone.

### DV-28

- **Our artifact:** `proof/EraseProof/Spec.lean`: `EraseProof.ErasesAlt` (rules `done`, `lam` and
  `etaLam`) and `EraseProof.MarkAlt.intro`.
- **Reference artifact:** the alternatives of `erases_tCase`
  (`erasure/theories/Extract.v:109`), related to the erased branches by the erasure relation under
  the case's branch contexts; the relation has no η-introduction rule.
- **What differs:** Not applicable on this branch. `EraseProof.ErasesAlt` has no rule that
  η-introduces an alternative: the η-introduction is a mark (`EraseProof.MarkAlt.intro`, DV-23), the
  marked alternative is an `eta`-marked λ, and `etaLam` peels it as `lam` peels a λ. The relation is
  as MetaRocq's.
- **Why it is forced:** not applicable: the entry exists for the citations of the earlier
  registers; the substitution lemma that forced the entry there concerns a rule that is absent
  here.
- **What was considered instead:** dropping the id, which would leave the earlier citations without
  an entry.

### DV-29

- **Our artifact:** `proof/EraseProof/Spec.lean`: the rules `EraseProof.SrcEval.quotMk` and
  `EraseProof.SrcEval.quotLift`; `EraseProof.quotEvalArity` in `EraseProof.specialArity`, so that
  `EraseProof.MarkEta.intro` η-expands `Quot.mk` and `Quot.lift` spines with missing arguments; the
  quotient clauses of `EraseProof.OwnRules`, under which `EraseProof.EvalEnv.isAtom` makes the type
  former `Quot` an atom, and of `EraseProof.BlocksCong` (`Quot.mk` spines); the rules
  `EraseProof.Erases.quotMk` and `EraseProof.Erases.quotLift`.
- **Reference artifact:** none: PCUIC has no primitive quotients. The closest rules are `eval_beta`
  (`pcuic/theories/PCUICWcbvEval.v:234`) and `eval_construct`
  (`pcuic/theories/PCUICWcbvEval.v:303`) of `eval`, and `erases_tApp`
  (`erasure/theories/Extract.v:101`) and `erases_tConstruct` (`erasure/theories/Extract.v:106`) of
  `erases`.
- **What differs:** Lean's quotients are primitive constants with their own reduction, the quotient
  ι `Quot.lift f h (Quot.mk r a) ⤳ f a`. The source evaluates `Quot.mk α r a` by evaluating the
  element `a`, the type and the relation unevaluated, and `Quot.lift α r β f h q` by evaluating `f`
  to a λ and `q` to `Quot.mk α' r' a` and continuing with the λ's body at `a`; each step carries the
  certificate `EraseProof.CLOk` of the term it forms (DV-33). A `Quot.mk` value blocks application
  congruence as a constructor value does. The type former `Quot` is an atom, as an inductive type
  former is (DV-11): a quotient type `Quot α r` evaluates its arguments by application congruence
  and is a value, so it may be a constructor parameter or a β-argument, and it erases only to `□`.
  `Quot.ind` has no rule: a program that evaluates it, for instance as an argument, is stuck, and
  the final theorem holds vacuously for it. The erasure represents a quotient by its elements:
  `Quot.mk α r a` erases as `a` and `Quot.lift α r β f h q` as `f q`, applied to the erasures of
  the arguments beyond the arity.
- **Why it is forced:** the reference has no rule for quotients, and the eraser erases the quotient
  constants in this way, as Lean's code generator does (`visitConstApp`,
  `LeanToLambdaBox/Erasure.lean:958`). con-leche installs each quotient constant from its own pin
  (CL ConLeche/Kernel/Checker.lean:467 checkQuotRecord), so a program that mentions them is accepted
  with the constants' fixed types and its model interprets them; the source rules are the quotient
  ι under call by value. `Quot.ind` is a proof, but its statement ends in an application of its
  motive and is not an evident proposition, so the oracle is not known to erase its spines and the
  eraser may keep it as a λ□ axiom, while an atom erases only to `□`.
- **What was considered instead:** erasing `Quot.mk` and `Quot.lift` to λ□ axioms, under which
  every program that computes through a quotient is stuck in λ□; no source rule for quotients,
  under which such programs do not evaluate and the final theorem says nothing about them.

### DV-30

- **Our artifact:** `proof/EraseProof/Spec.lean`: the rule `EraseProof.SrcEval.recIota` with
  `EraseProof.natLitCtor`; the rules `EraseProof.Erases.recLet` and `EraseProof.Erases.recFix` with
  `EraseProof.RecFixOf`, `EraseProof.recMembers`, `EraseProof.recLets` and
  `EraseProof.EvalEnv.recBlock?`; the recursor clause of `EraseProof.specialArity`; the recursor
  exclusion of `EraseProof.Erases.const`; `EraseProof.RecInFragment` in `EraseProof.PhaseIDecl`;
  `proof/EraseProof/Target.lean`: `EraseProof.lbLift` and `EraseProof.LBFixed`.
- **Reference artifact:** none: PCUIC has no recursors (eliminators are `tCase` and `tFix`). The
  closest rules are `eval_fix` (`pcuic/theories/PCUICWcbvEval.v:273`), `eval_zeta` and `eval_iota`
  of `eval`, and `erases_tFix` (`erasure/theories/Extract.v:122`), `erases_tLetIn`
  (`erasure/theories/Extract.v:96`) and `erases_tCase` (`erasure/theories/Extract.v:109`) of
  `erases`.
- **What differs:** the source evaluates a saturated recursor `T.rec ps ms mins maj` of a single
  inductive `T` without indices, whose recursive fields take no arguments and come after the other
  fields of their constructor, by evaluating the minors to `mvs` and the major to a constructor
  value `C qs fs` (a Nat literal major is read as its constructor form `natLitCtor`: `0` as
  `Nat.zero`, `k + 1` as `Nat.succ` applied to the literal `k`, as Lean's kernel reads it), then
  each induction hypothesis `T.rec ps ms mvs f` (one per recursive field `f`, in the order of the
  minor's hypotheses) to a value, and continuing with the minor's value applied to the fields and
  these values; the step carries the certificate `EraseProof.CLOk` of the recursor application with
  its evaluated minors and major (DV-33). The parameters and the motive are not evaluated. There is
  no source ι for recursors of mutual, nested or indexed inductives, for higher-order recursive
  fields, for recursive fields before non-recursive ones, nor on a major that is not a constructor
  value (a frozen proof, a theorem: DV-24; `recK` and structure η are not rules). The fragment test
  admits exactly the recursors of this shape that the eraser does not keep as constants
  (`RecInFragment`). The erasure is the eraser's: the λ□ fixpoint of `recFix` under `let`s of the
  erased minors, applied to the erased major and the extra arguments (`Erases.recLet`);
  `Erases.recFix` relates the same fixpoint with closed λ□ values of the minors substituted, the
  form λ□ reaches after the `let`s and in which the recursive calls appear. The `direct` form of
  the fixpoint (alternatives applied to `□`) is admitted only for blocks whose one-constructor
  members are declared in `Prop` or have no fields, a declaration condition in place of a typing of
  the major.
- **Why it is forced:** the reference has no recursors, and the eraser compiles them to λ□
  fixpoints (`visitRec`, `LeanToLambdaBox/Erasure.lean:1003`). λ□ evaluates the minors (`let`) and
  every argument of an application by value, so the source evaluates the minors and the induction
  hypotheses first. Under `nat := .peano` the eraser emits a Nat literal as λ□'s constructor chain
  (`visitLiteral`; `Erases.litZero`, `Erases.litSucc`), on which the erased fixpoint computes, and
  Lean's kernel reduces a recursor on a literal; without the reading of a literal major as its
  constructor form the source would be stuck on these programs (structural recursion on `2`
  included). The λ□ rule `iota` needs a non-propositional block, and nothing types a constructor
  value of a `Prop` inductive, so the `direct` form rests on the declaration.
- **What was considered instead:** a source ι on the unevaluated induction hypotheses, under which
  the λ□ evaluation of a hypothesis the minor ignores has no source counterpart; erasing recursors to
  λ□ axioms (as `recStaysConstant` does for the excluded cases), under which every program that
  computes through a recursor is stuck in λ□; for a literal major, a source step `k + 1 ⤳
  Nat.succ k` on literals, which would make a literal a non-value, or a separate rule repeating the
  premises of `recIota` (as `casesLitZero` and `casesLitSucc` do for `casesOn`).

### DV-31

- **Our artifact:** `proof/EraseProof/Spec.lean`, `EraseProof.NoPreDefs`, the hypothesis `hnopre`
  of `EraseProof.erase_correct_statement`.
- **Reference artifact:** none: MetaRocq's `erase_correct`
  (`erasure/theories/ErasureFunctionProperties.v:657`) has no counterpart, since a PCUIC
  environment holds the recursive definition itself.
- **What differs:** Not applicable on this branch. The statement has no hypothesis on the
  pre-definitions of the program (no `PreDefsOK`, no typing of the `_unsafe_rec` companion): the
  declarations whose compiled pre-definition the traversal would erase are excluded (DV-35), and
  `EraseProof.ViewAgrees` only places the constants the pre-definitions name in the program, for
  what the fragment test reads through the view (DV-3).
- **Why it is forced:** not applicable: the entry exists for the citations of the earlier
  registers.
- **What was considered instead:** dropping the id, which would leave the earlier citations without
  an entry.

### DV-32

- **Our artifact:** `proof/EraseProof/Spec.lean`: `EraseProof.MarkOf` (with `EraseProof.MarkEta`,
  `EraseProof.MarkSat`, `EraseProof.MarkAlt`, `EraseProof.markErase`, `EraseProof.markMD`), which
  writes the eraser's erasability decisions on the source term (hypothesis `hmark` of
  `EraseProof.erase_correct_statement`); `EraseProof.unmark`; the frozen rules of
  `EraseProof.SrcEval`: `EraseProof.SrcEval.frozen`, `EraseProof.SrcEval.frozenApp`,
  `EraseProof.SrcEval.projFrozen` and `EraseProof.SrcEval.casesFrozen`; `EraseProof.Erases.box`,
  which relates `□` to the `erase`-marked terms only; `EraseProof.ArityTypes`;
  `EraseProof.markOf_det_statement` and `EraseProof.markOf_exists_statement`.
- **Reference artifact:** `erases_box` (`erasure/theories/Extract.v:140`) with `isErasable`
  (`erasure/theories/Extract.v:18`), which relates `□` to every term whose type is a proof or an
  arity; `eval_box` (`erasure/theories/EWcbvEval.v:121`); the premises `wf_ext Σ` and
  `welltyped Σ [] t` of `erases_correct` (`erasure/theories/ErasureCorrectness.v:51`), and
  `ind_arity_eq` (`common/theories/EnvironmentTyping.v:1651`) of a well-formed environment.
- **What differs:** the source semantics evaluates the marked term, not the input. `MarkOf` is a
  function of the input, the closure, the configuration and the locals (on a closure without free
  variables, `markOf_det_statement`), defined wherever the traversal runs
  (`markOf_exists_statement`); every node the traversal asks the oracle about is marked `erase` when
  the oracle answers `true`. A frozen subterm is a value (`frozen`), no rule evaluates inside it, a
  frozen function applied is frozen (`frozenApp`, λ□'s `eval_box`), a projection of a frozen proof
  is frozen (`projFrozen`), a `casesOn` reduced at erasure time continues at frozen projections
  (`casesFrozen`, DV-25). `Erases.box` relates `□` to exactly the `erase`-marked terms and asks the
  certificate `cert` of the mark (DV-37) where MetaRocq asks `isErasable`; `unmark` removes the
  marks. `erases_correct_statement` has no `wf_ext`, no `welltyped` and no typing premise;
  it has `ArityTypes` (the declared type of every inductive of the closure is syntactically an
  arity, `Erasure.arityShape`) where a well-formed environment gives `ind_arity_eq`, besides
  `KernameInj`, `BlockNamesInj` (DV-14) and `LenvClosed` (DV-13). The oracle
  `Erasure.Pure.isErasable` defines the marks and is not verified; the statement reads it through
  `MarkOf`, so a change to the oracle changes the statement (`proof/spec.pin` pins it by digest).
  The theorem does not prove that the erased subterms are irrelevant to the computation: if the
  eraser erases a subterm the computation needs, the marked evaluation is stuck or `hcert` fails,
  and the theorem says nothing about that program.
- **Why it is forced:** con-leche has no typing judgement and no subject reduction, so
  `isErasable Σ Γ t` (a typing statement) cannot be asked, and the premises `wf_ext` and
  `welltyped` have no counterpart (`EraseProof.ConLecheAccepts` and `EraseProof.CLTyped` are runs of
  the checker, DV-1, DV-38). The semantic substitute is not available: con-leche's model does not
  separate type formers from data (`Nat.zero`, the type `Empty` and `PUnit.unit.{1}` have one
  denotation, CL ConLeche/SetModel/Value.lean:625 bval), so "t is erased" cannot be a property of
  what t denotes. Evaluating inside an erased subterm would give the subterm a meaning to preserve
  and a run to evaluate, which types and proofs under binders do not have; freezing it makes `□`
  match `eval_box` and leaves the meaning claim to the certificate (DV-37).
- **What was considered instead:** semantic erasability in the model, which is false for types
  (no separation of type formers from data); `ErasableS`-style typing on Lean terms, which no
  development of this repository provides for con-leche; no marks, evaluating the erased subterms,
  under which `hev` is unsatisfiable on programs with an erased type or proof argument; verifying
  the oracle, which needs a typing metatheory for Lean that con-leche does not have.

### DV-33

- **Our artifact:** `proof/EraseProof/Spec.lean`: `EraseProof.CLOk` and `EraseProof.CLErasable` as
  premises of the rules of `EraseProof.SrcEval`: `EraseProof.SrcEval.beta`,
  `EraseProof.SrcEval.etaBeta`, `EraseProof.SrcEval.zeta`, `EraseProof.SrcEval.ctor`,
  `EraseProof.SrcEval.casesIota`, `EraseProof.SrcEval.quotMk`, `EraseProof.SrcEval.quotLift`,
  `EraseProof.SrcEval.recIota`, `EraseProof.SrcEval.proj`, `EraseProof.SrcEval.lit` and
  `EraseProof.SrcEval.appCong` ask `CLOk`; `EraseProof.SrcEval.frozen`, `frozenApp`, `projFrozen` and
  `casesFrozen` ask `CLErasable`.
- **Reference artifact:** `eval` (`pcuic/theories/PCUICWcbvEval.v:231`) has no typing premise;
  `subject_reduction_eval` (`pcuic/theories/PCUICClassification.v:1093`) derives the typing of the
  value from that of the input.
- **What differs:** a rule that forms a redex or a data value from evaluated parts asks con-leche's
  inference to accept the closed term it forms (`CLOk`, which is `EraseProof.CLTyped`); a rule that
  freezes a term asks con-leche to type it as a proof or a type former (`CLErasable`). The
  hypothesis `hev` of the final theorem is therefore an evaluation together with a list of runs of
  con-leche's checker, one per step.
- **Why it is forced:** con-leche gives a meaning only to the terms its checker has typed (a term
  inferred to have a type denotes a member of it, `CL ConLeche/Model/Claims.lean:112 InferClaim`), and
  it has no subject reduction by which the typing of the contractum would follow from that of the
  redex. `EraseProof.Sound` is proved from these certificates, step by step.
- **What was considered instead:** no certificate, which leaves `Sound` without a reason that each
  intermediate term denotes anything; proving subject reduction for con-leche's checker, a
  syntactic metatheory that its theory does not contain.

### DV-34

- **Our artifact:** `proof/EraseProof/Spec.lean`: `EraseProof.Sound` (with `EraseProof.CLStrictType`),
  the conclusion of `EraseProof.srcEval_sound_statement` and the last conjunct of
  `EraseProof.erase_correct_statement`; `EraseProof.sound_nonvacuous_statement`.
- **Reference artifact:** subject reduction: `subject_reduction`
  (`pcuic/theories/PCUICSR.v:3129`) and `subject_reduction_eval`
  (`pcuic/theories/PCUICClassification.v:1093`), which `erase_correct`
  (`erasure/theories/ErasureFunctionProperties.v:657`) uses to type the value that `erases_correct`
  relates to the erased one.
- **What differs:** the final theorem concludes `Sound env e v`: the unmarked value has a con-leche
  reading, and in every model of the accepted environment (every `V` with `[SetTheory V]`, every
  `ConLeche.Model.EnvModelM` model, level valuation and variable assignment) it denotes what the
  input denotes, provided that is not the proof point. It is not type preservation: con-leche's
  model gives `Nat.zero`, the type `Empty` and `PUnit.unit.{1}` one denotation, so a value of another
  type with the input's denotation satisfies it; the value's type is fixed by `EraseProof.SrcEval`
  and, for a first-order value, by `EraseProof.CLTyped` on it. `SetTheory` is a hypothesis
  (an instance argument). `EraseProof.sound_nonvacuous_statement` shows that the antecedent has
  content: if con-leche types an application of the input to closed arguments with a type whose
  members are never the proof point (a sort, or an inductive whose sort is never zero,
  `EraseProof.CLStrictType`), the input has a reading in every model that is not the proof point.
- **Why it is forced:** con-leche's results are about denotations in its set model: its claims on
  head normalisation, definitional equality and inference preserve denotations
  (CL ConLeche/Model/Claims.lean:52 WhnfCoreClaim) and say nothing about proofs, which all denote
  the proof point (CL ConLeche/SetTheory/Derive/Pt.lean:69 pt); there is no typing judgement to
  preserve. A model exists only under an inaccessibility hypothesis that this development does
  not use, so the model is a hypothesis of the statement, as in
  `CL ConLeche/MainTheorem.lean:102 model_exists`.
- **What was considered instead:** type preservation, which needs a typing judgement and subject
  reduction; denotation equality unconditionally, which is false where the input denotes the proof
  point and the value is a term that does not.

### DV-35

- **Our artifact:** `proof/EraseProof/Spec.lean`: `EraseProof.NoPreDefs`, the hypothesis `hnopre`
  of `EraseProof.erase_correct_statement`, with the premise in `EraseProof.collectDeps_sub_statement`
  and `EraseProof.erasePure_erases_statement`.
- **Reference artifact:** none: MetaRocq's `erase_correct`
  (`erasure/theories/ErasureFunctionProperties.v:657`) has no counterpart, since a PCUIC
  environment holds the recursive definition itself, evaluated by `eval_fix`
  (`pcuic/theories/PCUICWcbvEval.v:273`) and erased by `erases_tFix`
  (`erasure/theories/Extract.v:122`).
- **What differs:** no declaration of the closure that the traversal erases by its value has a
  compiled pre-definition (`Erasure.preDef?` is `none`); a remapped `@[extern]` definition
  (`Erasure.axiomatized`) is exempt, since `visitMutual` gives it no body. A structurally recursive
  definition erased through its `_unsafe_rec` companion, which is the default
  `structural := .unsafeRec`, is therefore outside the theorem; under `structural := .kernel` it is
  inside, erased through its kernel value.
- **Why it is forced:** the companion is a `partial` definition that con-leche does not read
  (`EraseProof.DeclsOf?` leaves unsafe and partial constants out), so it has no denotation, and a
  source rule that unfolds it could not be proved to preserve the meaning of the input
  (`EraseProof.Sound`).
- **What was considered instead:** a source rule that evaluates the companion and asks the
  conversion of its application with the constant's as a premise at each call, which gives the
  companion no denotation in con-leche's model; adding the companion to the program, which
  `DeclsOf?` skips as partial.

### DV-36

- **Our artifact:** `proof/EraseProof/Spec.lean`: `EraseProof.ConLecheAccepts`
  (hypothesis `hacc` of `EraseProof.erase_correct_statement`), through `EraseProof.DeclsOf?`, which
  passes every axiom record of the program to con-leche's fold.
- **Reference artifact:** MetaRocq's `wf_ext` (`pcuic/theories/PCUICTyping.v:507`), which admits a
  constant without a body, and `erases_constant_body` (`erasure/theories/Extract.v:264`), which
  relates it to a constant without a body.
- **What differs:** a program with a user axiom is outside the theorem: con-leche installs only its
  pinned axioms (`propext`, `Classical.choice`, `Quot.sound` and the compiler-trust family
  `Lean.trustCompiler`, `Lean.ofReduceBool`, `Lean.ofReduceNat`) and tolerates a declared, unused
  `sorryAx` (CL ConLeche/Kernel/CheckDecl.lean:88-102); its fold declines any other axiom, so
  `hacc` is false of such a program. Axioms that a program mentions without declaring them are the
  pinned ones.
- **Why it is forced:** con-leche's model gives a meaning to an axiom only for the ones it pins; an
  arbitrary axiom has none, and the statement is about con-leche's acceptance.
- **What was considered instead:** admitting user axioms as atoms (DV-11), under which `hacc` is
  unsatisfiable on every program that declares one, so the theorem would hold vacuously for them
  without saying so.

### DV-37

- **Our artifact:** `proof/EraseProof/Spec.lean`: `EraseProof.CLCert` (with `EraseProof.CLVerdict`,
  `EraseProof.CLFormer`, `EraseProof.CLProof`, `EraseProof.lamTele`, `EraseProof.openLams`,
  `EraseProof.CLTypedAt`), `EraseProof.MarksCert` and `EraseProof.ProgCert`, the hypothesis
  `hcert` of `EraseProof.erase_correct_statement`, and `EraseProof.clCert_proof_pt_statement`.
- **Reference artifact:** `isErasable` (`erasure/theories/Extract.v:18`), asked of every `□` by
  `erases_box` (`erasure/theories/Extract.v:140`) and computed by `is_erasableb`
  (`erasure/theories/ErasureFunction.v:894`) with a type inference; MC §7.2.
- **What differs:** the erased subterms are certified by runs of con-leche's checker on the given
  program, not by a typing derivation. `ProgCert` asks that con-leche types the marked input as a
  whole and each constant's marked value the emitted environment holds a body for
  (`EraseProof.CLTypedAt`), and that every `erase` mark and the discriminant of every `reduced` mark
  is certified in the context of its enclosing binders (`MarksCert`): the closed telescope of its
  binders is typed, and the subterm opened as con-leche opens binders has a type that is a
  proposition (`CLProof`: the subterm then denotes the proof point in every model,
  `EraseProof.clCert_proof_pt_statement`) or a type-former type (`CLFormer`, the checker's own
  reducing test, a syntactic verdict with no model content). The checks run at the checker's fuel
  `checkFuel` and are decidable. A `□` of the λ□ value under a binder is a certified mark with
  evaluated values substituted, which no check repeats. The `□`s that the relation does not pair with
  a mark (the direct-mode placeholders of a recursor's fixpoint, DV-30) rest on declaration
  conditions and the fragment test, not on a certificate. The oracle's answers are checked on this
  program, not proved.
- **Why it is forced:** con-leche has neither a typing judgement nor a semantic criterion for type
  formers (DV-32), so `isErasable` can be replaced only by what its checker decides; the oracle
  (`Erasure.Pure.isErasable`) is unverified, and the certificate recovers the property per program.
  The context of the binders is part of the check because con-leche types a term only closed, and
  the domain of a binder must itself be checked.
- **What was considered instead:** a semantic predicate on the denotation of the mark, which is false
  for types (DV-32); verifying the oracle, which needs a typing metatheory for Lean; certificates
  on the closed mark alone, which cannot type a mark that mentions its enclosing binders.

### DV-38

- **Our artifact:** `proof/EraseProof/Spec.lean`: `EraseProof.ConLecheAccepts`, hypothesis `hacc` of
  `EraseProof.erase_correct_statement`, and `proof/EraseProof/Bridge/CLAccept.lean`,
  `EraseProof.ConLecheAccepts.accepted`.
- **Reference artifact:** `wf_ext` (`pcuic/theories/PCUICTyping.v:507`), the well-formedness of the
  global environment that `erase_correct` (`erasure/theories/ErasureFunctionProperties.v:657`) takes
  as a hypothesis.
- **What differs:** acceptance is con-leche's pure fold `ConLeche.checkDeclsPure` at
  `ConLeche.fueledOps` with the checker's fuel, with the empty `Nat.div`/`Nat.mod` pin list
  (CL ConLeche/MainTheorem.lean:70), on the declarations `EraseProof.DeclsOf?` builds from the
  program, starting from the empty environment (CL ConLeche/Kernel/CheckDecl.lean:180): `P`
  contains in dependency order everything its records use, and the basis declarations in `P` are
  checked against con-leche's pins. The binary runs a different fold, `Cached.checkDecls` at the
  committed pin variants (`ConLeche.natOpPinSets`) and a Nat-size bound, on lean4export's output
  (CL ConLeche/MainTheorem.lean:102 model_exists); the two are compared on the test programs and on
  Lean's `Eq`, `Quot` and `Nat` only. A program that declares `Nat.div` or `Nat.mod` is declined by
  the pure fold at the empty list. What acceptance gives is con-leche's own: the environment is well
  formed, has a model in every set theory, and its claims hold in every model
  (`EraseProof.ConLecheAccepts.accepted`).
  Acceptance also requires `EraseProof.RulesCanonical`: every stored recursor rule has the shape
  con-leche's generator writes (CL ConLeche/Kernel/Inductives/GenRec.lean:189 `classGenRule`, stored
  by `classRuleOk`, :444). con-leche proves that syntax at install only
  (CL ConLeche/Model/Inductives/GenRuleSyn.lean:292) and states of the accepted environment's
  rules their scoping and `λ`-count (CL ConLeche/Verify/EnvWF.lean:217); it is true of every
  accepted environment, is decidable, and is not derived from the fold here. `RulesCanonical` also
  requires that the rules of each recursor `T.rec` select by constructor (one rule per constructor
  of `T`, in order, each headed by its own constructor's minor premise, with that constructor's
  field count and as many arguments as the minor premise has binders,
  `EraseProof.RulesSelected`) and that its K flag is the one con-leche's block check expects
  (CL ConLeche/Kernel/Inductives/RecCheck.lean:463 recKExpected), which con-leche checks at install
  and does not state of the accepted environment.
  Acceptance also requires `EraseProof.TablesCanonical`: every stored projection table names its
  structure's single constructor, at that constructor's parameter and field counts and level
  parameters; con-leche installs a table only from a structure's constructor but states of a stored
  table only its lookup (CL ConLeche/Verify/EnvWF.lean:22 Env.findProj?_some).
  Acceptance also rejects a program whose declarations include an unsafe inductive: con-leche skips
  an unsafe block, so its constructors and recursors would be unchecked.
  It also rejects a program with a nested inductive (`numNested ≠ 0`, `EraseProof.blockShapeOK`): nested
  occurrences are outside the fragment (the simulation has no source ι for their recursors), and for a
  non-nested block the records' recursors name members of the block, which the closure's reads use.
  It also requires that every recursor's type names every member of its block
  (`EraseProof.blockShapeOK`): the fragment test reads a recursor's block only through its type,
  and con-leche compares the type with the generated one up to definitional equality, so a type
  that reaches a member only through a definition would pass. And it requires that every
  recursor's minor premises be syntactic domains of its type without `mdata`: the traversal counts
  a minor premise's binders with `Erasure.minorArity`, which stops at `mdata`, while con-leche's
  reading `EraseProof.toCL?` drops it.
- **Why it is forced:** the main theorem of con-leche is stated for every pin list, so the empty list
  needs no pin data, which comes from con-leche's pin generator and is outside the hygiene allow
  list of check C6; the binary's driver is IO code (check C6) and the cached fold reads a
  lean4export stream, not Lean records, so neither is a function of the program's records.
- **What was considered instead:** the binary's fold at `natOpPinSets`, which needs the generated
  pin data and a stream; acceptance defined by con-leche's frontend on an export of the program,
  which is not a function of the records. `RulesCanonical` proved from the fold's block branch (about 1000 lines of the installer's
  machinery) instead of stated, and likewise `TablesCanonical` from the structure installer.

### DV-39

- **Our artifact:** `proof/EraseProof/Spec.lean`: `EraseProof.NoMarkKeys`, the hypothesis `hclean`
  of `EraseProof.erase_correct_statement` (also in `EraseProof.srcEval_sound_statement` and
  `EraseProof.markOf_exists_statement`; its closure form `EraseProof.NoMarkKeysDecls` is a premise of
  `EraseProof.srcEval_sound_statement` and `EraseProof.erase_correct_firstorder_statement`) and a
  condition of `EraseProof.DeclsOf?`.
- **Reference artifact:** none: PCUIC terms carry no metadata, so MetaRocq's erasure has nothing
  that could be mistaken for a mark.
- **What differs:** the input and the types and values of the program carry no `mdata` node whose
  key is the anonymous name, the key of the marks (`EraseProof.markMD`). Elaboration never writes
  such a key.
- **Why it is forced:** a mark is an `mdata` node (Lean's `Expr` has no other carrier that the
  reading `toCL?` ignores, DV-1), and `unmark` removes the marks; an input node with the same key
  would be read as a mark, and `Sound` would compare the value with a term from which that node
  was removed.
- **What was considered instead:** marks on a separate syntax, which duplicates every operation on
  `Expr` that the traversal, the source semantics and the bridge use; an `mdata` key chosen per
  program, which makes `MarkOf` depend on the key.

### DV-40

- **Our artifact:** `proof/EraseProof/Test/NV1Premises.lean` and `proof/EraseProof/Test/NV2Premises.lean`:
  `EraseProof.Test.NV1.hacc` and `EraseProof.Test.NV2.hacc` take the fold equation
  `ConLeche.checkDeclsPure … = .ok env` as a premise, and a `#guard` in each file checks it by
  compiled evaluation (`EraseProof/Test/NV0Premises.lean` proves it in the kernel: NV-0 has no
  inductive type).
- **Reference artifact:** `erase_correct` (`erasure/theories/ErasureFunctionProperties.v:657`),
  whose hypotheses (`wf_ext` among them, `pcuic/theories/PCUICTyping.v:507`) have no
  non-vacuity requirement: MetaRocq does not exhibit a program that satisfies them.
- **What differs:** the non-vacuity instances of `EraseProof.erase_correct_statement` discharge
  every hypothesis in the kernel for NV-0. For a program with an inductive type (NV-1, NV-2) the
  hypothesis `hacc` is discharged in the kernel except the one equation that con-leche's fold
  accepts the declarations and returns the stated environment; that equation is the premise of
  the theorem `hacc`, and the build fails if the compiled `#guard` finds it false. The instances
  are therefore conditional on a computed, not a kernel-checked, fact. MetaRocq counterpart: none.
- **Why it is forced:** the kernel cannot reduce the fold on an inductive block. The block
  installer keeps its tables in `Std.HashMap`s (CL ConLeche/Kernel/FEnv.lean:36 FBase) hashed by
  Lean's `mixHash` (CL ConLeche/Kernel/Expr.lean:49 hashData), which is opaque to the kernel; and the
  checks that follow call the well-founded instantiateList
  (CL ConLeche/Kernel/ExprOps.lean:551 instantiateList) and leqCore
  (CL ConLeche/Kernel/Level.lean:87 leqCore), which the kernel does not unfold to a value. A
  program without an inductive type reduces to the end, which is why NV-0 needs no premise.
- **What was considered instead:** `native_decide` or `ofReduceBool`, which adds the compiler to
  the trust base and is forbidden; a symbolic proof that the fold accepts the block, which needs
  the installer's `Std.HashMap` reasoning and every comparison above proved by hand; kernel-reducible
  twins of these functions in con-leche, which the verification does not add (it never extends
  con-leche); restricting the non-vacuity programs to those without inductive types, which leaves
  every rule about `casesOn`, constructors and η-expanded constructors without an instance.

### DV-41

- **Our artifact:** `proof/EraseProof/Statements.lean`: the hypothesis `hev` of
  `EraseProof.erase_correct_statement` and of `EraseProof.erase_correct_firstorder_statement`, and
  the evaluation premise of `EraseProof.srcEval_sound_statement`: `EraseProof.SrcEval` in
  `EraseProof.evalEnvOf view cfg decls`, over the closure `decls` the fragment test returns.
- **Reference artifact:** MetaRocq's `erase_correct`
  (`erasure/theories/ErasureFunctionProperties.v:657`), whose source evaluation `eval`
  (`pcuic/theories/PCUICWcbvEval.v:230`; MC §5.6) is in the global environment `Σ`.
- **What differs:** the source semantics is the program's evaluation in its dependency closure as
  `#erase` computes it (`Erasure.collectDeps`): δ unfolds, and the `casesOn`, constructor,
  recursor and projection rules look up, only declarations of the closure, and δ marks an unfolded
  value with `EraseProof.MarkOf` over the closure. The closure is a sub-environment of the program
  (`EraseProof.collectDeps_sub`), so con-leche's acceptance of the program and its models apply to
  every declaration the evaluation reads. MetaRocq evaluates in the whole global environment.
- **Why it is forced:** the marks are the eraser's oracle's decisions (`Erasure.Pure.isErasable`),
  which it takes over the closure, and its reductions unfold the definitions of the list it reads;
  the closure does not read the value of a recognized `casesOn`, whose constants may lie outside
  it (a mutual `casesOn`'s value mentions `PUnit`), so the marking over the program can differ from
  the marking over the closure, and δ over the program would mark unfolded values with decisions
  the eraser does not take.
- **What was considered instead:** evaluation over the program with a theorem that the marking
  over the closure is the marking over the program on the expressions the traversal reads, which
  needs an agreement theory of the oracle between two declaration lists and an invariant for the
  `casesOn` values the closure does not read (about 2500 to 2900 lines); a change of the shipping
  closure so that it reads those values, which still needs the agreement theory (about 1300 lines).
