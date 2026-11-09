# Divergence register

This register lists every place where the verification code on the `ml/verification` branch
(`proof/`, library `EraseProof`), or the statements it proves, diverge from the references —
Letouzey, "A New Extraction for Coq" (TYPES 2002), and Sozeau et al., "Correct and Complete Type
Checking and Certified Erasure for Coq, in Coq" (J. ACM 2025), including its MetaRocq sources at
commit `4b201296` (branch 9.1). The verification follows these references as closely as the
differences between Lean's kernel, as Metalean (`github.com/intgrah/metalean`, commit `0146928`)
models it, and Rocq/PCUIC/MetaRocq allow; every place it does not, for any reason, is recorded
here. Entries land with the artifact that diverges.

Each entry has an id `DV-<n>` and exactly these fields:

- **Our artifact:** file and declaration on the `ml/verification` branch that carries the
  divergence.
- **Reference artifact:** the paper section/figure/theorem and the MetaRocq `file:identifier` it
  corresponds to.
- **What differs:** the concrete difference between our artifact and the reference artifact.
- **Why it is forced:** the concrete reason the divergence is necessary — a difference between
  Lean's kernel and CIC, a gap in what Metalean provides, a scope boundary of the verified
  fragment, or similar. This field must name a real constraint; "it was simpler" or "we chose to"
  is not a forcing reason.
- **What was considered instead:** the alternative(s) that would have kept the divergence from
  existing, and why each was rejected.

An entry without a forcing reason is a defect, not a divergence: it must be removed and the
statement or definition restated to match the reference instead. Differences of representation
alone (a judgment in `Prop` where MetaRocq's lives in `Type`, explicit flags, bundled helpers) get
no entry.

The ids numbered 1 to 22 continue those of the register of the lean4lean experiment of this
repository (commit `ca56b85`), which the shipping sources and the ported definitions cite. An id
whose divergence does not arise against Metalean keeps an entry that says so ("Not applicable
here"), so that no citation is left without an entry; ids from 23 on are new.

## Trust base

What the statements and the checks rely on without proof:

- Lean's kernel at the pinned toolchain (`lean-toolchain`), and the axioms `propext`,
  `Classical.choice` and `Quot.sound`: every declaration of the library stays within them (checks
  C3 to C5), and its modules are replayed through the kernel (check `replay`, `leanchecker`).
  The replay covers the library's modules `EraseProof.*` and the shipping code's `LeanToLambdaBox.*`;
  the compiled `.olean` files of Metalean and Mathlib that they import are trusted as built.
- Metalean at the pinned revision (`0146928`, `lake-manifest.json`, pinned in `proof/spec.pin`):
  its typing (`Metalean.Typing`), conversion and well-formedness `Metalean.EnvWF`, which the
  statements use as their notion of typing, the way MetaRocq's statements use PCUIC's. Metalean's
  axiom `Cardinal.exists_inaccessibles` (its set-theoretic model) is never reached (C3).
- Five total term builders of Metalean's translator, `Metalean.Frontend.indTerm`,
  `Metalean.Frontend.ctorTerm`, `Metalean.Frontend.recrTerm`, `Metalean.Frontend.wrapCase` and
  `Metalean.Frontend.quotTerm` (`Metalean/Frontend/Translate.lean`), with the constants they reach
  (156, none `partial`, `opaque`, `unsafe` or `implemented_by`; check C6 exempts exactly these).
  The bridge `EraseProof.TrM` (rules of `EraseProof.SatTr`) uses them for the η-terms of
  constructors, recursors, inductive types and quotients with fewer arguments than their arity
  (DV-1). They shape the hypotheses `henv` and `he` of the final theorem, and, through
  `EraseProof.ErasableS` in the rule `EraseProof.Erases.box`, its conclusion: a wrong builder could
  make the premises unsatisfiable, which the non-vacuity instances would show, or change which
  terms count as erasable. They are not proved correct; the rest of Metalean's frontend (its
  `partial` translator and loader) is not used.
- The statement definitions themselves (`proof/EraseProof/Statements.lean`, with
  `proof/EraseProof/Spec.lean` and `proof/EraseProof/Target.lean`), which a reader checks against
  the references with the entries below; `proof/spec.pin` holds a SHA-256 digest of each of them
  and of every definition of the library, of the shipping code or of Metalean they reach (check
  C12b). A digest covers a declaration's kind, type and value, not its name alone, so a change of a
  Metalean definition the statements reach changes the pin at that definition even when the
  revision line is the only other change; the remaining dependencies (Lean's library, Mathlib,
  Batteries) are pinned by name and by revision. The
  shipping definitions among them are part of what the statements say: the λ□ syntax (`LBTerm`,
  `Program`), the configuration `Erasure.ErasureConfig`, the view `Erasure.EnvView`, the fuel
  bound `Erasure.collectFuel`, and the helpers through which the source semantics, the relation
  and the bridge are defined, among them the `casesOn` recognizer `Erasure.casesInfo?`,
  `Erasure.Pure.instLevels`, `Erasure.axiomatized`, `Erasure.indexFields`, `Erasure.minorArity`,
  `Lean.Expr.instantiate1'`, `toKername` and `mutualBlockKername`. The three functions under
  verification, `Erasure.collectDeps`, `Erasure.erasePure` and `Erasure.eraseEntry`, are pinned by
  name only, and the definitions reached only through them are not pinned, so that a change to
  the code under verification leaves the pin unchanged while the proofs decide whether the
  theorems still hold.
- The shipping view `Erasure.EnvView.ofEnvironment` (`LeanToLambdaBox/Erasure/Collect.lean`), the
  environment `#erase` reads: the final theorem assumes it agrees with the program (`hview`).
- Lean's compiler and runtime for the shipping code. The theorems are about the logical
  definitions of `Erasure.collectDeps`, `Erasure.erasePure` and `Erasure.eraseEntry`; `#erase` runs
  their compiled code. The constants reached from `Erasure.eraseEntry` without its `CoreM` path
  (`Erasure.erase`) include 186 whose compiled code is not their logical definition (counted at
  this revision): 133 `@[extern]` constants (operations on `Nat`, `Int`, `Array`, `String` and
  `ByteArray`, `Lean.Name.beq`, `mixHash`, `panicCore`, `Lean.Expr.eqv`, `Lean.Expr.replaceImpl`),
  34 with an `@[implemented_by]` target (among them the constructors and `casesOn` of `Lean.Expr`,
  `Lean.Level` and `Lean.Name`, through their `_override` implementations, and the monadic array
  loops), and 19 `opaque` constants, among them the `partial` shipping functions `LBTerm.isValue`,
  `LBTerm.inlinedSize` and `LBTerm.stripLambdas`, which compute only the inlining hints, not the
  program. `Lean.Expr.eqv` and `Lean.Expr.replaceImpl` are reached only in the index-field branches
  of `Erasure.visitCases`, which no input that the fragment test accepts reaches (DV-26). The non-vacuity instances
  are kernel-checked on the logical definitions; the compiled code is exercised on eight of them
  (NV-1, NV-2, NV-Q, NV-R, NV-S, NV-QP, NV-L and NV-A) by `proof/tools/NVEmit.lean` and on the regression corpus.
- What `#erase` does around `Erasure.eraseEntry`, which the theorems do not cover: the
  elaboration of the input and of the `config` term (`Erasure.eraseElab`,
  `LeanToLambdaBox/Erasure/Command.lean`, which evaluates the configuration with `unsafe`
  `Lean.Elab.Term.evalTerm`), the printer `Serialize.to_sexpr` that writes the program as an
  S-expression (`LeanToLambdaBox/Printing.lean`, whose term printer `LBTerm.to_sexpr` is
  `partial`), the `.inlinings` file built from the second component of the result (the
  statements ignore it), and the `.mli` signature.

## Entries

### DV-1

- **Our artifact:** `proof/EraseProof/Spec.lean`: `EraseProof.SrcEval` evaluates and
  `EraseProof.Erases` erases Lean terms (`Expr`), the eraser's input, whose types are those of
  their images in Metalean's syntax `Metalean.Expr` under the bridge `EraseProof.TrM` (with
  `EraseProof.SatTr`, `EraseProof.MLCtx` and the name table `EraseProof.Binds`).
- **Reference artifact:** PCUIC's weak call-by-value evaluation `eval`
  (`pcuic/theories/PCUICWcbvEval.v:231`; MC §5.6) and the erasure relation `erases`
  (`erasure/theories/Extract.v:88`; MC §7.3, Fig. 18), both on PCUIC terms, the syntax PCUIC's
  typing judges; Letouzey §3.1 (CIC terms).
- **What differs:** the syntax that evaluates and the syntax that is typed differ. `Expr` has
  `let`, metadata, projections, literals, and constructors, recursors, inductive types and
  quotients as constants applied in spines; `Metalean.Expr` is intrinsically scoped, inlines
  `let`, and has saturated nodes for inductive types, constructors (fields in Metalean's order,
  `EraseProof.MetaOrderOK`), recursors and quotients. `EraseProof.TrM` relates the two rule by rule
  after Metalean's translator (`Metalean/Frontend/Translate.lean:318-347`); a spine with fewer
  arguments than the node takes is related to the η-term of Metalean's total builders (trust
  base) applied to its arguments. `EraseProof.SrcEval` evaluates a `let` as `eval_zeta`
  (`pcuic/theories/PCUICWcbvEval.v:241`) does, and `EraseProof.Erases` relates a `let` to a λ□
  `tLetIn` as `erases_tLetIn` does, with the binder rules taking the translation of the binder's
  type as a premise. A projection's levels and parameters are those of its major's type in a
  context that extends the context of the translation (`EraseProof.TypedExt`), the context in
  which the Metalean term places the major: inside a minor premise that `wrapCase`
  (`Metalean/Frontend/Translate.lean:84`) wraps, it contains the case telescope; the translator
  reads them from the type it infers in the context of the translation.
- **Why it is forced:** the eraser consumes `Expr`, and Metalean's typing is stated on its own
  syntax. Metalean's translator is a `partial` function that decides projections with an
  unverified type inference, so it cannot be used in a statement; a relation modelled on it can.
  Typing the major in the context of the translation would need, after a substitution inside a
  wrapped minor premise, to move a typing out of the case telescope (strengthening), which
  Metalean does not prove; in the context where the major lives, the typing follows from the
  typing of the whole term by inversion.
  The λ□ image of a `let` evaluates the value first (`eval_zeta`,
  `erasure/theories/EWcbvEval.v:134`), which no semantics on `Metalean.Expr`, where the value is
  substituted, can follow.
- **What was considered instead:** a source semantics on `Metalean.Expr`, which loses the
  evaluation of `let` values and every term shape that the translator saturates; Metalean's
  translator as a function, which is `partial` (opaque to proofs) and outside the verified part
  of Metalean (check C6).

### DV-2

- **Our artifact:** `proof/EraseProof/Spec.lean`, the rules `EraseProof.TrM.lit`,
  `EraseProof.TrM.projStruct` and `EraseProof.TrM.projProof` of `EraseProof.TrM`.
- **Reference artifact:** MetaRocq's translation of Template terms into PCUIC terms, `trans`
  (`template-pcuic/theories/TemplateToPCUIC.v:63`; MC §9).
- **What differs:** Not applicable here. In the lean4lean experiment the bridge had no rule for
  literals and projections; `EraseProof.TrM` translates Nat literals as Metalean's fast checker
  does and projections as Metalean's translator does (`Metalean/Checker/Slow/Projection.lean:54`).
- **Why it is forced:** not applicable: the gap was forced by lean4lean's lemmas on projections,
  which are not proved, and by its lack of inductive types; Metalean has both.
- **What was considered instead:** dropping the id, which would leave the citations of the earlier
  register without an entry.

### DV-3

- **Our artifact:** `proof/EraseProof/Spec.lean`: `EraseProof.ProgEnv` with
  `EraseProof.IndBlock`, `EraseProof.ConstTyped`, `EraseProof.BindsExt` and `EraseProof.findDecl`,
  the relation between a program's declarations, a newest-first list of Lean `ConstantInfo`s, and
  a Metalean environment with its name table; `EraseProof.SubEnv`, and the evaluation environment
  `EraseProof.EvalEnv`, whose declarations are a sub-environment of the program in
  `EraseProof.erases_correct_statement` (hypothesis `SubEnv σ.decls P`) and the dependency closure
  in `EraseProof.erasePure_erases_statement` (`EraseProof.evalEnvOf view cfg decls`).
- **Reference artifact:** the well-formed global environment `wf_ext`
  (`pcuic/theories/PCUICTyping.v:507`; MC §3.6), whose declarations are a newest-first list
  searched by `lookup_env` (`common/theories/Environment.v:483`); MetaRocq's `erase_correct`
  (`erasure/theories/ErasureFunctionProperties.v:657`) evaluates the erased term over the erasure
  of the dependency closure `erase_global_deps` (`erasure/theories/ErasureFunction.v:1602`).
- **What differs:** the environment is a list of Lean declarations related, entry by entry, to a
  Metalean environment as Metalean's loader builds it (`Metalean/Checker/Slow/Loader.lean:55-130`):
  axioms, non-recursive definitions, theorems as opaque constants (DV-24), opaques, inductive blocks
  with their constructors and recursors, quotients; names are fresh, and a table maps each Lean name
  to its Metalean head. Each recursor's Lean type is related to Metalean's by translation and,
  besides, syntactically in one point: the minor premise of a constructor has
  `nfields + 2 * nrecFields` leading Π's, one per field and per induction hypothesis
  (`EraseProof.IndBlock`, field `minors`), and the major premise's type is headed by the recursor's
  inductive (field `recMajor`); each quotient constant has the kind of its name, and the

  Lean types of `Quot`, `Quot.mk` and `Quot.lift` are an arity and Π-telescopes of their arities, as
  Lean's kernel declares them (`EraseProof.QuotShape`). The relation-level theorem types in the environment of the whole program `P` and
  evaluates over a sub-environment of it.
- **Why it is forced:** the eraser reads Lean declarations (`Erasure.EnvView`), while a Metalean
  environment `Metalean.Env` is a list of entries typed by their signatures and addressed by
  position, not by name. The minor arities are the count the shipping `casesOn` recognizer reads
  from the recursor's Lean type (`Erasure.minorArity`), and the translation fixes a type only up to
  metadata and definitional equality, so it does not fix that count. Evaluation and the λ□
  dependencies range over the closure because a λ□ constant is found by its kername (DV-14), and
  kernames are injective only where `Erasure.collectDeps` checks it, on the closure; the λ□
  environment the eraser emits holds the closure only.
- **What was considered instead:** Metalean's loader itself, which is `partial` code outside the
  verified part of Metalean (check C6); one environment for typing and evaluation, which fails
  for programs whose names collide outside the closure.

### DV-4

- **Our artifact:** `proof/EraseProof/Spec.lean`, `EraseProof.IsErasable` with
  `EraseProof.IsArity`.
- **Reference artifact:** `isErasable` (`erasure/theories/Extract.v:18`; MC §7.3, Fig. 18), with
  `isArity` (`pcuic/theories/PCUICTyping.v:29`) and `Sort.is_propositional`
  (`common/theories/Universes.v:1528`).
- **What differs:** Not applicable here. The propositional case is Metalean's typing at `Prop`
  (`E[Γ] ⊢ T : .prop`), and `EraseProof.IsArity` is an arity up to Metalean's conversion, as
  `isErasable` is up to PCUIC's; Lean has no `SProp`, a difference of the object theory.
- **Why it is forced:** not applicable: in the lean4lean experiment the test had to be "the level
  is zero under every assignment" because lean4lean's levels are syntax; Metalean's levels are
  compared semantically, so its `Prop` already is that test. The shipping oracle's structural test
  (`Erasure.Pure.alwaysZero`) is a sound approximation of it.
- **What was considered instead:** dropping the id, which would leave the shipping citation
  without an entry.

### DV-7

- **Our artifact:** `proof/EraseProof/Spec.lean`: the rule `EraseProof.ProgEnv.defn` (a
  definition's `all` is its own name), `EraseProof.ErasesDecl` (no recursive branch) and
  `EraseProof.ErasesDeps` (its rule for λ□ `tFix`, `EraseProof.ErasesDeps.fix`, is for the
  fixpoints of erased recursors, DV-30, not for recursive definitions).
- **Reference artifact:** PCUIC's fixpoints `tFix`, `eval_fix`
  (`pcuic/theories/PCUICWcbvEval.v:273`) and `erases_tFix` (`erasure/theories/Extract.v:122`).
- **What differs:** Not applicable here: no source program of the fragment is recursive.
  Metalean's environment has no recursive definitions (recursion goes through recursors). The
  fragment test excludes every definition with a compiled recursive companion except, under
  `structural := .kernel`, a definition by structural recursion, whose kernel definition recurses
  through `T.brecOn` and the recursor and does not mention itself. It also excludes every
  definition, theorem and opaque of a mutual block. So the recursive branch of the eraser's
  `visitMutual` (`Erasure.isRecursiveDecl`) is not reached on the pure path for an input of the
  fragment.
- **Why it is forced:** not applicable: in the lean4lean experiment recursive constants were in
  the fragment, modelled as fixpoints; Metalean has none to model.
- **What was considered instead:** dropping the id, which would leave the shipping citations
  without an entry.

### DV-10

- **Our artifact:** `proof/EraseProof/Spec.lean`, `EraseProof.EvalEnv.unfold?`: the source
  semantics unfolds definitions only; an opaque constant has no δ rule.
- **Reference artifact:** `eval_delta` (`pcuic/theories/PCUICWcbvEval.v:247`; MC §5.6), which
  unfolds every constant whose declaration has a body.
- **What differs:** a Lean `opaque` declaration has a value, and the eraser emits it as the body of
  its λ□ constant, but `EraseProof.EvalEnv.unfold?` does not unfold it: evaluation is stuck where
  λ□ evaluation unfolds.
- **Why it is forced:** Metalean's environment keeps an opaque constant without its value
  (`Metalean.Entry.opaque`, `Metalean/Syntax/Env.lean:21`), so unfolding it is not a definitional
  equality of Metalean, and the final theorem's last conjunct relates every evaluation to one.
- **What was considered instead:** unfolding opaques as `eval_delta` does, under which evaluation
  no longer preserves types: with `opaque c : T := t` and an axiom `f : (x : T) → F x`, `f c : F c`
  would evaluate to `f t : F t`, and Metalean does not equate `F c` with `F t`.

### DV-11

- **Our artifact:** `proof/EraseProof/Spec.lean`: `EraseProof.EvalEnv.isAtom` with
  `EraseProof.EvidentZero`, `EraseProof.DeltaFree`, `EraseProof.EvidentProp` and
  `EraseProof.IsThm`, the rule `EraseProof.SrcEval.constAtom` and the spines
  `EraseProof.AtomSpine`: the constants without a δ rule that are values; and the premise
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
  value whose erasure, a λ□ constant without a body, is not a λ□ value; no δ-free constant a value,
  under which programs that pass lemmas never evaluate.

### DV-12

- **Our artifact:** `proof/EraseProof/Spec.lean`: `EraseProof.EvalEnv` with its field
  `axiomatized`, `EraseProof.EvalEnv.unfold?`, `EraseProof.evalEnvOf` (the shipping test
  `Erasure.axiomatized`), and the remapped branch of `EraseProof.ErasesDecl`.
- **Reference artifact:** `eval` (`pcuic/theories/PCUICWcbvEval.v:231`), whose `eval_delta` unfolds
  a constant exactly when it has a body, and `erases_constant_body`
  (`erasure/theories/Extract.v:264`).
- **What differs:** a definition that the configuration remaps to foreign code (`@[extern]` under
  `extern := .preferAxiom`) has a Lean value but no δ rule, and `EraseProof.ErasesDecl` relates it
  to a λ□ declaration without a body, a pair `erases_constant_body` excludes.
- **Why it is forced:** the eraser emits such a declaration as a λ□ axiom so that it is linked
  with its foreign implementation; neither Metalean nor λ□ models that implementation, so the
  source can only leave the constant stuck, as λ□ leaves the axiom.
- **What was considered instead:** excluding programs that mention a remapped constant, which
  also excludes programs that never evaluate it.

### DV-13

- **Our artifact:** `proof/EraseProof/Spec.lean`: `EraseProof.MLCtx` (with `EraseProof.MLCtx.findF`)
  and the rules `EraseProof.TrM.fvar` and `EraseProof.Erases.fvar`: the eraser's free variables,
  related to Metalean variables and to themselves in λ□; `proof/EraseProof/Target.lean`,
  `EraseProof.hasFVar` and `EraseProof.LenvClosed`: no body of the λ□ environment has a free
  variable.
- **Reference artifact:** PCUIC's de Bruijn contexts and MetaRocq's `erase`
  (`erasure/theories/ErasureFunction.v:989`), which works on de Bruijn indices; `closed_env`
  (`erasure/theories/EGlobalEnv.v:181`).
- **What differs:** the shipping traversal is locally nameless: it opens binders with free
  variables and closes them with `abstract` before a body is stored. The bridge and the erasure
  relation therefore have rules for free variables, and the closedness of the λ□ environment
  includes the absence of free variables.
- **Why it is forced:** the theorem is about the shipping traversal, which uses Lean's locally
  nameless `Expr` interface (`LeanToLambdaBox/Erasure/Pure.lean`); its intermediate states contain
  free variables, which the induction over the traversal must relate.
- **What was considered instead:** a relation on closed terms only, under which no intermediate
  state of the traversal is related.

### DV-14

- **Our artifact:** `proof/EraseProof/Spec.lean`: the rule `EraseProof.ErasesDeps.const`, indexed
  by the source constant `c` and finding its λ□ declaration at `toKername c`;
  `EraseProof.KernameInj`, the hypothesis `KernameInj σ.decls` of
  `EraseProof.erases_correct_statement`; and `EraseProof.BlockNamesInj`, a hypothesis of
  `EraseProof.collectDeps_ok_of_statement`.
- **Reference artifact:** `erases_deps_tConst` (`erasure/theories/Extract.v:324`; MC §7.4), where
  the PCUIC and the λ□ declaration are found at the same kername.
- **What differs:** a Lean constant and its λ□ constant have different names (`toKername`), and two
  Lean names may have the same kername, so the rule names the source declaration it uses, and the
  simulation assumes that kernames are distinct on the evaluation environment.
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
  for fixpoints and primitive values, which the fragment does not produce (DV-7, DV-26).
- **Why it is forced:** the theorem is about the eraser's output, an `LBTerm`, the λ□ that
  peregrine reads; the missing terms cannot occur in it.
- **What was considered instead:** extending `LBTerm`, a shipping change no output needs; a
  separate transcription of `term`, which every statement would reach through a translation.

### DV-17

- **Our artifact:** `proof/EraseProof/Statements.lean`: `EraseProof.erase_correct_statement`
  assumes a run of `Erasure.eraseEntry` that returns a program (`hrun`) and an evaluation of the
  source (`hev`); `EraseProof.collectDeps_ok_of_statement` bounds the closure by the fragment
  test's fuel (`decls.length ≤ collectFuel`). The shipping oracle, fragment test and traversal are
  fuelled (`Erasure.oracleFuel`, `Erasure.collectFuel`, `Erasure.travFuel`).
- **Reference artifact:** MetaRocq's `is_erasableb` (`erasure/theories/ErasureFunction.v:894`)
  and `erase` (`erasure/theories/ErasureFunction.v:989`; MC §7.2), total under the hypothesis
  `NormalizationIn` (`pcuic/theories/PCUICSN.v:44`); `erases_erase`
  (`erasure/theories/ErasureFunction.v:1228`) and `erase_correct`
  (`erasure/theories/ErasureFunctionProperties.v:657`), which hold for every input.
- **What differs:** the final theorem is partial correctness: it says nothing about a run that
  fails (out of fuel, for example, an error of `#erase` and never an output) and nothing about a
  source term that does not evaluate. No statement has a normalization hypothesis.
- **Why it is forced:** Metalean proves neither normalization nor canonicity, so a total oracle by
  well-founded recursion cannot be defined from its results, and a normalization hypothesis would
  stand in for a theorem Metalean does not have. For the same reason the call-by-value source
  semantics `EraseProof.SrcEval` is tied to Metalean only through definitional equality (the last
  conjunct of the final theorem), and nothing shows that a typed program evaluates.
- **What was considered instead:** a normalization hypothesis as MetaRocq's `NormalizationIn`,
  which would assume what Metalean does not prove.

### DV-23

- **Our artifact:** `proof/EraseProof/Spec.lean`: `EraseProof.EvalEnv.etaSpine?` (with
  `EraseProof.piInst`, `EraseProof.lamsOf`, `EraseProof.specialArity`), the rule
  `EraseProof.SrcEval.eta` and `EraseProof.ShortSpine`: a constructor, recognized `casesOn`,
  `Quot.mk`, `Quot.lift` or recursor spine with fewer arguments than its arity evaluates to its
  η-expansion, the arguments unevaluated under the new binders; and the rule
  `EraseProof.Erases.eta`: such a spine erases as its η-expansion.
- **Reference artifact:** PCUIC's `eval` evaluates the arguments of an application eagerly
  (`eval_app_cong`, `pcuic/theories/PCUICWcbvEval.v:311`; `eval_construct`,
  `pcuic/theories/PCUICWcbvEval.v:303`); MetaRocq η-expands constructors in λ□ by a separate pass
  (`isEtaExp`, `erasure/theories/EEtaExpanded.v:61`).
- **What differs:** an under-applied constructor, `casesOn`, quotient or recursor spine is not a
  value whose arguments are values: it steps to a λ that keeps its arguments as they are.
- **Why it is forced:** the eraser η-expands such spines (`withAppEtaToMinArity`,
  `LeanToLambdaBox/Erasure.lean`), and the λ□ value of the expansion is a closure whose arguments
  are not evaluated; with eager evaluation the source value has an evaluated argument where the λ□
  value has the unevaluated one, and the final theorem is false (on `P2.mk ((fun x => x) B.t)`).
  Metalean's constructor nodes are saturated, so the bridge relates such a spine to the same
  η-expansion (DV-1).
- **What was considered instead:** PCUIC's eager evaluation, under which the final theorem is false
  on under-applied constructors; an η-expansion pass on the source before evaluation, which is not
  what the eraser runs.

### DV-24

- **Our artifact:** `proof/EraseProof/Spec.lean`: `EraseProof.EvalEnv.unfold?` (no δ for
  theorems), `EraseProof.IsThm` in `EraseProof.EvalEnv.isAtom` (theorems are atoms), the rules
  `EraseProof.SrcEval.casesProof` and `EraseProof.SrcEval.projProp`, and `EraseProof.PropProj`.
- **Reference artifact:** `eval_delta` (`pcuic/theories/PCUICWcbvEval.v:247`), which unfolds a
  lemma like any constant with a body; λ□'s `eval_iota_sing` (`erasure/theories/EWcbvEval.v:162`)
  and `eval_proj_prop` (`erasure/theories/EWcbvEval.v:238`), which reduce a `case` or a projection
  on a proof erased to `□`.
- **What differs:** theorems are not unfolded, so a proof may evaluate to an atom spine instead of
  a constructor. A `casesOn` of a field-less `Prop` constructor on such a proof continues with the
  alternative (`casesProof`), and a projection of a `Prop` structure out of it is a neutral value
  (`projProp`). A `casesOn` on a lemma of an inductive with proof fields does not evaluate, nor
  does a recursor on a lemma (`True.rec`, `And.rec` or `PUnit.rec.{_, 0}` applied to a theorem):
  `SrcEval.recIota` needs a constructor value as its major premise (DV-30), while λ□ reduces the
  erased fixpoint's `case` on `□`. Programs defined by well-founded recursion, whose recursion
  reduces only through a proof of accessibility, do not evaluate either: the final theorem holds
  vacuously for all of these, and the fragment test excludes the last (DV-26).
- **Why it is forced:** Metalean's loader adds a theorem as an opaque constant, its statement only
  (`Metalean/Checker/Slow/Loader.lean:65-72`, `:126`), and `EraseProof.ProgEnv` follows it: the value of
  a theorem is not translated, and typically uses recursors and tactics outside the fragment, so
  unfolding it has no Metalean counterpart for the last conjunct of the final theorem.
- **What was considered instead:** δ for theorems with a translated value, which excludes every
  program that mentions a lemma whose proof leaves the fragment; a recursor analogue of
  `casesProof`, which covers only recursors of a field-less `Prop` constructor (`True.rec`;
  `And.rec` on a lemma stays stuck as `And.casesOn` does) and needs its own subject-reduction
  case through proof irrelevance and the recursor ι.

### DV-25

- **Our artifact:** `proof/EraseProof/Spec.lean`: `EraseProof.EvalEnv.casesOn?` (the shipping
  recognizer `Erasure.casesInfo?`), the rules `EraseProof.SrcEval.casesIota`,
  `EraseProof.SrcEval.casesLitZero` and `EraseProof.SrcEval.casesLitSucc`; the rules
  `EraseProof.Erases.cases` and `EraseProof.Erases.casesReduced` with `EraseProof.CasesReduced` and
  `EraseProof.FieldsErasable`.
- **Reference artifact:** PCUIC's `tCase`, a term, with `eval_iota`
  (`pcuic/theories/PCUICWcbvEval.v:253`); `erases_tCase` (`erasure/theories/Extract.v:109`); λ□'s
  `eval_iota_sing` (`erasure/theories/EWcbvEval.v:162`).
- **What differs:** Lean has no case term: `T.casesOn` is a definition through the recursor
  `T.rec`. The source treats a recognized `casesOn` as primitive, without δ, reducing on the
  constructor its major evaluates to; it does not unfold it to the recursor, which has a rule of
  its own (`EraseProof.SrcEval.recIota`, DV-30). A `casesOn` on a
  one-constructor inductive whose sort may be `Prop` erases to its alternative applied to `□`s,
  without a λ□ `case` (`casesReduced`), the reduction `eval_iota_sing` makes at run time.
- **Why it is forced:** the eraser translates recognized `casesOn` spines to λ□ `case` and never
  unfolds them (`LeanToLambdaBox/Erasure.lean`); a recursor it erases to a λ□ fixpoint of its own
  (DV-30), not to a `case`. The reduced form is what the eraser emits when the discriminant's
  sort may be `Prop`, since λ□ marks a whole block as propositional or not.
- **What was considered instead:** δ-unfolding `casesOn` to `T.rec` and evaluating the recursor,
  which has no counterpart in the eraser's output.

### DV-26

- **Our artifact:** `proof/EraseProof/Statements.lean`: the hypothesis `hfrag` of
  `EraseProof.erase_correct_statement`, that the shipping fragment test `Erasure.collectDeps`
  accepts the input; and `EraseProof.collectDeps_ok_of_statement`, a sufficient condition for it
  (`EraseProof.ReadClosed`, `EraseProof.PhaseIDecl`, `EraseProof.PlainExpr`,
  `EraseProof.RecShaped`, `EraseProof.KernameInj`, `EraseProof.BlockNamesInj`), which covers the
  recursors and the structural recursion that the test admits.
- **Reference artifact:** MetaRocq's `erase_correct`
  (`erasure/theories/ErasureFunctionProperties.v:657`), which holds for every well-typed term.
- **What differs:** the final theorem covers the inputs the fragment test accepts. Its exclusion
  classes: recursors that a read expression names other than those of a single inductive without
  indices that eliminates into every sort and whose induction hypotheses take no arguments and are
  about the last fields (`EraseProof.RecInFragment`; `Erasure.recShapeInFragment`), and those the
  eraser keeps as constants (`Erasure.recStaysConstant`), recursive definitions (every definition
  with a compiled `_unsafe_rec` companion, except, under `structural := .kernel`, a definition by
  structural recursion, `Erasure.isStructuralRecursive`), definitions, theorems and opaques of
  mutual blocks (whose `all` is not their own name alone, as in a mutual structural block),
  `partial`, `unsafe` and `implemented_by` constants, nested inductives, string
  literals, Nat literals and Nat or Int constructors under `nat := .machine`, `casesOn` on a
  constructor with an index field, eliminations of an inductive whose sort may be both `Prop` and
  not `Prop`, `remove_irrel_constr_args`, metavariables. On the corpus (294 `#erase` calls), 225
  are in the fragment, 66 out (20 of them recursive definitions, one of which, `Defects.log2`, is
  defined by well-founded recursion) and 3 are rejected for a name collision; with
  `structural := .kernel` as the default, 233 are in, 57 out and 4 rejected for a name
  collision.
- **Why it is forced:** `#erase` sends an input outside the fragment to the `Meta` path
  (`Erasure.route`, `LeanToLambdaBox/Erasure/Entry.lean:321-325`), `CoreM` code about which
  nothing is proved, and some of the excluded constructs have no Metalean counterpart (nested
  inductives, `unsafe` constants).
  Typed inputs outside the fragment exist, so the hypothesis cannot be derived from typing as in
  the lean4lean experiment.
- **What was considered instead:** deriving the hypothesis from `henv`, `hview` and `he`, which is
  false on typed programs that use a mutual recursor; leaving the fragment unstated, which makes it
  impossible to tell how much the hypothesis excludes, which `collectDeps_ok_of` states.

### DV-27

- **Our artifact:** `proof/EraseProof/FirstOrder.lean`: `EraseProof.FirstOrderValue`, the values
  on which `EraseProof.erase_correct_firstorder` determines the λ□ value, and their structural
  erasure `EraseProof.foErase`.
- **Reference artifact:** `firstorder_value` (`pcuic/theories/PCUICFirstorder.v:115`), with the
  first-order inductives of `firstorder_con` (`pcuic/theories/PCUICFirstorder.v:52`), and
  `erase_correct_strong` (`erasure/theories/ErasureFunctionProperties.v:2269`).
- **What differs:** MetaRocq's first-order value is a typed constructor application of an inductive
  that is not propositional, every argument (parameters included) a first-order value, and its
  first-order inductives have neither type parameters nor proof fields. Ours is syntactic: a
  constructor node needs its inductive's declared sort to be never zero (`Level.isNeverZero`), and
  two kinds of leaves erased to `□` are admitted as arguments: constructor applications of an
  inductive declared in `Prop`, and atom spines (type formers such as `Nat` or `List Nat` as type
  parameters, theorems or axioms applied to arguments as proof fields). The conclusion compares
  with the structural erasure, which keeps parameters (DV-23), instead of the erasure function's
  output.
- **Why it is forced:** a Lean inductive in `Sort u` is universe-polymorphic over `Prop`: at
  `u := 0` its constructor applications are proofs and erase to `□` or to a λ□ constructor, so
  `¬ PropInductive` (Metalean's block level) does not determine the value; the declared sort being
  never zero does (`EraseProof.SimInd.ctor_not_erasable`). λ□ keeps parameters in constructor
  applications (DV-23), and Lean's data inductives take type parameters (`Prod`, `Option`, `List`)
  and its structures proof fields (`Subtype`, `Fin`), so MetaRocq's notion would leave only
  monomorphic inductives without proofs; the relation erases an atom spine in many ways (an
  application of an atom may erase to `□` applied to `□`), and only the λ□ value restricts it to
  `□` (`EraseProof.Erases.atomSpine_box`). There is no erasure function on the relation's side to
  compare with.
- **What was considered instead:** MetaRocq's notion exactly (all arguments first-order, the
  inductive not propositional), which is false for universe-polymorphic inductives at `Prop` and
  excludes every value with a type parameter; comparing with `Erasure.erasePure`'s output, which
  reads the configuration and the view instead of the value alone.

### DV-28

- **Our artifact:** `proof/EraseProof/Spec.lean`: the rule `EraseProof.ErasesAlt.intro`
  (`proof/EraseProof/Spec.lean:1167`), which η-introduces a `casesOn` alternative.
- **Reference artifact:** the alternatives of `erases_tCase`
  (`erasure/theories/Extract.v:109`), related to the erased branches by the erasure relation under
  the case's branch contexts; the relation has no η-introduction rule.
- **What differs:** the rule η-introduces an alternative to the arity of its constructor, and has
  no premise on the alternative's shape. Before, it carried `∀ x A b bi, e ≠ .lam x A b bi`, so
  that a λ alternative was related only by `ErasesAlt.lam` (peeling):

      | intro : (∀ x A b bi, e ≠ .lam x A b bi) → TrM E B lps Γ Δ e e' →
          E[Γ] ⊢ e' : .forallE A' B'' → … → ErasesAlt E B lps σ Γ Δ (k + 1) e (nm :: ns, t)

  After:

      | intro : TrM E B lps Γ Δ e e' →
          E[Γ] ⊢ e' : .forallE A' B'' → … → ErasesAlt E B lps σ Γ Δ (k + 1) e (nm :: ns, t)

  The relation is more permissive: a λ alternative is also related to the λ□ β-redex
  `.app a' (.bvar 0)` of its peeled branch, which evaluates to the same value.
- **Why it is forced:** the substitution lemma `EraseProof.Erases.inst` is false with the premise.
  An alternative that is a variable erases by `intro` to the branch `([x], .app (.bvar (k + 1))
  (.bvar 0))`; substituting a λ `a` for the variable gives the source alternative `a`, which only
  `ErasesAlt.lam` can relate, and to the erasure of its body, never to the β-redex
  `.app a' (.bvar 0)`. The substitution lemma is needed for the β and ζ steps of the simulation.
- **What was considered instead:** keeping the premise and restricting substitution to non-λ
  values, which excludes the β-redexes the simulation has to step; adding a rule that relates a
  λ alternative to the β-redex only under the substitution lemma's hypotheses, which is the same
  relation with a more complicated shape.

### DV-29

- **Our artifact:** `proof/EraseProof/Spec.lean`: the rules `EraseProof.SrcEval.quotMk` and
  `EraseProof.SrcEval.quotLift`; `EraseProof.quotEvalArity` in `EraseProof.specialArity`, so that
  `EraseProof.SrcEval.eta` and `EraseProof.Erases.eta` η-expand `Quot.mk` and `Quot.lift` spines
  with missing arguments; the quotient clauses of `EraseProof.OwnRules`, under which
  `EraseProof.EvalEnv.isAtom` makes the type former `Quot` an atom, of `EraseProof.BlocksCong`
  (`Quot.mk` spines) and of `EraseProof.SpecialSpine`; the rules `EraseProof.Erases.quotMk` and
  `EraseProof.Erases.quotLift`.
- **Reference artifact:** none: PCUIC has no primitive quotients. The closest rules are `eval_beta`
  (`pcuic/theories/PCUICWcbvEval.v:234`) and `eval_construct`
  (`pcuic/theories/PCUICWcbvEval.v:303`) of `eval`, and `erases_tApp`
  (`erasure/theories/Extract.v:101`) and `erases_tConstruct` (`erasure/theories/Extract.v:106`) of
  `erases`.
- **What differs:** Lean's quotients are primitive constants with their own reduction, the quotient
  ι `Quot.lift f h (Quot.mk r a) ⤳ f a` (`quotIota`, `Metalean/Syntax/Reduction.lean:74`). The
  source evaluates `Quot.mk α r a` by evaluating the element `a`, the type and the relation
  unevaluated, and `Quot.lift α r β f h q` by evaluating `f` to a λ and `q` to `Quot.mk α' r' a`
  and continuing with the λ's body at `a`; spines with fewer arguments are η-expanded as
  constructor spines are (DV-23), and a `Quot.mk` value blocks application congruence as a
  constructor value does. The type former `Quot` is an atom, as an inductive type former is
  (DV-11): a quotient type `Quot α r` evaluates its arguments by application congruence and is a
  value, so it may be a constructor parameter or a β-argument, and it erases only to `□`.
  `Quot.ind` has no rule: a program that evaluates it, for instance as an argument, is stuck, and
  the final theorem holds vacuously for it. The erasure represents a quotient by its elements:
  `Quot.mk α r a` erases as `a` and `Quot.lift α r β f h q` as `f q`, applied to the erasures of
  the arguments beyond the arity.
- **Why it is forced:** the reference has no rule for quotients, and the eraser erases the quotient
  constants in this way, as Lean's code generator does (`visitConstApp`,
  `LeanToLambdaBox/Erasure.lean:949`). The source rule is Metalean's quotient ι, which the
  subject-reduction theorem `EraseProof.SrcEval.defeq` justifies through
  `Metalean.WHRed.quotIota_defeq`. A quotient type is in weak-head normal form in Metalean (no
  rule of `Metalean.WHRed` reduces a `Metalean.Expr.quot` node), so it is a value there too.
  `Quot.ind` is a proof (Metalean reduces it on `Quot.mk` by `quotIndIota`,
  `Metalean/Syntax/Reduction.lean:78`), but its statement ends in an application of its motive and
  is not an evident proposition, so the oracle is not known to erase its spines and the eraser may
  keep it as a λ□ axiom, while an atom erases only to `□`.
- **What was considered instead:** erasing `Quot.mk` and `Quot.lift` to λ□ axioms, under which
  every program that computes through a quotient is stuck in λ□; no source rule for quotients,
  under which such programs do not evaluate and the final theorem says nothing about them.

### DV-30

- **Our artifact:** `proof/EraseProof/Spec.lean`: the rule `EraseProof.SrcEval.recIota` with
  `EraseProof.natLitCtor`; the rules
  `EraseProof.Erases.recLet` and `EraseProof.Erases.recFix` with `EraseProof.RecFixOf`,
  `EraseProof.recMembers`, `EraseProof.recLets` and `EraseProof.EvalEnv.recBlock?`; the recursor
  clause of `EraseProof.SpecialSpine`; the recursor exclusion of `EraseProof.Erases.const`; the
  recursor clause of `EraseProof.specialArity`; the clauses `EraseProof.IndBlock.recIHs` and
  `EraseProof.IndBlock.recMajor`; `EraseProof.RecInFragment` in `EraseProof.PhaseIDecl`;
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
  `Nat.zero`, `k + 1` as `Nat.succ` applied to the literal `k`, as Lean's kernel reads it with
  `nat_lit_to_constructor` before the ι; Metalean has no literal, `TrM.lit` translates one to the
  unary chain `natLitM`, the translation of its constructor form), then each induction hypothesis
  `T.rec ps ms mvs f` (one per recursive field `f`,
  in the order of the minor's hypotheses) to a value, and continuing with the minor's value applied
  to the fields and these values. The parameters and the motive are not evaluated. There is no
  source ι for recursors of mutual, nested or indexed inductives, for higher-order recursive
  fields, for recursive fields before non-recursive ones, nor on a major that evaluates to a proof
  other than a constructor value, such as a theorem (DV-24; `recK` and
  structure η are not rules). Recursor spines with missing arguments are η-expanded, as constructor
  spines are (DV-23). The fragment test admits exactly the recursors of this shape that the eraser
  does not keep as constants (`RecInFragment`). The erasure is the eraser's: the λ□ fixpoint
  of `recFix` under `let`s of the erased minors, applied to the erased major and the extra
  arguments (`Erases.recLet`); `Erases.recFix` relates the same fixpoint with closed λ□ values of
  the minors substituted, the form λ□ reaches after the `let`s and in which the recursive calls
  appear.
- **Why it is forced:** the reference has no recursors, and the eraser compiles them to λ□
  fixpoints (`visitRec`, `LeanToLambdaBox/Erasure.lean:1003`). λ□ evaluates the minors (`let`) and
  every argument of an application by value, so the source evaluates the minors and the induction
  hypotheses first; the restrictions make Metalean's ι apply to the minors as they are, unwrapped by
  `wrapCase` (`RecWhred.orders_identity`), which the subject-reduction theorem
  `EraseProof.SrcEval.defeq` uses through `Metalean.WHRed.iota`. `IndBlock.recIHs` states which
  field each induction hypothesis of the recursor's Lean type is about, as Lean's kernel generates
  it; without it the pinned hypotheses do not fix that field (`ConstTyped` relates types only up to
  definitional equality). `IndBlock.recMajor` states that the major premise of the recursor's Lean
  type is of its inductive, as the kernel generates it; without it the fragment test's closure
  need not hold the block of a recursor it reads, which the evaluation over the closure needs.
  Under `nat := .peano` the eraser emits a Nat literal as λ□'s constructor chain (`visitLiteral`;
  `Erases.litZero`, `Erases.litSucc`), on which the erased fixpoint computes, and Lean's kernel
  reduces a recursor on a literal; without the reading of a literal major as its constructor form
  the source would be stuck on these programs (structural recursion on `2` included).
- **What was considered instead:** a source ι on the unevaluated induction hypotheses, under which
  the λ□ evaluation of a hypothesis the minor ignores has no source counterpart; erasing recursors to
  λ□ axioms (as `recStaysConstant` does for the excluded cases), under which every program that
  computes through a recursor is stuck in λ□; for a literal major, a source step `k + 1 ⤳
  Nat.succ k` on literals, which would make a literal a non-value, or a separate rule repeating the
  premises of `recIota` (as `casesLitZero` and `casesLitSucc` do for `casesOn`).
