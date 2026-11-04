# Divergence register

This register lists every place where the verification code on the `ml/verification` branch
(`proof/`, library `EraseProof`), or the statements it proves, diverge from the references —
Letouzey, "A New Extraction for Coq" (TYPES 2002), and Sozeau et al., "Correct and Complete Type
Checking and Certified Erasure for Coq, in Coq" (J. ACM 2025), including its MetaRocq sources at
commit `4b201296` (branch 9.1). The verification follows these references as closely as the
differences between Lean's kernel, as Metalean (`github.com/intgrah/metalean`, commit `9407ba4`)
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
  after Metalean's translator (`Metalean/Frontend/Translate.lean:316-345`); a spine with fewer
  arguments than the node takes is related to the η-term of Metalean's total builders (trust
  base) applied to its arguments. `EraseProof.SrcEval` evaluates a `let` as `eval_zeta`
  (`pcuic/theories/PCUICWcbvEval.v:241`) does, and `EraseProof.Erases` relates a `let` to a λ□
  `tLetIn` as `erases_tLetIn` does, with the binder rules taking the translation of the binder's
  type as a premise.
- **Why it is forced:** the eraser consumes `Expr`, and Metalean's typing is stated on its own
  syntax. Metalean's translator is a `partial` function that decides projections with an
  unverified type inference, so it cannot be used in a statement; a relation modelled on it can.
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
  Metalean environment as Metalean's loader builds it (`Metalean/Checker/Slow/Loader.lean:55-139`):
  axioms, non-recursive definitions, theorems as opaque constants (DV-24), opaques, inductive
  blocks with their constructors and recursors, quotients; names are fresh, and a table maps each
  Lean name to its Metalean head. The relation-level theorem types in the environment of the whole
  program `P` and evaluates over a sub-environment of it.
- **Why it is forced:** the eraser reads Lean declarations (`Erasure.EnvView`), while a Metalean
  environment `Metalean.Env` is a list of entries typed by their signatures and addressed by
  position, not by name. Evaluation and the λ□ dependencies range over the closure because a λ□
  constant is found by its kername (DV-14), and kernames are injective only where
  `Erasure.collectDeps` checks it, on the closure; the λ□ environment the eraser emits holds the
  closure only.
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
  `EraseProof.ErasesDeps` (no rule for λ□ `tFix`).
- **Reference artifact:** PCUIC's fixpoints `tFix`, `eval_fix`
  (`pcuic/theories/PCUICWcbvEval.v:273`) and `erases_tFix` (`erasure/theories/Extract.v:122`).
- **What differs:** Not applicable here: no source program of the fragment is recursive.
  Metalean's environment has no recursive definitions (recursion goes through recursors), and the
  fragment test excludes every definition with a compiled recursive companion, so the recursive
  branch of the eraser's `visitMutual` (`Erasure.isRecursiveDecl`) is not reached on the pure
  path for an input of the fragment.
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
  `EraseProof.SrcEval.eta` and `EraseProof.ShortSpine`: a constructor or recognized `casesOn` spine
  with fewer arguments than its arity evaluates to its η-expansion, the arguments unevaluated under
  the new binders; and the rule `EraseProof.Erases.eta`: such a spine erases as its η-expansion.
- **Reference artifact:** PCUIC's `eval` evaluates the arguments of an application eagerly
  (`eval_app_cong`, `pcuic/theories/PCUICWcbvEval.v:311`; `eval_construct`,
  `pcuic/theories/PCUICWcbvEval.v:303`); MetaRocq η-expands constructors in λ□ by a separate pass
  (`isEtaExp`, `erasure/theories/EEtaExpanded.v:61`).
- **What differs:** an under-applied constructor or `casesOn` spine is not a value whose arguments
  are values: it steps to a λ that keeps its arguments as they are.
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
  (`projProp`). A `casesOn` on a lemma of an inductive with proof fields does not evaluate, and
  programs defined by well-founded recursion, whose recursion reduces only through a proof of
  accessibility, do not evaluate either: the final theorem holds vacuously for them, and the
  fragment test excludes the latter (DV-26).
- **Why it is forced:** Metalean's loader adds a theorem as an opaque constant, its statement only
  (`Metalean/Checker/Slow/Loader.lean:122-127`), and `EraseProof.ProgEnv` follows it: the value of
  a theorem is not translated, and typically uses recursors and tactics outside the fragment, so
  unfolding it has no Metalean counterpart for the last conjunct of the final theorem.
- **What was considered instead:** δ for theorems with a translated value, which excludes every
  program that mentions a lemma whose proof leaves the fragment.

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
  constructor its major evaluates to; the recursor itself has no rule. A `casesOn` on a
  one-constructor inductive whose sort may be `Prop` erases to its alternative applied to `□`s,
  without a λ□ `case` (`casesReduced`), the reduction `eval_iota_sing` makes at run time.
- **Why it is forced:** the eraser translates recognized `casesOn` spines to λ□ `case` and never
  unfolds them (`LeanToLambdaBox/Erasure.lean`); recursors are outside the fragment, whose erasure
  the eraser does not handle. The reduced form is what the eraser emits when the discriminant's
  sort may be `Prop`, since λ□ marks a whole block as propositional or not.
- **What was considered instead:** δ-unfolding `casesOn` to `T.rec` and evaluating the recursor,
  which has no counterpart in the eraser's output.

### DV-26

- **Our artifact:** `proof/EraseProof/Statements.lean`: the hypothesis `hfrag` of
  `EraseProof.erase_correct_statement`, that the shipping fragment test `Erasure.collectDeps`
  accepts the input; and `EraseProof.collectDeps_ok_of_statement`, a sufficient condition for it
  (`EraseProof.ReadClosed`, `EraseProof.PhaseIDecl`, `EraseProof.PlainExpr`,
  `EraseProof.RecFree`, `EraseProof.KernameInj`, `EraseProof.BlockNamesInj`).
- **Reference artifact:** MetaRocq's `erase_correct`
  (`erasure/theories/ErasureFunctionProperties.v:657`), which holds for every well-typed term.
- **What differs:** the final theorem covers the inputs the fragment test accepts. Its exclusion
  classes: recursors other than the `T.rec` of a recognized `T.casesOn`, quotients, recursive
  definitions (structural or well-founded: every definition with a compiled `_unsafe_rec`
  companion), `partial`, `unsafe` and `implemented_by` constants, nested inductives, string
  literals, Nat literals and Nat or Int constructors under `nat := .machine`, `casesOn` on a
  constructor with an index field, eliminations of an inductive whose sort may be both `Prop` and
  not `Prop`, `remove_irrel_constr_args`, metavariables. On the corpus (294 `#erase` calls), 223
  are in the fragment, 68 out (20 of them recursive definitions, one of which, `Defects.log2`, is
  defined by well-founded recursion) and 3 are rejected for a name collision.
- **Why it is forced:** `#erase` sends an input outside the fragment to the `Meta` path
  (`Erasure.route`, `LeanToLambdaBox/Erasure/Entry.lean:270-274`), `CoreM` code about which
  nothing is proved, and some of the excluded constructs have no Metalean counterpart (nested
  inductives, `unsafe` constants); recursors and quotients are outside the eraser's pure path.
  Typed inputs outside the fragment exist, so the hypothesis cannot be derived from typing as in
  the lean4lean experiment.
- **What was considered instead:** deriving the hypothesis from `henv`, `hview` and `he`, which is
  false on typed programs that use a recursor; leaving the fragment unstated, which makes it
  impossible to tell how much the hypothesis excludes, which `collectDeps_ok_of` states.
