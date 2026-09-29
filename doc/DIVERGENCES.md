# Divergence register

This register lists every place where the verification code, or the statements it proves, diverge
from the references of spec §3.1–§3.2 — Letouzey, "A New Extraction for Coq" (§3.1), and Sozeau et
al., "Correct and Complete Type Checking and Certified Erasure for Coq, in Coq" (§3.2), including
its MetaRocq sources. The verification effort follows these references as closely as the
differences between Lean's kernel/`lean4lean`'s model and Rocq/PCUIC/MetaRocq allow; every place it
does not, for any reason, is recorded here.

Each entry has an id `DV-<n>` and exactly these fields:

- **Our artifact:** file and declaration on the `verification` branch that carries the divergence.
- **Reference artifact:** the paper section/figure/theorem (§3.1 or §3.2) and the MetaRocq
  `file:identifier` it corresponds to.
- **What differs:** the concrete difference between our artifact and the reference artifact.
- **Why it is forced:** the concrete reason the divergence is necessary — a difference between
  Lean's kernel and CIC, a gap in what `lean4lean` `master` provides, a scope boundary from §2 of
  the spec, or similar. This field must name a real constraint; "it was simpler" or "we chose to"
  is not a forcing reason.
- **What was considered instead:** the alternative(s) that would have kept the divergence from
  existing, and why each was rejected.

An entry without a forcing reason is a defect, not a divergence: it must be removed and the
statement or definition restated to match the reference instead.

Entries are headed `### DV-<n>`. They cite declarations by full name in backquotes (ours as
`EraseProof.<name>`, lean4lean's as `Lean4Lean.<name>`), our files by their path in the repository
(`proof/...`), lean4lean `master` sources by path and line (`Lean4Lean/...lean:<line>`), and
MetaRocq sources by path relative to the MetaRocq repository and line. Check C9 of
`proof/scripts/check.sh` fails if a cited `EraseProof.*` or `Lean4Lean.*` name is not a
declaration, a cited file or line does not exist, an entry's fields differ from the list above, or
an entry's artifact field cites no declaration of `EraseProof`.

The blueprint renders this register.

## Entries

### DV-2

- **Our artifact:** `proof/EraseProof/Typing/Basic.lean`, `EraseProof.TrS`, the translation of
  Lean terms into lean4lean's model.
- **Reference artifact:** MetaRocq's translation of Template terms into PCUIC terms, `trans`
  (`template-pcuic/theories/TemplateToPCUIC.v:63`; the MetaCoq paper's "certified type-preserving
  translation from Coq's syntax to PCUIC's syntax", §9), which erasure (§7) consumes; the
  translation `EraseProof.TrS` follows is lean4lean's `Lean4Lean.TrExprS`
  (`Lean4Lean/Verify/Typing/Expr.lean:75`).
- **What differs:** `EraseProof.TrS` has the rules of `Lean4Lean.TrExprS` except `lit` and `proj`:
  literals (`Expr.lit`) and projections (`Expr.proj`) have no translation, so terms containing
  them are outside the fragment. Like `Lean4Lean.TrExprS` and unlike `trans`, it is a relation
  (its image is unique: `EraseProof.TrS.det`).
- **Why it is forced:** the lemmas of `Lean4Lean.TrExprS` handle `proj` with `sorry` proofs
  (`Lean4Lean/Verify/Typing/Lemmas.lean:642,723,727,893,938,1240,1509`); reusing them puts
  projection sorries into a fragment without projections. The `lit` rule translates a literal
  through constructors of `Nat` and `String` (`Lean4Lean.VEnv.ContainsLits`,
  `Lean4Lean/Verify/Typing/Expr.lean:70`), which are inductive types, absent from the model (DV-6).
  Secondarily, projections are translated through `Lean4Lean.TrProj`, a `sorry` definition
  (`Lean4Lean/Verify/Typing/Expr.lean:68`), which every hypothesis stated with
  `Lean4Lean.TrExprS` would mention.
- **What was considered instead:** `Lean4Lean.TrExprS` with a side condition excluding
  projections and literals: the hypotheses would still mention `Lean4Lean.TrProj`, and its lemmas
  would reach the `sorry` proofs of the `proj` cases.

### DV-3

- **Our artifact:** `proof/EraseProof/Env.lean`, `EraseProof.ProgEnv`, with `EraseProof.TrConst`,
  `EraseProof.TrDef` and `EraseProof.findDecl`: the relation between a program's declarations and
  their model in lean4lean.
- **Reference artifact:** the well-formed global environment `wf_ext Σ`
  (`pcuic/theories/PCUICTyping.v:507`; MetaCoq paper §3.6), a hypothesis of `erases_correct`
  (`erasure/theories/ErasureCorrectness.v:51`), whose declarations are a newest-first list searched
  by `lookup_env` (`common/theories/Environment.v:483`); and lean4lean's relation between a kernel
  environment and its model, `Lean4Lean.TrEnv'` (`Lean4Lean/Verify/Environment/Basic.lean:128`),
  which `EraseProof.ProgEnv` restates.
- **What differs:** the environment is a newest-first list of Lean `ConstantInfo`s, searched like
  `lookup_env` by `EraseProof.findDecl`, instead of a Lean `Environment` or the constant map of
  `Lean4Lean.TrEnv'`. `EraseProof.ProgEnv` has the rules `axiom`, `defn`, `thm`, `opaque` and
  `mutualDef` (named `block`) of `Lean4Lean.TrEnv'` at safety `.unsafe`, with `EraseProof.TrS` in
  place of `Lean4Lean.TrExprS`; `EraseProof.TrConst` and `EraseProof.TrDef` restate
  `Lean4Lean.TrConstant` and `Lean4Lean.TrDefVal` without their safety conjunct, which holds for
  every declaration at `.unsafe`. It has no `ignore` rule (at `.unsafe` no declaration is
  ignored), no `quot` rule, no `induct` rule, and no freshness premise on a constant map (a name is
  fresh in the model because `Lean4Lean.VEnv.addConst` succeeds). It has one premise that
  `Lean4Lean.TrEnv'` lacks: the field `all` is what Lean's elaborator sets, the declaration's own
  name for a single definition, theorem or opaque constant, and the block's names in order for
  each member of a block. Compared with `wf_ext Σ`, the environment has no inductive declarations,
  and its typing is lean4lean's (DV-5).
- **Why it is forced:** a Lean `Environment` always contains the inductive types of `Init`, and
  `Lean4Lean.TrEnv'` at `.unsafe` relates no constant map that contains an inductive type
  (lean4lean's `TrEnv'.no_inductInfo`, `Lean4Lean/Verify/Environment/Extension.lean:18`), because
  lean4lean `master` has no inductive types (DV-6); so a program is stated as an inductive-free
  list of declarations. The rule `quot` needs a constant named `Eq`
  (`Lean4Lean.VEnv.QuotReady`, `Lean4Lean/Theory/Quot.lean:13`), which is an inductive type in
  every Lean environment. `Lean4Lean.TrEnv'` is stated with `Lean4Lean.TrExprS`, whose projection
  rule and lemmas carry `sorry` (DV-2). The eraser reads `all` to lay out a block of mutual
  definitions (`visitMutual`, `LeanToLambdaBox/Erasure.lean`), and lean4lean's kernel does not
  check it (`addDefinition` to `addMutual`, `Lean4Lean/Environment.lean:36-118`), so the premise
  states what the elaborator guarantees.
- **What was considered instead:** `Lean4Lean.TrEnv'` of a real Lean environment, which does not
  hold for any (`TrEnv'.no_inductInfo`); `Lean4Lean.TrEnv'` of a kernel environment
  built from the program's declarations, whose hypotheses would mention `Lean4Lean.TrProj`
  through `Lean4Lean.TrExprS` (DV-2); no `all` premise, under which the eraser's reading of `all`
  is unconstrained.

### DV-5

- **Our artifact:** `proof/EraseProof/Typing/Basic.lean`: all typing in `EraseProof` is
  lean4lean's typing judgment `Lean4Lean.VEnv.IsDefEq` (through `Lean4Lean.VEnv.HasType`,
  `Lean4Lean.VEnv.IsType`, `Lean4Lean.VExpr.WF`), as in the premises of `EraseProof.TrS` and the
  conclusion of `EraseProof.TrS.wf`.
- **Reference artifact:** PCUIC typing, MetaCoq paper §3.3 (cumulativity) and §3.5 (typing,
  Fig. 21), MetaRocq `pcuic/theories/PCUICTyping.v:198` `typing` with `type_Cumul` (`:294`), on
  which erasure (§7) is stated; Letouzey §3.1 (CIC).
- **What differs:** the judgment has definitional proof irrelevance (`proofIrrel`,
  `Lean4Lean/Theory/Typing/Basic.lean:51`) and η for functions (`eta`, `:48`; PCUIC has no η,
  MetaCoq paper §2.4); it has no cumulativity (conversion only, `defeqDF`, `:44`); levels have
  the operator `imax` (`Lean4Lean/Theory/VLevel.lean:12`), in which the sort of a Π-type is
  stated (`forallEDF`, `Lean4Lean/Theory/Typing/Basic.lean:40`), and are compared up to evaluation
  (`Lean4Lean.VLevel.Equiv`, `Lean4Lean/Theory/VLevel.lean:58`, in `sortDF`,
  `Lean4Lean/Theory/Typing/Basic.lean:22`).
- **Why it is forced:** the eraser's inputs are Lean terms, typed by Lean's kernel; the spec (§2)
  requires lean4lean `master` as the model of that kernel, and it models Lean's theory, not PCUIC.
- **What was considered instead:** none: PCUIC typing does not type Lean terms (it has
  cumulativity, and neither definitional proof irrelevance nor `imax`), so no judgment closer to
  the reference types the eraser's inputs.

### DV-6

- **Our artifact:** the fragment: the source terms `EraseProof.TrS` translates
  (`proof/EraseProof/Typing/Basic.lean`).
- **Reference artifact:** MetaRocq's erasure relation `erases` in full
  (`erasure/theories/Extract.v:88`; MetaCoq paper §7.3, Fig. 18), with its rules
  `erases_tConstruct` (`:106`), `erases_tCase` (`:109`), `erases_tProj` (`:118`), `erases_tFix`
  (`:122`), `erases_tCoFix` (`:129`), `erases_tPrim` (`:137`), and PCUIC's weak call-by-value
  evaluation `eval` (`pcuic/theories/PCUICWcbvEval.v:231`) with its ι-rules; Letouzey Def. 3 (all
  cases of 𝓔, fixpoints) and Def. 8 (ι).
- **What differs:** no constructors, case analysis, projections, source fixpoints, cofixpoints,
  primitive values or evars, and no ι-reduction: `EraseProof.TrS` has no rule for `Expr.proj`,
  `Expr.lit` or `Expr.mvar`, and Lean's `Expr` has no node for constructors, case analysis,
  fixpoints or cofixpoints (in Lean these are constants of inductive declarations, which
  `EraseProof.TrS` translates only as constants of the model's environment).
- **Why it is forced:** lean4lean `master` has no inductive types: `Lean4Lean.VInductDecl.WF` and
  `Lean4Lean.VEnv.addInduct` are `sorry` definitions (`Lean4Lean/Theory/Inductive.lean:5,7`), so
  the model has no constructors, recursors or ι-reduction; projections are translated through the
  `sorry` definition `Lean4Lean.TrProj` (`Lean4Lean/Verify/Typing/Expr.lean:68`); literals are
  values of the inductive types `Nat` and `String` (DV-2); the kernel's terms have no
  metavariables.
- **What was considered instead:** axiomatized inductive types (types, constructors and recursors
  as constants, ι as definitional equalities) in an ordered environment: the rule
  `Lean4Lean.VEnv.Ordered.defeq` (`Lean4Lean/Theory/Typing/Lemmas.lean:258`) admits any
  well-typed definitional equality, such as `Sort 0 ≡ (Sort 0 → Sort 0)`, so the injectivity of
  Π-types that the simulation proof needs fails there; master proves that injectivity
  (`Lean4Lean.VEnv.IsDefEqU.forallE_inv`, `Lean4Lean/Theory/Typing/Injectivity.lean:23`) only
  under `Lean4Lean.VEnv.WF`, whose inductive part is the `sorry` definition above.

### DV-10

- **Our artifact:** `proof/EraseProof/Source/EvalEnv.lean`, `EraseProof.EvalEnv.unfold?`, the
  constants the source semantics unfolds: it returns the value of a definition or theorem and
  nothing for an opaque constant.
- **Reference artifact:** the δ rule of PCUIC's weak call-by-value evaluation, `eval_delta`
  (`pcuic/theories/PCUICWcbvEval.v:247`; MetaCoq paper §5.6), which unfolds every constant whose
  declaration has a body (`cst_body decl = Some body`).
- **What differs:** a Lean `opaque` declaration (`ConstantInfo.opaqueInfo`) has a value, but
  `EraseProof.EvalEnv.unfold?` does not return it, so evaluation does not unfold the constant.
  The shipping eraser emits the opaque's value as the body of its λ□ constant
  (`ci.value? (allowOpaque := true)` in `LeanToLambdaBox/Erasure.lean`), so λ□ evaluation unfolds
  what the source semantics leaves stuck.
- **Why it is forced:** lean4lean's model gives an opaque constant no defining equation (rule
  `opaque` of `Lean4Lean.TrEnv'`, `Lean4Lean/Verify/Environment/Basic.lean:164-169`, adds the
  constant only), and `EraseProof.ProgEnv` follows it; so unfolding an opaque is not a
  definitional equality of the model. The proof relates each evaluation step of the source to a
  typed definitional equality of the model; for a δ step, `EraseProof.ProgEnv.unfold` gives it
  for definitions (their defining equation) and theorems (their type is a proposition, so proof
  irrelevance equates them with their value), and nothing gives it for opaques, whose type need
  not be a proposition.
- **What was considered instead:** unfolding opaques as `eval_delta` does: evaluation steps would
  no longer be definitional equalities of the model, and type preservation fails for terms whose
  type depends on an opaque's value (with `opaque c : T := t` and an axiom `f : (x : T) → F x`,
  `f c : F c` evaluates to `f t : F t`, and the model does not equate `F c` with `F t`).

### DV-12

- **Our artifact:** `proof/EraseProof/Source/EvalEnv.lean`, `EraseProof.EvalEnv` with its field
  `axiomatized`, and `EraseProof.EvalEnv.unfold?`: the evaluation environment carries the
  constants the configuration remaps to foreign code, and evaluation does not unfold them.
- **Reference artifact:** the environment of PCUIC's weak call-by-value evaluation `eval`
  (`pcuic/theories/PCUICWcbvEval.v:231`), whose rule `eval_delta` (`:247`) unfolds a constant
  exactly when its declaration has a body; and `erases_constant_body`
  (`erasure/theories/Extract.v:264`), which erases a constant with a body to one with a body and
  a constant without a body to one without.
- **What differs:** a definition or theorem for which `axiomatized` holds has a Lean value but no
  δ rule in the source semantics: it is stuck, like the λ□ axiom the eraser emits for it. Which
  constants are remapped is an input of the source semantics, besides the declarations.
- **Why it is forced:** under the configuration `extern := .preferAxiom` (the default of
  `ErasureConfig`, `LeanToLambdaBox/Erasure.lean`), the shipping eraser emits a declaration tagged
  `@[extern]` as a λ□ axiom, although it has a Lean value, so that it is linked with a foreign
  implementation (Dima §4.2). Neither lean4lean's model nor λ□ evaluation models that
  implementation; the source semantics can only leave the constant stuck, as λ□ evaluation leaves
  the axiom.
- **What was considered instead:** a scope condition excluding programs that mention a remapped
  constant: it also excludes programs that never evaluate the constant.

### DV-21

- **Our artifact:** `proof/EraseProof/Env.lean`, `EraseProof.ProgEnv`: its rule `axiom` admits
  axioms, declarations without a value, in the program's environment.
- **Reference artifact:** Letouzey §3.4 (p. 10), "from now to the end of this paper we will only
  consider contexts with no assumptions", the hypothesis of Theorems 12, 13 and 15. MetaRocq's
  `erases_correct` (`erasure/theories/ErasureCorrectness.v:51`) has no such hypothesis: `wf_ext Σ`
  admits constants without a body, and `axiom_free` (`erasure/theories/Extract.v:381`) is a
  hypothesis only of the first-order results, such as `erase_correct_firstorder`
  (`erasure/theories/ErasureFunctionProperties.v:2310`).
- **What differs:** programs may depend on axioms: `EraseProof.ProgEnv` relates lists containing
  Lean `axiom` declarations to models in which they are constants without a defining equation.
  This follows MetaRocq and diverges from Letouzey.
- **Why it is forced:** the spec (§2) puts in scope every input whose verification needs nothing
  beyond lean4lean `master`, and `master` models axioms (rule `axiom` of `Lean4Lean.TrEnv'`,
  `Lean4Lean/Verify/Environment/Basic.lean:134`). Letouzey needs the hypothesis for canonicity (a
  closed term of an inductive type reduces to a constructor), in the ι cases of the proof of
  Theorem 12 (Appendix A, cases 1 and 2) and in Theorem 15; the fragment has no inductive types
  and no ι-reduction (DV-6).
- **What was considered instead:** excluding axioms from `EraseProof.ProgEnv`, as Letouzey does:
  it narrows the scope the spec fixes without a gap in `master` that forces it.
