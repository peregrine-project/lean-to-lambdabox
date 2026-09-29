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

### DV-1

- **Our artifact:** `proof/EraseProof/Source/Eval.lean`, `EraseProof.SrcEval`: the source
  semantics evaluates Lean terms (`Expr`), the eraser's input, whose types are those of their
  images under `EraseProof.TrS` in lean4lean's syntax `VExpr`; and
  `proof/EraseProof/Relation/Basic.lean`, `EraseProof.Erases`: the erasure relation relates these
  Lean terms, under a lean4lean context `Lean4Lean.VLCtx` of their images, to λ□ terms.
- **Reference artifact:** PCUIC's weak call-by-value evaluation `eval`
  (`pcuic/theories/PCUICWcbvEval.v:231`; MetaCoq paper §5.6) and the erasure relation `erases`
  (`erasure/theories/Extract.v:88`; §7.3, Fig. 18), both on PCUIC terms, the syntax that PCUIC's
  typing judges; Letouzey §3.1 (CIC terms).
- **What differs:** the syntax that evaluates and the syntax that is typed are different: `Expr`,
  with `let` (`Expr.letE`) and metadata (`Expr.mdata`), for evaluation, and lean4lean's `VExpr`
  (`Lean4Lean/Theory/VExpr.lean:7-13`), which has neither, for typing; `EraseProof.TrS` relates
  them. In PCUIC both are the same terms. `EraseProof.SrcEval` evaluates a `let` as `eval_zeta`
  does (`pcuic/theories/PCUICWcbvEval.v:241`): the value first, then the body with the value
  substituted; metadata is transparent (rule `EraseProof.SrcEval.mdata`). `EraseProof.Erases`
  relates `Expr` to λ□ as `erases` relates PCUIC terms, under a context of `VExpr` images: its
  binder rules `EraseProof.Erases.lam` and `EraseProof.Erases.letE` take the translation of the
  binder's type (and of a `let` value) as a premise, and extend the context with it, where
  `erases_tLambda` and `erases_tLetIn` (`erasure/theories/Extract.v:93`, `:96`) extend `Γ` with the
  PCUIC binder itself; a `let` erases to a `tLetIn` of the erased value, as in `erases_tLetIn`, and
  metadata is transparent (rule `EraseProof.Erases.mdata`).
- **Why it is forced:** the eraser consumes `Expr`, and the λ□ image of a `let` evaluates its
  value first (`eval_zeta`, `erasure/theories/EWcbvEval.v:134`; rule `EraseProof.LBEval.zeta`).
  `VExpr` has no `let`: `EraseProof.TrS` translates `let x := v; b` to the translation of `b` in a
  context whose entry for `x` is the translation of `v` (rule `EraseProof.TrS.letE`, as rule `letE`
  of `Lean4Lean.TrExprS`, `Lean4Lean/Verify/Typing/Expr.lean:97-101`), that is, with the value
  substituted. A semantics on `VExpr` therefore never evaluates a `let` value, and relating it to
  λ□ evaluation, which does, when the value diverges would need a normalization theorem, which
  lean4lean `master` does not have. The erasure relation that the simulation carries along
  `EraseProof.SrcEval` is on the same syntax, and its context, in which erasability
  (`EraseProof.ErasableS`) is judged, is a lean4lean typing context, whose entries are `VExpr`.
- **What was considered instead:** a semantics on `VExpr`: with the recursive
  `unsafe def loop : A → A := fun x => loop x` and `a : A`, the term `let x := loop a; a` has the
  image `a`, a value, while its λ□ image evaluates `loop a` first and diverges.

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
  (its image is unique: `EraseProof.TrS.det`). Every derivation of `EraseProof.TrS` is one of
  `Lean4Lean.TrExprS` (test `EraseProof.Test.TrS.toTrExprS`, whose statement reaches the `sorry` of
  `Lean4Lean.TrProj`).
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
  each member of a block. Every `EraseProof.ProgEnv` gives a `Lean4Lean.TrEnv'` at `.unsafe` of
  the same model, with a constant map that holds each of the program's declarations under its name
  (test `EraseProof.Test.ProgEnv.toTrEnv'`, whose statement reaches the `sorry` definitions
  `Lean4Lean.TrProj` and `Lean4Lean.VInductDecl.WF`). Compared with `wf_ext Σ`, the environment has no inductive declarations,
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

### DV-4

- **Our artifact:** `proof/EraseProof/Erasability.lean`, `EraseProof.IsErasable`, with
  `EraseProof.IsArity`: a term of the model is erasable when some type of it is an arity, or has a
  sort whose level is equivalent to zero.
- **Reference artifact:** `isErasable` (`erasure/theories/Extract.v:18`; MetaCoq paper §7.3,
  Fig. 18), which asks for a type `T` of the term that is an arity (`isArity`,
  `pcuic/theories/PCUICTyping.v:29`) or whose sort `u` satisfies `Sort.is_propositional u`
  (`common/theories/Universes.v:1528`: `u` is `Prop` or `SProp`); Letouzey Def. 1 (type schemes)
  and the □ clause of Def. 3.
- **What differs:** the propositional case asks for `u ≈ .zero`, that is, the level `u`
  evaluates to zero under every assignment of the level parameters (`Lean4Lean.VLevel.Equiv`,
  `Lean4Lean/Theory/VLevel.lean:58`, over `Lean4Lean.VLevel.eval`, `:34-39`), in place of
  `Sort.is_propositional u`, and has no `SProp` case. `EraseProof.IsArity` is `isArity` on
  `Lean4Lean.VExpr`: sorts and Π-types ending in a sort, without the `tLetIn` clause of `isArity`.
- **Why it is forced:** Lean has no `SProp`, and its `Prop` is `Sort 0`, where a level is an
  expression over level parameters with `succ`, `max` and `imax` (`Lean4Lean.VLevel`,
  `Lean4Lean/Theory/VLevel.lean:8-13`). A sort is therefore a proposition under every
  instantiation of the level parameters exactly when its level evaluates to zero under every
  assignment: `Sort (imax u 0)` is `Prop` for every `u`, while `Sort u` is `Prop` for some
  instantiations only. lean4lean's typing identifies sorts whose levels are equivalent in this sense
  (`sortDF`, `Lean4Lean/Theory/Typing/Basic.lean:22`), so only a test up to this equivalence is
  invariant under definitional equality. `Lean4Lean.VExpr` has no `let`
  (`Lean4Lean/Theory/VExpr.lean:7-13`): `EraseProof.TrS` translates a `let` to its body with the
  value substituted, so no model type has a `tLetIn` clause to follow.
- **What was considered instead:** the syntactic test `u = .zero` (a type whose sort is written
  `Sort 0`): it misses propositions whose sort is written `imax u 0` or `max 0 0`, which the model
  equates with `Sort 0`, so erasability would depend on how a sort is written rather than on its
  level.

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

### DV-7

- **Our artifact:** `proof/EraseProof/Source/Eval.lean`: `EraseProof.RecursiveDecl` (with
  `EraseProof.OccursV`), the rules `EraseProof.SrcEval.fixAtom` and `EraseProof.SrcEval.fixApp` of
  `EraseProof.SrcEval`, the value shape `EraseProof.SrcValue.fixConst` and the head condition
  `EraseProof.BlocksCong`: recursion in the source semantics; and
  `proof/EraseProof/Relation/Basic.lean`: the rule `EraseProof.Erases.constRec` of
  `EraseProof.Erases` and the admissible targets `EraseProof.RecIn`: recursion in the erasure
  relation.
- **Reference artifact:** PCUIC's fixpoints: the term `tFix`, a value (`atom`,
  `pcuic/theories/PCUICWcbvEval.v:51`), unfolded when applied by `eval_fix` (`:273`) and excluded
  as a head of `eval_app_cong` (`:311`, `isFixApp`); their erasure `erases_tFix`
  (`erasure/theories/Extract.v:122`); Letouzey Def. 3 (the fixpoint case of 𝓔).
- **What differs:** Lean has no fixpoint term; recursion lives in constants. A constant is
  recursive (`EraseProof.RecursiveDecl`) when its block has several members or its value mentions
  its own name in a value position (`EraseProof.OccursV`). `EraseProof.SrcEval` treats a recursive
  constant as a PCUIC `tFix` with `rarg = 0`: the constant evaluates to itself
  (`EraseProof.SrcEval.fixAtom`, `eval_delta` to a `tFix` value), and applied to an argument it
  evaluates the argument, then its value, at the occurrence's levels, applied to the argument's
  value (`EraseProof.SrcEval.fixApp`, `eval_fix` with `rarg = 0` and no earlier arguments).
  Recursive constants of every type are values, including those whose value is not a λ: with
  `unsafe def x : A → A := x`, `x` is a value of `EraseProof.SrcEval`, as its image, a `tFix`, is
  a value of λ□, while Lean's own evaluation of `x` (`lean --run`) does not terminate.
  Non-recursive constants unfold when evaluated (`EraseProof.SrcEval.delta`, `eval_delta`). Which
  constants are recursive is a syntactic property of the declaration. In the erasure relation, a
  constant that is not an atom erases to its `tConst` (`EraseProof.Erases.const`) or to any
  admissible target that the relation's parameter `rc` gives it (`EraseProof.Erases.constRec`);
  over a λ□ environment, the admissible targets of a constant are the `tFix` stored as its body
  (`EraseProof.RecIn`). They stand for the self-references of a block member's value once
  `cunfold_fix` has unfolded the member, where `erases_tFix` relates a PCUIC `tFix` to a λ□ `tFix`
  of erased bodies.
- **Why it is forced:** Lean's `Expr` has no fixpoint node: a recursive Lean definition is a
  constant whose value mentions itself, a member of a block (rule `block` of
  `EraseProof.ProgEnv`, whose values are translated in the model that contains the block). The
  eraser compiles a declaration to a member of a λ□ `tFix` exactly when it is not a single
  declaration whose value does not mention its own name (`name_occurs` in `visitMutual`,
  `LeanToLambdaBox/Erasure.lean`), and λ□ has fixpoint values only for these blocks. For the
  source semantics to be simulated, the constants it treats as fixpoints must be exactly these,
  so the split is the eraser's test, which `EraseProof.RecursiveDecl` states on the declaration.
  In a block member's value, the members are constants; in the member's λ□ body, which the
  eraser closes into a `tFix` (`mkDef`, `LeanToLambdaBox/Erasure.lean`) and `cunfold_fix` unfolds,
  they are the block's `tFix` terms. No rule of `erases` relates a constant to a `tFix`, so the
  relation needs `EraseProof.Erases.constRec`, and `EraseProof.RecIn` ties its targets to what the
  λ□ environment stores.
- **What was considered instead:** unfolding recursive constants when evaluated, as the others:
  it matches λ□'s `tFix` only when each member's value is a λ, so that one unfolding reaches a
  value; it would need a shipping change that η-expands members whose value is not a λ, which the
  theorem does not need (spec §5.1). In the relation, relating a constant only to its `tConst`, as
  `erases_tConst` does: the unfolded λ□ body of a block member, which `eval_fix` evaluates, has
  the block's `tFix` terms where the member's Lean value has constants, so no erasure would relate
  the two.

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
  definitional equality of the model. The proof relates each evaluation of the source to a typed
  definitional equality of the model (`EraseProof.SrcEval.defeq`, subject reduction); for a δ
  step, `EraseProof.ProgEnv.unfold` gives it
  for definitions (their defining equation) and theorems (their type is a proposition, so proof
  irrelevance equates them with their value), and nothing gives it for opaques, whose type need
  not be a proposition.
- **What was considered instead:** unfolding opaques as `eval_delta` does: evaluation steps would
  no longer be definitional equalities of the model, and type preservation fails for terms whose
  type depends on an opaque's value (with `opaque c : T := t` and an axiom `f : (x : T) → F x`,
  `f c : F c` evaluates to `f t : F t`, and the model does not equate `F c` with `F t`).

### DV-11

- **Our artifact:** `proof/EraseProof/Atoms.lean`, `EraseProof.EvalEnv.isAtom`, with
  `EraseProof.arityShape`, `EraseProof.EvidentZero`, `EraseProof.DeltaFree` and
  `EraseProof.EvidentProp`; `proof/EraseProof/Source/Eval.lean`, the rule
  `EraseProof.SrcEval.constAtom` and the values `EraseProof.AtomSpine` (in
  `EraseProof.SrcValue.spine`): the constants without a δ rule that are values of the source
  semantics; and `proof/EraseProof/Relation/Basic.lean`, the premise `ac c = false` of the rules
  `EraseProof.Erases.const` and `EraseProof.Erases.constRec` of `EraseProof.Erases`, whose
  parameter `ac` is the atom test: atoms erase only to `□`.
- **Reference artifact:** PCUIC's atoms `atom` (`pcuic/theories/PCUICWcbvEval.v:51`), which contain
  the inductive types `tInd` and the constructors `tConstruct`; `eval_atom` (`:331`) evaluates them
  to themselves, `eval_app_cong` (`:311`) evaluates their applications, and `value` (`:500`) lists
  the results; a constant without a body has no rule (`eval_delta`, `:247`, needs
  `cst_body decl = Some body`). On the erasure side, `erases` (`erasure/theories/Extract.v:88`)
  relates every constant to its `tConst` (`erases_tConst`, `:104`), has no rule for `tInd`, which erases only to `□` (`erases_box`, `:140`), and `erases_tConstruct`
  (`:106`) requires the inductive not to be propositional (`isPropositional`,
  `pcuic/theories/PCUICFirstorder.v:109`, which reads the inductive's declared arity
  syntactically: `isPropositionalArity`, `:103`, with `destArity`, `pcuic/theories/PCUICAst.v:486`).
- **What differs:** a constant without a δ rule in the source semantics is a value when its
  declared type is evidently an arity (`EraseProof.arityShape`: syntactically
  `Π x₁…xₙ, Sort u`) or evidently a proposition (`EraseProof.EvidentProp`): a Π-telescope over an
  application `h.{vs} a₁…aₙ` whose head `h` is an axiom or an opaque constant
  (`EraseProof.DeltaFree`) with declared type a syntactic arity `Π y₁…yₙ, Sort u` of exactly `n`
  binders, and whose sort at that occurrence, `u` with `h`'s level parameters instantiated by
  `vs` (`Erasure.Pure.instLevel`), is evidently zero (`EraseProof.EvidentZero`). Such a constant
  evaluates to itself (`EraseProof.SrcEval.constAtom`), and the applications it heads are values
  (`EraseProof.AtomSpine`). Atomhood is a property of the constant, decided on declared types, not
  on the levels of an occurrence: a proof `hq.{v} : P.{v}` (with `axiom P.{v} : Sort v`) whose
  propositionality depends on its own level parameter is not an atom, not even at `hq.{0}`. Every
  other constant without a δ rule is stuck. In the erasure relation, `erases_tConst` becomes
  `EraseProof.Erases.const` with the premise that the constant is not an atom (`ac c = false`,
  where `ac` is the atom test), and `EraseProof.Erases.constRec` has the same premise: an atom
  erases only to `□` (`EraseProof.Erases.box`), as `tInd` does.
- **Why it is forced:** the fragment has no inductive types (DV-6), so its base types and the
  canonical proofs of atomic propositions are axioms; without a rule that makes them values, no
  program that instantiates a polymorphic function at a base type or passes such a proof by value
  evaluates, and the correctness theorem says nothing about it. The class is syntactic
  ("evident") because the eraser must box each atom from the declared types alone, without a
  typing hypothesis: a semantic class (every erasable constant without a δ rule) would need the
  eraser's oracle `Erasure.Pure.isErasable` to box all of them, which needs canonicity (no neutral
  term is definitionally equal to a sort), and lean4lean `master` does not prove it. The head is
  `EraseProof.DeltaFree` because the head of a propositional constructor's type is an inductive
  type, which never δ-reduces: a proof whose proposition is headed by a definition that unfolds to
  a Π can be applied, and the oracle then answers from the arguments' types (with `axiom hq : Q`,
  `def Q : Prop := ∀ P : Prop, P → P`, `axiom A : Type` and `axiom a : A`, it keeps the ill-typed
  spine `hq A a`: `EraseProof.Test.Atoms.defHead_kept`). The head's sort is read at the
  occurrence because a Lean level can be `0`, whereas `isPropositional` reads an inductive's
  declared sort, which no Rocq universe instance turns into `Prop`. Atomhood does not depend on the
  occurrence because the eraser erases a universe-polymorphic body once, at its level parameters,
  where the oracle keeps the level-dependent proof `hq.{v}` (it boxes `hq.{0}`:
  `EraseProof.Test.Atoms.levelDependent_kept`): were `hq.{0}` a value, a body passing `hq.{v}`,
  evaluated at level `0`, would reach a value in the source while its λ□ image is stuck on the
  axiom `hq`, and erasure would not commute with level instantiation, which
  `erases_subst_instance_decl` (`erasure/theories/ErasureProperties.v:412`) states and
  `EraseProof.Erases.instLevels` proves (the relation's atom test `ac` reads a constant's name, not
  its levels). An atom is a value of the source semantics, while no rule of λ□ evaluation returns
  a `tConst`: the erasure of an atom that is the result of an evaluation must be the result of the
  λ□ evaluation, so it cannot be a `tConst`; it is `□`, which λ□ has for `tInd` too.
- **What was considered instead:** every constant without a δ rule stuck (the theorem then says
  nothing about the programs above); a semantic class (needs canonicity); heads that are
  definitions (the oracle keeps proofs with such heads, above); heads that δ-reduce to an
  `EraseProof.DeltaFree` head (further from the reference, and the eraser's boxing of the class
  would have to follow the oracle's δ steps through definitions); the head's declared sort instead
  of its sort at the occurrence (leaves proofs of `P.{0}`, with `axiom P.{v} : Sort v`, stuck with
  no forcing reason); atomhood decided at each occurrence (makes the theorem false, above); the
  head's declared type read up to the kernel's δ (the class would no longer be read syntactically,
  as `isPropositionalArity` reads the declared arity, and the eraser's boxing of the class would
  have to follow the oracle's δ steps through definitions; the oracle does box the constants this
  reading would add, such as `R` and `hR` of `EraseProof.Test.Oracle.irreducibleAlias`); in the
  relation, `erases_tConst` for atoms too (an atom that is the result of an evaluation would then
  erase to a `tConst`, which is not a result of λ□ evaluation).

### DV-12

- **Our artifact:** `proof/EraseProof/Source/EvalEnv.lean`, `EraseProof.EvalEnv` with its field
  `axiomatized`, and `EraseProof.EvalEnv.unfold?`: the evaluation environment carries the
  constants the configuration remaps to foreign code, and evaluation does not unfold them.
  `proof/EraseProof/Source/Restrict.lean`, `EraseProof.evalEnvOf`: the evaluation environment of
  a program, whose remapped constants are those of the shipping eraser's own test
  `Erasure.axiomatized` (`LeanToLambdaBox/Erasure/Pure.lean`): a single declaration that the view
  marks `@[extern]`, under the configuration `extern := .preferAxiom`.
- **Reference artifact:** the environment of PCUIC's weak call-by-value evaluation `eval`
  (`pcuic/theories/PCUICWcbvEval.v:231`), whose rule `eval_delta` (`:247`) unfolds a constant
  exactly when its declaration has a body; and `erases_constant_body`
  (`erasure/theories/Extract.v:264`), which erases a constant with a body to one with a body and
  a constant without a body to one without.
- **What differs:** a definition or theorem for which `axiomatized` holds has a Lean value but no
  δ rule in the source semantics: it is stuck, like the λ□ axiom the eraser emits for it. Which
  constants are remapped is an input of the source semantics, besides the declarations; for a
  program, `EraseProof.evalEnvOf` derives it from the configuration and the trusted view's
  `isExtern`, exactly as the eraser does.
- **Why it is forced:** under the configuration `extern := .preferAxiom` (the default of
  `ErasureConfig`, `LeanToLambdaBox/Erasure.lean`), the shipping eraser emits a declaration tagged
  `@[extern]` as a λ□ axiom, although it has a Lean value, so that it is linked with a foreign
  implementation (Dima §4.2). Neither lean4lean's model nor λ□ evaluation models that
  implementation; the source semantics can only leave the constant stuck, as λ□ evaluation leaves
  the axiom.
- **What was considered instead:** a scope condition excluding programs that mention a remapped
  constant: it also excludes programs that never evaluate the constant.

### DV-13

- **Our artifact:** `proof/EraseProof/Oracle/Whnf.lean`, `EraseProof.LocalsOK`: the eraser's
  locals, a list of free variables with their types and, for a `let`, their values, related to a
  lean4lean context `Lean4Lean.VLCtx` with free-variable entries only; and
  `proof/EraseProof/Oracle/Agree.lean`, `EraseProof.Pure.isErasable_agree`, with
  `EraseProof.ClosedDecls`, `EraseProof.LocalsSupport` and `EraseProof.LocalsAgree`: over closed
  declarations, the erasability oracle answers alike under two lists of locals that agree on the
  free variables the term reaches through the locals' types and values. With them,
  `proof/EraseProof/Target.lean`, `EraseProof.hasFVar` and `EraseProof.LenvClosed`: no body stored
  in the λ□ environment contains a free variable. And `proof/EraseProof/Relation/Basic.lean`, the
  rule `EraseProof.Erases.fvar` of `EraseProof.Erases`: the erasure relation relates the
  traversal's free variables to themselves, under a context `Lean4Lean.VLCtx` whose free-variable
  entries type them.
- **Reference artifact:** MetaRocq's erasure function `erase`
  (`erasure/theories/ErasureFunction.v:989`) and erasure relation `erases`
  (`erasure/theories/Extract.v:88`; MetaCoq paper §7.2–§7.3, Figs. 17–18), which work on de Bruijn
  indices under a context `Γ` of typed binders (rule `erases_tRel`, `:89`; named variables occur
  only in `erases_tVar`, `:90`, and typed terms contain none); and `erase_constant_body`
  (`erasure/theories/ErasureFunction.v:1309`), which erases a constant's body in the empty
  context.
- **What differs:** the erasure is locally nameless. Under a binder, the term is opened with a
  fresh free variable, recorded with its type (and, for a `let`, its value) in a list of locals,
  and the erased body is closed again by turning that variable into a bound variable. The oracle
  runs on open terms under these locals, not under a context of de Bruijn binders;
  `EraseProof.LocalsOK` gives the locals their meaning in the model. A constant's body is erased
  under the locals of the place where the traversal first meets the constant, not in the empty
  context: `EraseProof.Pure.isErasable_agree` equates the oracle's answers under the two, since a
  declaration's body is closed (`EraseProof.ClosedDecls`) and so reaches no local. The erasure
  relation is stated on these open terms: a free variable erases to itself
  (`EraseProof.Erases.fvar`, MetaRocq's `erases_tVar`, which applies to no typed term there), and
  where the relation judges erasability (`EraseProof.ErasableS`), the free-variable entries of the
  lean4lean context give these variables their types.
- **Why it is forced:** the theorem is about the shipping eraser (spec §2), whose traversal is
  written this way: `withLocalDecl` and `withLocalDef` (`LeanToLambdaBox/Erasure.lean`) open a
  binder with a fresh free variable pushed onto the locals, the oracle is called with these
  locals, `abstract` and `toBvar` (`LeanToLambdaBox/Basic.lean`) close the erased body, `mkDef`
  closes the members of a block of mutual definitions, which the traversal refers to by free
  variables, and `visitMutual` erases a constant's body without resetting the caller's locals.
- **What was considered instead:** a de Bruijn rewrite of the traversal, a large shipping change
  that no output needs (spec §5.1 allows only strictly necessary shipping changes); resetting the
  locals in `visitMutual`, a shipping change that the frame lemma
  `EraseProof.Pure.isErasable_agree` makes unnecessary.

### DV-15

- **Our artifact:** `proof/EraseProof/Relation/Basic.lean`, the rules `EraseProof.Erases.lam` and
  `EraseProof.Erases.letE` of `EraseProof.Erases`: the λ□ binder of a Lean binder with user name
  `n` is named `Erasure.binderNameOf n`, the shipping eraser's naming
  (`LeanToLambdaBox/Erasure.lean`).
- **Reference artifact:** `erases_tLambda` and `erases_tLetIn` (`erasure/theories/Extract.v:93`,
  `:96`; MetaCoq paper §7.3, Fig. 18), which give the λ□ binder the PCUIC binder's own name,
  `na.(binder_name)`.
- **What differs:** a Lean binder name is a hierarchical `Name`, a λ□ binder name is anonymous or a
  string (`BinderName`, `LeanToLambdaBox/Basic.lean`). `Erasure.binderNameOf n` is the string
  `n.toString` when each of its characters is printable ASCII (codes 33 to 126), and anonymous
  otherwise: binders named `x` and `a.b` keep their names, binders named `α₁` or `«a b»` become
  anonymous.
- **Why it is forced:** the relation describes the output of the shipping eraser (spec §2), which
  names binders by `Erasure.binderNameOf`: peregrine's `.ast` format admits non-ASCII characters
  only inside string literals, and names are bare atoms (peregrine-tool `doc/format.md`, lines 12
  and 68-69). Lean's and λ□'s names have different types, so some conversion is needed where
  MetaRocq needs none (PCUIC and λ□ share `name`).
- **What was considered instead:** λ□ binder names left unconstrained in `EraseProof.Erases.lam`
  and `EraseProof.Erases.letE`: the relation would no longer describe the names the eraser prints,
  and it would depart further from `erases_tLambda`, which fixes the name; keeping every Lean name,
  a shipping change whose output peregrine rejects.

### DV-16

- **Our artifact:** `proof/EraseProof/Target.lean`, `EraseProof.LBEval`, λ□ weak call-by-value
  evaluation, with its atoms `EraseProof.lbAtom`, stated on the shipping AST `LBTerm`
  (`LeanToLambdaBox/Basic.lean`); with it the functions `EraseProof.csubst`, `EraseProof.closedn`,
  `EraseProof.hasFVar` and the environment condition `EraseProof.LenvClosed`.
- **Reference artifact:** MetaRocq's λ□ evaluation `eval` (`erasure/theories/EWcbvEval.v:119`) on
  the λ□ terms `term` (`erasure/theories/EAst.v:29`), with `atom`
  (`erasure/theories/EWcbvEval.v:36`), `csubst` (`erasure/theories/ECSubst.v:14`), `closedn`
  (`erasure/theories/ELiftSubst.v:90`) and `closed_env` (`erasure/theories/EGlobalEnv.v:181`);
  MetaCoq paper §7.1 (Fig. 16 and the amended evaluation rules, p. 8:60).
- **What differs:** `LBTerm` has no `tVar`, `tEvar`, `tCoFix`, `tLazy` or `tForce`, and its only
  primitive values are 63-bit integers. So `EraseProof.LBEval` has no rules `eval_cofix_case`
  (`erasure/theories/EWcbvEval.v:198`), `eval_cofix_proj` (`:205`) or `eval_force` (`:279`), its
  rule `prim` (`eval_prim`, `:275`) evaluates an integer to itself, and `EraseProof.lbAtom` has no
  case for `tCoFix` or `tLazy`. `LBTerm` has a constructor that `term` lacks, `fvar`, a free
  variable named by a Lean `FVarId`: `EraseProof.LBEval` has no rule for it, `EraseProof.csubst`
  leaves it unchanged and `EraseProof.closedn` counts it as closed, as MetaRocq's `csubst` and
  `closedn` treat `tVar`; `EraseProof.hasFVar` tests whether it occurs, and has no MetaRocq
  counterpart; `EraseProof.LenvClosed` requires, besides the closedness of `closed_env`, that no
  body stored in the λ□ environment contains a free variable. The rules for constructors in block
  form, `eval_iota_block` (`:151`), `eval_proj_block` (`:228`) and `eval_construct_block`
  (`:254`), are absent; each requires the flag `with_constructor_as_block` to be true, which it is
  not in `default_wcbv_flags` (`:69`), the flags of `erases_correct`
  (`erasure/theories/ErasureCorrectness.v:51`). At flags where that flag is false,
  `EraseProof.LBEval` has exactly the rules of `eval` whose term constructors `LBTerm` has.
- **Why it is forced:** the theorem is about the shipping eraser (spec §2), whose output is an
  `LBTerm`, the λ□ that peregrine reads; evaluation is stated on that type. The terms without a
  constructor in `LBTerm` cannot occur in the eraser's output, so their rules have nothing to
  apply to. The constructor `fvar` is part of the shipping AST because the traversal is locally
  nameless (DV-13): it opens binders with free variables and closes them with `abstract` and
  `toBvar` (`LeanToLambdaBox/Basic.lean`) before a body is stored, which `EraseProof.LenvClosed`
  records. MetaRocq's erasure works on de Bruijn indices and maps `tVar` only to `tVar`
  (`erasure/theories/ErasureFunction.v:996`), which typed terms do not contain (PCUIC's typing has
  no rule for it), so `closed_env` needs no such clause. The block rules cannot fire at the flags
  of `erases_correct`, at which the simulation evaluates; results stated for every flag, such as
  `EraseProof.LBEval.closed`, are about the relation without them.
- **What was considered instead:** extending `LBTerm` with the missing constructors, a shipping
  change that no output of the eraser needs (spec §5.1 allows only strictly necessary shipping
  changes); stating evaluation on a separate transcription of `term` reached through a translation
  from `LBTerm`, which every statement would pass through and which would still need an image for
  `fvar`; including the block rules, which the statements never use at their flags.

### DV-18

- **Our artifact:** `proof/EraseProof/Oracle.lean`, `EraseProof.Pure.isErasable_sound`, with
  `EraseProof.Pure.isArity_sound` and `EraseProof.Pure.alwaysZero_sound`, and the soundness of the
  steps they rest on, `EraseProof.Pure.inferType_sound` (`proof/EraseProof/Oracle/Infer.lean`) and
  `EraseProof.Pure.whnf_sound` (`proof/EraseProof/Oracle/Whnf.lean`): the eraser decides
  erasability with its own oracle, the shipping `Erasure.Pure.isErasable`
  (`LeanToLambdaBox/Erasure/Pure.lean`), with its type inference `Erasure.Pure.inferType`, its
  weak-head reduction `Erasure.Pure.whnf`, its arity test `Erasure.Pure.isArity` and its level
  test `Erasure.Pure.alwaysZero`.
- **Reference artifact:** `is_erasableb` (`erasure/theories/ErasureFunction.v:894`; MetaCoq paper
  §7.2, Fig. 17), which decides erasability with MetaRocq's verified type checker: it infers a type
  with `type_of_typing` (`safechecker/theories/PCUICSafeRetyping.v:806`), tests it with `is_arity`
  (`erasure/theories/ErasureFunction.v:784`), and otherwise reduces the type's type to a sort and
  tests it with `Sort.is_propositional` (`common/theories/Universes.v:1528`); `is_erasableP`
  (`erasure/theories/ErasureFunction.v:915`) proves that it reflects `isErasable`
  (`erasure/theories/Extract.v:18`) in both directions. Its reductions unfold every constant with
  a body (`hnf`, `safechecker/theories/PCUICSafeReduce.v:1839`, at `RedFlags.default`,
  `pcuic/theories/PCUICNormal.v:26`).
- **What differs:** the oracle is an infer-only retyping procedure of the eraser itself, with fuel,
  over the program's declarations and the eraser's locals: it infers a type of the term, answers
  "erasable" if that type reduces to an arity, and otherwise reduces the type's type to a sort and
  answers "erasable" exactly when the sort is structurally `≈ 0`. Only the `true` direction of
  `is_erasableP` is proved: an "erasable" answer gives `EraseProof.ErasableS`
  (`EraseProof.Pure.isErasable_sound`). There is no completeness: the oracle may answer "keep" on
  an erasable term, and it fails, with an error and no answer, when its fuel runs out or a type
  does not reduce to a Π or a sort. Its reductions unfold every definition, as those of
  `is_erasableb` do, whatever the elaborator attribute `@[irreducible]` says: on an environment
  whose aliases `IProp : Type := Prop` and `Endo : Type := A → A` are `@[irreducible]` in Lean, it
  types `fun (_ : R) (x : A) => x` and `fI a` and keeps them, and it boxes `R : IProp` and the
  proof `hR : R` (`EraseProof.Test.Oracle.irreducibleAlias`).
- **Why it is forced:** the verified checker available for Lean is lean4lean's, and its soundness
  carries debts that the fragment does not need. Every soundness theorem of lean4lean's type
  checker goes through `Methods.withFuel.WF` (`Lean4Lean/Verify/TypeChecker.lean:48`), which
  reaches the `sorry` lemmas of `Lean4Lean.TrProj` (`Lean4Lean/Verify/Typing/Expr.lean:68`), the
  projection, recursor and η-structure sorries `reduceProjCore.WF`
  (`Lean4Lean/Verify/TypeChecker/Reduce.lean:143`), `reduceRecursor.WF`
  (`Lean4Lean/Verify/TypeChecker/WHNF.lean:6`), `inferProj.WF`
  (`Lean4Lean/Verify/TypeChecker/InferType.lean:388`), `tryEtaStructCore.WF` and
  `isDefEqUnitLike.WF` (`Lean4Lean/Verify/TypeChecker/IsDefEq.lean:225,486`), the strengthening
  sorry `Lean4Lean.VEnv.IsDefEqU.weakN_iff` (`Lean4Lean/Theory/Typing/UniqueTyping.lean:172`),
  and the axioms of `Lean4Lean/Verify/Axioms.lean` (the pure meaning of `Expr.instantiate1`,
  `Expr.abstract`, `Level.normalize` and others) together with `bv_decide` axioms. MetaRocq's
  `is_erasableb` rests on a checker without such debts. The soundness of the eraser's own oracle
  reaches only lean4lean's sorries L1–L5, which the simulation needs anyway. General completeness
  would need canonicity (no neutral term is convertible to a sort or a Π), which lean4lean
  `master` does not prove, and the correctness theorem needs only soundness.
- **What was considered instead:** lean4lean's checker on the eraser's path (the debts above);
  reductions that skip `@[irreducible]` in the arity and sort tests, as Lean's `Meta` does at
  default transparency: the oracle would keep the proof `hR : R` of `R : IProp`, as the `Meta`
  path does (`doc/SHIPPING-CHANGES.md`, R-14), a further divergence from `is_erasableb` with no
  forcing reason; skipping `@[irreducible]` in type inference too: the oracle then fails on
  `fun (_ : R) (x : A) => x`, whose domain has a sort only through `IProp`.

### DV-21

- **Our artifact:** `proof/EraseProof/Env.lean`, `EraseProof.ProgEnv`: its rule `axiom` admits
  axioms, declarations without a value, in the program's environment; and
  `proof/EraseProof/Source/Eval.lean`, `EraseProof.SrcEval`, which evaluates programs that use
  them.
- **Reference artifact:** Letouzey §3.4 (p. 10), "from now to the end of this paper we will only
  consider contexts with no assumptions", the hypothesis of Theorems 12, 13 and 15. MetaRocq's
  `erases_correct` (`erasure/theories/ErasureCorrectness.v:51`) has no such hypothesis: `wf_ext Σ`
  admits constants without a body, and `axiom_free` (`erasure/theories/Extract.v:381`) is a
  hypothesis only of the first-order results, such as `erase_correct_firstorder`
  (`erasure/theories/ErasureFunctionProperties.v:2310`).
- **What differs:** programs may depend on axioms: `EraseProof.ProgEnv` relates lists containing
  Lean `axiom` declarations to models in which they are constants without a defining equation. In
  evaluation an axiom has no δ rule: an axiom whose declared type is evidently an arity or a
  proposition (`EraseProof.EvalEnv.isAtom`, DV-11) is a value (`EraseProof.SrcEval.constAtom`),
  and any other axiom is stuck (no rule of `EraseProof.SrcEval` evaluates it), as a constant
  without a body is in PCUIC's `eval` (`pcuic/theories/PCUICWcbvEval.v:231`). This follows
  MetaRocq and diverges from Letouzey.
- **Why it is forced:** the spec (§2) puts in scope every input whose verification needs nothing
  beyond lean4lean `master`, and `master` models axioms (rule `axiom` of `Lean4Lean.TrEnv'`,
  `Lean4Lean/Verify/Environment/Basic.lean:134`). Letouzey needs the hypothesis for canonicity (a
  closed term of an inductive type reduces to a constructor), in the ι cases of the proof of
  Theorem 12 (Appendix A, cases 1 and 2) and in Theorem 15; the fragment has no inductive types
  and no ι-reduction (DV-6).
- **What was considered instead:** excluding axioms from `EraseProof.ProgEnv`, as Letouzey does:
  it narrows the scope the spec fixes without a gap in `master` that forces it.

### DV-22

- **Our artifact:** `proof/EraseProof/Source/Eval.lean`, `EraseProof.SrcEval`: the source
  semantics is big-step, call-by-value evaluation.
- **Reference artifact:** Letouzey §3.4, Definition 9 (weak reductions: the β, ι, δ, ζ and □
  steps, closed under application, on either side, and under case analysis, but not under λ, so
  in any order), for which Theorem 13 (backward simulation) is stated step by step. MetaRocq's
  `erases_correct` (`erasure/theories/ErasureCorrectness.v:51`) is stated for PCUIC's big-step
  weak call-by-value evaluation `eval` (`pcuic/theories/PCUICWcbvEval.v:231`; MetaCoq paper §5.6),
  which `EraseProof.SrcEval` follows.
- **What differs:** `EraseProof.SrcEval` fixes one order, call-by-value: an application evaluates
  its function and its argument before the β-step (`EraseProof.SrcEval.beta`), and a `let` its
  value before its body (`EraseProof.SrcEval.zeta`). Reductions in any other order, which
  Definition 9 admits, are not steps of the source semantics, which is big-step: it relates a term
  to its value, not to its one-step reducts.
- **Why it is forced:** the target is λ□'s call-by-value evaluation (`EraseProof.LBEval`,
  MetaRocq's `eval`, `erasure/theories/EWcbvEval.v:119`, which peregrine implements), and a value
  reached in another order need not be reached by it: with the recursive
  `unsafe def loop : A → A := fun x => loop x` and `a : A`, `(fun _ => a) (loop a)` reduces to `a`
  by one β-step, while λ□ evaluation of its image evaluates `loop a` first and diverges. So the
  theorem, which is about the λ□ evaluator, needs a source semantics that evaluates in the
  evaluator's order; MetaRocq's `erases_correct` is stated in the same way.
- **What was considered instead:** weak reduction in any order, as Definition 9, with a
  step-by-step simulation, as Theorem 13: it relates single steps and says nothing about the value
  the call-by-value evaluator reaches, and a value reached in another order need not be reached by
  it (above).
