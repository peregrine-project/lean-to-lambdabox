# Track K (kernel): three-way divergences, MetaRocq vs. Carneiro's thesis vs. lean4lean

## 1. Scope and method

This compares three things notion by notion: (1R) MetaRocq's kernel theory and verified checker
for Rocq -- [JACM] Sec 3-6 canonical, [HAB] Ch. 2-5 for current naming, [CCC] Sec 2-3 for the
original framing, and the MetaRocq 1.5.1 PCUIC and safechecker sources; (1L) Carneiro's thesis
[CT], the pen-and-paper theory lean4lean names as its target; and (code) the lean4lean fork in
`lean4lean-blueprint/Lean4Lean/`, read through its blueprint chapters, which carry a `\thesisref`
per node. Citations are `file:line` plus the reference of record. Rocq paths are relative to the
MetaRocq 1.5.1 opam sources (`pcuic/theories/`, `safechecker/theories/`, `common/theories/`);
Lean paths are relative to the `lean4lean-blueprint` root. Every divergence is read off a source
file or off the project's own status documents (`blueprint/src/chapters/status.tex`,
`divergences.md`); none is inferred from a paper alone. Notation is ASCII: `|-` for a judgment,
`==` for definitional equality, `>>` for parallel reduction, `|>` for inference, `~>` for
reduction. The kind FORCED-ERASER does not occur here: nothing in the kernel layer is forced by
the shipping eraser, which sits downstream of everything below.

## 2. Summary table

| id | area | reference element | our element | kind | reason |
|---|---|---|---|---|---|
| K-A1 | universes | PCUIC `sort` = `sProp \| sSProp \| sType univ` over constraint sets, `common/theories/Universes.v:1459` | `VLevel` = `zero\|succ\|max\|imax\|param`, one `Sort u`, `Theory/VLevel.lean:8` | FORCED-LEAN | Lean has one sort family with `Prop = Sort 0` and `imax`, no constraint store |
| K-A2 | level order | [CT] `axioms.tex`: `l <= l'+n` by nine syntactic rules | `VLevel.LE`/`Equiv` over all valuations, `Theory/VLevel.lean:41,58` | DESIGN | a semantic order needs no rule-completeness proof |
| K-A3 | cumulativity | `cumulSpec0` with `cumul_Sort`/`cumul_Ind`/`cumul_Construct`, `PCUICCumulativitySpec.v:63` | no subtyping; `IsDefEq.defeqDF` is symmetric conversion, `Theory/Typing/Basic.lean:44` | FORCED-LEAN | Lean has no universe cumulativity and no cumulative inductives |
| K-A4 | proof irrelevance | `cumulSpec0` has no irrelevance rule, `PCUICCumulativitySpec.v:63-203` | `IsDefEq.proofIrrel`, `Theory/Typing/Basic.lean:52` | FORCED-LEAN | Lean identifies any two proofs of a `Sort 0` type |
| K-A5 | eta, functions | no eta rule in `cumulSpec0`; [JACM] p.8:3 lists eta as out of scope | `IsDefEq.eta`, `Theory/Typing/Basic.lean:49` | FORCED-LEAN | Lean's kernel has definitional eta for functions |
| K-A6 | eta, structures | neither PCUIC nor its checker has structure eta | kernel has `tryEtaStruct`/`isDefEqUnitLike`, model has no rule, both `sorry`, `Verify/TypeChecker/IsDefEq.lean:227,488` | GAP | the checker accepts equalities the model cannot derive |
| K-A7 | let / zeta | `tLetIn` a term former with `cumul_zeta`, `cumul_rel`, `PCUICAst.v:201`, `PCUICCumulativitySpec.v:163,167` | no `let` in `VExpr`; `TrExprS.letE` substitutes it away, `Verify/Typing/Expr.lean:164` | DESIGN | six-constructor model; zeta becomes a translation-time operation |
| K-A8 | projections | `tProj` with `type_Proj`, `cumul_proj`, `PCUICAst.v:208`, `PCUICTyping.v:263`, `PCUICCumulativitySpec.v:196` | no projection node; `TrProj` expands into the structure's recursor, `Verify/Typing/Expr.lean:171` | DESIGN | reuses the iota registry instead of a node with its own iota and eta |
| K-A9 | projections, coverage | `type_Proj` covers every declared projection | `TrProj` covers only `TrProjCtor` shapes; `inferProj.WF` not provable as stated, `Verify/TypeChecker/InferType.lean:410` | GAP | reflexive, indexed, nested structures have no derivation |
| K-A10 | iota and K-like reduction | PCUIC has no K; [CT] `axioms.tex` `sec:iota` has it for subsingleton eliminators | `pats` registry plus one generic rule; `addRecRule` registers the constructor rule only, `Theory/Inductive.lean:257` | GAP | the model under-approximates the kernel's recursor reduction |
| K-A11 | quotients | PCUIC has none | four constants plus `quotDefEq` as a `VDefEq`, not a `pats` entry, `Theory/Quot.lean:11,16` | DESIGN | a delta axiom needs no pattern machinery; cost is `Params`'s one instance |
| K-A12 | inductive blocks | `on_global_env`/`on_inductive` with positivity, established by `check_wf_env` | `VInductDecl.WF`, 20 syntactic fields, nothing derives it from the kernel's checker | GAP | block well-formedness is asserted; `RuleShape` under-constrains the reduct |
| K-A13 | primitives | `tPrim` with `primitive_invariants`, `PCUICTyping.v:290` | no literal node; `TrExprS.lit` unfolds to constructors; GMP ops verified as `Reflects` | DESIGN | keeps the model at six constructors |
| K-A14 | native reduction | PCUIC models none | `reduceNative` refuses `reduceBool`; `reduceNative.WF` vacuous | OPEN | `divergences.md:5` states it needs verified compilation |
| K-B1 | judgment shape | two relations joined by `type_Cumul`, `PCUICTyping.v:198,296` | one relation `IsDefEq Gamma e1 e2 A`, typing its diagonal, `Theory/Typing/Basic.lean:18,69` | DESIGN | one induction instead of two mutually dependent ones |
| K-B2 | typed conversion | `cumulSpec0` is untyped, `PCUICCumulativitySpec.v:63` | `IsDefEq` carries the type; `IsDefEqU` forgets it, agreeing only via unique typing, `Theory/Typing/UniqueTyping.lean:113` | FORCED-LEAN | `proofIrrel` and `eta` read the type of both sides |
| K-B3 | binder names | `term` carries `aname`; `eq_binder_annot` in every congruence, `PCUICAst.v:195` | `VExpr` has no names, `Theory/VExpr.lean:7` | DESIGN | names carry no logical content |
| K-B4 | algorithmic equality | MetaRocq formalises an algorithmic spec, proved equivalent ([JACM] Sec 4) | `<=>` of [CT] is not formalised; its stand-in is the `Verify/TypeChecker` chain | GAP | no relation sits between the kernel's algorithm and `IsDefEq` |
| K-B5 | bidirectional layer | `Bidirectional/`, `t \|> A`, consumed by `infer`, `safechecker/theories/PCUICTypeChecker.v:1502` | `VEnv.InferType` exists, `Theory/Typing/HeadReduction.lean:508`, but no executable function is proved against it | GAP | the completeness route is present but unwired |
| K-B6 | reduction relation | `red1` first class; reductions are rules of `cumulSpec0` | `WHRed`/`ParRed`/`StRed` only under `[Params]`, `Theory/Typing/ChurchRosser.lean:12` | DESIGN | reduction is a proof device over an abstract rule family |
| K-B7 | environments | one `wf Sigma` = `on_global_env` | two notions, `VEnv.WF'` and `Ordered`, plus `OrderedStrong`, `Theory/Typing/Env.lean:48`, `Lemmas.lean:257`, `Strong.lean:679` | DESIGN | `Ordered` is the weaker invariant the structural lemmas need |
| K-C1 | confluence | `PCUICConfluence.v`, unconditional for `wf Sigma` ([CCC] Thm 2.2, p.8:13) | `ParRedS.church_rosser` under `Params`, with two `sorry`s, `Theory/Typing/ChurchRosser.lean:1302,1193,1212` | GAP | holds for no environment carrying a `def` or the quotient rule |
| K-C2 | subject reduction | `subject_reduction`, proved, `PCUICSR.v:3129` | built into `IsDefEq.pat`; the honest form is `VEnv.WF.patsStrong = sorry`, `Theory/Typing/EnvLemmas.lean:334` | GAP | the widest-reaching gap: 343 declarations |
| K-C3 | principality | `principal_type`, proved without normalization, `PCUICPrincipality.v:74` | `IsDefEq.uniq` via `HasTypeStratified`, `Theory/Typing/UniqueTyping.lean:13`, tainted twice | GAP | unique typing available only modulo two open obligations |
| K-C4 | type-former injectivity | derived from confluence, `PCUICConvCumInversion.v` | all three principles `sorry`, `Theory/Typing/Injectivity.lean:12,21,34` | GAP | the foundation `patsStrong` itself names as missing |
| K-C5 | strong normalization | assumed as `NormalizationIn`/`Normalization`, `PCUICSN.v:44,49`, used once | no normalization statement; the checker runs on fuel, `FuelConfig.lean` | DESIGN | drops the SN axiom, and with it any completeness claim |
| K-C6 | canonicity, consistency | `pcuic_canonicity`, `pcuic_consistent`, `PCUICCanonicity.v:20`, `PCUICConsistency.v:40` | none; the result is soundness relative to the model | GAP | no Lean-side canonicity for a downstream erasure proof |
| K-C7 | evaluation | weak-CBV evaluation and `wcbv_standardization`, [JACM] Sec 5.6 | `ParRedS.standard` about the ideal reduction, `Theory/Typing/HeadReduction.lean:466` | GAP | nothing plays the role erasure correctness needs |
| K-D1 | what the checker proves | sound AND complete: `typing_result_comp` carries `A -> False`, `safechecker/theories/PCUICErrors.v:401` | soundness only: `fun b _ => b -> ...`, `Verify/TypeChecker.lean:218` | FORCED-LEAN | [CT] proves `==` undecidable and `<=>` non-transitive, so completeness is false |
| K-D2 | verification method | checker written in Rocq against the spec, extracted ([JACM] Sec 6) | port of the C++ kernel on real `Lean.Expr`, verified through `TrExprS`/`TrEnv`, `Verify/Typing/Expr.lean:142` | DESIGN | fidelity to the shipping kernel, at the price of a refinement layer |
| K-D3 | open obligations | none | six `sorry`s in `Verify/TypeChecker/`, tabulated in the block | GAP | every top-level entry point is partial as stated |
| K-D4 | pointer equality | none; the Rocq checker is pure | `ptrEqExpr_eq`, `ptrEqConstantInfo_eq`, `PtrEq.lean:17,22` | FORCED-LEAN4LEAN | the ported algorithm branches on pointer identity |
| K-D5 | host data structures | MetaRocq defines its own containers in Rocq | 32 bridge axioms over `PersistentHashMap`, `PersistentArray`, `Expr`, `Level`, `Syntax`, `Verify/Axioms.lean:1` | FORCED-LEAN4LEAN | the kernel runs on Lean's own unverified containers |
| K-D6 | guard condition | `Axiom guard_checking`, `Axiom guard_checking_correct`, `PCUICTyping.v:54`, `PCUICGuardCondition.v:59` | nothing to axiomatise | FORCED-LEAN | Lean compiles recursion to recursors before the kernel |
| K-D7 | termination | fuel-free, well-founded on the SN axiom ([CCC] Sec 3.1-3.2) | explicit fuel counters, `FuelConfig.lean`, `divergences.md:20` | DESIGN | Lean definitions need termination witnesses |
| K-D8 | level algorithm | graph acyclicity equivalent to a satisfying valuation ([CCC] Sec 3.3) | canonical form with `normalize_complete`, `Verify/Level.lean:3721`, plus coNP-hardness, `Theory/LevelSat.lean:331` | DESIGN | a complete decision procedure, and a hardness result neither reference states |
| K-E1 | boundary shape | two named axioms plus the quoting layer | no single trust axiom: 16 live `sorry`s, 110 `axiom`, 12 `opaque`, quoted per theorem | GAP | the boundary must be recomputed per top-level statement |
| K-E2 | reification | Template quoting is unverified ([MR] Sect. 3) | no quoting layer; `Replay.lean` reads the real environment | DESIGN | closes the reification gap, opens K-D5 instead |
| K-E3 | vacuity | none reported | `addDecl.WF`'s `inductDecl` case `sorry`, `Params` needs `DefEqsAsPats`, `TrEnv.proj_defeq` unconsumed | GAP | three apparatuses are correct but true of nothing reachable |
| K-T1 | thesis vs. code | [CT] level rule system | semantic `VLevel.LE` | DESIGN | see K-A2 |
| K-T2 | thesis vs. code | [CT] states no complexity result | `equiv_iff_unsat`, coNP-hardness, `Theory/LevelSat.lean:331` | DESIGN | bounds what any complete level algorithm can cost |
| K-T3 | thesis vs. code | [CT] keeps a zeta rule | no zeta rule; `let` removed from the syntax | DESIGN | see K-A7 |
| K-T4 | thesis vs. code | [CT] `typesys.tex` results are about `<=>` | `<=>` unformalised | GAP | the thesis's negative results have no formal counterpart |
| K-T5 | thesis vs. code | [CT] `thm:unique` via the `\|-_n` stratification | `IsDefEq.uniq` via `HasTypeStratified`, `Theory/Typing/Strong.lean:944` | DESIGN | a strong annotated judgment replaces the alternation count |
| K-T6 | thesis vs. code | [CT] rec-normal forms and the eta-expansion argument | no counterpart | GAP | the partially-applied-eliminator fight is not modelled |
| K-T7 | thesis vs. code | [CT] `Wtypes.tex` eight-primitive system | not formalised; only its Sigma-projection shape reused, without its eta rule | DESIGN | the shape is what `TrProj` needs, the reduction is not |
| K-T8 | thesis vs. code | [CT] `soundness.tex` ZFC model and consistency | no counterpart | GAP | see K-C6 |
| K-T9 | thesis vs. code | [CT] `normalization.tex` splits `K+` from iota | one uniform iota rule | DESIGN | matches the stub's weaker relation, not its split |
| K-T10 | thesis vs. code | [CT] `compilation.tex` | no counterpart; native reduction refused | OPEN | `divergences.md:5` |
| K-T11 | thesis vs. code | [CT] generates recursor types and iota rules from a block spec | `VInductDecl.WF` pins them as 20 fields | DESIGN | makes block well-formedness decidable, at the cost of K-A12 |
| K-T12 | thesis vs. code | [CT] has no standardization theorem | `ParRedS.standard` after Kashima (2000) | DESIGN | beyond the reference; serves the head-reduction lemmas |
| K-T13 | thesis vs. code | [CT] calls regularity of reductions an easy induction | it is `patsStrong`, the branch's one open obligation | GAP | the widest-reaching gap in the project |

## 3. Divergences in full

### K-A1 -- universes and their algebra
- **Reference** PCUIC sorts `sProp | sSProp | sType (_ : univ)`, `common/theories/Universes.v:1459`; a universe is a
  set of `(level, bool)` pairs read through a valuation, with a global constraint store checked for consistency
  ([JACM] Sec 3; [CCC] Fig. 3, p. 8:6-7; [HAB] Ch. 2). Product formation uses `Sort.sort_of_product`
  (`Universes.v:1585`) in `type_Prod`, `pcuic/theories/PCUICTyping.v:208`.
- **Ours** `VLevel`, `Theory/VLevel.lean:8`: `zero`, `succ`, `max`, `imax`, `param i`, with parameters as de Bruijn
  indices. One sort family, `VExpr.sort u` (`Theory/VExpr.lean:7`); `Prop` is `sort .zero`, named nowhere. Product
  formation is `IsDefEq.forallEDF`, landing in `.sort (.imax u v)`, `Theory/Typing/Basic.lean:40`. Well-formedness is
  `VLevel.WF` (`Theory/VLevel.lean:20`): every `param i` satisfies `i < U`. No constraint store.
- **Nature** FORCED-LEAN.
- **Reason** Lean's universes are closed expressions over a declaration's own parameters, with `imax` giving `Prop`'s
  impredicativity; no `SProp`, no constraint graph, no `Set`.
- **Consequence** Judgments are indexed by a universe arity `U` rather than a constraint set, and universe
  polymorphism is level instantiation (`IsDefEq.instL`, `Theory/Typing/Lemmas.lean:646`) rather than
  `consistent_instance_ext`. None of MetaRocq's universe-graph machinery has or needs a counterpart.
- **Evidence** `common/theories/Universes.v:1459,1585`; `pcuic/theories/PCUICTyping.v:208`; `Theory/VLevel.lean:8,20`;
  `Theory/Typing/Basic.lean:40`; blueprint `syntax.tex`, `ind:vlevel`.

### K-A2 -- the level order is semantic, not a rule system
- **Reference** [CT] `axioms.tex` gives `l <= l' + n` by nine syntactic rules, including three `imax` normalisation
  identities and a case-split-on-a-parameter rule. MetaRocq's counterpart is `leq_universe` over valuations plus a
  graph procedure ([CCC] Sec 3.3, Fig. 9).
- **Ours** `VLevel.LE a b := forall ls, a.eval ls <= b.eval ls` (`Theory/VLevel.lean:41`) and `VLevel.Equiv a b :=
  a.eval = b.eval` (`:58`), with `eval` at `:34` reading `imax` through `Lean.Nat.imax` and out-of-range parameters as
  `0`.
- **Nature** DESIGN.
- **Reason** The semantic definition is the specification the algorithm is proved against, so no rule-system
  completeness proof is needed; [CT]'s `imax` identities become one `simp` each (`Theory/VLevel.lean:45` onward).
- **Consequence** `sortDF` and `constDF` compare levels by equivalence, so two sorts are definitionally equal exactly
  when they denote the same function of the parameters. The decision problem is then genuinely hard (K-T2), and the
  executable side must supply a complete procedure to match (K-D8).
- **Evidence** `Theory/VLevel.lean:34,41,58`; `Theory/Typing/Basic.lean:22,26`; blueprint `syntax.tex`,
  `def:vlevel-le-equiv`; `intro.tex`, thesis map row for `axioms.tex` (corrected: `VLevel.Equiv` is defined at line 58,
  not 71, which is `le_antisymm_iff`).

### K-A3 -- no cumulativity
- **Reference** `cumulSpec0 Sigma Gamma pb`, `pcuic/theories/PCUICCumulativitySpec.v:63`, is indexed by a direction
  `pb` and has directed rules: `cumul_Sort` with `compare_sort`, `cumul_Ind` and `cumul_Construct` with
  `cmp_global_instance` ([JACM]'s cumulative-inductive addition over [CCC]). Typing consumes it through `type_Cumul`,
  `PCUICTyping.v:296`.
- **Ours** No directed relation. `IsDefEq.symm` (`Theory/Typing/Basic.lean:20`) is a rule, so the relation is an
  equivalence, and `defeqDF` (`:44`) transports along a definitional *equality* of types.
- **Nature** FORCED-LEAN.
- **Reason** Lean has neither universe cumulativity nor cumulative inductive types.
- **Consequence** [JACM] Sec 4's cumulative-inductive pattern-matching fix and [HAB] Ch. 3's
  cumulativity-for-conversion machinery have no counterpart and need none. Unique typing is correspondingly simpler:
  `IsDefEq.uniq` gives an equality of the two types, not a common lower bound as `principal_type` does. Downstream
  this removes the need for [JACM]'s "unique sort quality" strengthening, which exists precisely because `Prop <=
  Type` must be disabled for erasability to be stable under expansion.
- **Evidence** `PCUICCumulativitySpec.v:63-100`; `PCUICTyping.v:296`; `Theory/Typing/Basic.lean:20,44`; blueprint
  `typing.tex`, `def:isdefeq`.

### K-A4 -- definitional proof irrelevance
- **Reference** `cumulSpec0`, `PCUICCumulativitySpec.v:63-203`, has no proof-irrelevance rule: its rules are
  transitivity, symmetry, reflexivity, the cumulativity rules, the congruences, and the reductions beta / zeta / rel /
  iota / fix / cofix / delta / proj. `SProp` exists as a sort (`Universes.v:1459`) but conversion does not identify
  its inhabitants. [CT] `axioms.tex` states the rule for Lean: from `p:P`, `h:p`, `h':p` derive `h == h'`.
- **Ours** `IsDefEq.proofIrrel`, `Theory/Typing/Basic.lean:52`: from `Gamma |- p : .sort .zero`, `Gamma |- h : p`,
  `Gamma |- h' : p`, derive `Gamma |- h == h' : p`.
- **Nature** FORCED-LEAN.
- **Reason** Lean's kernel identifies any two proofs of a `Prop`.
- **Consequence** Three things follow that the Rocq side does not carry. The conversion relation must be typed (K-B2),
  because the rule reads the type of both sides. Ordinary Church-Rosser is unavailable: confluence is proved only up
  to a separate `NormalEq` congruence (`Theory/Typing/ChurchRosser.lean:84`) absorbing irrelevance and eta, which is
  [CT]'s `==_p`. And definitional equality is undecidable outright ([CT] `typesys.tex` `sec:undecidable`), which is
  why the checker can only be sound (K-D1).
- **Evidence** `PCUICCumulativitySpec.v:63-203`; `Theory/Typing/Basic.lean:52`; `Theory/Typing/ChurchRosser.lean:84`;
  blueprint `metatheory.tex`, `def:normaleq`.

### K-A5 -- eta for functions as a primitive rule
- **Reference** PCUIC has no eta: `cumulSpec0` contains no such rule, [JACM] p. 8:3 names eta among the omitted
  features, and [HAB] Ch. 8 lists eta and `SProp` extensionality as open.
- **Ours** `IsDefEq.eta`, `Theory/Typing/Basic.lean:49`: from `Gamma |- e : forallE A B` derive `Gamma |- lam A (app
  e.lift (bvar 0)) == e : forallE A B`. The checker's counterpart `tryEtaExpansion` is proved sound,
  `Verify/TypeChecker/IsDefEq.lean:218`.
- **Nature** FORCED-LEAN.
- **Reason** Lean's kernel has definitional eta for functions.
- **Consequence** Eta cannot be a reduction, so it appears in `NormalEq` as two directed rules `etaL`/`etaR`
  (`Theory/Typing/ChurchRosser.lean:84`), which is why that relation is not symmetric by construction and needs
  `NormalEq.symm` as a theorem (`:147`). Confluence then needs the eta-expansion context machinery `ParRedExt`
  (`:998`), which has no Rocq counterpart. The rule also requires `e`'s type, reinforcing K-B2.
- **Evidence** `PCUICCumulativitySpec.v:63-203`; `Theory/Typing/Basic.lean:49`;
  `Theory/Typing/ChurchRosser.lean:84,147,998`; `Verify/TypeChecker/IsDefEq.lean:218`.

### K-A6 -- eta for structures, and unit-like types, are not modelled
- **Reference** Neither PCUIC nor MetaRocq's checker has structure eta or a unit-like rule, and the two agree, so no
  obligation arises.
- **Ours** The executable kernel has both, wired at `Verify/TypeChecker/IsDefEq.lean:227,488`. `IsDefEq` has no rule
  for either, and both `.WF` theorems are literal `sorry`:

      theorem tryEtaStructCore.WF {c : VContext} {s : VState}
          (he1 : c.TrExprS e1 e1') (he2 : c.TrExprS e2 e2') :
          RecM.WF c s (tryEtaStructCore e1 e2) fun b _ => b -> c.IsDefEqU e1' e2' := sorry

- **Nature** GAP.
- **Reason** The model would need a structure-eta rule on `IsDefEq` or a derivation from the recursor expansion of
  K-A8; neither is present. The statement is not derivable from the current rule set, so this is not a proof-effort
  gap alone.
- **Consequence** `inferType.WF'`, `checkType.WF` and `isDefEq.WF` (`Verify/TypeChecker.lean:204,215,218`) are partial
  as stated: the checker returns `true` on pairs the model cannot relate.
- **Evidence** `Verify/TypeChecker/IsDefEq.lean:227,488`; blueprint `status.tex`, sorry table and issue K9.

### K-A7 -- let is substituted away; no zeta rule
- **Reference** `tLetIn (na : aname) (b B t : term)`, `pcuic/theories/PCUICAst.v:201`, typed by `type_LetIn`,
  `PCUICTyping.v:219`, whose conclusion keeps the let in the *type*. Reduction has both `cumul_zeta`
  (`PCUICCumulativitySpec.v:163`) and `cumul_rel` (`:167`), the latter unfolding a let-bound context variable. [CT]
  `axioms.tex` Sec "let binders" keeps zeta as a rule with a conservativity argument.
- **Ours** `VExpr` has six constructors and no `let` (`Theory/VExpr.lean:7`). `TrExprS.letE`
  (`Verify/Typing/Expr.lean:164`) extends the translation context with `(none, .vlet ty' val')` and returns the body's
  translation, so the let is gone before the model sees the term. `IsDefEq` has no zeta rule and no
  context-variable-unfolding rule.
- **Nature** DESIGN.
- **Reason** [CT]'s own conservativity argument says a let can be expanded away; taking that to the syntax keeps the
  model at six constructors, removes a rule from every induction, and leaves `Lookup` (`Theory/Typing/Basic.lean:6`)
  with assumptions only.
- **Consequence** The kernel's `whnfCore` zeta step must be proved to preserve *translation* rather than to be a rule
  of the judgment, and `VLCtx` carries two kinds of entry that `Delta.toCtx` then collapses. The blueprint records the
  divergence from [CT] explicitly.
- **Evidence** `PCUICAst.v:201`; `PCUICTyping.v:219`; `PCUICCumulativitySpec.v:163,167`; `Theory/VExpr.lean:7`;
  `Verify/Typing/Expr.lean:164`; blueprint `intro.tex`, thesis map.

### K-A8 -- projections are recursor applications, not a term former
- **Reference** `tProj (p : projection) (c : term)`, `PCUICAst.v:208`, typed by `type_Proj`, `PCUICTyping.v:263`, with
  its own reduction `cumul_proj` (`PCUICCumulativitySpec.v:196`) and congruence `cumul_Proj` (`:139`). [CT] has no
  projection form; `Wtypes.tex` gives a Sigma-projection typing shape with an eta rule the text marks as not a Lean
  definitional equality.
- **Ours** No projection node in `VExpr`. `TrExprS.proj` (`Verify/Typing/Expr.lean:171`) defers to `TrProj env U Gamma
  s i e' e''`, which builds

      P_i = S.rec (uss i) ps (fun x => F_i[f_j := P_j x]) (fun f_0 .. f_{n-1} => f_i)

  -- an application of the recursor the kernel already generates for the structure, chaining earlier fields'
  projection functions into later fields' motives so a dependent field type is expressible (`Theory/Proj.lean`;
  blueprint `def:trproj`, `struct:trprojctor`). The reduction is then derived, not postulated: `TrEnv.proj_defeq`
  (blueprint `trenv.tex`, `thm:tr-env-proj-defeq`) obtains it from the registered iota rule of K-A10.
- **Nature** DESIGN.
- **Reason** A projection node would need its typing rule, its iota rule and (for Lean) its eta rule added to
  `IsDefEq`, with a new case in every structural lemma. The expansion reuses the iota registry and the existing
  metatheory, and makes the projection's reduction a theorem about the environment rather than an axiom of the
  judgment.
- **Consequence** Two costs. `TrProj` is not purely syntactic: `major_ty` and `fn_ty` are `HasType` side conditions
  carried inside a translation relation, unlike every other clause of `TrExprS`, so translation and typing are
  entangled at this node. And coverage is partial (K-A9).
- **Evidence** `PCUICAst.v:208`; `PCUICTyping.v:263`; `PCUICCumulativitySpec.v:139,196`;
  `Verify/Typing/Expr.lean:171`; `Theory/Proj.lean`; blueprint `proj.tex`, `contrib-trproj.tex`.

### K-A9 -- the projection expansion covers only some structures
- **Reference** `type_Proj`, `PCUICTyping.v:263`, applies to every `declared_projection`, with no restriction on the
  structure's shape.
- **Ours** `inferProj.WF_struct` (`Verify/TypeChecker/InferType.lean:398`) is stated only for a structure that is
  non-mutual, single-constructor, non-indexed and non-recursive, and is `sorry`. The general `inferProj.WF` (`:410`)
  is `sorry`, and its docstring says it is not provable as stated: "the model has no projection node, and `TrProj` is
  the recursor expansion of one, which exists only for the structures of `inferProj.WF_struct`, while `inferProj` also
  accepts projections of reflexive, indexed and nested single-constructor types [...] those have no `TrExprS`
  derivation at all."
- **Nature** GAP.
- **Reason** The expansion exists only where the generated recursor has the shape the construction assumes. Reflexive,
  indexed and nested structures need a selector binding the inductive-hypothesis binders, a motive abstracting the
  indices, extra motives and minors for a nested block, or a projection node with its own iota and eta rules.
- **Consequence** `inferType.WF'` and `checkType.WF` (`Verify/TypeChecker.lean:204,215`) are, as stated, unprovable
  without extending the model, not merely unproved: a kernel-accepted term mentioning such a projection has no
  `TrExprS` derivation, so no statement about it can be formed. `TrProj.uniq` (`Verify/Typing/Lemmas.lean:995`) and
  `TrProj.weak'_inv` (`:747`) stay `sorry`, gating `TrExprS.uniq` and reaching 138 and 92 constants.
- **Evidence** `Verify/TypeChecker/InferType.lean:398,410`; `Verify/Typing/Lemmas.lean:747,995`; blueprint
  `status.tex`, issue K6.

### K-A10 -- iota as a schematic rewrite registry; K-like reduction absent
- **Reference** PCUIC has one iota rule, `cumul_iota` (`PCUICCumulativitySpec.v:175`), firing on a `tCase` whose
  scrutinee is a constructor application, plus `cumul_fix` guarded by `is_constructor` (`:182`). [CT] `axioms.tex`
  `sec:iota` gives both the constructor rule and K-like reduction for subsingleton eliminators, connecting the latter
  to axiom K.
- **Ours** `VEnv` carries a third field `pats : (p : Pattern) -> p.RHS x p.Check -> Prop` (`Theory/VEnv.lean:16`), a
  registry of schematic rewrite rules, and one generic rule fires them:

      | pat {p : Pattern} {r : p.RHS x p.Check} {m1 m2 chk} :
        env.pats p r -> p.Matches e m1 m2 -> Gamma |- e : A ->
        r.2.Realizes m1 m2 chk ->
        (forall t in chk, Gamma |- t.1 == t.2.1 : t.2.2) ->
        Gamma |- e == r.1.apply m1 m2 : A

  at `Theory/Typing/Basic.lean:60`. `VEnv.addRecRule` (`Theory/Inductive.lean:257`) registers one entry per recursor
  rule, and its docstring records the omission: only the constructor rule of [CT] Sec 2.6.4 is registered, K-like
  reduction is not. `VRecursor.k` is recorded and never read.
- **Nature** DESIGN for the registry; GAP for K-like reduction.
- **Reason** One generic rule with a registry gives every recursor a reduction without a per-block rule, keeping
  `IsDefEq` at a fixed number of constructors. K-like reduction is omitted because it needs a proof-irrelevance step
  to reconstruct a constructor application from a non-constructor major premise, which the pattern machinery does not
  express.
- **Consequence** The kernel reduces `Eq.rec` on a non-constructor proof; the model does not, so `reduceRecursor.WF`
  (`Verify/TypeChecker/WHNF.lean:149`) is `sorry`. Separately, `VExpr.RuleShape` (`Theory/Inductive.lean:174`) pins
  only the argument count the reduct passes the minor premise, not its shape, so `VInductDecl.WF` accepts iota rules
  the kernel would never generate.
- **Evidence** `PCUICCumulativitySpec.v:175,182`; `Theory/VEnv.lean:16`; `Theory/Typing/Basic.lean:60`;
  `Theory/Inductive.lean:174,257`; `Verify/TypeChecker/WHNF.lean:149`; blueprint `status.tex`, issues K4, K5.

### K-A11 -- quotients are a delta axiom, not an iota rule
- **Reference** PCUIC has no quotient types. [CT] `axioms.tex` Sec "Non-primitive axioms" gives `Quot`, `mk`, `sound`,
  `lift` and the computation rule `lift_R b f h (mk_R a) ~> f a`, calling the group semi-builtin because only `sound`
  is an axiom while the computation rule is a genuine reduction.
- **Ours** `quotDefEq` (`Theory/Quot.lean:11`) is a `VDefEq` -- an entry of `env.defeqs`, fired by `IsDefEq.extra`
  (`Theory/Typing/Basic.lean:55`) -- and `VEnv.addQuot` (`Theory/Quot.lean:16`) adds the four constants and then this
  one axiom. It is not a `pats` entry, although [CT] calls the rule iota.
- **Nature** DESIGN.
- **Reason** The rule is a single closed equation with no pattern variables and no side conditions, so the delta
  mechanism suffices; routing it through `pats` would need a `Pattern` and a `PatWF` proof.
- **Consequence** Two. `VEnv.WF.patsStrong` (`Theory/Typing/EnvLemmas.lean:334`) must handle the asymmetry: the prefix
  environment it quantifies over may already carry delta rules and the quotient rule while it reasons about `pats`
  subject reduction. And the `Params` class (`Theory/Typing/ChurchRosser.lean:12`) requires `DefEqsAsPats` -- every
  axiom realised by a rule -- which fails as soon as an environment declares a `def` or the quotient rule, so the
  confluence development of K-C1 applies to no realistic environment.
- **Evidence** `Theory/Quot.lean:11,16`; `Theory/Typing/Basic.lean:55`; `Theory/Typing/ChurchRosser.lean:12`;
  blueprint `typing.tex`, `thm:addquot-wf` Caveat; `status.tex`, issue K2.

### K-A12 -- inductive-block well-formedness is asserted, not derived
- **Reference** `on_global_env` / `on_inductive` carries positivity, universe and allowed-elimination conditions,
  established for a real environment by `check_wf_env` (`safechecker/theories/PCUICSafeChecker.v:2398`). [JACM] p. 8:3
  notes nested inductives are outside PCUIC.
- **Ours** `VInductDecl.WF` (`Theory/Inductive.lean`; blueprint `structure:ind-wf`) is a 20-field syntactic
  specification, pinning recursor types and iota rules directly rather than generating them from the block's
  specification as [CT] does. Nothing derives it from the kernel's own inductive checker: `TrEnv'.induct`
  (`Verify/Environment/Basic.lean:583`) takes it as a bare hypothesis, validated by `decide` on concrete data in
  `Tests/IotaShape.lean` (48 type formers), not proved. The executable kernel additionally implements nested-inductive
  elimination (`Inductive/Add.lean`), for which the model has no account.
- **Nature** GAP.
- **Reason** Deriving `VInductDecl.WF` from `Environment.addInductive` is the missing `inductDecl` case of
  `addDecl.WF` (K-E3); the 20-field form makes block well-formedness decidable so it can be checked against real
  declarations.
- **Consequence** Every theorem about inductive blocks is conditional on a hypothesis no proof supplies for an
  environment the kernel actually builds. With K-E3, the whole apparatus is correct but vacuous end to end.
- **Evidence** `Theory/Inductive.lean`; `Verify/Environment/Basic.lean:583`; `Verify/Environment.lean:208`; blueprint
  `status.tex`, issues K3, K10.

### K-A13 -- no literal node; primitives verified as reflection
- **Reference** `tPrim (prim : prim_val term)`, `PCUICAst.v:211`, is a term former with its own typing rule
  `type_Prim` (`PCUICTyping.v:290`) requiring `primitive_constant`, `primitive_invariants` and
  `primitive_typing_hyps`, and its own congruence `cumul_Prim` (`PCUICCumulativitySpec.v:152`). [CT] has no
  primitives.
- **Ours** No literal constructor in `VExpr`. `TrExprS.lit` (`Verify/Typing/Expr.lean:169`) requires `env.ContainsLits
  l` and translates through `l.toConstructor`, so `Nat` and `String` literals become constructor applications
  (`VExpr.natLit`, `Verify/Typing/Expr.lean:186`). GMP-accelerated arithmetic is not a reduction rule either:
  `Primitive.checkDef` (`Primitive.lean:561`) recognises a declaration by name and type and runs `isDefEq` on its
  value, and the verification closes those open equations into `Reflects` statements transported onto the constant
  (blueprint `primitives-core.tex`, `vpc:thm:reflects-toconst`).
- **Nature** DESIGN.
- **Reason** Keeping the model at six constructors; the acceleration is a property of a declaration the environment
  already contains, not a new rule of the judgment.
- **Consequence** Eighteen per-primitive obligations appear in the Verify layer (blueprint `primitives-arith.tex`)
  with no counterpart on either reference side, all tainted through `VEnv.WF.orderedStrong`. Note a divergence in the
  other direction: `Primitive.checkDef` verifies that primitives are declared with the correct types and definitional
  behaviour, which Lean's own kernel does not (`divergences.md:6`), so lean4lean is stricter than the kernel it models
  here.
- **Evidence** `PCUICAst.v:211`; `PCUICTyping.v:290`; `Verify/Typing/Expr.lean:169,186`; `Primitive.lean:561`;
  `divergences.md:6` (corrected: `.lit` and `VExpr.natLit` line numbers were off by one/eight).

### K-A14 -- native reduction refused
- **Reference** PCUIC models no VM or native conversion; [HAB] Ch. 8 lists primitive-operation coverage among the open
  problems.
- **Ours** `TypeChecker.Inner.reduceNative` does not support `reduceBool`, and `reduceNative.WF` is vacuous -- the
  branch never fires (blueprint `typechecker.tex`, `thm:vtc-reducenative`).
- **Nature** OPEN.
- **Reason** `divergences.md:5` states it: this "would involve implementing verified compilation, which while possible
  would be an additional chunk of work comparable to this entire repo".
- **Consequence** lean4lean rejects declarations Lean's kernel accepts through native reduction. The obligation is not
  carried as an axiom: the code path is absent, so soundness is unaffected and only coverage is reduced.
- **Evidence** `divergences.md:5`; blueprint `typechecker.tex`, `thm:vtc-reducenative`.

### K-B1 -- one relation instead of two
- **Reference** MetaRocq keeps `typing` (`PCUICTyping.v:198`) and `cumulSpec0` (`PCUICCumulativitySpec.v:63`) as
  separate inductives joined by `type_Cumul` (`PCUICTyping.v:296`). [CT] likewise keeps typing and definitional
  equality separate.
- **Ours** One four-place relation `VEnv.IsDefEq env U Gamma e1 e2 A` (`Theory/Typing/Basic.lean:18`), with typing as
  its diagonal, `HasType env U Gamma e A := IsDefEq env U Gamma e e A` (`:69`). Each rule is simultaneously a typing
  rule and a congruence (`sortDF`, `constDF`, `appDF`, `lamDF`, `forallEDF`).
- **Nature** DESIGN.
- **Reason** Proof irrelevance and eta make the two relations mutually dependent anyway ([CT] `unique.tex` opens by
  naming this circularity), so merging turns a mutual induction into one.
- **Consequence** Every structural lemma is proved once instead of twice, and the typing-only judgment `HasTypeStrong`
  (`Theory/Typing/Strong.lean:108`) has to be reconstructed separately where syntax-directed inversion is needed. The
  price is that `IsDefEq` is not syntax-directed, so the inversion lemmas (`Theory/Typing/Strong.lean:886`) route
  through the strong judgment and inherit its hypotheses.
- **Evidence** `PCUICTyping.v:198,296`; `PCUICCumulativitySpec.v:63`; `Theory/Typing/Basic.lean:18,69`;
  `Theory/Typing/Strong.lean:108,886`.

### K-B2 -- conversion is typed
- **Reference** `cumulSpec0 Sigma Gamma pb : term -> term -> Type` (`PCUICCumulativitySpec.v:63`) relates two terms in
  a context with no type index; only `cumul_Trans` carries side conditions, and those are closedness.
- **Ours** `IsDefEq` carries the type as its last argument. The untyped form is derived: `IsDefEqU env U Gamma e1 e2
  := exists A, IsDefEq env U Gamma e1 e2 A` (`Theory/Typing/Basic.lean:76`). Their agreement is a theorem,
  `isDefEq_iff` (`Theory/Typing/UniqueTyping.lean:113`), proved *from* unique typing, hence inheriting its taint.
- **Nature** FORCED-LEAN.
- **Reason** `proofIrrel` reads the shared type of both sides and `eta` reads the `forallE A B` type of `e`; neither
  can be stated untyped.
- **Consequence** Composing equalities stated at different types is not free: the family `trans_r`, `trans_l`,
  `transU_r`, `transU_l`, `IsDefEqU.trans` (`Theory/Typing/UniqueTyping.lean:124`) exists only to do it, each one line
  from `uniq` plus `defeqDF`, and each therefore depends on `IsDefEq.uniq`. On the Rocq side these are free, because
  `cumul_Trans` is unconditional.
- **Evidence** `PCUICCumulativitySpec.v:63-70`; `Theory/Typing/Basic.lean:49,52,76`;
  `Theory/Typing/UniqueTyping.lean:113,124`.

### K-B3 -- no binder names in the model
- **Reference** `term` carries `aname` on `tProd`, `tLambda`, `tLetIn` (`PCUICAst.v:199-201`), and `eq_binder_annot na
  na'` is a premise of `cumul_Lambda`, `cumul_Prod`, `cumul_LetIn` (`PCUICCumulativitySpec.v:114,120,127`).
- **Ours** `VExpr.lam (binderType body)` and `VExpr.forallE (binderType body)` (`Theory/VExpr.lean:7`): no name, no
  `BinderInfo`. Names live only on the kernel side; `Expr`'s `==` ignores binder names and `BinderInfo`, so only
  `EquivBEq` and not `LawfulBEq` holds for it (blueprint `trexpr.tex`, `family:expr-beq`).
- **Nature** DESIGN.
- **Reason** Names carry no logical content; dropping them removes a premise from three congruence rules and makes the
  model's equality plain structural equality.
- **Consequence** The `Expr`-side lawfulness facts the hash maps and the `EquivManager` cache need must be proved as
  `EquivBEq`/`LawfulHashable` instances rather than assumed, and `Expr.data_eq` -- equivalent expressions share their
  header word -- becomes load-bearing.
- **Evidence** `PCUICAst.v:199-201`; `PCUICCumulativitySpec.v:114,120,127`; `Theory/VExpr.lean:7`; blueprint
  `trexpr.tex`, `family:expr-beq`.

### K-B4 -- algorithmic equality is not formalised
- **Reference** [CT] `axioms.tex` presents `<=>` as an inference system -- no transitivity, a head-reduction escape
  hatch, an extensionality principle replacing eta -- and `typesys.tex` then proves it non-transitive and proves that
  the algorithmic typing judgment fails subject reduction. MetaRocq goes the other way and formalises a full
  algorithmic specification, proved equivalent to the declarative one ([JACM] Sec 4; [HAB] Ch. 3, Specs 4, 6, 7, 8).
- **Ours** No relation corresponding to `<=>` exists. The blueprint states it: the algorithmic relation of [CT] Sec
  2.3 "is itself unformalised, its role played by `TypeChecker.lean`". Its stand-in is the `Verify/TypeChecker`
  correctness chain, topped by `isDefEqCore.WF`.
- **Nature** GAP.
- **Reason** With `<=>` unformalised there is no object to state [CT]'s negative results about, and no intermediate
  layer between the executable algorithm and the declarative judgment.
- **Consequence** Every algorithmic fact is proved directly about the monadic program, in the program logic of
  `Verify/TypeChecker/Basic.lean`, rather than about a relation. There is no place to record that the algorithm is
  non-transitive, so nothing warns a consumer that "the kernel accepted this" is weaker than "this is definitionally
  equal" -- a distinction the erasure work downstream depends on, because it must assume `==`, not `<=>`.
- **Evidence** blueprint `intro.tex`, thesis map row for `axioms.tex` Sec 2.3; `typechecker.tex`, at-a-glance Thesis
  line.

### K-B5 -- the bidirectional layer exists but is unwired
- **Reference** MetaRocq's `Bidirectional/` defines `Sigma ;;; Gamma |- t |> A` and proves it equivalent to
  declarative typing; `infer` is stated against it, `safechecker/theories/PCUICTypeChecker.v:1502`. This intermediate
  specification is what makes the completeness proof possible ([JACM] Sec 4, Sec 6; [HAB] Ch. 3, Ch. 5).
- **Ours** `VEnv.InferType` (`Theory/Typing/HeadReduction.lean:508`) is the corresponding algorithmic reading:
  variables, sorts and constants read their type off the context or environment; application weak-head-reduces the
  function's type to a `Pi`; `Pi` reduces both components' inferred types to sorts. It is sound and deterministic, and
  `InferType.exists` (`:633`) is its completeness statement. No executable function is proved against it: the
  executable `inferType'` is proved against `TrTyping` instead (`Verify/TypeChecker.lean:204`).
- **Nature** GAP.
- **Reason** `InferType` lives in `Theory/` under the `Params` class of K-C1, which no realistic environment
  satisfies, while the executable checker is verified in the `Verify/` refinement layer against `VEnv.IsDefEq`
  directly.
- **Consequence** The completeness route is present in outline and unusable in practice. `InferType.exists` is itself
  tainted twice, via `IsDefEq.church_rosser` and via `VEnv.WF.patsStrong`.
- **Evidence** `safechecker/theories/PCUICTypeChecker.v:1502`; `Theory/Typing/HeadReduction.lean:508,633`;
  `Verify/TypeChecker.lean:204`; blueprint `metatheory.tex`, `thm:infertype-exists`.

### K-B6 -- reduction is abstract and parameterised
- **Reference** PCUIC has `red1` as a first-class one-step reduction, and `cumulSpec0` carries the reductions directly
  as rules (`cumul_beta` through `cumul_proj`, `PCUICCumulativitySpec.v:159-199`). Confluence, subject reduction and
  standardization are all stated about `red1` and its closures, unconditionally over `wf Sigma`.
- **Ours** `ParRed` (`Theory/Typing/ChurchRosser.lean:473`), `CParRed` (`:488`), `WHRed`
  (`Theory/Typing/HeadReduction.lean:59`) and `StRed` (`:293`) all live under the `Params` class
  (`Theory/Typing/ChurchRosser.lean:12`), which fixes an environment, its well-formedness, a universe count, and an
  *abstract* family `Pat p r` with coherence conditions (`pat_simple`, `pat_uniq`, `pat_wf`, `pat_app_l`,
  `pat_app_l_uniq`, `pat_app_uniq`, `extra_pat`, `pat_env`). `IsDefEq` has no reduction relation.
- **Nature** DESIGN.
- **Reason** Abstracting over the rule family proves the confluence argument once for delta and iota rules alike, so
  adding an inductive block adds a registry entry, not a proof case.
- **Consequence** Confluence is only as good as the instance. The one instance, `VEnv.toParams`
  (`Theory/Typing/InductiveParams.lean:393`), requires `DefEqsAsPats`, which fails for any environment with a `def` or
  the quotient rule, so the whole `ChurchRosser.lean`/`HeadReduction.lean` development applies to no realistic
  environment. This is K-C1's real content.
- **Evidence** `PCUICCumulativitySpec.v:159-199`; `Theory/Typing/ChurchRosser.lean:12,473,488`;
  `Theory/Typing/HeadReduction.lean:59,293`; `Theory/Typing/InductiveParams.lean:393`; blueprint `status.tex`, issue
  K2.

### K-B7 -- two environment invariants, bridged silently
- **Reference** `wf Sigma` is `on_global_env` over the declaration list, one predicate carrying everything, and every
  metatheorem takes it.
- **Ours** Two. `VEnv.WF' ds E` (`Theory/Typing/Env.lean:48`) says `E` is reached from empty by a list of `VDecl.WF`
  steps (`:18`; seven forms: axiom, def, opaque, example, mutualDef, quot, induct), and `VEnv.WF` is its existential
  closure; `Ordered` (`Theory/Typing/Lemmas.lean:257`) is the weaker builds-in-order invariant the structural lemmas
  consume. `WF.ordered` (`Theory/Typing/EnvLemmas.lean:87`) bridges them with a `CoeOut`. A third layer,
  `OrderedStrong` (`Theory/Typing/Strong.lean:679`), bundles `Ordered`, `OnTypes env (EnvStrong env)` and
  `PatsStrongOn env`.
- **Nature** DESIGN.
- **Reason** `Ordered` is monotone and cheap, so weakening, substitution and regularity are proved under it without
  the declaration history; `OrderedStrong` names exactly what the strengthening argument needs.
- **Consequence** The `CoeOut` instances make the passage silent, which is what the status chapter flags: `CoeOut
  (VEnv.WF env) env.OrderedStrong` (`Theory/Typing/EnvLemmas.lean:343`) hides a `sorry`-backed hypothesis at every
  call site, so any `E.WF` hypothesis inherits `VEnv.WF.patsStrong` with no visible cue.
- **Evidence** `Theory/Typing/Env.lean:18,48`; `Theory/Typing/Lemmas.lean:257`; `Theory/Typing/Strong.lean:679`;
  `Theory/Typing/EnvLemmas.lean:87,339,343`; blueprint `metatheory.tex`, `instance:coeout-orderedstrong` Caveat.

### K-C1 -- confluence holds only for an unrealistic class of environments
- **Reference** Confluence of PCUIC reduction is proved by the triangle method with the optimal reduction function
  `rho` ([CCC] Thm 2.2, Cor 2.2.1, p. 8:13; `pcuic/theories/PCUICParallelReductionConfluence.v`, `PCUICConfluence.v`),
  unconditionally for any `wf Sigma`. [CT] `thm:church_rosser` proves the analogue for the restricted kappa reduction,
  up to `==_p`.
- **Ours** `ParRedS.church_rosser` (`Theory/Typing/ChurchRosser.lean:1302`): if `Gamma |- e : A`, `e >>* e1` and `e
  >>* e2`, the two reducts converge up to `NormalEq` -- structurally [CT]'s theorem. Two qualifications. It is stated
  under `[Params]` (K-B6), whose one instance excludes any environment with a `def` or the quotient rule. And it
  depends on `NormalEq.parRed` (`:1181`), which has two literal `sorry`s at `:1193` and `:1212`, where a pattern or
  delta step meets a `constDF` resp. `appDF` normal equality -- the cases [CT] settles by unique typing and smallness
  of the eliminator (`thm:gg_compat`).
- **Nature** GAP.
- **Reason** The `Params` restriction is the price of K-B6's abstraction; the two sorries are upstream holes predating
  both contributed branches.
- **Consequence** Church-Rosser, standardization (`Theory/Typing/HeadReduction.lean:466`), `IsDefEq.church_rosser`
  (`:1347`), `reduce_sort`, `reduce_forallE` and `InferType.exists` are all unproved, independently of the
  `patsStrong` gap. Nothing in the Verify layer consumes them today, so the checker's soundness does not depend on
  them -- but nothing downstream gets a usable confluence result either.
- **Evidence** `pcuic/theories/PCUICConfluence.v`; `Theory/Typing/ChurchRosser.lean:12,1181,1193,1212,1302,1347`;
  `Theory/Typing/InductiveParams.lean:393`; blueprint `metatheory.tex` Caveats; `status.tex`, issue K2.

### K-C2 -- subject reduction for iota is a rule, not a theorem
- **Reference** `subject_reduction` (`pcuic/theories/PCUICSR.v:3129`) is a proved theorem ([JACM] Sec 5; [HAB] Ch. 4);
  its one-step form is `sr_red1` (`:1529`). [CT] `typesys.tex` "Regularity continued" item `red_equiv` states the
  corresponding fact and dismisses it as an easy induction.
- **Ours** `IsDefEq.pat` (`Theory/Typing/Basic.lean:60`) asserts the reduct at the redex's type with *no typing
  premise on the reduct*, so subject reduction for iota is built into the judgment; the note at
  `Theory/Typing/Basic.lean:57` says so. The rule is false over a merely `Ordered` environment, with the author's own
  counterexample at `Theory/Typing/EnvLemmas.lean:327`: a definitional axiom `List Nat == List Bool` gives `List.rec`
  a well-typed redex with an ill-typed reduct. The honest form is `IsDefEqStrong.pat`
  (`Theory/Typing/Strong.lean:89`), reached from `VEnv.WF` only through

      theorem VEnv.WF.patsStrong {env : VEnv} (H : env.WF) : env.PatsStrong := sorry

  at `Theory/Typing/EnvLemmas.lean:334`.
- **Nature** GAP for the obligation, DESIGN for the rule's shape.
- **Reason** Building it into the rule lets `IsDefEq` be stated before the strong system exists; the repayment is
  deferred. A proof needs inversion of the redex's typing with injectivity of the block's type formers -- K-C4, itself
  open -- and must handle iota in the presence of delta and the quotient rule (K-A11).
- **Consequence** Via the `CoeOut` of K-B7 all 343 `VEnv.WF`-dependent constants become conditional on it: all of
  `UniqueTyping.lean`, most of `ChurchRosser.lean` and `HeadReduction.lean`, and the whole Verify primitives layer.
  The upstream entry point it replaces, `Ordered.strong`, is a proved theorem, so the iota branch converts a proof
  into an obligation.
- **Evidence** `PCUICSR.v:1529,3129`; `Theory/Typing/Basic.lean:57,60`; `Theory/Typing/EnvLemmas.lean:327,334`;
  `Theory/Typing/Strong.lean:89`; blueprint `status.tex`, sorry table, issue K1.

### K-C3 -- unique typing by a different route, and tainted
- **Reference** `principal_type` (`pcuic/theories/PCUICPrincipality.v:74`), proved, and explicitly "without relying on
  normalization"; the computational counterpart is `principal_types` (`safechecker/theories/PCUICSafeRetyping.v:915`),
  which is what [JACM] Sec 6.4's retyping algorithm delivers and what `is_erasableb` consumes downstream. [CT]
  `thm:unique` proves unique typing for the ideal judgment via a `|-_n`-indexed joint induction with Church-Rosser.
- **Ours** `IsDefEq.uniq` (`Theory/Typing/UniqueTyping.lean:13`): for a well-formed environment and context, `Gamma |-
  e1 == e2 : A` and `Gamma |- e2 == e3 : B` give `exists u, Gamma |- A == B : sort u`. The route is not [CT]'s:
  strengthen to `IsDefEqStrong`, project to the syntax-directed `HasTypeStrong`, stratify via `HasTypeStratified`
  (`Theory/Typing/Strong.lean:944`), then well-founded induction on the max of the two levels.
- **Nature** GAP for the taint, DESIGN for the route.
- **Reason** `HasTypeStratified` counts derivation levels of a syntax-directed judgment rather than alternations
  between typing and conversion, avoiding [CT]'s mutual recursion. The taint has two independent sources: the
  application case appeals to `IsDefEqU.forallE_inv_stratified` (K-C4) and the strengthening step to
  `VEnv.WF.patsStrong` (K-C2).
- **Consequence** Unique typing is available to the rest of the development, conditionally. Because K-B2 routes almost
  every composition of equalities through `uniq`, the taint is pervasive: `isDefEq_iff`, the mixing family,
  `NormalEq.defeq`, `ParRed.defeq` and the inversion lemmas all inherit it.
- **Evidence** `PCUICPrincipality.v:74`; `safechecker/theories/PCUICSafeRetyping.v:915`;
  `Theory/Typing/UniqueTyping.lean:13,113,124`; `Theory/Typing/Strong.lean:944`; blueprint `metatheory.tex`,
  `thm:unique-typing`.

### K-C4 -- type-former injectivity is entirely open
- **Reference** In MetaRocq, injectivity of sorts and products under conversion follows from confluence and is proved
  (`pcuic/theories/PCUICConvCumInversion.v`, `PCUICInversion.v`), feeding the inversion lemmas the checker and erasure
  use. [CT] `thm:1dinv` is the thesis's Definitional Inversion theorem, proved as the step that closes the
  unique-typing induction; `soundness.tex` Sec "Type injectivity" gives the set-theoretic analogue.
- **Ours** `Theory/Typing/Injectivity.lean` has three declarations, all `sorry`: `IsDefEqU.sort_inv` (`:12`),
  `IsDefEqU.forallE_inv_stratified` (`:21`), `IsDefEqU.sort_forallE_inv` (`:34`). The derived `IsDefEqU.forallE_inv`
  (`:23`) is proved from them plus `IsDefEq.strong`, so it carries two independent gaps.
- **Nature** GAP.
- **Reason** Pre-existing upstream holes, not contributed. Two routes are in flight: the Church-Rosser line of K-C1,
  blocked by its own two sorries and the `Params` restriction, and the experimental logical-relations line
  (`Experimental/ShapeLogRel.lean`), whose fundamental theorem has a `sorry` in its `const` case.
- **Consequence** These are the ingredient `patsStrong` names as missing (`Theory/Typing/EnvLemmas.lean:323`), so
  K-C2's obligation rests on an already-open foundation: the two widest gaps are not independent. Unique typing,
  `reduce_sort` and `reduce_forallE` all appeal to them.
- **Evidence** `Theory/Typing/Injectivity.lean:12,21,23,34`; `Theory/Typing/EnvLemmas.lean:323`; blueprint
  `typing.tex`, `thm:injectivity-open`; `experimental-logrel.tex`, at-a-glance Status.

### K-C5 -- no normalization statement; the checker runs on fuel
- **Reference** MetaRocq assumes normalization as typeclasses rather than axiom constants: `NormalizationIn`
  (`pcuic/theories/PCUICSN.v:44`) and `Normalization` (`:49`), so every theorem needing it names it. [JACM] Sec 5.6
  identifies `wcbv_standardization` as the one place it is used in that part of the development, and the checker's
  fuel-free weak-head normalisation is well-founded on it ([CCC] Sec 3.1-3.2, Fig. 8). [CT] `normalization.tex` sets
  out to give a terminating reduction and ends unfinished before stating any theorem.
- **Ours** No normalization statement in any form. The executable checker is total by construction using explicit fuel
  counters (`FuelConfig.lean`), and the `.WF` theorems are shaped so that running out of fuel is unconstrained:
  `withFuel.WF` justifies what the checker returns and says nothing about what it fails to return.
- **Nature** DESIGN.
- **Reason** Lean definitions need explicit termination witnesses, and a fuel counter is one; `divergences.md:20`
  records that the native kernel bounds mutual checking through `maxRecDepth` while lean4lean exposes several
  independent counters.
- **Consequence** The largest single axiom of the Rocq trust boundary is absent. In exchange, completeness is not
  merely unproved but unstatable in the current shape: a fuel-exhausted run is indistinguishable from a rejection and
  nothing relates the two. Downstream, there is no Lean-side normalization result for an erasure proof to lean on,
  where [JACM]'s erasure correctness consumes `wcbv_standardization`.
- **Evidence** `PCUICSN.v:44,49`; `FuelConfig.lean`; `divergences.md:20`; blueprint `typechecker.tex`, at-a-glance
  Goal.

### K-C6 -- no canonicity, no consistency
- **Reference** `pcuic_canonicity` (`pcuic/theories/PCUICCanonicity.v:20`) and `pcuic_consistent`
  (`pcuic/theories/PCUICConsistency.v:40`), both proved under `NormalizationIn` ([JACM] Sec 5.7-5.8; [HAB] Ch. 4).
  [CT] `soundness.tex` proves soundness of a proof-split variant of Lean in ZFC plus countably many inaccessibles,
  with consistency as a corollary -- on paper, and for a system the text itself flags as slightly stronger than Lean's
  (`Wtypes.tex` Sec "The menagerie" adopts two eta-style rules that are not Lean definitional equalities).
- **Ours** None. The blueprint's thesis map records, against [CT] Sec 6: "none. lean4lean proves kernel correctness
  relative to the `Theory` model, not consistency of the type theory."
- **Nature** GAP.
- **Reason** Out of scope by design: the project's statement is that the checker accepts a term only if the model
  derives its typing -- a refinement result, not a metamathematical one.
- **Consequence** The trust chain terminates at `VEnv.IsDefEq`: nothing says that relation is consistent, and the only
  evidence is [CT]'s pen-and-paper argument for a nearby system. Downstream this matters twice: an erasure correctness
  proof needing canonicity of the source calculus (as [JACM] Sec 7.3 does) has nothing Lean-side to cite, and a claim
  that lean4lean establishes Lean's consistency is false.
- **Evidence** `PCUICCanonicity.v:20`; `PCUICConsistency.v:40`; blueprint `intro.tex`, thesis map row for Sec 6;
  `status.tex`, Sec Trust boundary.

### K-C7 -- standardization is about the wrong reduction for downstream use
- **Reference** [JACM] Sec 5.6, pp. 8:46-8:48, defines one-shot big-step weak call-by-value evaluation of PCUIC on
  closed terms, with `progress`, `SN_to_WN` and `wcbv_standardization`; the lambda-box evaluation the erasure theorem
  is stated against is this relation transported and amended, not an independent invention
  (`pcuic/theories/PCUICWcbvEval.v`; [HAB] Spec 21).
- **Ours** `ParRedS.standard` (`Theory/Typing/HeadReduction.lean:466`): if `Gamma |- e : A` and `e >>* e'` then `e`
  reduces standardly to `e'` -- following Kashima (2000), with no thesis counterpart. This is standardization of the
  *ideal* reduction, under the `Params` restriction, tainted through `StRed.triangle`. There is no weak call-by-value
  evaluation relation for Lean terms anywhere in the development, and no value predicate.
- **Nature** GAP.
- **Reason** The theorem serves `reduce_sort` and `reduce_forallE` (`Theory/Typing/HeadReduction.lean:470,488`) --
  exposing the head shape of a type -- not an observational statement about running programs.
- **Consequence** For track K alone this is immaterial. For the surrounding project it is the sharpest omission: a
  Lean-side forward simulation in the shape of `erases_correct` needs a source-language evaluation relation to
  simulate, and none exists here, so any such statement must introduce its own.
- **Evidence** `pcuic/theories/PCUICWcbvEval.v`; `Theory/Typing/HeadReduction.lean:466,470,488`; blueprint
  `metatheory.tex`, `thm:parreds-standard`.

### K-D1 -- soundness only, and completeness is not merely unproved
- **Reference** MetaRocq's checker is proved sound **and complete** against the declarative specification ([JACM] Sec
  6, pp. 8:56-8:59; [HAB] Ch. 5, Specs 16-17), with completeness carried in the return type:

      Inductive typing_result_comp (A : Type) :=
      | Checked_comp (a : A)
      | TypeError_comp (t : type_error) (a : A -> False).

  at `safechecker/theories/PCUICErrors.v:401`. Every rejection carries a proof that the corresponding derivation does
  not exist -- the method that found the completeness bug fixed in Rocq 8.14 ([JACM] pp. 8:2, 8:4).
- **Ours** Soundness only. The three public entry points (`Verify/TypeChecker.lean:204,215,218`) have the shape

      nonrec theorem isDefEq.WF {c : VContext} {s : VState}
          (he1 : c.TrExprS e1 e1') (he2 : c.TrExprS e2 e2') :
          M.WF c s (isDefEq e1 e2) fun b _ => b -> c.IsDefEqU e1' e2'

  -- if the checker returns `true`, the model relates the two terms. Returning `false`, raising an error and running
  out of fuel are all unconstrained.
- **Nature** FORCED-LEAN in part, DESIGN in part.
- **Reason** Completeness against `==` is not available to be proved: [CT] `typesys.tex` `sec:undecidable` shows
  definitional equality undecidable via `acc` in an inconsistent local context, so no algorithm decides it; the same
  example shows `<=>` non-transitive and shows the algorithmic typing judgment failing subject reduction. Any
  completeness claim would have to be relative to `<=>`, which K-B4 says is not formalised. Leaving failure
  unconstrained, rather than proving a relative-completeness statement, is the design part.
- **Consequence** The guarantee is exactly "the checker accepts a term only if the model derives its typing", a
  one-directional trust reduction. A user cannot conclude from a rejection that the term is ill-typed, and nothing
  detects an incompleteness bug of the kind MetaRocq's method found. This is the deepest structural difference in the
  comparison and is not closable by more proof effort alone.
- **Evidence** `safechecker/theories/PCUICErrors.v:401`; `safechecker/theories/PCUICTypeChecker.v:1502`;
  `Verify/TypeChecker.lean:204,215,218`; blueprint `typechecker.tex`, at-a-glance Goal; `intro.tex`, Verify bullet.

### K-D2 -- verification by translation to a model, not by construction
- **Reference** MetaRocq's checker is written in Rocq, as `Equations`-defined functions whose types carry their own
  specification, against the same syntax the specification uses, then extracted to OCaml ([JACM] Sec 6; [CCC] Sec
  3.6). There is no refinement layer: the checked object and the specified object are the same terms.
- **Ours** The checker is a port of Lean's C++ kernel, operating on the real `Lean.Expr`, `Lean.Level`,
  `Lean.LocalContext` and `Lean.Kernel.Environment` -- the `README.md` states it is "derived directly from the C++
  kernel implementation, and as such likely shares some implementation bugs with it". Correctness therefore goes
  through a translation: `TrExprS : VLCtx -> Expr -> VExpr -> Prop` (`Verify/Typing/Expr.lean:142`),
  `TrConstant`/`TrDefVal`/`TrEnv` (`Verify/Environment/Basic.lean:21`), and each kernel function `f` gets a companion
  `f.WF` justifying what `f` returns when its inputs translate.
- **Nature** DESIGN.
- **Reason** Fidelity: the verified object is the algorithm that runs, at the performance of the real kernel, and
  `Replay.lean` can replay an imported environment through it. MetaRocq's method cannot apply to Lean, whose kernel is
  not written in the prover.
- **Consequence** An entire refinement layer exists with no counterpart -- 25976 lines in `Verify/` against 10455 in
  `Theory/` -- bringing its own trust boundary (K-D4, K-D5) and its own vacuity risks (K-E3). One illustration:
  `addDecl.WF`'s `inductDecl` case is `sorry`, so no environment the kernel builds inhabits the block apparatus.
- **Evidence** `README.md`; `Verify/Typing/Expr.lean:142`; `Verify/Environment/Basic.lean:21`; blueprint `intro.tex`,
  Architecture table and line counts; `contrib-trproj.tex`, Goal Caveat.

### K-D3 -- six open obligations in the checker's verification
- **Reference** MetaRocq's checker has no open per-function obligations; `PCUICTypeChecker.v` and
  `PCUICSafeConversion.v` are proved.
- **Ours** Six `sorry`s in `Verify/TypeChecker/`, four master's and two contributed:

  | declaration | source | missing | |---|---|---| | `tryEtaStructCore.WF` | `Verify/TypeChecker/IsDefEq.lean:227` |
  structure-eta obligation (K-A6) | | `isDefEqUnitLike.WF` | `Verify/TypeChecker/IsDefEq.lean:488` | unit-like
  structure obligation (K-A6) | | `reduceProjCore.WF` | `Verify/TypeChecker/Reduce.lean:145` | structure-projection
  reduction (K-A8) | | `reduceRecursor.WF` | `Verify/TypeChecker/WHNF.lean:149` | full recursor reduction (K-A10) | |
  `inferProj.WF_struct` | `Verify/TypeChecker/InferType.lean:398` | `TrProjCtor` inhabited from a kernel-accepted
  projection | | `inferProj.WF` | `Verify/TypeChecker/InferType.lean:410` | not provable as stated (K-A9) |

- **Nature** GAP.
- **Reason** Four of the six trace to K-A6 and K-A8: the model has no structure eta and no projection node.
  `reduceRecursor.WF` traces to K-A10.
- **Consequence** Every statement in the top-level triple -- `inferType.WF'`, `checkType.WF`, `isDefEq.WF` -- is
  partial as stated. The pure iota step *is* proved (`inductiveReduceRecCore`, blueprint `thm:vtc-iota-reduce-core`)
  but is not wired into `reduceRecursor.WF`; and `TrEnv.proj_defeq` -- the projection reduction the
  `TrProj`/`TrProjCtor` metatheory supports -- has no consumer, `reduceProjCore.WF` being unattempted.
- **Evidence** the six locations above; blueprint `status.tex`, sorry table, issues K7, K9; `typechecker.tex`,
  function/status table.

### K-D4 -- pointer equality as an axiom
- **Reference** MetaRocq's checker is a pure Rocq function with no physical-identity test; its fast paths are
  structural.
- **Ours** `PtrEq.lean:15,17`:

      opaque ptrEqExpr (a b : Expr) : Bool := unsafe ptrAddrUnsafe a == ptrAddrUnsafe b
      axiom ptrEqExpr_eq : ptrEqExpr a b -> a = b

  and likewise for `ptrEqConstantInfo` at lines 20/22, reaching 65 and 63 declarations. The `EquivManager` union-find cache
  (`EquivManager.lean`) is verified separately (blueprint `levels.tex`, `thm:eqvmgr-isdefeq-wf`).
- **Nature** FORCED-LEAN4LEAN.
- **Reason** The ported algorithm branches on pointer identity for performance; the axiom states honestly what that
  branch assumes. The file's comment says the function is type-restricted "to avoid thorny questions about equality of
  closures".
- **Consequence** Mostly benign, with one exception the status chapter flags: at `TypeChecker.lean:739`,
  `ptrEqConstantInfo_eq` gates a *different algorithm*, not merely a shortcut, so the assumption is load-bearing for
  the result there and not only for its speed.
- **Evidence** `PtrEq.lean:15,17,20,22`; `TypeChecker.lean:739`; blueprint `status.tex`, Trust boundary bullet "Pointer
  equality", issue K11 (corrected: the code block's lines are 15/17, not 16/20).

### K-D5 -- bridge axioms over the host's own data structures
- **Reference** MetaRocq defines its environments, maps and arrays in Rocq, so nothing is assumed about them; the
  corresponding trust is in extracting those definitions to OCaml, which [JACM] Sec 6 treats as part of the pipeline
  rather than as an axiom.
- **Ours** 32 axioms in `Verify/Axioms.lean:1` relate the `VEnv`/`VExpr` model to Lean's own unverified `Expr`,
  `Level`, `PersistentHashMap`, `PersistentArray` and `Syntax`. The most relied on are `PersistentHashMap.WF.find?_eq`
  and `.WF.toList'_insert`, each reaching 229 declarations, `PersistentArray.toList'_push` at 154,
  `Level.instLawfulBEqLevel` at 152. Two `Std.TreeMap` axioms (`Verify/Axioms.lean:10,14`), each citing an open issue,
  additionally gate the level-comparison soundness of K-D8. Seven `bv_decide`-generated LRAT certificate axioms appear
  at `Verify/Expr.lean:1` and `Verify/Level.lean:1`.
- **Nature** FORCED-LEAN4LEAN.
- **Reason** The kernel runs on Lean's own container implementations; verifying them is a separate project, and the
  axioms name exactly the lemmas the refinement needs.
- **Consequence** The trust boundary is not a short list of mathematical assumptions, as on the Rocq side, but a
  mixture of mathematical gaps and library lemmas. `TrEnv.proj_defeq`'s pinned axiom profile shows it: `[propext,
  Classical.choice, Quot.sound, sorryAx, Lean.PersistentHashMap.WF.find?_eq, .WF.toList'_insert, .findAux_isSome]`.
- **Evidence** `Verify/Axioms.lean:1,10,14`; `Verify/Expr.lean:1`; `Verify/Level.lean:1`; blueprint `status.tex`,
  Trust boundary.

### K-D6 -- no guard condition to axiomatise
- **Reference** The guard condition is MetaRocq's second named axiom and its largest single hole:

      Class GuardChecker :=
      { guard : FixCoFix -> global_env_ext -> context -> mfixpoint term -> Prop }.
      Axiom guard_checking : GuardChecker.

  at `pcuic/theories/PCUICTyping.v:49,54`, with `Axiom guard_checking_correct` at
  `pcuic/theories/PCUICGuardCondition.v:59`. `type_Fix` and `type_CoFix` (`PCUICTyping.v:272,281`) take
  `fix_guard`/`cofix_guard` as premises, and `cumul_fix` (`PCUICCumulativitySpec.v:182`) is guarded by
  `is_constructor`. [HAB] Ch. 8 lists verifying the guard checker as an open problem.
- **Ours** Nothing. Lean's elaborator compiles structural and well-founded recursion into recursor applications before
  the kernel sees a declaration, so the kernel has no fixpoint form and no guard predicate. `VExpr` has no `fix`
  constructor and `IsDefEq` has no fix rule.
- **Nature** FORCED-LEAN.
- **Reason** Lean's design puts termination checking outside the kernel.
- **Consequence** The Lean side's boundary is *smaller* than the Rocq side's here: one of the two Rocq axioms does not
  arise, and with K-C5 removing the other, neither of MetaRocq's named trust axioms has a counterpart. What replaces
  them is a larger and less tidy set (K-E1). The two boundaries are comparable in kind, not in size.
- **Evidence** `PCUICTyping.v:49,54,272,281`; `PCUICGuardCondition.v:59`; `PCUICCumulativitySpec.v:182`;
  `Theory/VExpr.lean:7`; `Theory/Typing/Basic.lean:18`.

### K-D7 -- fuel instead of well-founded recursion on normalization
- **Reference** MetaRocq's weak-head reduction is fuel-free: `reduce_stack` is defined by well-founded recursion on a
  stack-and-position order whose accessibility comes from the normalization assumption ([CCC] Sec 3.1-3.2, Fig. 8, pp.
  8:14-8:17).
- **Ours** Several independent fuel counters (`FuelConfig.lean`); `withFuel` threads a fuel-indexed method table and
  `withFuel.WF` is the corresponding statement.
- **Nature** DESIGN.
- **Reason** `divergences.md:20`: the native kernel bounds mutually recursive checking through `maxRecDepth`, and
  lean4lean's Lean definitions need explicit termination witnesses, so it exposes independent counters; replay
  comparison then uses each implementation's default bound.
- **Consequence** The SN axiom is avoided (K-C5), and the two implementations can disagree on deeply recursive inputs
  purely by bound. Because fuel exhaustion is indistinguishable from rejection in the `.WF` statements, this
  reinforces K-D1.
- **Evidence** `FuelConfig.lean`; `divergences.md:20`; blueprint `typechecker.tex`, `thm:vtc-withfuel`.

### K-D8 -- a complete level decision procedure, and a hardness result
- **Reference** MetaRocq decides universe constraints by weighted-graph acyclicity, with `lsp` and the equivalence
  between acyclicity and the existence of a correct labelling ([CCC] Sec 3.3, Fig. 9) -- a decision procedure for
  constraint consistency, not for equivalence of level expressions. [CT] `axioms.tex` gives the rule system of K-A2
  and states no algorithm and no complexity.
- **Ours** `Level.lean` implements Geran's canonical form -- a `Std.TreeMap` from `imax`-chain condition sets to nodes
  bundling a constant and variable sublevels -- and `Verify/Level.lean` proves it sound and canonical:
  `normalize_eval` (`:1214`), `le_eval` (`:1237`, Geran's Theoreme 39), `separation` (`:2674`, its converse),
  `le_complete` (`:2886`) and `normalize_complete` (`:3721`), which says `normalize u == normalize v` iff the
  translated levels are equivalent `VLevel`s. Independently, `Theory/LevelSat.lean:331` (`equiv_iff_unsat`) proves the
  decision problem coNP-hard by reduction from CNF unsatisfiability.
- **Nature** DESIGN.
- **Reason** K-A2's semantic order is what must be decided, and the canonical form decides it completely rather than
  approximating it.
- **Consequence** Three. lean4lean decides level equality and `>=` for *more* pairs than either the standard library
  or the C++ kernel, so it accepts declarations the kernel rejects for level incompleteness and never the converse
  (`divergences.md:13`) -- a deliberate, stated, one-directional divergence from the kernel it models. Because
  `instantiateLevelParams` uses the standard library's smart constructors rather than the kernel's, unfolding a
  universe-polymorphic constant can produce a term meaning the same as the kernel's but not syntactically equal to it,
  not sharing its `Expr.hash` (`divergences.md:12`). And the coNP-hardness result bounds what any complete algorithm
  can cost, which is why the flat fast path (`normalize'`, transparent by `Verify/Level.lean:3793`) exists. Only
  `isEquivList_wf` (`Verify/Level.lean:3837`) reaches the type checker.
- **Evidence** `Verify/Level.lean:1214,1237,2674,2886,3721,3793,3837`; `Theory/LevelSat.lean:331`;
  `divergences.md:12,13`; blueprint `levels.tex`, Caveats.

### K-E1 -- the shape of the trust boundary
- **Reference** MetaRocq's boundary is short and named: the guard condition (`Axiom guard_checking`, `Axiom
  guard_checking_correct`) and normalization (`NormalizationIn`/`Normalization`), plus the unverified Template quoting
  layer (K-E2) and the extraction of the checker to OCaml. [JACM] frames the result as moving from a Trusted Code Base
  to a Trusted Theory Base, and those two axioms are that theory base.
- **Ours** No single labelled trust axiom. The boundary is the union of: 16 live `sorry` occurrences outside
  `Experimental/` across 13 declarations (11 master, 4 trproj, 1 iota); 110 declared `axiom` constants and 12 `opaque`
  constants, of which 32 are the bridge axioms of K-D5, 7 are `bv_decide` LRAT certificates and 2 are the
  pointer-equality axioms of K-D4; and the three standard Lean axioms `propext`, `Classical.choice`, `Quot.sound`. The
  project states that the boundary must be quoted per top-level theorem, and does so:
  `inferType.WF'`/`checkType.WF`/`isDefEq.WF` depend on `sorryAx` through the four structure/recursor obligations of
  K-D3 and through `patsStrong` wherever `OrderedStrong` is discharged from `VEnv.WF`.
- **Nature** GAP.
- **Reason** The refinement method of K-D2 spreads the boundary across two layers -- theory gaps and library
  assumptions -- where a correct-by-construction checker has only the first.
- **Consequence** A reader cannot state what lean4lean assumes in one line. The census gives the scale: 629 of 7833
  user-level declarations (8.0%) are `sorryAx`-tainted, concentrated in `Theory` (5.7%) and `Verify` (8.6%), with
  `kernel` and `Tests` at zero.
- **Evidence** `PCUICTyping.v:54`; `PCUICGuardCondition.v:59`; `PCUICSN.v:44,49`; blueprint `status.tex`, Sec Census,
  Sec Live sorries, Sec Trust boundary.

### K-E2 -- no reification layer
- **Reference** MetaRocq's Template layer quotes Rocq's `constr` into `Ast.term` and back, in OCaml, unverified ([MR]
  Sect. 3, pp. 973-977; [MR] Sect. 2.7, p. 973 also records that the early checker had no soundness or completeness
  proof). Everything MetaRocq proves is about the quoted syntax, so the quoting is part of the trust boundary.
- **Ours** No quoting step. `Replay.lean` reads declarations out of a real imported `Lean.Kernel.Environment` and
  replays them through the executable kernel, and the verification relates that same `Lean.Expr` to the model through
  `TrExprS` (`Verify/Typing/Expr.lean:142`) -- a relation in Lean, not an external translation.
- **Nature** DESIGN.
- **Reason** Lean's syntax is already a Lean datatype, so no reification is needed.
- **Consequence** One item of MetaRocq's boundary closes outright: the object checked is the object the user wrote,
  with no unverified transport in between. The trade is K-D5: reading the real environment means depending on Lean's
  own container implementations, which MetaRocq's quoted view avoids.
- **Evidence** `Replay.lean`; `Verify/Typing/Expr.lean:142`; blueprint `intro.tex`, Executable-kernel bullet;
  references README Sec 3 item 1.

### K-E3 -- three vacuous layers
- **Reference** MetaRocq reports no layer that is proved but inhabited by nothing; its theorems are stated over `wf
  Sigma`, which `check_wf_env` (`safechecker/theories/PCUICSafeChecker.v:2398`) establishes for a real environment.
- **Ours** Three places where a proved result is true of nothing reachable. First, `addDecl.WF`'s `inductDecl` case is
  `sorry` at `Verify/Environment.lean:208`, so no proof builds an `AddInduct` witness from `Environment.addInductive`
  and the whole inductive-block refinement apparatus of both branches -- about 1000 lines across
  `Verify/Environment/{Basic,Lemmas}.lean` and `Theory/Typing/InductiveLemmas.lean` -- is correct but end-to-end
  vacuous. Second, `Params` has one instance requiring `DefEqsAsPats` (K-A11, K-B6), so the Church-Rosser and
  standardization development applies to no environment declaring a `def` or the quotient rule. Third,
  `TrEnv.proj_defeq`, the strongest projection result on the trproj branch, has no consumer anywhere except a `#print
  axioms` check, because `reduceProjCore.WF` is unattempted.
- **Nature** GAP.
- **Reason** Each is the same failure in a different place: the specification side is finished and the refinement side
  that would inhabit it is not.
- **Consequence** Counting proved declarations overstates what is established. A vacuity pass -- checking that each
  major specification is inhabited by something the kernel actually produces -- is the only honest reading, and the
  project's own issue registry records all three.
- **Evidence** `Verify/Environment.lean:208`; `Verify/Environment/Lemmas.lean:1021`;
  `Theory/Typing/InductiveParams.lean:393`; blueprint `status.tex`, issues K2, K7, K10, and the Trust boundary
  paragraph on the `add-induct` family.

### K-T1 to K-T13 -- thesis versus code, collected
Where the code departs from or goes beyond [CT]; the blueprint's thesis map (`intro.tex`, Sec "The thesis map") is
the source for all of them. Each row's full treatment is the cross-referenced block.

| id | kind | departure | see |
|---|---|---|---|
| K-T1 | DESIGN | levels defined semantically, not by [CT] `axioms.tex`'s nine-rule system | K-A2 |
| K-T2 | DESIGN | `Theory/LevelSat.lean:331` proves level equivalence coNP-hard, hence coNP-complete; the thesis states no complexity result | K-A2, K-D8 |
| K-T3 | DESIGN | no zeta rule: `let` is substituted away, where [CT] Sec "let binders" keeps zeta with a conservativity argument | K-A7 |
| K-T4 | GAP | `<=>` of [CT] Sec 2.3 unformalised, so its undecidability, non-transitivity and subject-reduction-failure results have no formal counterpart | K-B4, K-D1 |
| K-T5 | DESIGN | unique typing by `HasTypeStratified` (`Theory/Typing/Strong.lean:944`), not the thesis's `\|-_n` stratification | K-C3 |
| K-T6 | GAP | [CT] `unique.tex`'s rec-normal forms and eta-expansion argument -- the eta-versus-iota fight on partially applied subsingleton eliminators -- have no counterpart | -- |
| K-T7 | DESIGN | [CT] `Wtypes.tex`'s eight-primitive system not formalised; only its Sigma-projection typing shape is reused, without its eta rule | K-A8 |
| K-T8 | GAP | [CT] Sec 6 soundness has no counterpart: correctness relative to the model, not consistency of the type theory | K-C6 |
| K-T9 | DESIGN | one uniform iota rule, no subsingleton special case: diverges from [CT] `normalization.tex`'s `K+`/iota split, matches its weaker relation | K-A10 |
| K-T10 | OPEN | [CT] `compilation.tex` has no counterpart; native reduction refused, per `divergences.md:5` | K-A14 |
| K-T11 | DESIGN | `VInductDecl.WF` pins recursor types and iota rules as 20 syntactic fields, where the thesis generates them from the block's specification | K-A12 |
| K-T12 | DESIGN | `ParRedS.standard` after Kashima (2000); the thesis has no standardization theorem | K-C7 |
| K-T13 | GAP | [CT] calls regularity of reductions an easy induction; here it is `VEnv.WF.patsStrong` (`Theory/Typing/EnvLemmas.lean:334`), the widest-reaching gap | K-C2 |

## 4. What is aligned
The divergence list is complete relative to the references' structure because the remaining notions line up name for
name. Each row is a MetaRocq or [CT] element and its lean4lean counterpart, with no divergence of kind. Rocq paths
omit the `pcuic/theories/` prefix where unambiguous.

| notion | reference | ours | [CT] |
|---|---|---|---|
| variable lookup | `type_Rel`, `PCUICTyping.v:199` | `Lookup`, `IsDefEq.bvar`, `Theory/Typing/Basic.lean:6,19` | `axioms.tex` variable rule |
| sorts | `type_Sort`, `PCUICTyping.v:204` | `IsDefEq.sortDF`, `Theory/Typing/Basic.lean:22` | -- |
| product formation, impredicative `Prop` | `type_Prod` with `Sort.sort_of_product`, `PCUICTyping.v:208`, `Universes.v:1585` | `IsDefEq.forallEDF` with `.imax u v`, `Theory/Typing/Basic.lean:40` | Pi-formation, `imax` clause |
| abstraction | `type_Lambda`, `PCUICTyping.v:214` | `IsDefEq.lamDF`, `Theory/Typing/Basic.lean:36` | -- |
| application | `type_App`, `PCUICTyping.v:224` | `IsDefEq.appDF`, `Theory/Typing/Basic.lean:32` | -- |
| universe-polymorphic constants | `type_Const`, `PCUICTyping.v:232` | `IsDefEq.constDF`, `Theory/Typing/Basic.lean:25` | -- |
| conversion | `type_Cumul`, `PCUICTyping.v:296` | `IsDefEq.defeqDF`, `Theory/Typing/Basic.lean:44` (modulo K-A3) | -- |
| context well-formedness | `wf_local` | `OnCtx Gamma (env.IsType U)`, `Theory/Typing/Lemmas.lean:152` | `\|- Gamma ok` |
| beta | `cumul_beta`, `PCUICCumulativitySpec.v:159` | `IsDefEq.beta`, `Theory/Typing/Basic.lean:46` | -- |
| delta | `cumul_delta`, `PCUICCumulativitySpec.v:192` | `IsDefEq.extra` over `env.defeqs`, `Theory/Typing/Basic.lean:55` | Sec "Definitions" |
| iota | `cumul_iota`, `PCUICCumulativitySpec.v:175` | `IsDefEq.pat` over `env.pats`, `Theory/Typing/Basic.lean:60` (modulo K-A10) | `sec:iota` |
| weakening | `weakening_typing`, `PCUICWeakening.v` | `VEnv.IsDefEq.weakN`, `Theory/Typing/Lemmas.lean:546` | `thm:weak` |
| substitution | `substitution`, `PCUICSubstitution.v` | `VEnv.IsDefEq.instN`, `Theory/Typing/Lemmas.lean:691` | `thm:subst` item `subst_ty` |
| validity, regularity of types | `validity`, `PCUICValidity.v` | `VEnv.IsDefEq.isType`, `Theory/Typing/Lemmas.lean:912` | `thm:reg` item 4 |
| free variables in the context | `PCUICClosed` | `VEnv.IsDefEq.closedN`, `Theory/Typing/Lemmas.lean:329` | `thm:reg` item 2 |
| context conversion | `PCUICContextConversion` | `IsDefEqCtx` (`Theory/Typing/Lemmas.lean:302`), `IsDefEq.defeqDFC` (`:783`, corrected: was cited at 302, the relation's own definition) | -- |
| environment weakening | `weakening_env`, `PCUICWeakeningEnv.v` | `IsDefEq.mono` along `VEnv.LE`, `Theory/Typing/Lemmas.lean:397` | -- |
| universe instantiation | `typing_subst_instance` | `IsDefEq.instL`, `Theory/Typing/Lemmas.lean:646` | universe-polymorphic constants |
| simultaneous substitution | `subslet`, [CCC] Sec 2.3.1 | `Ctx.SubstEq`, `IsDefEq.substDF`, `Theory/Typing/Lemmas.lean:973`, `Strong.lean:1282` (corrected: was 1273, the neighboring `IsDefEqStrong.subst`) | -- |
| parallel reduction | `pred1`, [CCC] Fig. 6, p. 8:11 | `ParRed`, `Theory/Typing/ChurchRosser.lean:473` | `>>_kappa` |
| complete parallel reduction | `rho`, [CCC] Fig. 7 | `CParRed`, `Theory/Typing/ChurchRosser.lean:488` | `>>>_kappa` |
| triangle lemma | [CCC] Thm 2.2, p. 8:13 | `ParRed.triangle`, `Theory/Typing/ChurchRosser.lean:766` | `thm:tri` |
| confluence | `PCUICConfluence.v` | `ParRedS.church_rosser`, `Theory/Typing/ChurchRosser.lean:1302` (status differs, K-C1) | `thm:church_rosser` |
| defeq factored through reduction plus irrelevance | -- | `IsDefEq.church_rosser`, `Theory/Typing/ChurchRosser.lean:1347` | `thm:ckappa` |
| bidirectional inference | `Bidirectional/`, `t \|> A` | `VEnv.InferType`, `Theory/Typing/HeadReduction.lean:508` (unwired, K-B5) | -- |
| head-reduce to a sort or a product | `reduce_to_sort`/`reduce_to_prod`, `safechecker/theories/PCUICSafeReduce.v` | `IsDefEq.reduce_sort`, `.reduce_forallE`, `Theory/Typing/HeadReduction.lean:470,488` | -- |
| level valuation semantics | `Universes.val`/`satisfies`, `common/theories/Universes.v` | `VLevel.eval`/`VLevel.LE`, `Theory/VLevel.lean:34,41` | level semantics paragraph |
| declaration admission | `check_wf_decl`/`add_global_decl` | `VDecl.WF`, `VEnv.WF'`, `Theory/Typing/Env.lean:18,48` | Sec 2.5, 2.6, 2.7.1 |
| mutual blocks | MetaRocq's mutual definitions | `VEnv.addConsts` then `addDefEqs`, `Theory/Typing/Env.lean:18` | -- |
| monotonicity of well-formedness | `weakening_env_decl` | `VConstant.WF.mono`, `VDefEq.WF.mono`, `PatWF.mono`, `Theory/Typing/Lemmas.lean:430,434,468` (corrected: was 419,464 -- 419 is blank and 464 is the neighboring `PatTyped.mono`) | -- |
