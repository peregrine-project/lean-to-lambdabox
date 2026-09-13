# W3R — the repair wave: the premises `erases_correct` is allowed to have

W3 closed T5 (`erases_correct`, `ErasesCorrect/Close.lean`) under one extra named premise,
`StepPremises`, with six fields, and left `LowerEnv.specBlocks` refuted, `Erases.proj` false at
a propositional structure, and `SourceTableAdequate` uninhabited on a matcher-bearing
declaration. This wave repairs the definitions those facts are about, so that

```
erases_correct : env.WF → TrExprS → SEval → Erases → Lower → ErasesEnv → LowerEnv → UpstreamAsks → …
```

is MetaRocq's five premises (`wf`, `welltyped`, evaluation, `erases`, `erases_deps`), plus
`LowerEnv` for the pass layer MetaRocq does not have, plus `UpstreamAsks` for the lean4lean
facts the pin does not yet prove — and nothing else. Every repair is in the file that owns the
relation stating the fact in the wrong direction; none is a proof patch at a use site, and none
is a pin bump.

## 0. Finding → decision

| # | Finding (W3 unit, obstruction) | Decision |
|---|---|---|
| 1 | `ErasesEnv.decls` runs entry ⇒ justified; the `ctorVal`, β, ι and proj arms need justified ⇒ entry (U3.1-1, U3.2-1, U3.2b-4) | `ErasesEnv` is restated in `erases_deps`' direction: `decls` and `ErasesDecl` are **deleted**, and the relation gains `tabled`, `axioms`, `blocks`, `elims` beside `defns` — seven clauses. `axioms` carries `ErasesDecl.ax`'s content; `elimsOnly` is **not** a clause, it is a theorem of `defns` and `axioms` (§1, §16 S1/S2) |
| 2 | `Erases.proj` fires at a propositional structure, where no target rule reduces `.proj p □`; the arm is refutable at `And` (U3.2b-1) | `Erases.proj` gains `hinf : InformativeInd env S`, with `InformativeInd` **restated semantically** — the result level never evaluates to zero, not a syntactic `.succ`, which is refuted at `Prod` and at six more corpus projection heads (§2, §16 F1); `IndDeclOf` comes from `ErasesEnv.blocks`, not from the rule |
| 3 | `SEval.iota`/`SEval.proj` leave `np` free and `SEval.proj` does not classify the value's head; the defeq-shaped repair is refutable at `(x, x) : Nat × Nat` (U3.2-4, U3.2b-2, U3.2b-3) | `SEval.iota` gains `hnp : IndArity env I np nfs` and `hinf`; `SEval.proj` gains `hct : CtorOf env ctor S cidx` and `hnp : IndArity env S np [nf]`. `IndArity` is `IndInfo` minus the λ□ identifier, so no target datum enters the source semantics, and the block it names is the rule's own by ask 2's block uniqueness (§3, §16 F6) |
| 4 | `CasesOnShape` constrains a name and a block, not the eliminator's type, so the ι head step's discriminant typing is unavailable (U3.2-2) | `CasesOnShape` gains `major`, the declared type's major-premise position; `ElimTyping.major` becomes a theorem off `major` + `UpstreamAsks.mkAppsInv` (§4) |
| 5 | `LowerEnv.specBlocks : BlockBodiesLambda Γspec` is refuted by one declared non-λ body, and five of T5's eight arms spend it (W2b-F1; U3.1-4, U3.2-5, U3.2b-5, U3.3-2) | `BlockBodiesLambda` and `specBlocks` are **deleted**; `LowerBlock` gains `hfl`, the λ-headedness of the **emitted** definitions — `LBWfPeregrine.fixLambda`'s clause at this block, one home for one assertion — and the source-side `lambda_of_fixLambda` stays the theorem it already is. Measured: 51 of 51 emitted `FixDef` bodies are λ-headed (§5, §16 F5) |
| 6 | `ReifiedDecl.Prepared` demands binder-name-stable preparation, which `inlineMatchers` denies; `htbl` is uninhabited on a `match` and on `Nat.add`, and on `benchArith`'s closure (G3-3) | `Prepared` pins the compiler body **up to α**, with `Expr.AlphaEq` an inductive relation of our own, blind to binder names and binder info and to **nothing else** — no `mdata` arms, which would falsify the deferred `SEval.alpha` (§16 F2). The decision procedure stays in `lake exe reify --check`, which now also runs a Boolean written arm-for-arm against the relation; the rungs' `by rfl` discharges are untouched (§6) |
| 7 | T7 takes `FOFields`, which no local fact supplies (U3.5-3) | Derived: `FOFields` is a theorem off `UpstreamAsks`' two new fields (asks **9** and **10**) and ask 2's new block-uniqueness conjunct, plus `CtorOf.constant_ctorResult`. The `TrEnv'`-shaped third ask is **withdrawn** (§7, §13, §16 F8) |
| 8 | `Simulates` cannot run its own induction: the β/ζ arms need `ErasesEnv` at the contractum (U3.1-2) | Kept as landed — the accumulator is MetaRocq's own device; `ErasesEnv.substPair`/`.mkApps`/`.box`/`.subterm` are the closure kit, and every clause of the restated `ErasesEnv` is antitone in the term, so the kit re-proves clause by clause (§8) |
| 9 | The β arm's function value can lower to a `.fix` node (U3.1-3) | Kept as landed: `Lower.appReady`, by induction on the `Lower` derivation, no premise; `LowerBlock.hfl` makes its `fixBody` sub-case a projection (§9) |
| 10 | `hygiene --schedule` reports two inversions, both false positives of the plan's own §4 rows (U3.1-5, G3-2) | `02-PLAN.md` §4's W1 and W2 rows are rewritten so that a file that stands is not spelled as a deleted `.lean` (§10) |
| 11 | `doc/coverage.md`'s five-program verdicts are stale; Arith is inside the fragment (G3-4) | The stale rows are replaced by the re-measurement; G7's remaining asks are named (§11) |
| 12 | A rung on a tracked program cannot name its subject: `VerifyBench` roots run `#erase` on elaboration (G3-3, ladder rows G7/G8) | `VerifyBench/Src/` holds the programs minus the `#erase` line; the roots import it and keep the run; a byte-freeze check pins the copies (§12) |

Two facts about the shape of the wave. Four of the six `StepPremises` fields die by a
definition changing in `Erases.lean`, `SourceEval.lean` and `ErasesEnv.lean`; the other two
(`indSpine`, `elimTyping`) die into `UpstreamAsks`, which is the tracked lean4lean binder T5
already carries. So the wave removes a premise bundle and adds no new binder.

## 1. `ErasesEnv`, in `erases_deps`' direction

**Finding.** `ErasesEnv.decls : ∀ kn d, envLookup Γspec kn = some d → ErasesDecl env bo kn d`
answers "what justifies this entry", and every arm asks the converse: "the source has this
declaration — what does the environment hold for it?". Nothing recovers the converse from it: an
arm holding `IndInfo env I iid np nfs` has no entry to feed `decls`, and `deps` gives it only
`isSome`. That is the whole defect, and it is what forced `ErasesEnvFwd`, `SpecElims` and
`ProjSpec.informative`.

The first round of this section argued the reading is also *ambiguous* — that `ErasesDecl.ax`
justifies a block key as well as `.ind` does, and `.defn` any `ElimBody`-shaped entry. Checked,
that argument is wrong in both halves and is withdrawn: `decls` is applied to a key **and its
entry**, and the four arms conclude at four distinct entry shapes (`⟨some b₀⟩`, `⟨none⟩`,
`.inductiveDecl mib`, `⟨some body⟩`), so `.ax` and `.ind` cannot compete at one entry; and
`erases_ne_elimBody` (`ErasesCorrect/Delta.lean:78`) proves no erasure image is an `ElimBody`, so
`.defn` cannot justify an eliminator's entry either. The direction alone carries the decision —
and `erases_ne_elimBody`, the lemma that refutes the second half, is the same lemma that makes
`elimsOnly` unnecessary below.

**Decision.** `ErasesEnv` is stated the way `erases_deps` is stated. MetaCoq's predicate is
inductive **on the erased term** and each clause reads *source declares X → target declares X'
→ X' is the erasure of X*: `erases_deps_tConst` carries `declared_constant Σ kn cb`,
`declared_constant Σ' kn cb'` and `erases_constant_body`; `erases_deps_tConstruct` and
`_tCase`/`_tProj` carry `declared_minductive Σ` / `declared_inductive Σ`, the same in `Σ'`, and
`erases_mutual_inductive_body` (`doc/rework/refs/metacoq-erasure.md:355`). Not one clause
quantifies over the target environment's entries. Ours keeps the reachability form — the
closure `ReachableFrom Γspec t` is the same bottom-up dependency set, and it is what
`ErasesEnv.subterm`/`.ofReach` thread — and puts the per-kind readings in it:

* **definitions** — `defns`, unchanged, plus `tabled`, which is `declared_constant Σ kn cb`: a
  constant the compiler table defines is declared as a plain constant in `env`. `tabled` carries
  no reachability trigger because the reading it refutes is at a constant the erasure emits **no**
  key for (a constructor erases to a `.construct` node), so there is no occurrence to trigger on.
* **axioms** — `axioms`, `ErasesDecl.ax`'s content in the forward direction: a reached key whose
  constant has no compiler body, and is not an eliminator, is declared body-less. Without it
  nothing stops the environment from holding `⟨some junk⟩` where the source cannot step, which
  the target would δ-unfold; `Eq.rec` is such a key on a tracked program (§16 S2).
* **inductive blocks** — `blocks`: at a reached block kername the entry is that block's
  `.inductiveDecl`, with the arity and propositionality data the ι, proj and `ctorVal` arms read
  (`IndBodyOf`), together with `IndDeclOf env I`, which is `declared_inductive Σ`, the source
  half MetaCoq's `tCase`/`tProj`/`tConstruct` clauses carry and the half
  `not_erasable_of_informative` consumes.
* **eliminators** — `elims`: at a reached `casesOn` constant **of a relevant inductive** the
  entry is that eliminator's, i.e. `ElimDecl Γspec (toKername c) iid np dp nfs` with the
  source-side agreement (`IndInfo env I iid np nfs`, `nfs.length = nm`). Relevance is a
  *hypothesis*, not a conclusion: the registry declares no eliminator of a non-informative
  inductive (`IndCovered.elims`, `ColdStartShape.lean:91`), so the clause could not be
  established with it in the conclusion (§16 F1). The ι arm supplies it from `SEval.iota`'s own
  `hinf` (§3). `RuntimeKey` is immediate from `ElimDecl`, which is `SpecElims.key`;
  `SpecElims.decl` is `elims` plus `ElimDecl.uniq`.
* **constructors** — no clause. A constructor constant has no entry (`ErasesDecl.ctor` was
  deleted at U2.8 and `Erases.ctor` emits the node); what the `ctorVal` arm reads is the
  **block**'s arity, and `constRefs (.construct iid k args)` already contains
  `iid.mutualBlockName`, so `blocks` at the reached block key is the whole constructor reading.
  `ErasesEnv.ctorArity` is `ErasesEnvFwd.ctorArity` re-proved off it.
* **the `toKername` tax** — **no clause.** W3R proposed `elimsOnly`; it is false at a
  constructible Γ, because `RuntimeKey` tests the entry's body shape and never the key's name
  (§16 S1). Its content is a *theorem* of `defns` and `axioms`: a reached key carrying an
  eliminator's declaration belongs to no tabled constant (no erasure image is an `ElimBody`,
  `erases_ne_elimBody`) and to no body-less non-eliminator (whose entry is `⟨none⟩`), so the
  constant behind it is a `casesOn` name. Proved, kernel-checked, in 25 lines:
  `refute3/s1_answer.lean`'s `runtimeKey_isCasesOn`, `[propext, Classical.choice, Quot.sound]`.

`ErasesEnv.decls` has **no consumer**: measured, its only occurrences are the re-packings
`.mk h.keys h.decls …` in `Steps.lean:354,387,402,416` and `SpecEnv.lean:73`. It is deleted, and
with it `ErasesDecl` — its four arms' content is exactly what the five forward clauses
(`defns`, `axioms`, `blocks`, `elims`, and `tabled` beside them) say, in the direction the arms
read them, and the ambiguity of "which arm justifies this entry" was the cause of four of the six
`StepPremises` fields. `keys` stays: it is `wf Σ'`'s `fresh_global` half, and it is what stops a
shadowing entry from retargeting `Lower`. `ErasesDecl` is also read by **inversion** in
`RegInvShape'.defns` (`SpecEnv.lean:151-175`), the only existing derivation of `defns`, which is
therefore rewritten rather than re-packed; ~14 sites across `SpecEnv.lean` and
`ColdStartShape.lean` mention it (§16 S3d), which is what U3R.4's budget is scoped on.

**Signature.**

```lean
inductive ErasesEnv (env : VEnv) (bo : Name → Option Expr) :
    GlobalDeclarations → LBTerm → Prop
  | mk {Γspec : GlobalDeclarations} {t : LBTerm}
      (keys : (Γspec.map Prod.fst).Nodup)
      (deps : ∀ kn, ReachableFrom Γspec t kn → (LBTerm.envLookup Γspec kn).isSome)
      (tabled : ∀ c b, bo c = some b → ConstOrigin env c)
      (defns : ∀ c b, bo c = some b → ReachableFrom Γspec t (toKername c) →
        ∃ b₀, LBTerm.envLookup Γspec (toKername c) = some (.constantDecl ⟨some b₀⟩) ∧
          ∀ Us' ups us, Erases env Us' [] (b.instantiateLevelParams ups us) b₀)
      (axioms : ∀ c, bo c = none → ConstOrigin env c → isCasesOnName c = false →
        ReachableFrom Γspec t (toKername c) →
        LBTerm.envLookup Γspec (toKername c) = some (.constantDecl ⟨none⟩))
      (blocks : ∀ {I : Name} {iid : InductiveId} {np : Nat} {nfs : List Nat},
        IndInfo env I iid np nfs → ReachableFrom Γspec t iid.mutualBlockName →
        IndDeclOf env I ∧ ∃ mib,
          LBTerm.envLookup Γspec iid.mutualBlockName = some (.inductiveDecl mib) ∧
          IndBodyOf iid np nfs mib)
      (elims : ∀ {c I : Name} {dp nm : Nat},
        CasesOnShape env c I dp nm → InformativeInd env I → ConstOrigin env c →
        ReachableFrom Γspec t (toKername c) →
        ∃ iid np nfs, ElimDecl Γspec (toKername c) iid np dp nfs ∧
          IndInfo env I iid np nfs ∧ nfs.length = nm) :
      ErasesEnv env bo Γspec t

/-- **`elimsOnly`, as a theorem.** `refute3/s1_answer.lean`, no `sorryAx`. -/
theorem ErasesEnv.runtimeKey_isCasesOn (h : ErasesEnv env bo Γspec t)
    (hco : ConstOrigin env c) (hr : ReachableFrom Γspec t (toKername c))
    (hrk : RuntimeKey Γspec (toKername c)) : isCasesOnName c = true ∧ bo c = none
```

**What the β arm's exclusion becomes.** `ErasesEnvFwd.noElimSpine` was discharged by
`elimsOnly` handing `SEval.no_elimSpine_value` a `CasesOnShape` for the constant behind the key.
Without the clause the route is shorter and the source rule's premises do the work.
`runtimeKey_isCasesOn`'s second conjunct is `bo c = none` — the tabled case is refuted by
`erases_ne_elimBody`, so it falls out of the same case analysis. So at an under-applied eliminator spine: `deltaC` is blocked by
`bo c = none` (not by an eliminator guard), `ctorVal`/`indVal` by `ConstOrigin` and ask 2, `beta`
by the induction on the spine length, and `iota` by its **own** premises — the arm supplies
`hsh : CasesOnShape env c I' dp' nm'` and `hinf : InformativeInd env I'` (§3), `elims` at the
reached key turns them into an `ElimDecl`, and `ElimDecl.uniq` equates its `dp'`/`nfs'` with the
target entry's, contradicting the under-application bound. `SEval.no_elimSpine_value`
(`Steps.lean:430`) therefore trades its `hsh` premise for `hnone : bo c = none`; U3R.2 restates
it and U3R.7 consumes it.

Every clause is antitone in `t` (a subterm reaches no more kernames), so `ErasesEnv.subterm`,
`.ofReach`, `.box`, `.mkApps` and `.substPair` re-prove with `ReachableFrom.subterm` threaded
through four reachability-triggered clauses instead of one (`tabled` has no trigger).

**Discharge.** `IndCovered` (`ColdStartShape.lean:84`) is the registration step's own
granularity and already has the right three fields; its `block` and `elims` clauses are
strengthened from `(envLookup …).isSome` to the forward readings above — the registration step
inserts `.inductiveDecl mib` built from the source block and the eliminator's `ElimBody`, so it
establishes them as it stands, and `elims` keeps `InformativeInd` where `IndCovered` already has
it, in the hypotheses. Three clauses are not free:

* `IndDeclOf env I` in `blocks` needs `env`'s **own** declaration list, which `IndInfo` does not
  give. It is `UpstreamAsks.constsOrigin`'s new declaration-level conjunct (§13, ask 2
  strengthened) — not a new ask and not a `TrEnv'` fact (§16 F8).
* `tabled` needs a kind transfer from the table: `bo c = some b` gives `compilerInfo? lenv c`,
  whose kind is `defnInfo`/`opaqueInfo` (`reifiesBody`, `Witness/SourceTable.lean:121`), and
  ask 2's classification conjunct then reads `ConstOrigin env c` off `env.constants c`. The
  transfer itself passes through the class-**D** environment connection
  (`ErasureSpec.env_connect`), so the named lemma is `constOrigin_of_tabled`
  (`Origin.lean`, U3R.5), which takes `A : UpstreamAsks env` **and** `P : ErasureSpec …`;
  `SpecEnv.erasesEnv` takes its conclusion as a premise beside `hdefns`, discharged where `P` is
  in scope. Measured: across the six rung tables and the five programs, no tabled name is a
  constructor and none is absent from the environment (`refute3/tabled.lean`).
* `axioms` needs the same `hkinj` side condition `RegInvShape'.defns` already assumes
  (`SpecEnv.lean:158`), because its trigger is a constant and its subject a key. Inhabited at
  G4's environment under exactly that condition and the rung's own block readings:
  `refute3/joint.lean`'s `g4_axioms`, kernel-checked.

## 2. `Erases.proj` and relevance

**Finding.** `Erases.proj` (`Erases.lean:213`) fires at any `IndInfo env S iid np [nf]`. At
`S = And` every premise holds, the discriminant is a proof, so its induction hypothesis may
answer `dv₀ = .box`, and at `eraseFlags` no target rule reduces `.proj p .box`
(`WcbvEval.proj` needs an applied-form construct spine, `proj_block` needs
`with_constructor_as_block`, `proj_prop` needs `with_prop_case` **and**
`isPropositionalInductive`, which the erasure never sets — measured over the 11 committed
environments, 82 of 82 emitted `one_inductive_body` entries carry `propositional = false` and
none carries `true`, out of 296 declarations; `Basic.lean:164` is where the field defaults). The
arm is refutable, not merely unprovable.

**Decision.** `Erases.proj` gains `(hinf : InformativeInd env S)`, and `InformativeInd` is
restated **semantically**: the declared result level never evaluates to zero.

```lean
def VLevel.IsNeverZero (l : VLevel) : Prop := ∀ ls, l.eval ls ≠ 0

def InformativeInd (env : VEnv) (I : Name) : Prop :=
  ∃ ci, env.constants I = some ci ∧ ∃ l, vResultSort ci.type = some l ∧ l.IsNeverZero
```

The syntactic form the tree carries — `vResultSort ci.type = some (.succ l)` — is **refuted** at
`Prod`, whose declared type ends in `Sort (max (u+1) (v+1))`, and `VLevel.ofLevel` is a plain
homomorphism, so the `.max` survives translation (`refute3/notinf.lean`, `[propext]`). It is not
one head: measured over every `.proj` head in the corpus, the syntactic test rejects `HAdd`,
`HMul`, `HPow`, `HSub`, `Pow`, `HAppend`, `Prod`, `Subtype`, `Sigma`, `PProd` and `PSigma` — 11
of the 24 heads tested — while the semantic test accepts all of them and still rejects `And`,
`Iff`, `Exists` and the `Sort u`-valued `PUnit` (`refute3/projheads.lean`). With the syntactic
form on the rule, `Erases.proj` could not fire at a single typeclass projection, `ErasesEnv.defns`
would be uninhabitable at `Prod.fst` in G4's own environment, and the `.proj` machinery would be
dead on every tracked program (§16 F1).

Decidable where a rung needs it: `neverZeroB : VLevel → Bool` (`zero`/`param` false, `succ` true,
`max` either side, `imax` the right side) is **sound and complete** for `IsNeverZero`, both
proved and kernel-checked (`refute3/amend1.lean`, `neverZeroB_sound`, `neverZeroB_complete`), and
`informativeInd_of_succ` shows every producer of the old shape is a producer of the new one — so
`FirstOrderDecl.informative` keeps its successor clause, a declared scope restriction of the
first-order fragment (`01-DESIGN.md` §4.12), and still supplies relevance through it.
`Supported.lean`'s `informativeB` becomes the matching Boolean, so the fragment checker and the
relation agree (U3.8's `Prod` finding); the first-order path keeps the strictly stronger test
under the name `succSortB`, which is what `foMemberB` reads.

This is a fact about erasure, not a restriction of it, **at the propositional structures the
criterion actually excludes**. Fig. 18's proj rule is a plain congruence because Rocq's typing
excludes projections out of `Prop`: primitive projections exist only for non-propositional
records. Lean's `Expr.proj` does occur at a `Prop` structure — `h.1` on `And` elaborates to
`Expr.proj And 0 h` — but the kernel's projection rule forbids large elimination, so every field
of a propositional structure is itself a proof and every such projection is `Erasable`. The box
rule therefore covers exactly the cases the semantic side condition removes, and `Erases` stays
total on them: `ProjInfo` (`ErasesTotal.lean:170`) is where totality already takes the projection
head's block data, and it gains the same conjunct. What the *syntactic* form removed was not
covered by box — a `Prod` projection is not erasable — which is why it had to go.

`IndDeclOf env S` — which `not_erasable_of_informative` also needs, and which `IndInfo` does not
give because `IndInfo` exhibits a block *below* `env` while upstream ask 6 reads `env`'s own
list — is **not** put on the rule: it is not monotone in `env`, so `Erases.mono` would fail. It
comes from `ErasesEnv.blocks`, which the arm holds at the reached block kername
(`constRefs (.proj p e)` contains `p.indType.mutualBlockName`, `Output.lean:270`).
`InformativeInd` is monotone (`VEnv.LE.constants`), so `Erases.mono` survives with one extra
`.mono` call.

`InformativeInd`, `VLevel.IsNeverZero`, `neverZeroB` and `vResultSort` live in
`Erasability.lean`, beside `Erasable` and `IsArityUpTo`: `Erases.lean` imports `Erasability.lean`
and cannot import `Supported.lean`, which sits above `ErasureSpec` and the source table.

**Signature.**

```lean
  | proj {Δ S i e t iid np nf} (hs : IndInfo env S iid np [nf])
      (hinf : InformativeInd env S) (hi : i < nf) (hd : Erases env Us Δ e t) :
      Erases env Us Δ (.proj S i e) (.proj ⟨iid, np, i⟩ t)
```

## 3. `SEval.iota` and `SEval.proj`

**Finding.** Both rules bind `{np}` with nothing relating it to the block, while the emitted
node's parameter count is `IndInfo`'s; source and target can drop different prefixes.
`SEval.proj` also leaves the head of the discriminant's value unclassified, so an axiom of type
`S usS params` is an admissible constant-headed value and the target is stuck at
`.proj p (const-spine)`. The premise-shaped repair for `np` — "the same `StepDefeq` pins
`np = nps`" — is refutable: at `(x, x) : Nat × Nat` the spine is `[Nat, Nat, x, x]`, so
`cargs[2]! = cargs[3]!` and one `StepDefeq` witnesses both `np = 2` and `np = 3`.

**Decision.** Pin the data positively, from the source theory, at the rule — and in *source*
coordinates. `IndInfo` carries `iid.mutualBlockName = indBlockKername …`, a λ□ datum, which has
no business in a relation about `Lean.Expr` evaluation (§16 F6); the content the two rules need
is the block's parameter count and its constructors' field counts, so they take `IndArity`,
which is `IndInfo` with the `iid` conjunct dropped:

```lean
/-- `env`'s block data for `I` in **source** coordinates: parameter count and per-constructor
field counts, with no λ□ identifier. `IndInfo.arity` is the projection, so every introduction
site that has `IndInfo` has this. -/
def IndArity (env : VEnv) (I : Name) (np : Nat) (nfs : List Nat) : Prop :=
  ∃ (ds : List VDecl) (env₀ : VEnv) (decl : VInductDecl) (t : VInductiveType),
    VEnv.WF' ds env₀ ∧ VDecl.induct decl ∈ ds ∧ env₀ ≤ env ∧
    t ∈ decl.types ∧ t.name = I ∧ decl.nparams = np ∧ ctorFieldCounts np t = nfs

  | iota {Δ : VLCtx} {con I ctor : Name} {us cus : List Level}
      {pre prev minors minorsv extra extrav cargs : List Expr} {disc r : Expr}
      {np cidx : Nat} {nfs : List Nat} (hfl : fl.iota)
      (hsh : CasesOnShape env con I pre.length minors.length)
      (ho : ConstOrigin env con)
      (hct : CtorOf env ctor I cidx)
      (hnp : IndArity env I np nfs)          -- NEW: `np` is the block's parameter count
      (hinf : InformativeInd env I)          -- NEW: the target has a rule for this elimination
      …unchanged…

  | proj {Δ S ctor i discr cus cargs np nf cidx r} (hfl : fl.proj)
      (hct : CtorOf env ctor S cidx)         -- NEW: the value's head is a constructor of `S`
      (hnp : IndArity env S np [nf])         -- NEW: `np` is the block's parameter count
      (hdiscr : SEval env bo Us fl Δ discr (mkApps (.const ctor cus) cargs))
      (hlt : np + i < cargs.length)
      (hdef : StepDefeq env Us Δ (.proj S i discr) cargs[np + i]!)
      (hcont : SEval env bo Us fl Δ cargs[np + i]! r) :
      SEval env bo Us fl Δ (.proj S i discr) r
```

All four are positive premises available at every introduction site (`CtorOf.indArity hct`
produces the ι one; `InformativeInd` is `informativeInd_of_tabled` on the table, or a `rfl`-grade
level computation at a fixture), so `SEval.mono`, `.le`, `.defeq` (T4) and
`SEval.no_elimSpine_value` are re-established by threading fields, and no evaluation the source
theory admits *and the target can follow* is lost: a projection whose discriminant's value is not
a constructor spine of `S` has no kernel reduction either, and an ι step at a non-informative
inductive is the elimination restriction **N18** already draws — the emitted `.case` is stuck on
every value a run produces, `supportedHead` rejects it with `propElimIntoData`, and the registry
declares no eliminator for it, which is why `ErasesEnv.elims` cannot conclude relevance and the
rule must carry it (§16 F1). `hinf` is the ι twin of `Erases.proj`'s: **the source relations model
only the eliminations the target performs**, stated once per eliminating rule.

`np` is pinned to the rule's **own** block, not merely to some block declaring `I`: `hsh` and
`hnp` each exhibit a `WF'` list below `env`, and ask 2's new block-uniqueness conjunct (§13)
identifies the two declarations, whence `CasesOnShape.agree A hsh hnp : pre.length = np + 1 +
nindices ∧ minors.length = nfs.length` (`Origin.lean`, U3R.5). Without it the two existentials
are independent and `np` is still free (§16 F6).

`ProjSpec` disappears whole — `ctorHead` is `hct`, `field` is `hnp` (with `CtorOf.lt_nfs A hct`
forcing `cidx = 0` at a single-constructor block), `informative` is §2's rule premise plus
`ErasesEnv.blocks`. `ElimTyping.params` disappears with `hnp` and `CasesOnShape.agree`.

## 4. `CasesOnShape` and the discriminant's typing

**Finding.** `CasesOnShape env c I dp nm` (`SourceEval.lean:153`) is three facts about a
**name** and a **block**: `isCasesOnName c`, `c.getPrefix = I`, and the block's arity
arithmetic. In a `VEnv` a `casesOn` constant is an ordinary constant, so its declared type is not
recoverable from any of them, and "the discriminant is typed at `I` applied to its indices" —
which the ι head step opens with, and without which the `.box` readings of the discriminant
cannot be refuted at all — is not a lemma anyone can find.

**Decision.** The predicate gains the clause its name claims. `CasesOnShape` is the *shape* of
an eliminator, and a shape that says nothing about the eliminator's type is under-specified;
`Lean.mkCasesOnDecl` builds exactly this type, the reified table records it, and the hand-built
`NatWitness` fixture discharges it by `rfl`. It is not a restriction on programs: it pins what
the name means.

```lean
/-- The declared type peels `dp` binders and then takes a major premise headed by `I`. -/
def MajorPremiseAt (I : Name) : Nat → VExpr → Prop
  | 0,     T => ∃ A B ius iargs, T = .forallE A B ∧ A = VExpr.mkApps (.const I ius) iargs
  | n + 1, T => ∃ A B, T = .forallE A B ∧ MajorPremiseAt I n B

def CasesOnShape (env : VEnv) (c I : Name) (dp nm : Nat) : Prop :=
  isCasesOnName c = true ∧ c.getPrefix = I ∧
  (∃ ci, env.constants c = some ci ∧ ∀ us, MajorPremiseAt I dp (ci.type.instL us)) ∧
  ∃ (ds : List VDecl) (env₀ : VEnv) (decl : VInductDecl) (t : VInductiveType), …unchanged…
```

With it, `ElimTyping.major` is a **theorem**: `TrExprS` of the saturated spine gives
`HasType` of the head at `ci.type.instL us`; `UpstreamAsks.mkAppsInv` peels `dp + 1` arguments;
`MajorPremiseAt` says the domain reached is an `I`-spine; `IsDefEqU.forallE_inv_stratified`
transports the peel's domain onto it and `HasType`'s conversion retypes the discriminant.
`ElimTyping.ctorSat` is a theorem off `CtorOf.constant_ctorResult` (`SourceEval.lean:367`, which
already proves a constructor's type ends in an `I`-spine), `mkAppsInv` and `indSpineInj`;
`IndSpineNotProp` is a theorem off `mkAppsInv`, `InformativeInd`'s successor result sort and
`IsDefEqU.sort_inv`. The structure `ElimTyping` and the predicate `IndSpineNotProp` are deleted;
`not_erasable_of_informative` keeps its signature with `P : IndSpineNotProp env` replaced by
nothing — `A : UpstreamAsks env` covers both disjuncts of `Erasable`.

`IndSpineNotProp` is **not** kept as a separate class-C premise. It is a kernel fact, and the
wave's rule is that kernel facts live in `UpstreamAsks` and die with the pin. Under §2's semantic
relevance its route changes shape: instead of reading a syntactic `.succ` off the result sort,
`indSpine_not_prop` instantiates the former's declared level at `us` and contradicts
`IsDefEqU.sort_inv`'s `≈ .zero` with `IsNeverZero`, which needs one substitution lemma —
`(l.inst us).eval ls = l.eval (us.map (·.eval ls))` — beside `VLevel.inst`. Named and owned by
U3R.5.

Two costs of the amended `CasesOnShape`, named rather than left to the unit (§16 F7). Shrinking
the predicate by adding a conjunct makes `SEval.le`'s `hcs` (`SourceEval.lean:299`) strictly
harder to supply — it asks that the extension declare no `CasesOnShape` the base did not, and
that now includes the type clause; no consumer exists tree-wide, so the cost is recorded, not
paid. And `elim_major` additionally needs instantiation to commute with `mkApps`
(`(VExpr.mkApps f args).instL us = VExpr.mkApps (f.instL us) (args.map (·.instL us))`), a
structural lemma with no home yet; U3R.5 lands it beside the corollary that uses it.

## 5. `LowerEnv.specBlocks`

**Finding.** `BlockBodiesLambda Γ` quantifies over *every* `LowerBlock` over `Γ`, and
`LowerBlock`'s only membership condition is `hdecl : DefnDecl Γ kns[i]! bs[i]!`. So a single
declared non-λ body is a one-member block that refutes it (`ctorBodyEnv_block`,
`not_blockBodiesLambda_ctorBodyEnv`, `ErasesEnv.lean:271-312`), and `Unit.unit ↦ .construct …`
is such a body in all five programs. Five of T5's eight arms and all three step lemmas spend it.

**Decision.** Key the condition on the blocks the pass actually builds, by moving it into the
block former — and put it on the **target** side, where the run's own well-formedness already
makes it, so that one assertion has one home (§16 F5). `LowerBlock` gains

```lean
  /-- Every emitted definition's body is a λ. This is `LBWfPeregrine.fixLambda`'s clause
      (`Output.lean:218`) at this block: `Erasure.visitMutual` erases each member's compiler
      value and closes it with `mkDef`, and λ□'s own `tFix` well-formedness rejects anything
      else. The **source** side is not asserted twice — it is the theorem the tree already has,
      `LowerBlock.lambda_of_fixLambda` (`LowerFix.lean:821`), which reads this field instead of
      taking `hfl` as an argument. -/
  hfl : ∀ i, i < defs.length → isLambda (defs[i]!).body = true
```

and `BlockBodiesLambda`, `LowerEnv.specBlocks` and the three refutation theorems are deleted.
`LowerBlock.lambda_of_fixLambda` and `.targetLambda_of_fixLambda` lose their `hfl` *argument* and
keep their statements; `Lower.notFix_of_block` and `Lower.ne_fix_of_block` become premise-free —
the `fixBody` reading of a `.fix` target now carries λ-headedness in the derivation itself — and
the whole `Lower.source_*` inversion kit (`box`, `bvar`, `fvar`, `prim`, `letIn`, `proj`,
`construct`, `case`, `fix`, `const`, `app`, `mkApps`, `constApp`, `constSpine`, `const_body`)
loses its `hblk` argument.

**What W4 then owes, and it is not new.** Narrowing `LowerBlock` narrows `Lower`, so the bridge
must produce `hfl` for every block the run writes. It has it: `ErasureBridge` carries
`LBWfPeregrine Γ t` (`Capstone.lean:75`), whose `fixLambda` field is `OnProgram Γ t FixLambda`.
What W4 owes is the subterm-closure step from `OnProgram` to the `.fix defs j` node a block
produces — one lemma, `FixLambda.of_onProgram`, added to W4's row rather than left implicit.

`LowerEnv` keeps eight clauses and gains none:

```lean
structure LowerEnv (Γspec Γ : GlobalDeclarations) : Prop where
  keys       : (Γ.map Prod.fst).Nodup
  defs       : ∀ kn b₀ b, DefnDecl Γspec kn b₀ → DefnDecl Γ kn b →
                 Lower Γspec b₀ b ∨ ∃ kns bs defs j, LowerFix Γspec kns bs defs ∧
                   kns[j]? = some kn ∧ b = .fix defs j
  defsTotal  : ∀ kn b₀, DefnDecl Γspec kn b₀ → ¬ RuntimeKey Γspec kn → ∃ b, DefnDecl Γ kn b
  axioms     : ∀ kn, LBTerm.envLookup Γspec kn = some (.constantDecl ⟨none⟩) →
                 LBTerm.envLookup Γ kn = some (.constantDecl ⟨none⟩) ∨
                 LBTerm.envLookup Γ kn = none
  inds       : ∀ kn d, LBTerm.envLookup Γspec kn = some (.inductiveDecl d) →
                 LBTerm.envLookup Γ kn = some (.inductiveDecl d)
  sub        : ∀ kn, LBTerm.envLookup Γ kn ≠ none → LBTerm.envLookup Γspec kn ≠ none
  closed     : ClosedBodies Γ
  specClosed : ClosedBodies Γspec        -- `Lower.subst_comm`'s hypothesis; no `specBlocks`
```

**Why this is the honest form of "keyed on the environment's declared fix bodies".** The datum
that distinguishes a real block from the spurious one-member block is external to the `Lower`
derivation: it is that the *emitted* environment declares `kns[j]` with body `.fix defs j`.
`Lower Γspec` is parameterised by one environment, the specification one, so no clause of the
relation can name the emitted environment, and a `LowerEnv`-level clause keyed on it cannot be
routed at the inversion sites, which see a derivation and no key. Putting the condition on the
block former is the same restriction stated where the derivation carries it.

**Evidence that it is inhabited on the five programs.** `Erasure.visitMutual`
(`Erasure.lean:905-918`) registers each member as `(kn, .constantDecl ⟨some (.fix defs i)⟩)`,
where `defs[i]` is `mkDef`'s closing of `visitExpr (← prepare_erasure ci.value!)`; `closeFix` is
a `toBvar` fold and preserves λ-headedness. Measured (`scratchpad/amend3/fixdefs.py`, re-run):
**51 of 51** emitted `FixDef` bodies are `tLambda` — Arith 4/4, Sieve 10/10, BinaryTrees 10/10,
Quicksort 11/11, Fannkuch 15/15, G6 1/1.

**How the measurement is sited, since only six `.ast`s are tracked.** `git ls-files '*.ast'`
returns the six spike files; the five program `.ast`s are gitignored
(`VerifyBench/ast/.gitignore`) and are *regenerated* by the build, because each
`VerifyBench/<P>.lean` root runs `#erase` on elaboration. So the acceptance test is: build the
five roots, then run `fixdefs.py`; the CI-reproducible half without a build is G6's 1/1 plus the
five zero-`FixDef` spikes (§16 F5).

**Restriction N22** is recorded in `doc/coverage.md` beside N19-N21 as what it is: not a new
bound on programs but `LBWfPeregrine.fixLambda` read at a block — the pass relation covers a
mutual block only when the emitted definitions are λ-headed, which is a well-formedness clause
the shipping output already satisfies and `peregrine` itself requires. Its decidable check is the
one above; no tracked program fails it.

## 6. `ReifiedDecl.Prepared` modulo α

**Finding.** `Prepared` demands that *every* run of `Erasure.prepare_erasure` on the compiler
value return the tabled body. `Lean.Compiler.LCNF.inlineMatchers` draws its `let`-binder names
from the name generator, so a declaration whose preparation inlines a matcher has prepared
bodies that agree only up to binder names. Measured: `lake exe reify --check` returns
`TableMismatch.declBodyAlpha` on `match 3 with …` and on `Nat.add`, so `htbl` is uninhabited for
them and any rung built on either is vacuous. `benchArith`'s closure inlines matchers, so this,
not the fragment, is what blocks G7/G8.

**Decision.** `Prepared` pins the body **up to α**. Binder names are annotations: `Expr` is de
Bruijn, `VExpr` carries no binder names at all, and no relation in the development reads one
except `Erases.lam`/`Erases.letE`, which copy it into the emitted λ□ binder name — an
annotation the target semantics also does not read.

`Expr.eqv` is `@[extern]` and opaque, so it cannot be reasoned with in the kernel, and a
`Bool` checker of our own does not help either: `Expr` carries computed fields, so a
two-argument recursion over it finds no structural measure and Lean compiles it by
well-founded recursion, which the kernel will not unfold (measured, `scratchpad/amend3/alpha2.lean`:
`Could not find a decreasing measure`, and the nested-match variant reduces to a `propext`
dependency and a stuck `decide +kernel`). The relation is therefore inductive, and the
decision procedure stays where it already is — in `IO`, in `lake exe reify --check`.

```lean
/-- α-equivalence of `Lean.Expr`: structural equality ignoring binder names and binder info,
and **nothing else**. There is no `mdata`-blind arm: `SEval` has no `mdata` arm at all
(measured, `refute3/seval_arms.lean` — eleven arms, `TrExprS` has twelve), so a relation that
identified `.mdata d e` with `e` would make the deferred `SEval.alpha` transport false, and the
measured drift is binder names only (§16 F2). This relation is extensionally `Lean.Expr.eqv`:
measured on the four discriminating pairs, `eqv` ignores binder names and binder info and
distinguishes `mdata` (`refute3/eqv.lean`). -/
inductive Expr.AlphaEq : Expr → Expr → Prop
  | bvar {i} : AlphaEq (.bvar i) (.bvar i)
  | fvar {x} : AlphaEq (.fvar x) (.fvar x)
  | mvar {x} : AlphaEq (.mvar x) (.mvar x)
  | sort {u} : AlphaEq (.sort u) (.sort u)
  | const {c us} : AlphaEq (.const c us) (.const c us)
  | lit {l} : AlphaEq (.lit l) (.lit l)
  | app {f a g b} : AlphaEq f g → AlphaEq a b → AlphaEq (.app f a) (.app g b)
  | lam {n n' t t' b b' bi bi'} : AlphaEq t t' → AlphaEq b b' →
      AlphaEq (.lam n t b bi) (.lam n' t' b' bi')
  | forallE {n n' t t' b b' bi bi'} : AlphaEq t t' → AlphaEq b b' →
      AlphaEq (.forallE n t b bi) (.forallE n' t' b' bi')
  | letE {n n' t t' v v' b b' nd nd'} : AlphaEq t t' → AlphaEq v v' → AlphaEq b b' →
      AlphaEq (.letE n t v b nd) (.letE n' t' v' b' nd')
  | proj {s i e e'} : AlphaEq e e' → AlphaEq (.proj s i e) (.proj s i e')
  | mdata {d e e'} : AlphaEq e e' → AlphaEq (.mdata d e) (.mdata d e')

def ReifiedDecl.Prepared (lenv : Environment) (n : Name) (d : ReifiedDecl) : Prop :=
  ∀ b, d.body? = some b →
    ∃ ci v, compilerInfo? lenv n = some ci ∧ ci.value? (allowOpaque := true) = some v ∧
      ∀ (s s' : Erasure.ErasureState) (ctx : Erasure.ErasureContext) (cctx : Core.Context)
        (ref : ST.Ref IO.RealWorld Core.State) (w w' : Void IO.RealWorld) (b' : Expr),
        ctx.config.csimp = false →
        Erasure.prepare_erasure v s ctx cctx ref w = .ok (b', s') w' → Expr.AlphaEq b' b
```

`SourceTableAdequate.body?_prepared` carries the same weakening. Measured, nothing consumes
either today (`grep -rn "body?_prepared"` matches its own declaration only), so the weakening
costs no proof in W3R; the α-transports are written when a rung consumes a tabled body, in W5,
and not before — policy 6 forbids landing them without their consumer.

**What the deferred transports have to cover, exactly** (§16 F4). `Erases.lam`/`letE` copy the
source binder name into the λ□ binder (`Erases.lean:196,207`), so `Erases` is *not* invariant
under `Expr.AlphaEq`: it is invariant up to λ□ binder names. W5's row therefore owes four things
and no more, because λ□ binder names occur in exactly two node formers (`.lambda`, `.letIn`) and
are read by exactly one predicate outside them (`LBWfPeregrine.asciiNames`, a fact about the
frozen emitted environment, unaffected):

1. `LBTerm.AlphaEq`, λ□ equality up to `.lambda`/`.letIn` binder names, decidable;
2. `TrExprS.alpha` — the same `VExpr`, since `VExpr` has no binder names;
3. `SEval.alpha` — an α-variant evaluates to an α-variant (true now that the `mdata` arms are
   gone);
4. `Erases.alpha` and `Lower.alpha`, each up to `LBTerm.AlphaEq`, plus the invariance of `NoBox`,
   `constRefs`/`ReachableFrom` and `WcbvEval` under it.

What is **not** in scope: the rung conclusions and the emitted-term equations. A rung's answer is
a peano numeral or a constructor spine — binder-free — so the literal answer, `NoBox` and the
uniqueness clause are unaffected; the slack lives between the tabled body and `t₀`, and is
absorbed where `t₀` is existentially quantified. The table equations (`g5Table.body? … = some …`)
stay `rfl`: they are facts about the committed table.

**What changes in the checker and what does not.** `Tools/Reify.lean`'s `--check` already computes
the comparison — `checkDecl` (`Witness/SourceTable.lean:342-352`) tests `Expr.equal` and reports
`declBodyAlpha` when `==` (`Expr.eqv`) succeeds where `equal` fails — so the pass condition
becomes `eqv`, and α-agreement is a **pass** with a note, a hard mismatch remaining for any
difference beyond binder names. Two honest halves, since the tool is class **D** either way
(§16 F3): the checker's notion is now the relation's notion, measured — `eqv` accepts exactly
binder-name and binder-info differences and rejects `mdata` differences, which is `Expr.AlphaEq`
arm for arm; and *no theorem* connects the `IO`-side Boolean to the `Prop`, because `Expr.eqv` is
`@[extern]` and opaque. To keep the two texts in step rather than trusting the extern's
documentation, `--check` also runs `partial def Expr.alphaEqB`, written one arm per `AlphaEq`
constructor, and reports a disagreement between it and `eqv` as a hard mismatch. Green's `by rfl` discharges are equations
between a tabled body and a literal (`g5Table.body? ``Unit.unit = some (.const ``PUnit.unit …)`,
`VerifyBench/Spikes/G5.lean`), which are facts about the committed table and stay `rfl`-grade.
A kernel-side α-check appears only where a rung consumes a tabled body as *the* body — W5, at
G7 — and there it is a `Expr.AlphaEq` derivation on closed terms, built by the constructors.

This adds no restriction and removes one: the ladder's "matcher-free subjects only" bound
(`doc/coverage.md`, the paragraph on why G5 and G6 are written with `Nat.casesOn`) is what the
repair lifts, and the two subjects it forced can stay as they are.

## 7. T7's `FOFields`

**Finding.** The ctor case of `firstorder_erases_core` needs, per constructor argument, a
first-order type former and a typing at its spine. Three facts are missing: spine typing
inversion, the identification of the constructor's own former with the one the value is typed
at, and uniqueness of the block declaring a former.

**Decision.** Derive it. All three are kernel facts about a `VEnv`, so all three live in
`UpstreamAsks`, and `FOFields` becomes a theorem `fOFields_of_asks (A : UpstreamAsks env) :
FOFields env Us`:

* spine typing inversion is `A.mkAppsInv` (§13, **ask 9**), also T5's ι arm's and
  `indSpine_not_prop`'s;
* `I' = I` is `A.indSpineInj` (**ask 10**) applied to `CtorOf.constant_ctorResult`'s `I'`-spine
  and the value's `I`-spine, which `mkAppsInv` proves defeq;
* block uniqueness at the declaration level is **ask 2's new conjunct**, not a third new ask:
  `constsOrigin` equated the *coordinates* (`iid`, `np`, `nfs`) of two blocks declaring one
  former, and it now also equates the declarations, which is what `FirstOrderDecl.fields` and
  `CtorOf.constant_ctorResult` speak about. The `TrEnv'`-shaped ask W3R filed for this
  (`TrEnv'.induct_block`) is **withdrawn**: it duplicates filed ask 4, it cannot be a field of
  `structure UpstreamAsks (env : VEnv)` because `TrEnv'` needs a `Lean.Environment`, and its
  named consumer `firstOrderIndB_sound` does not exist in the tree (§16 F8).

`IndDeclOf` for the two formers T7 speaks about is free: `FirstOrderInd.indDeclOf`
(`FirstOrderInd.lean:83`) already proves it from `FOClosed`'s `HasInduct`, and
`FirstOrderInd.informativeInd` (`:90`) already proves relevance from `FirstOrderDecl.informative`
— which keeps its successor shape, so §2's weakening costs T7 one `informativeInd_of_succ` call
and nothing else. What `firstOrderIndB_sound` rests on after the withdrawal is unchanged and
already recorded in the module header: **filed ask 4**, the `TrEnv'` inversion at an inductive
name, which the pinned fork does not have; until it lands, `FirstOrderInd` is reached only
through `FOModel.firstOrderInd_E`, and `hfo` stays a rung binder.

The boxed-prefix readings cost nothing: `erasable_mkApps` against the value's own
non-erasability refutes them, as U3.5 measured.

## 8. The accumulator in `Simulates`

`Simulates`' fourth conjunct `ErasesEnv env bo Γspec v₀` stays as U3.1 landed it. It is
MetaCoq's own device — "`erases_deps` adds fairly involved reasoning with an **accumulator** to
account for these dependencies" (`refs/metacoq-erasure.md:355,575`) — and it is what makes the
β and ζ arms' induction hypothesis at `subst v₀ 0 b'` available: the environment premise at the
contractum's image is `ErasesEnv.substPair` (`Steps.lean:398`) applied to the body's environment
(`.subterm` through the λ) and to `v₀`'s (the hypothesis's fourth conjunct). The closure kit is
`.subterm`, `.ofReach`, `.box`, `.mkApps`, `.substPair`, and `ReachableFrom.through_body`
(`Output.lean:805`) for δ. All five re-prove against the restated `ErasesEnv` because every
clause is antitone in the term. `ErasesCorrectStmt` keeps three conjuncts;
`erases_correct_of_steps` drops the fourth.

## 9. The β arm's `.fix`-valued function

`Erases.lam` sends a β redex's function value to `.lambda _ b₀`, and `Lower` sends a λ to a λ or
— at a declared block member — to that block's `.fix defs j`, where the target fires
`WcbvEval.fix_guarded` at `principalArgIdx = 0` (`LowerBlock.hrarg`) instead of β. The lemma is
`Lower.appReady` (`Steps.lean:567`), by induction on the `Lower` derivation with
`motive_2 := True`, no premise, class A; §5's `LowerBlock.hfl` turns its `fixBody` sub-case
into a projection (through `lambda_of_fixLambda`) instead of a case split on `bs'[j]!`. §5 of `01-DESIGN.md` records the case;
it is not a premise and not an exclusion.

## 10. The two `--schedule` false positives — landed

`lake exe hygiene --schedule` reports **0 inversions** at HEAD (measured: 6 deletion rows, 50
deleted files, 20 live imports). This decision is done; what follows is the record of why.


`Tools/Hygiene.lean:246` treats every backticked `*.lean` token in a §4 deletion row as a
deleted file. Two rows name a file that stands: the W1 cut row names `SubjectReduction.lean`,
which U1.4 re-lands under the same name inside W1, and the W2 U2.8/U2.9 row names
`ErasesEnv.lean`, of which only declarations are deleted. The rows are rewritten so that a file
that stands is not spelled as a deleted path — the surgical form the §4 preamble already asks
for, rather than the `importers' import lines` marker, which would mark the whole 30-file cut
row covered. The tool's own defect (a partial-deletion row has no syntax) is a
`doc/rework/03-DEV-FIX.md` row, not a design deliverable.

## 11. `doc/coverage.md` after the compiler-body table fix, and what G7 needs

The five-program table's "in the fragment?" column and its `Nat.brecOn` verdicts were measured
against a `Reify.visit` that tabled kernel bodies. Commit `e1cebf7` points the body column at
`compilerInfo?`, so the table closure and the eraser closure coincide, and the re-measurement
(`supportedTerm` on the entry constant and on every tabled body of `reify% <entry>`) is:
Arith 43 decls / entry `ok` / **0** erroring bodies; Sieve 81/`ok`/2; BinaryTrees 89/`ok`/3;
Quicksort 126/`ok`/9; Fannkuch 95/`ok`/6. **Arith is inside the fragment**, and the sentence
"No tracked program is inside the fragment" is false. The stale rows are replaced rather than
annotated; the four other programs keep `F-EQREC` and their own listed causes, and the `Prod`
false exclusion is **removed rather than recorded**: §2 replaces `informativeB`'s syntactic
`Level.succ` test by the never-zero test, so `Prod.casesOn` is no longer reported
`propElimIntoData` on Quicksort, BinaryTrees and Fannkuch, and the paragraph in
`doc/coverage.md:151-157` describing the false exclusion goes with it. The re-measurement is
re-run after that change, since it widens the fragment.

G7 (`arithClosed : Nat := benchArith 0`) then needs, and only needs: §6 (so that `htbl` is
inhabited on a matcher-bearing closure), §12 (so that the rung can name its subject), `hsup` by
`supportedB` on the reified table (measured clear), `hnb` by `NoBodylessRefs` (measured clear),
the target evaluation by `lbEval` on the committed `.ast`, and `hwt` by
`Witness.trExprS_const_of_table`. `hev`, `hvwt`, `hty` stay binders as they do at G1-G4 and G6;
`hcb` is four checker runs. Nothing in G7 depends on a pin bump.

## 12. Rung subjects for tracked programs

`VerifyBench/<P>.lean` defines the program **and** runs `#erase` on elaboration, so no library
module can import it: `lake build` would write `.ast` files. The rung theorem must name the
subject, which is why G1-G6's subjects live in `LeanToLambdaBox/Green.lean` and only the
`#erase` line lives under `VerifyBench/Spikes/`.

**Decision.** The same split for the tracked programs. `VerifyBench/Src/<P>.lean` holds the
program — the frozen original's definitions, no `#erase`, no `import LeanToLambdaBox`;
`VerifyBench/<P>.lean` becomes `import VerifyBench.Src.<P>` plus the unchanged `#erase` line;
`Green.lean` imports `VerifyBench.Src.Arith` for G7/G8's subject. Building `LeanToLambdaBox`
then elaborates a definition and writes nothing. `test/frozen/<P>.lean.expected` is a committed
byte copy of the sibling `benchmarks` repository's original and `scripts/frozen.sh` diffs
`VerifyBench/Src/<P>.lean` against it, so an edit to a benchmark source fails CI instead of
silently changing what the coverage table measures. Assigned to **W5 U5.0**, before U5.2's rungs.

The split keeps the `.ast` files being written: the roots still run `#erase` on elaboration, so a
build regenerates the five gitignored program `.ast`s, which is what makes §5's 51/51 measurement
reproducible in CI even though `git ls-files '*.ast'` returns only the six spikes (§16 F5). What
the split changes is that a *library* module can now name a tracked program's subject.

## 13. Upstream asks: one strengthened, two added, one withdrawn

Filed in `doc/upstream-asks.md` by U3R.5 and carried until the pin moves as fields of
`UpstreamAsks env` — the tracked class-**C** binder T5 already has. No consumer's statement
changes when they land. The numbering is the file's document-wide running list, in which 7 and 8
are the two non-ask sections ("Reported, not asked", "Proved here"), so the new asks are **9** and
**10**.

**Ask 2, strengthened** (`VEnv.WF'.consts_origin`, `Upstream.lean:41`). Its prose already claims
"the block declaring a given type former is unique"; its conjuncts only equated `IndInfo`
coordinates. Two conjuncts are added, both `VEnv`-only and both in the same family:

```lean
    -- a block below `env` that declares `I` is a block of `env`'s own declaration list
    (∀ I iid np nfs, IndInfo env I iid np nfs → IndDeclOf env I) ∧
    -- and there is only one such block
    (∀ (I : Name) decl decl', HasInduct env decl → HasInduct env decl' →
      (∃ t ∈ decl.types, t.name = I) → (∃ t ∈ decl'.types, t.name = I) → decl = decl')
```

The first is what `ErasesEnv.blocks` needs (§1) and what W3R wrongly filed as a `TrEnv'` ask; the
second is what `fOFields_of_asks` needs (§7) and what pins `SEval.iota`'s `np` to the rule's own
block (§3, `CasesOnShape.agree`).

9. **`HasType.mkApps_inv`** — spine typing inversion. There is no lemma anywhere in
   `Lean4Lean/Theory/Typing/` about `HasType U Γ (VExpr.mkApps f args) V`. Stated **with
   `OrderedStrong env` explicit**, in `HasType.app_inv`'s own idiom (`Strong.lean:885`), so that
   the ask itself is `sorryAx`-free exactly as `app_inv` is (measured: `app_inv` is
   `[propext, Quot.sound]`). Home: at or below `Theory/Typing/UniqueTyping.lean`, beside
   `app_inv`. Consumers: `elim_major`, `ctor_saturated`, `indSpine_not_prop`, `fOFields_of_asks`.
   **What it does not buy**: sorry-freedom at the consumers. Supplying `OrderedStrong` from
   `env.WF` goes through `VEnv.WF.orderedStrong`, whose `patsStrong` is `sorry`
   (`EnvLemmas.lean:334`), and the second half of the ask needs `IsDefEq.uniqU` and
   `IsDefEqU.forallE_inv`, also `sorry` at the pin. The consumers already inherit those roots;
   the ask buys the *statement*, not the trust (§16 F8).
10. **`IsDefEqU.indSpine_inj`** — two spines headed by **inductively declared** formers that are
    defeq have the same head name. The `IndDeclOf` premises are load-bearing and not decoration:
    without them the claim is false, since a `VDecl.def` gives
    `IsDefEqU (.const Foo []) (.const Nat [])`. Home: `Theory/Typing/Injectivity.lean`, beside
    ask 6 — a file in which three of the four theorems are `sorry` at the pin (`sort_inv`,
    `forallE_inv_stratified`, `sort_forallE_inv`) and the fourth is derived from one of them, so
    the honest expectation is that this ask lands with Church–Rosser and not before.
    Consumers: `ctor_saturated`, `fOFields_of_asks`.

**Withdrawn: `TrEnv'.induct_block`.** W3R filed it as ask 9 and as a field `indDeclUniq`. It
cannot be a field of `structure UpstreamAsks (env : VEnv)` — `TrEnv'` is indexed by a
`Lean.Environment`, and the only witness of that connection is the class-**D**
`ErasureSpec.env_connect`, so the field would have converted a class-C binder into a class-D one.
It also duplicates **filed ask 4** (`doc/upstream-asks.md:105`), and the consumer W3R named for
it, `firstOrderIndB_sound`, is a planned signature (`01-DESIGN.md` §4.12) with no declaration in
the tree. What it was filed for is covered above: `blocks`' `IndDeclOf` and `fOFields`' block
uniqueness are ask 2's two new conjuncts; `firstOrderIndB_sound` stays blocked on filed ask 4,
which is where that blockage was already recorded.

## 14. What T9's premises rest on after the wave

| Premise of T9 | After W3R | Inhabited at |
|---|---|---|
| `env.WF`, `TrExprS`, `SEval`, `Erases`, `Lower` | unchanged | G1-G6; `hwt` by `trExprS_const_of_table` at every rung |
| `ErasesEnv` | 7 clauses, all forward (`keys`, `deps`, `tabled`, `defns`, `axioms`, `blocks`, `elims`) | `SpecEnv.exists` from the registry; `blocks`' `IndDeclOf` and `elims`' block agreement by ask 2's new conjuncts; `tabled` by `constOrigin_of_tabled` (needs `P`); `keys`/`deps`/`axioms` measured inhabited at G4 and G5 (`refute3/joint.lean`) |
| `LowerEnv` | 8 clauses, `specBlocks` gone | `lowerEnv_idEnv`; the registry (U3R.4) — **no longer refuted** |
| `UpstreamAsks` | 4 fields (ask 2 strengthened, ask 6, asks 9 and 10) | class **C**, dies with the pin |
| `StepPremises` | **deleted** | — |
| `htbl` | modulo α | class **D**, `reify --check`; now inhabited on `benchArith` |
| `hrun`, `hsafe`, `ErasureSpec`'s fields | unchanged | class **D** |
| `hbridge` | unchanged in statement; the bridge now also owes `LowerBlock.hfl` per block | W4, from `ErasureBridge`'s own `LBWfPeregrine Γ t` through `FixLambda.of_onProgram` (§5) |
| `hfo : FirstOrderInd env ``Nat` | unchanged | a rung binder; `firstOrderIndB_sound` is not in the tree and stays blocked on filed ask 4 |
| `hev`, `hvwt`, `hty`, `hcb` | unchanged | `hev` at G5; the others are rung binders |

## 15. Probes

Under `scratchpad/amend3/` (the wave's first round) and `scratchpad/refute3/` (the refutation
round), run with `lake env lean <file>` from the repository root.

| Probe | What it establishes |
|---|---|
| `amend3/sigs.lean` | every signature the wave's first round printed elaborates against the tree at the W3 checkpoint (exit 0). The three signatures §2, §3 and §5 have since changed; the file is re-run and updated by U3R.1/U3R.2/U3R.3 |
| `amend3/alpha2.lean` | why `Expr.AlphaEq` is inductive: a two-argument `Bool` recursion over `Expr` finds no structural measure, and the nested-match variant compiles by well-founded recursion and is stuck under `decide +kernel` |
| `amend3/fixdefs.py` | 51 of 51 emitted `FixDef` bodies are λ-headed, across the five programs and the six rungs — §5's inhabitation evidence (re-run; five of the eleven `.ast`s are build artefacts, §16 F5) |
| `refute3/prod_sort.lean` | the declared result sorts: `Prod`, `Subtype`, `Sigma`, `PProd` are `.max`-headed, `Nat`, `List`, `Fin`, `Array` are `.succ`-headed, `And` is `.zero` |
| `refute3/notinf.lean` | `¬ InformativeInd env ``Prod` for the syntactic criterion, at the faithful translation — `[propext]`. The refutation §2 answers |
| `refute3/projheads.lean` | the two criteria over every `.proj` head in the 11 emitted environments: they differ at 11 of 24 heads, all of them accepted by the semantic one |
| `refute3/amend1.lean` | `neverZeroB` sound **and** complete for `IsNeverZero`; `informativeInd'_of_succ`; `Prod` accepted, `And` and a `Sort u` structure rejected — all `sorryAx`-free |
| `refute3/eqv.lean` | `Expr.eqv` ignores binder names and binder info and distinguishes `mdata`: the amended `Expr.AlphaEq`, extensionally |
| `refute3/seval_arms.lean` | `SEval` has eleven arms and no `mdata` arm; `TrExprS` has one — why `mdataL`/`mdataR` had to go |
| `refute3/elimsOnly.lean` | the refuter's Γ: an ordinary constant whose entry is `mkElimBody`-shaped is a `RuntimeKey`, so `elimsOnly` is **false** there — `sorryAx`-free |
| `refute3/s1_answer.lean` | `runtimeKey_isCasesOn`: `elimsOnly`'s content is a **theorem** of `defns` and `axioms`, in 25 lines, `sorryAx`-free — which is why the clause is dropped and the refuter's Γ is excluded by the clause set rather than by fiat |
| `refute3/joint.lean` | the environment-side clauses, inhabited: `keys`, `deps` and `axioms` at G4's `(g4Env, g4Term)` under `hkinj` and the rung's own block readings; `keys`, `deps` and `elims` at G5's **specification** environment — `g5Env` plus the `Nat.casesOn` entry `Lower.elimApp` reads — with `SpikeNatFacts` supplying the source side. All `[propext, Classical.choice, Quot.sound]` |
| `refute3/tabled.lean` | no bodied tabled name in any of the six rung tables is a constructor or absent from the environment — `tabled`'s empirical half |
| `refute3/ax_now.lean` | `not_erasable_of_informative` is `[propext, sorryAx, Classical.choice, Quot.sound]` **today**, so U3R.5's first-round acceptance criterion was unsatisfiable (§16 F8) |

## 16. Refutation round

The wave was refuted before any unit ran. Ten findings and three supplementary ones; every one is
re-checked here against the tree, and the decision each produces is folded into §§1-15 above.
Two of the refutations are kernel-checked (F1 at `Erases.proj`, S1 at `elimsOnly`) and both are
**accepted**. Nothing in this section is an open question: where a finding is wrong or partial,
the correction is measured.

**F1 — accepted, and it is worse than reported. `Erases.proj`'s relevance premise cannot be the
syntactic `InformativeInd`.** Verified: the criterion is refuted at `Prod`
(`refute3/notinf.lean`), and — not in the report — at `HAdd`, `HMul`, `HPow`, `HSub`, `Pow`,
`HAppend`, `Subtype`, `Sigma`, `PProd` and `PSigma`, which is 11 of the 24 heads tested and
includes a `.proj` head in *every* tracked program, not only `Prod` at G4
(`refute3/projheads.lean`). Decision: the semantic criterion, §2 — `IsNeverZero` on the declared
result level, with `neverZeroB` sound and complete beside it. One correction of degree: G4's rung
theorem does not "go red". `green_G4` takes its `ErasesEnv` through `hbridge`
(`Green.lean:534`), so it would still elaborate; what dies is its *inhabitation* — `ErasesEnv`'s
`defns` at `Prod.fst`, whose emitted body is `λλλ .proj ⟨prodIid,2,0⟩ (.bvar 0)`
(`Green.lean:485-488`), would be underivable, W4 could never discharge the bridge, and the rung
would be vacuous. That is the non-vacuity lane failing, which is the point of the lane. The
report's second site is also accepted: `ErasesEnv.elims` had `InformativeInd` in the
**conclusion** while `IndCovered.elims` (`ColdStartShape.lean:91`) and `SpecEnv.elims`
(`SpecEnv.lean:47`) have it in the hypotheses, so the registry could not discharge it; it moves
to the hypotheses (§1), and the ι arm supplies it from `SEval.iota`'s new `hinf` (§3).

**F2 — accepted.** `SEval` has no `mdata` arm (eleven arms, measured), so `mdataL`/`mdataR` would
make the deferred `SEval.alpha` false, and the measured drift is binder names only. Both arms are
deleted and one congruence kept (§6). Bonus, measured after the fact: the amended relation is
extensionally `Expr.eqv`, which is what the checker already computes.

**F3 — accepted, with the honest half stated.** `checkDecl` (`Witness/SourceTable.lean:342-352`)
tests `Expr.equal` and classifies with `==`; under the weakening the pass condition becomes `==`,
i.e. `Expr.eqv`, which is `@[extern]` and opaque, so no theorem connects a `--check` pass to
`Expr.AlphaEq`. §6 now says so in those words, adds `partial def Expr.alphaEqB` written one arm
per constructor as the procedure that *is* the relation, and keeps `eqv` as a cross-check that
must agree. `htbl` remains class **D**; the weakening changes what counts as agreement, not the
class of the evidence.

**F4 — accepted.** §6 under-scoped the λ□-binder-name slack. It is now scoped in four numbered
items, with the reason the rung conclusions are *not* in scope (a rung's answer is binder-free),
and assigned to W5's row (§6, "What the deferred transports have to cover").

**F5 — accepted.** `LBWfPeregrine.fixLambda` (`Output.lean:218`) already asserts what `hlam`
would have asserted, and `lambda_of_fixLambda` (`LowerFix.lean:821`) already derives the source
side from it. One home: the field goes on the **target** side (`hfl`, over `defs`) and the source
side stays a theorem (§5). The unscoped W4 obligation is now scoped — `FixLambda.of_onProgram`,
named in §5 and added to W4's row. The measurement is re-sited: `git ls-files '*.ast'` returns 6
(spikes only), the five program `.ast`s are gitignored build artefacts regenerated by the
`VerifyBench` roots, so the acceptance test builds them first and the build-free half is G6's
1/1.

**F6 — accepted, and repaired without a new premise.** `hsh` and `hi` each exhibit a block, and
`constsOrigin` equated two `IndInfo`s or two `CasesOnShape`s, never an `IndInfo` with a
`CasesOnShape`, so `np` was still free. Ask 2 gains the declaration-level uniqueness conjunct
(§13) and `CasesOnShape.agree` is the derived link (§3). The report's principled point is also
accepted: `IndInfo` drags `iid.mutualBlockName = indBlockKername …` into a source relation, so
the rules take `IndArity` — `IndInfo` minus the λ□ identifier — and `IndInfo.arity` is the
projection, so G5's discharge is still one step from `SpikeNatFacts.natInd`.

**F7 — not refuted; the two unnamed costs are now named.** `MajorPremiseAt` is derivable at
`NatWitness.natCTy` and at real `casesOn` declarations. §4 records the costs: `SEval.le`'s `hcs`
becomes strictly harder to supply (no consumer exists, so nothing is paid), and `elim_major`
needs instantiation to commute with `mkApps`, a lemma U3R.5 lands.

**F8 — accepted in full.** Measured here: `not_erasable_of_informative` is
`[propext, sorryAx, Classical.choice, Quot.sound]` today, `VEnv.WF.orderedStrong` carries
`patsStrong := sorry`, and `Injectivity.lean` has three `sorry`s of four theorems. So U3R.5's
acceptance criterion was unsatisfiable and is replaced by "the same roots as at the W3
checkpoint, no new root". Asks 7/8 are renumbered **9/10** (7 and 8 are taken by the file's two
non-ask sections), ask 9 (`HasType.mkApps_inv`) is restated with `OrderedStrong` explicit and
re-homed at or below `UniqueTyping.lean`, ask 10 keeps the `IndDeclOf` premises that make it true
and its home's own three `sorry`s are recorded. The `TrEnv'` ask is **withdrawn** — it cannot be
an `UpstreamAsks` field, it duplicates filed ask 4, and `firstOrderIndB_sound` is not in the
tree. What replaces it: ask 2's two new conjuncts for `blocks`' `IndDeclOf` and for block
uniqueness; filed ask 4, unchanged, for `firstOrderIndB_sound` (§7, §13).

**F9 / S1 — accepted; `elimsOnly` is dropped, not re-keyed.** Re-run: `elimsOnly_false` and its
neighbours are `[propext, Classical.choice, Quot.sound]`. `RuntimeKey` tests the entry's body
shape and never the key's name, so an ordinary constant whose specification body is
`mkElimBody`-shaped refutes the clause. Re-keying it on `isCasesOnName` would make it true and
useless — the consumer (`erases_elimSpine_no_value`) reaches it holding a constant and a key, not
a name test. Instead the clause is deleted and its content proved: with S2's `axioms` clause
restored, a reached key carrying an eliminator declaration belongs to no tabled constant
(`erases_ne_elimBody`, `Delta.lean:78`) and to no body-less non-eliminator, hence to a `casesOn`
name — `refute3/s1_answer.lean`, 25 lines, `sorryAx`-free. The refuter's Γ is then excluded by
`defns` and `axioms` *for a stated reason* rather than by a clause assuming its own hazard. Two
corrections to the report: `hkinj` is not the route (injectivity says nothing about a
non-eliminator's key being a `RuntimeKey`), and the tree's concession
(`RegInvShape'.defsTotal`'s `¬ RuntimeKey`) is a different hazard — a key the pass consumes
rather than emits.

**F10 — accepted, all four points.** `lake exe hygiene --rules` does not exist; the rules-table
check is `--tables` (`Hygiene.lean:387-397`), and the six acceptance lines that cited `--rules`
are corrected in the unit specs and in `02-PLAN.md`. `--schedule` is **0** at HEAD (measured: 6
rows, 50 files, 20 live imports), so decision 10 is landed and §10 says so. `IndDeclOf` moves to
`Erases.lean` in U3R.1, so U3R.1 co-owns its deletion from `ErasesCorrect/Iota.lean:265`, and
U3R.6's FILES record the co-ownership. The `fun {..} => erases_correct` check is mechanical and
currently red — `H : StepPremises` is explicit at `Close.lean:58` — which is exactly what makes it
a gate.

**S2 — accepted; it is the finding that pays for S1.** `ErasesDecl.ax` (`ErasesEnv.lean:63-66`)
had no forward counterpart, so a reached key whose constant has no compiler body was unconstrained
and could hold `⟨some junk⟩` the target δ-unfolds. Measured: `Fannkuch.ast` has exactly one
body-less entry and it is `Eq.rec`, referenced by a `tConst` inside a reached body — the
"no value found, emitting axiom" path (`Erasure.lean:875`). The `axioms` clause is restored (§1),
guarded by `isCasesOnName c = false` — without that guard it would contradict `elims` at every
eliminator key, since a `casesOn` constant is never tabled (`RegInvShape'.defns`'s `hnc`) and its
entry is the `ElimBody`. Nothing else of `ErasesDecl` is lost: `defn` is `defns`, `ind` is
`blocks`, `elim` is `elims`, `ctor` was already deleted at U2.8. `RegInvShape'.defns`
(`SpecEnv.lean:151-175`) is built by `cases` on `ErasesDecl` and must be rewritten, not re-packed;
U3R.4 is re-budgeted for that (§16 S3d).

**S3 — accepted in part; three of the five measurements are corrected here.**

* (a) **Accepted.** "The eraser emits no casesOn/recursor declarations" is right for `casesOn`
  and wrong for recursors: `Eq.rec` is emitted body-less in Fannkuch. §1's bullet list no longer
  makes the claim; the `axioms` clause is what covers the case.
* (b) **Corrected.** "`ElimDecl` holds nowhere in the corpus, so `elims` is content-free at every
  rung" measures the **emitted** environments. `ErasesEnv` is stated at `Γspec`, and
  `Lower.elimApp` (`Lower.lean:172-184`) reads `ElimDecl Γspec kn …` — the specification
  environment is *where eliminator entries live*, and the registry writes them
  (`IndCovered.elims`). That the emitted `.ast`s hold none is the pass working: `visitConstApp`
  routes a `casesOn` to a `.case` node and the key is pruned. So `elims` is exercised at G5,
  through the bridge's `Γspec`: `refute3/joint.lean` builds that environment — `g5Env` plus the
  `Nat.casesOn` entry — and discharges `elims` at it from `SpikeNatFacts`. The ι rung is not
  content-free, and the acceptance fixture for U3R.4 is that environment, not `demoEnv`.
* (c) **Accepted, and the lemma is named.** `tabled`'s discharge is not free: it routes through
  ask 2's classification conjunct plus a kind transfer from the table, whose only witness is the
  class-**D** `ErasureSpec.env_connect`. The lemma is `constOrigin_of_tabled`, owner U3R.5, and
  `SpecEnv.erasesEnv` takes its conclusion as a premise beside `hdefns` (§1, Discharge).
* (d) **Accepted.** `ErasesDecl`'s blast radius is ~14 mentions across `SpecEnv.lean`,
  `ColdStartShape.lean` and `ErasesEnv.lean` (measured: 16 in `ErasesEnv.lean`, 7 in
  `SpecEnv.lean`, 5 in `ColdStartShape.lean`, 1 in `Iota.lean`), and `RegInvShape'.defns` is an
  inversion on it. U3R.4 is re-budgeted from 900 to 1,300 lines (§`02-PLAN.md` W3R).
* (e) **Corrected.** §5's 51/51 reproduces. §2's "683/683 propositional := false" does not: the
  correct measurement over the 11 committed environments is **82 of 82** emitted
  `one_inductive_body` entries with `propositional = false`, **0** with `true`, among **296**
  declarations. The report's own 410 is not reproducible either; 82/296 is what the files hold.

**Feasibility, re-checked.** The refuter's serial-path judgement stands. The concentration of
risk in U3R.4 is confirmed and re-budgeted; G4 does not go red, because F1's amendment is
adopted before U3R.1 runs and `ErasesEnv` at G4 is inhabitable under it (`refute3/joint.lean`).

## 17. Delivery findings

The units of this wave ran against the decisions of §§1-16. Twenty-three of their own reports
carry a finding against what this document or `01-DESIGN.md` §4/§5 printed at the time — a
signature this section's plan could not state as written, a name it asked for that turns out to
already exist upstream, or a lemma its route silently assumed. None retires a rule; each
narrows a signature or a status this document's text must now match (policy §6/§9.1), the same
convention as `01-DESIGN.md` §2.4's "Wave-2 delivery findings". `01-DESIGN.md` §4/§5 are already
transcribed against the delivered shapes; this table is the index.

| # | Unit | §16/design text | What is true | Delivered as | Evidence |
|---|------|-------------------|--------------|---------------|----------|
| **WD1** | U3R.1 | §2's `neverZeroB`/`InformativeInd` text prints a fresh `def VLevel.IsNeverZero` | `Lean4Lean.VLevel.IsNeverZero (a) := ∀ ls, a.eval ls ≠ 0` already exists at the pin (`Theory/VLevel.lean:109`), body-for-body, and is the kernel theory's own relevance notion (`VInductDecl.LargeElim`) | Nothing named `IsNeverZero` is declared in `LeanToLambdaBox`; every statement reads the upstream one under `open Lean4Lean`. `neverZeroB`/`neverZeroB_sound`/`neverZeroB_complete` land as planned | `Erasability.lean:236-276` |
| **WD2** | U3R.1 | Spec asks for "one induction on the level" for `informativeInd_of_tabled`'s never-zero reading | `Lean4Lean.ofLevel_isNeverZero (h : VLevel.ofLevel Us u = some u') (H : u.isNeverZero) : u'.IsNeverZero` already exists at the pin (`Verify/Typing/Lemmas.lean:1536`) | No new induction; `informativeB`'s test is core's `Level.isNeverZero`, arm-for-arm `neverZeroB`'s shape, rather than a fourth transcription | `Supported.lean:197-200` |
| **WD3** | U3R.5 | Ask 2's uniqueness conjunct was to be stated over `FirstOrderInd.lean`'s `HasInduct env decl := ∃ ds, VEnv.WF' ds env ∧ …` | `HasInduct` lives in `FirstOrderInd.lean`, which imports `Upstream.lean` (a cycle to state it there), and it bounds the declaration list by `env` itself while every consumer (`IndInfo`, `IndArity`, `CtorOf`, `CasesOnShape`) bounds theirs by an `env₀ ≤ env` below it — inapplicable at both named consumers | `def IndBlockBelow (env) (decl) := ∃ ds env₀, VEnv.WF' ds env₀ ∧ env₀ ≤ env ∧ VDecl.induct decl ∈ ds`, in `Upstream.lean`; strictly stronger, `HasInduct env decl → IndBlockBelow env decl` is the case `env₀ = env` | `doc/upstream-asks.md` item 2 |
| **WD4** | U3R.5 | `indSpine_not_prop`'s printed premises carry `hdec : IndDeclOf env I` and no `env.WF` | `UpstreamAsks.mkAppsInv` is stated with `VEnv.OrderedStrong env` explicit, introduced only from `VEnv.WF.orderedStrong`; `hdec` turns out unused — the route reads the former's type off `InformativeInd` itself | Gains `henv : env.WF`; drops `hdec` | `Origin.lean:150-161` |
| **WD5** | U3R.5 | `elim_major`/`ctor_saturated` were expected to take `(A : UpstreamAsks env)` for ask 9 (`mkAppsInv`) | Both premises are spines reached through a `TrExprS` translation, whose `app` arm already carries the function's typing at a Π and the argument's at its domain, so ask 9 is unneeded — a THEOREM, `trExprS_spine_peel`, peels them | `elim_major` takes no `A`; `ctor_saturated` keeps `A` only for ask 6/ask 2 | `Origin.lean:167,436` (`trExprS_spine_peel`); `doc/upstream-asks.md` item 9 |
| **WD6** | U3R.5 | `constOrigin_of_tabled` (`ErasesEnv.tabled`'s discharge) was to be one theorem | The route needs a transfer of a constant's *kind* from `lenv` to the model; nothing at the pin performs it (`compilerInfo?` may answer the `_unsafe_rec` companion, and no `TrEnv'` inversion exists) — filed ask 4 | Two theorems either side of the gap: `constants_of_tabled` (tabled ⇒ `env.constants c = some vc`) and `constOrigin_of_constants` (declared + excluded ⇒ `ConstOrigin`); no theorem spans them | `Origin.lean` (both); `doc/upstream-asks.md` item 4; ledger rows in place of the non-existent name |
| **WD7** | U3R.5 | Two lemmas were scheduled to be landed beside `indSpine_not_prop`/`PiSpine` | `Lean4Lean.VLevel.eval_inst` (`Theory/VLevel.lean:139`) and `Lean4Lean.VExpr.mkApps_instL`/`.mkApps_inst` (`Theory/VExpr.lean:1069,1073`) already exist at the pin | Not re-landed (rule 5); only their one-line consequence `isNeverZero_inst` is new, and `PiSpine.instL`/`.inst`/`MajorPremiseAt.inst` call the upstream lemmas directly | `Origin.lean` |
| **WD8** | U3R.2 | §3's replacement table implies every `SEval` arm now reads `IndArity`, not `IndInfo` | `ctorVal` and `indVal` are not in this wave's F6/F3 scope (only `iota`/`proj` are), and re-keying them would silently widen ask 2 in a file this unit does not own | `IndInfo` stays in `ctorVal`'s `hi` and `indVal`'s `hi`; only `iota`'s `hnp`/`proj`'s `hnp` are `IndArity` | `SourceEval.lean:232,240` vs `:868,927` |
| **WD9** | U3R.3 | §5's `LowerBlock.hfl` repair implies only the field itself moves | With `BlockBodiesLambda` deleted, `Lower.notFix_of_block` can only exclude the `fixBody` reading through `LowerBlock.lambda_of_fixLambda`, which sat in the downstream module `LowerFix.lean` | Six declarations relocated into `Lower.lean`: `isLambda_toBvar`, `isLambda_closeFix`, `ConstToFVar.isLambda_eq`, `LowerBlock.targetLambda_of_fixLambda`, `Lower.source_isLambda`, `LowerBlock.lambda_of_fixLambda` | `Lower.lean:1338-1388` |
| **WD10** | U3R.4 | §1's `ErasesEnv` restatement and `01-DESIGN.md` §4.8 (pre-repair) print `SpecEnv` with five direct fields (`keys`, `tabled`, `consts`, `inds`, `elims`) | `ErasesEnv.blocks`/`.elims` are triggered by *reachability*, which `deps` turns into "the key is declared"; a registration-keyed clause cannot supply that, since `indBlockKername` is not injective and `RegSaturated.inds` yields *some* registered name with a block kername, not the `I` in hand | `SpecEnv` re-keyed through two new bundles, `IndCovered` (one type former's content) and `SpecContent` (the five `Γspec`-only clauses at declaredness); `SpecEnv := { spec : SpecContent …, consts, inds }` | `ErasesEnv.lean:139-193`; `SpecEnv.lean:26-34` |
| **WD11** | U3R.4 | §1's discharge line lists `hdeps`, `hdefns`, `htab` and `hax` as `SpecEnv.erasesEnv`'s four premises | `hax` (the `axioms` clause) is a fact about `Γspec`'s entries alone; it is a `SpecContent` field, carried by `RegInvShape'` and copied unchanged by every registration step, so it is *derived*, not assumed | `SpecEnv.erasesEnv` takes exactly three explicit premises: `hdeps`, `hdefns`, `htab` | `SpecEnv.lean:56-63` |
| **WD12** | U3R.4 | The plan's route for `RegInvShape'.defns` keeps the `hkinj`/`hnc`/`hblkname` side conditions W2b-F3 introduced | Those three existed only to disambiguate a `cases … with | defn …` inversion on `ErasesDecl`, which no longer exists (`SpecContent.defns` runs forward) | `RegInvShape'.defns` takes `hdeps` and `hlp` only; the dropped premises' work moves to the concrete-environment checks (`DemoSource`'s fields) | `SpecEnv.lean:145-162` |
| **WD13** | U3R.4 | `IndCovered` was implicit in §1's `ErasesEnv.elims`/`.blocks` prose, not named as a standalone bundle | `ErasesEnv`'s two inductive clauses at one type former recur three times (`SpecEnv.inds`, `SpecContent.blocks`/`.elims`'s conclusion, `RegInvShape'.inds`) | `structure IndCovered (env) (Γspec) (n)`, in `ErasesEnv.lean` (not `ColdStartShape.lean`, since `SpecContent` must see it and `ColdStartShape.lean` imports `ErasesEnv.lean`, not the reverse) | `ErasesEnv.lean:139-151` |
| **WD14** | U3R.4 | §1 lists `CasesOnOf`/`CasesOnOf'`, `demoCtor`, `regInvShape'_ctorBody` as living declarations | Each one's last reader is gone: `ErasesDecl.elim`/`IndCovered.elims`/`SpecEnv.elims` now read `CasesOnShape`; no `decls`/constructor clause reads a constructor-bodied entry; `LowerEnv.specBlocks`, the premise `regInvShape'_ctorBody` refuted, no longer exists | All three deleted (rule 5); the surviving refutation is `LowerCtorBodyFixture.lowerBlock_needs_lambda_bodies` (Lower.lean); `natEnv_erasedDecl_elim` is restated as `natEnv_elimCovered` | `ErasesEnv.lean`, `SpecEnv.lean` |
| **WD15** | U3R.6 | §3's replacement table says `ElimTyping.params`/`ProjSpec.field` retire onto `SEval.iota`/`.proj`'s new `hnp` plus `CasesOnShape.agree`(ask 2) alone | `CasesOnShape.agree`'s first conjunct is the arithmetic tautology `np + 1 ≤ dp`; it says nothing about a SECOND arity reading, so applying it at `hnp` and at `hi.arity` yields two instances of the same tautology, not `np = np'` | New lemma `IndArity.inj (A) : IndArity env I np nfs → IndArity env I np' nfs' → np = np' ∧ nfs = nfs'`, by `CasesOnShape.agree`'s own route; no new ask | `Origin.lean`, beside `CasesOnShape.agree` and its three siblings |
| **WD16** | U3R.6 | §16 F1/F6's acceptance line asks the ι `_fires` witness to "now also exhibit `hnp` and `hinf`" at `LowerElimFixture.iota_overapplied_fires` | That witness is a pure λ□-side `WcbvEval` derivation with no `SEval`, no `VEnv` and no source term — nothing for `IndArity`/`InformativeInd` to attach to | The source-side exhibition is U3R.2's `NatWitness.seval_iota_fires`/`seval_iota_overapplied_fires`, which pass `nat_indArity`/`nat_informativeInd`; the λ□-side witnesses are unchanged | `SourceEval.lean`; `ErasesCorrect/Iota.lean` |
| **WD17** | U3R.7 | §1's route for `erases_elimSpine_no_value` says "`Erases.const_inv` gives the source head `c`" | `Erases.const_inv` inverts at a *source* `.const`; the premise inverts at a *target* constant spine, and the source need not be a spine (`Erases.lit`/`.mdata` wrap it, `Erases.app` recurses); `SEval` cannot be `cases`d at `.app f a` when four arms are indexed by `mkApps (.const c us) args` | Two new lemmas supply the missing step: `erases_constSpine_value` (by induction on the evaluation) and `erases_constSpine_head`; conclusion is `as.length ≤ args.length`, not `=` | `ErasesCorrect/Steps.lean:825-867` |
| **WD18** | U3R.7 | §16 F1 amends `SEval.no_elimSpine_value`'s `hagree` in prose but `01-DESIGN.md:2071-2074` (pre-repair) prints it without the extra hypothesis | `ErasesEnv.elims`'s relevance premise moved into the HYPOTHESES (F1), so `hagree : ∀ I dp' nm', CasesOnShape env c I dp' nm' → dp' = dp ∧ nm' = nm` is not derivable from `erases_elimSpine_no_value`'s premises at an arbitrary `I` | `hagree` gains `InformativeInd env I`; the `iota` case already binds its own `hinf`, so the amendment is free | `ErasesCorrect/Steps.lean:463-469` |
| **WD19** | U3R.7 | §9's `hfl` simplification was expected to touch only `Lower.appReady`'s `fixBody` case | With the `rcases Lower.source_lambda …` split gone, `Lower.appReady`'s only remaining consumer of `ConstToFVar.fix_inv` disappears | `ConstToFVar.fix_inv` deleted (rule 5); `Lower.appReady` is a `cases`, not an `induction … using Lower.rec` | `ErasesCorrect/Steps.lean:595` |
| **WD20** | U3R.7 | §1's five moved clauses for the closure kit's reachability transport | Measured: the transport applies to `deps`, `defns`, `axioms`, `blocks`, `elims` — five clauses, not four as first counted; `keys`/`tabled` are carried unchanged | `ErasesEnv.subterm`/`.ofReach`/`.box`/`.substPair`/`.mkApps`, each a seven-clause `.mk` | `ErasesCorrect/Steps.lean:358-438` |
| **WD21** | U3R.8 | §7/§13's ask-9 paragraph implied `fOFields_of_asks` was among ask 9's (`mkAppsInv`) consumers | Measured (closure walk over each `UpstreamAsks` projection): `fOFields_of_asks` projects `constsOrigin` (ask 2), `constArityInv` (ask 6) and `indSpineInj` (ask 10), never `mkAppsInv` — its spine is a TRANSLATED one, peeled by the theorem `trExprS_spine_peel` | `fOFields_of_asks` consumes asks 2, 6, 10; ask 9's sole consumer is `indSpine_not_prop` | `doc/upstream-asks.md` items 2, 6, 9, 10 (corrected by this reconciliation, Task B) |
| **WD22** | U3R.8 | §7's helper lemmas (`peel_piSpine_head`, `MajorPremiseAt.instL`, `majorPremiseAt_of_piBinders`) were expected beside `peel_piSpine`/`MajorPremiseAt.inst` | U3R.5's `Origin.lean` had already landed when U3R.8 ran, and U3R.8 owned only `FirstOrderInd.lean` | A rename-free cut-and-paste onto their natural home | `Origin.lean`, beside `peel_piSpine` and `MajorPremiseAt.inst` |
| **WD23** | Gate (G3R) | §0's retirement of `StepPremises` reads as "`simulate_of_erases_correct` loses its `(hc : ErasesCorrectStmt …)` argument's `H`" | Two readings are available: drop `hc` and call `erases_correct` inline, or keep `hc` and drop only the premise a caller used to feed it. The ledger schedules NO footprint change for this row; reading (a) would add `sorryAx` to a class-**A** row | `hc` is KEPT as an explicit parameter — the row's `[propext, Classical.choice, Quot.sound]` footprint is unchanged, and the theorem stays about the gap between T5's subject-level premises and `ErasureBridge.simulate`'s spine-level quantification | `ErasesCorrect/Close.lean:49-59`; `test/ledger.expected` row 7 |
