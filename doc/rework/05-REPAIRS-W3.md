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
| 1 | `ErasesEnv.decls` runs entry ⇒ justified; the `ctorVal`, β, ι and proj arms need justified ⇒ entry (U3.1-1, U3.2-1, U3.2b-4) | `ErasesEnv` is restated in `erases_deps`' direction: `decls` and `ErasesDecl` are **deleted**, and the relation gains `tabled`, `blocks`, `elims`, `elimsOnly` beside `defns` (§1) |
| 2 | `Erases.proj` fires at a propositional structure, where no target rule reduces `.proj p □`; the arm is refutable at `And` (U3.2b-1) | `Erases.proj` gains `hinf : InformativeInd env S`; `IndDeclOf` comes from `ErasesEnv.blocks`, not from the rule (§2) |
| 3 | `SEval.iota`/`SEval.proj` leave `np` free and `SEval.proj` does not classify the value's head; the defeq-shaped repair is refutable at `(x, x) : Nat × Nat` (U3.2-4, U3.2b-2, U3.2b-3) | `SEval.iota` gains `hi : IndInfo env I iid np nfs`; `SEval.proj` gains `hct : CtorOf env ctor S cidx` and `hi : IndInfo env S iid np [nf]` (§3) |
| 4 | `CasesOnShape` constrains a name and a block, not the eliminator's type, so the ι head step's discriminant typing is unavailable (U3.2-2) | `CasesOnShape` gains `major`, the declared type's major-premise position; `ElimTyping.major` becomes a theorem off `major` + `UpstreamAsks.mkAppsInv` (§4) |
| 5 | `LowerEnv.specBlocks : BlockBodiesLambda Γspec` is refuted by one declared non-λ body, and five of T5's eight arms spend it (W2b-F1; U3.1-4, U3.2-5, U3.2b-5, U3.3-2) | `BlockBodiesLambda` and `specBlocks` are **deleted**; `LowerBlock` gains `hlam`, so the premise is keyed on the blocks the pass builds. Measured: 51 of 51 emitted `FixDef` bodies are λ-headed (§5) |
| 6 | `ReifiedDecl.Prepared` demands binder-name-stable preparation, which `inlineMatchers` denies; `htbl` is uninhabited on a `match` and on `Nat.add`, and on `benchArith`'s closure (G3-3) | `Prepared` pins the compiler body **up to α**, with `Expr.AlphaEq` an inductive relation of our own (`Expr.eqv` is opaque and a `Bool` checker over `Expr` is not kernel-reducible); the decision procedure stays in `lake exe reify --check`, and the rungs' `by rfl` discharges are untouched (§6) |
| 7 | T7 takes `FOFields`, which no local fact supplies (U3.5-3) | Derived: `FOFields` is a theorem off `UpstreamAsks`' three new kernel fields plus `CtorOf.constant_ctorResult` (§7) |
| 8 | `Simulates` cannot run its own induction: the β/ζ arms need `ErasesEnv` at the contractum (U3.1-2) | Kept as landed — the accumulator is MetaRocq's own device; `ErasesEnv.substPair`/`.mkApps`/`.box`/`.subterm` are the closure kit, and every clause of the restated `ErasesEnv` is antitone in the term, so the kit re-proves clause by clause (§8) |
| 9 | The β arm's function value can lower to a `.fix` node (U3.1-3) | Kept as landed: `Lower.appReady`, by induction on the `Lower` derivation, no premise; `LowerBlock.hlam` makes its `fixBody` sub-case a projection (§9) |
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
declaration — what does the environment hold for it?". At a block key the answer is ambiguous
(`toKername I = indBlockKername [I]` for a single-type block, so `ErasesDecl.ax` justifies
`Nat`'s key as well as `.ind` does, and `indBlockKername` is `String.join`, not injective); at an
eliminator key it is ambiguous too (`ErasesDecl.defn` justifies any entry whose body happens to
be `ElimBody`-shaped). Hence `ErasesEnvFwd`, `SpecElims` and `ProjSpec.informative`.

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
  constant the compiler table defines is declared as a definition in `env`. `tabled` carries no
  reachability trigger because the reading it refutes is at a constant the erasure emits **no**
  key for (a constructor erases to a `.construct` node), so there is no occurrence to trigger on.
* **inductive blocks** — `blocks`: at a reached block kername the entry is that block's
  `.inductiveDecl`, with the arity and propositionality data the ι, proj and `ctorVal` arms read
  (`IndBodyOf`), together with `IndDeclOf env I`, which is `declared_inductive Σ`, the source
  half MetaCoq's `tCase`/`tProj`/`tConstruct` clauses carry and the half
  `not_erasable_of_informative` consumes.
* **eliminators** — `elims`: at a reached `casesOn` constant the entry is that eliminator's,
  i.e. `ElimDecl Γspec (toKername c) iid np dp nfs` with the source-side agreement
  (`IndInfo env I iid np nfs`, `InformativeInd env I`, `nfs.length = nm`). `RuntimeKey` is
  immediate from `ElimDecl`, which is `SpecElims.key`; `SpecElims.decl` is `elims` plus
  `ElimDecl.uniq`.
* **constructors** — no clause. A constructor constant has no entry (`ErasesDecl.ctor` was
  deleted at U2.8 and `Erases.ctor` emits the node); what the `ctorVal` arm reads is the
  **block**'s arity, and `constRefs (.construct iid k args)` already contains
  `iid.mutualBlockName`, so `blocks` at the reached block key is the whole constructor reading.
  `ErasesEnv.ctorArity` is `ErasesEnvFwd.ctorArity` re-proved off it.
* **the `toKername` tax** — `elimsOnly`: at a reached key that carries an eliminator's
  declaration, the source constant behind the key **is** that eliminator. MetaCoq needs no such
  clause because its kernames are structured and injective; `toKername` is not
  (`SpecEnv.lean:154`, `ErasesEnv.lean:410`), and this clause is the whole difference. It is
  what discharges `ErasesEnvFwd.noElimSpine`: the β arm's under-applied eliminator spine is the
  erasure of `.const c` for some `c` with `ConstOrigin env c` (`Erases.const_inv`), `elimsOnly`
  makes `c` the eliminator, and `SEval.no_elimSpine_value` then refutes the value.

`ErasesEnv.decls` has **no consumer**: measured, its only occurrences are the re-packings
`.mk h.keys h.decls …` in `Steps.lean:354,387,402,416` and `SpecEnv.lean:73`. It is deleted, and
with it `ErasesDecl` — the four arms' content is exactly what the four forward clauses say, in
the direction the arms read them, and the ambiguity of "which arm justifies this entry" was the
cause of four of the six `StepPremises` fields. `keys` stays: it is `wf Σ'`'s `fresh_global`
half, and it is what stops a shadowing entry from retargeting `Lower`.

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
      (blocks : ∀ {I : Name} {iid : InductiveId} {np : Nat} {nfs : List Nat},
        IndInfo env I iid np nfs → ReachableFrom Γspec t iid.mutualBlockName →
        IndDeclOf env I ∧ ∃ mib,
          LBTerm.envLookup Γspec iid.mutualBlockName = some (.inductiveDecl mib) ∧
          IndBodyOf iid np nfs mib)
      (elims : ∀ {c I : Name} {dp nm : Nat},
        CasesOnShape env c I dp nm → ConstOrigin env c →
        ReachableFrom Γspec t (toKername c) →
        ∃ iid np nfs, ElimDecl Γspec (toKername c) iid np dp nfs ∧
          IndInfo env I iid np nfs ∧ InformativeInd env I ∧ nfs.length = nm)
      (elimsOnly : ∀ {c : Name}, ConstOrigin env c →
        ReachableFrom Γspec t (toKername c) → RuntimeKey Γspec (toKername c) →
        ∃ I dp nm, CasesOnShape env c I dp nm) :
      ErasesEnv env bo Γspec t
```

Every clause is antitone in `t` (a subterm reaches no more kernames), so `ErasesEnv.subterm`,
`.ofReach`, `.box`, `.mkApps` and `.substPair` re-prove with `ReachableFrom.subterm` threaded
through five clauses instead of two.

**Discharge.** `IndCovered` (`ColdStartShape.lean:84`) is the registration step's own
granularity and already has the right three fields; its `block` and `elims` clauses are
strengthened from `(envLookup …).isSome` to the forward readings above — the registration step
inserts `.inductiveDecl mib` built from the source block and the eliminator's `ElimBody`, so it
establishes them as it stands. `IndDeclOf env I` is the one conjunct the registry cannot build:
it needs `env`'s **own** declaration list, which is the upstream ask `TrEnv'.induct_block`
(§13, ask 8), the same ask `firstOrderIndB_sound` is blocked on. `tabled` and `elimsOnly` are
registry facts of the same kind as `RegInvShape'.defns`' existing side conditions
(`SpecEnv.lean:161-164`).

## 2. `Erases.proj` and relevance

**Finding.** `Erases.proj` (`Erases.lean:213`) fires at any `IndInfo env S iid np [nf]`. At
`S = And` every premise holds, the discriminant is a proof, so its induction hypothesis may
answer `dv₀ = .box`, and at `eraseFlags` no target rule reduces `.proj p .box`
(`WcbvEval.proj` needs an applied-form construct spine, `proj_block` needs
`with_constructor_as_block`, `proj_prop` needs `with_prop_case` **and**
`isPropositionalInductive`, which the erasure never sets — 683/683 emitted entries carry
`propositional := false`). The arm is refutable, not merely unprovable.

**Decision.** `Erases.proj` gains `(hinf : InformativeInd env S)`.

This is a fact about erasure, not a restriction of it. Fig. 18's proj rule is a plain congruence
because Rocq's typing excludes projections out of `Prop`: primitive projections exist only for
non-propositional records. Lean's `Expr.proj` does occur at a `Prop` structure — `h.1` on `And`
elaborates to `Expr.proj And 0 h` — but the kernel's projection rule forbids large elimination,
so every field of a propositional structure is itself a proof and every such projection is
`Erasable`. The box rule therefore covers exactly the cases the side condition removes, and
`Erases` stays total on them: `ProjInfo` (`ErasesTotal.lean:170`) is where totality already
takes the projection head's block data, and it gains the same conjunct.

`IndDeclOf env S` — which `not_erasable_of_informative` also needs, and which `IndInfo` does not
give because `IndInfo` exhibits a block *below* `env` while upstream ask 6 reads `env`'s own
list — is **not** put on the rule: it is not monotone in `env`, so `Erases.mono` would fail. It
comes from `ErasesEnv.blocks`, which the arm holds at the reached block kername
(`constRefs (.proj p e)` contains `p.indType.mutualBlockName`, `Output.lean:270`).
`InformativeInd` is monotone (`VEnv.LE.constants`), so `Erases.mono` survives with one extra
`.mono` call.

`InformativeInd` and `vResultSort` move from `Supported.lean` down to `Erasability.lean`, beside
`Erasable` and `IsArityUpTo`: `Erases.lean` imports `Erasability.lean` and cannot import
`Supported.lean`, which sits above `ErasureSpec` and the source table.

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

**Decision.** Pin the data positively, from the source theory, at the rule:

```lean
  | iota {Δ : VLCtx} {con I ctor : Name} {us cus : List Level} {iid : InductiveId}
      {pre prev minors minorsv extra extrav cargs : List Expr} {disc r : Expr}
      {np cidx : Nat} {nfs : List Nat} (hfl : fl.iota)
      (hsh : CasesOnShape env con I pre.length minors.length)
      (ho : ConstOrigin env con)
      (hct : CtorOf env ctor I cidx)
      (hi : IndInfo env I iid np nfs)            -- NEW: `np` is the block's parameter count
      …unchanged…

  | proj {Δ S ctor i discr cus cargs np nf cidx r} {iid : InductiveId} (hfl : fl.proj)
      (hct : CtorOf env ctor S cidx)             -- NEW: the value's head is a constructor of `S`
      (hi : IndInfo env S iid np [nf])           -- NEW: `np` is the block's parameter count
      (hdiscr : SEval env bo Us fl Δ discr (mkApps (.const ctor cus) cargs))
      (hlt : np + i < cargs.length)
      (hdef : StepDefeq env Us Δ (.proj S i discr) cargs[np + i]!)
      (hcont : SEval env bo Us fl Δ cargs[np + i]! r) :
      SEval env bo Us fl Δ (.proj S i discr) r
```

Both are positive premises available at every introduction site (`CtorOf.indInfo hct` produces
the ι one), so `SEval.mono`, `.le`, `.defeq` (T4) and `SEval.no_elimSpine_value` are
re-established by threading one more field, and no evaluation the source theory admits is lost:
a projection whose discriminant's value is not a constructor spine of `S` has no kernel
reduction either. `ProjSpec` disappears whole — `ctorHead` is `hct`, `field` is `hi` (with
`CtorOf.lt_nfs A hct` forcing `cidx = 0` at a single-constructor block), `informative` is §2's
rule premise plus `ErasesEnv.blocks`. `ElimTyping.params` disappears with `hi` and
`UpstreamAsks.constsOrigin`'s `IndInfo` uniqueness.

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
wave's rule is that kernel facts live in `UpstreamAsks` and die with the pin.

## 5. `LowerEnv.specBlocks`

**Finding.** `BlockBodiesLambda Γ` quantifies over *every* `LowerBlock` over `Γ`, and
`LowerBlock`'s only membership condition is `hdecl : DefnDecl Γ kns[i]! bs[i]!`. So a single
declared non-λ body is a one-member block that refutes it (`ctorBodyEnv_block`,
`not_blockBodiesLambda_ctorBodyEnv`, `ErasesEnv.lean:271-312`), and `Unit.unit ↦ .construct …`
is such a body in all five programs. Five of T5's eight arms and all three step lemmas spend it.

**Decision.** Key the condition on the blocks the pass actually builds, by moving it into the
block former: `LowerBlock` gains

```lean
  /-- Every member's specification body is a λ. `Erasure.visitMutual` erases each member's
      compiler value and closes it with `mkDef`; a block whose member body is not a λ is not
      one the pass writes, and λ□'s own `tFix` well-formedness rejects it. -/
  hlam : ∀ i, i < kns.length → isLambda bs[i]! = true
```

and `BlockBodiesLambda`, `LowerEnv.specBlocks` and the three refutation theorems are deleted.
`Lower.notFix_of_block` and `Lower.ne_fix_of_block` become premise-free — the `fixBody` reading
of a `.fix` target now carries `isLambda` in the derivation itself — and the whole
`Lower.source_*` inversion kit (`box`, `bvar`, `fvar`, `prim`, `letIn`, `proj`, `construct`,
`case`, `fix`, `const`, `app`, `mkApps`, `constApp`, `constSpine`, `const_body`) loses its
`hblk` argument. `LowerBlock.lambda_of_fixLambda` becomes the projection `LowerBlock.hlam`, and
its `hfl` premise (U3.1-3: still present after U2.7) dies with it.

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
a `toBvar` fold and preserves λ-headedness, so the emitted `FixDef.body` is a λ exactly when the
member's erased body is. Measured over the committed `.ast`s (`scratchpad/amend3/fixdefs.py`): **51 of 51**
emitted `FixDef` bodies are `tLambda` — Arith 4/4, Sieve 10/10, BinaryTrees 10/10,
Quicksort 11/11, Fannkuch 15/15, G6 1/1. The same measurement is the acceptance test.

**Restriction N22**, recorded in `doc/coverage.md` beside N19-N21: the pass relation covers a
mutual block only when every member's erased body is a λ. Its decidable check is the one above;
no tracked program fails it.

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
/-- α-equivalence of `Lean.Expr`: structural equality ignoring binder names, binder info
and `mdata`. -/
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
  | mdataL {d e e'} : AlphaEq e e' → AlphaEq (.mdata d e) e'
  | mdataR {d e e'} : AlphaEq e e' → AlphaEq e (.mdata d e')

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
costs no proof in W3R; the α-transports (`TrExprS.alpha`, `SEval.alpha`, and `Erases.alpha` up
to λ□ binder names) are written when a rung consumes a tabled body, in W5, and not before —
policy 6 forbids landing them without their consumer.

**What changes in the checker and what does not.** `Tools/Reify.lean --check` already computes
the comparison — it is what reports `TableMismatch.declBodyAlpha` — and it runs in `IO`, where
`Expr.eqv` is available; it reports α-agreement as a **pass** with a note and keeps a hard
mismatch for a difference beyond binder names. Green's `by rfl` discharges are equations
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

**Decision.** Derive it. All three are kernel facts, all three go into `UpstreamAsks`, and
`FOFields` becomes a theorem `fOFields_of_asks (A : UpstreamAsks env) : FOFields env Us`:

* spine typing inversion is `A.mkAppsInv` (§13, ask 7), also T5's ι arm's and `IndSpineNotProp`'s;
* `I' = I` is `A.indSpineInj` (ask 8) applied to `CtorOf.constant_ctorResult`'s `I'`-spine and
  the value's `I`-spine, which `mkAppsInv` proves defeq;
* block uniqueness at the declaration level is `A.indDeclUniq` (ask 9) — `constsOrigin` equates
  the *coordinates* (`iid`, `np`, `nfs`) of two blocks declaring one former, not their `types`
  and `ctors`, which is what `FirstOrderDecl.fields` and `CtorOf.constant_ctorResult` speak
  about.

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
`motive_2 := True`, no premise, class A; §5's `LowerBlock.hlam` turns its `fixBody` sub-case
into a projection instead of a case split on `bs'[j]!`. §5 of `01-DESIGN.md` records the case;
it is not a premise and not an exclusion.

## 10. The two `--schedule` false positives

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
false exclusion (`informativeB` tests for a syntactic `Level.succ`, `Prod`'s result sort is
`Level.max (succ u) (succ v)`) is recorded as conservative.

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

## 13. Upstream asks added

Filed in `doc/upstream-asks.md` by U3R.5 and carried until the pin moves as fields of
`UpstreamAsks env` — the tracked class-**C** binder T5 already has. No consumer's statement
changes when they land.

7. **`HasType.mkApps_inv`** — spine typing inversion. There is no lemma anywhere in
   `Lean4Lean/Theory/Typing/` about `HasType U Γ (VExpr.mkApps f args) V`. Home:
   `Theory/Typing/Strong.lean`, beside `HasType.app_inv`. Consumers: `ElimTyping.major`,
   `ElimTyping.ctorSat`, `IndSpineNotProp`, `FOFields`. Feasibility as measured by U3.2: the
   forward half is ~40 lines from `HasType.app_inv` plus `IsDefEq.uniqU`; the second half needs
   `IsDefEqU.forallE_inv` and an instantiation lemma under a binder.
8. **`IsDefEqU.indSpine_inj`** — two inductive-headed spines that are defeq have the same head
   name. Home: `Theory/Typing/Injectivity.lean`, beside ask 6. Consumers: `ElimTyping.ctorSat`,
   `FOFields`.
9. **`TrEnv'.induct_block`** — a `TrEnv'`-translated environment that knows `I` as an
   `inductInfo` exhibits the `VInductDecl` that declares it (U3.5's statement, ~70 lines in
   `TrEnv'.ctor_arity`'s style). Consumers: `ErasesEnv.blocks`' `IndDeclOf` conjunct,
   `firstOrderIndB_sound`, `FOFields`' block uniqueness (ask 9 subsumes the `indDeclUniq` field
   if it is proved in the `AddInduct`-uniqueness form).

## 14. What T9's premises rest on after the wave

| Premise of T9 | After W3R | Inhabited at |
|---|---|---|
| `env.WF`, `TrExprS`, `SEval`, `Erases`, `Lower` | unchanged | G1-G6; `hwt` by `trExprS_const_of_table` at every rung |
| `ErasesEnv` | 7 clauses, all forward | `SpecEnv.exists` from the registry; `blocks`' `IndDeclOf` by ask 9 |
| `LowerEnv` | 9 clauses, `specBlocks` gone | `lowerEnv_idEnv`; the registry (U3R.4) — **no longer refuted** |
| `UpstreamAsks` | 5 fields (2 + asks 7-9) | class **C**, dies with the pin |
| `StepPremises` | **deleted** | — |
| `htbl` | modulo α | class **D**, `reify --check`; now inhabited on `benchArith` |
| `hrun`, `hsafe`, `ErasureSpec`'s fields | unchanged | class **D** |
| `hbridge` | unchanged | W4 |
| `hfo : FirstOrderInd env ``Nat` | unchanged | `firstOrderIndB_sound` after ask 9 |
| `hev`, `hvwt`, `hty`, `hcb` | unchanged | `hev` at G5; the others are rung binders |

## 15. Probes

Under the wave's scratch directory `scratchpad/amend3/`, run with `lake env lean <file>` from the
repository root.

| Probe | What it establishes |
|---|---|
| `sigs.lean` | every signature this document prints elaborates against the tree at the W3 checkpoint (exit 0): `MajorPremiseAt` and the amended `CasesOnShape`, the seven-clause `ErasesEnv`, the three amended rules as inferences, `LowerBlock` extended by `hlam`, `Expr.AlphaEq` and the α-weakened `Prepared`, and `ErasesCorrectStmt` unchanged. It also derives `TabledNotCtor`, `SpecElims.key` and the block reading from the new clauses, so three of the six `StepPremises` fields are retired in the probe itself |
| `alpha2.lean` | why `Expr.AlphaEq` is inductive: a two-argument `Bool` recursion over `Expr` finds no structural measure, and the nested-match variant compiles by well-founded recursion and is stuck under `decide +kernel` |
| `fixdefs.py` | 51 of 51 emitted `FixDef` bodies are λ-headed, across the five programs and the six rungs — §5's inhabitation evidence |
