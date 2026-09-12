# Upstream asks

What this development needs from, or has found in, the projects it sits on: lean4lean
(the fork this repository pins), MetaRocq, and peregrine. Items 1-6, 9 and 10 are **asks**:
lemmas or fixes whose natural home is upstream, either because they are kernel-generic — a fact
about `VEnv`/`VExpr`/`HasType`/`IsDefEq`/`TrExprS` and not about erasure — or because the defect
is upstream's. Item 7 is **reported, not asked**: findings about consumers this repository
does not depend on fixing. Item 8 is **proved here and filed for consolidation**: kernel-generic
facts this repository already has, which need no fork change. The numbering is a single running
list, which is why the asks added by W3R are 9 and 10.

Four asks are **load-bearing for Wave 3**: item 2 (`WF'.consts_origin`), item 6
(`IsDefEqU.const_arity_inv`), item 9 (`HasType.mkApps_inv`) and item 10
(`IsDefEqU.indSpine_inj`). Editing the fork is a separate agent's work, so until the pin
moves each is taken as one named, auditable class-**C** hypothesis — the four fields of
`UpstreamAsks env` (`LeanToLambdaBox/Upstream.lean`), unweakened and unrestated — and every
consumer carries it in its statement. The pin bump discharges the structure with no change to
any consumer's statement shape; a refusal blocks the arms that consume it, and `doc/trust.md`
records which.

Paths under `.lake/packages/lean4lean/Lean4Lean/` are given relative to that directory.

## Asks — lean4lean

1. **`VEnv.WF'.defeqOwn`** — a `WF'` environment grants each constant at most one defining
   equation: the `defeqs` twin of `WF'.pats_origin` (`Theory/Typing/InductiveParams.lean:93`).
   This is the fact that settled whether the δ layer needs a second environment of compiler
   bodies, and the answer was no. The proof is written (about 130 lines, no frontend
   dependency; it was produced as a design-gate probe, `doc/rework/01-DESIGN.md` §8.3) and it
   belongs upstream, not here. In the idiom of `WF'.pats_origin`, and free to be sharpened:

   ```lean
   theorem VEnv.WF'.defeqOwn {ds : List VDecl} {env : VEnv} (H : env.WF' ds)
       {df df' : VDefEq} (h : env.defeqs df) (h' : env.defeqs df')
       {c : Name} {us us' : List VLevel}
       (hlhs : df.lhs = .const c us) (hlhs' : df'.lhs = .const c us') : df = df'
   ```

2. **`VEnv.WF'.consts_origin`**, the constants-keyed twin of `WF'.pats_origin`, together with
   a generic `iotaRHS'` — the missing link in the `largeElim_of_wf` argument. **Load-bearing
   from Wave 3**, for a reason unrelated to the one it was filed under: `Erases` distinguishes
   the three readings of `Expr.const` (constructor / inductive type name / plain constant), and
   the *exclusion* direction is what T7's uniqueness and T5's ι head step consume. The
   corollaries this repository consumes are `constOrigin_not_ctorOf`, `constOrigin_not_indInfo`,
   `IndInfo.inj`, `CtorOf.inj`, `CasesOnShape.inj`, the totality direction `consts_classified`
   and, off the two conjuncts below, `IndInfo.indDeclOf` and `indBlock_uniq`; they land in
   `LeanToLambdaBox/Origin.lean`. Its singleton-machinery use
   still waits on `F-PROP`. The origin statement asked for, in the idiom of `WF'.pats_origin`
   — one declaring step per constant, the name fresh below it — is what they are read off:

   ```lean
   theorem VEnv.WF'.consts_origin {ds : List VDecl} {env : VEnv} (H : env.WF' ds)
       {c : Name} {ci : VConstant} (hc : env.constants c = some ci) :
       ∃ (d : VDecl) (ds₀ : List VDecl) (env₀ env₁ : VEnv),
         (d :: ds₀) <:+ ds ∧ env₀.WF' ds₀ ∧ VDecl.WF env₀ d env₁ ∧ env₁ ≤ env ∧
         env₀.constants c = none ∧ env₁.constants c = some ci
   ```

   Until the fork holds it, the consequences are the `constsOrigin` field of
   `UpstreamAsks env` (`LeanToLambdaBox/Upstream.lean`), taken as one named class-**C**
   hypothesis and unpacked by `LeanToLambdaBox/Origin.lean`; `doc/trust.md` carries the row.

   **Two conjuncts added by W3R** (`doc/rework/05-REPAIRS-W3.md` §13), both consequences of the
   same origin statement and both `VEnv`-only, so they change nothing about the ask's home or its
   discharge — the prose above already claims the second ("the block declaring a given type
   former is unique"), which the coordinate-level conjunct did not deliver:

   ```lean
   -- a block below `env` that declares `I` is a block of `env`'s OWN declaration list
   (∀ I iid np nfs, IndInfo env I iid np nfs → IndDeclOf env I) ∧
   -- and there is only one such block, at the declaration level, not only in its coordinates
   (∀ (I : Name) decl decl', IndBlockBelow env decl → IndBlockBelow env decl' →
     (∃ t ∈ decl.types, t.name = I) → (∃ t ∈ decl'.types, t.name = I) → decl = decl')
   ```

   `IndBlockBelow env decl` is `∃ ds env₀, VEnv.WF' ds env₀ ∧ env₀ ≤ env ∧ VDecl.induct decl ∈ ds`
   (`LeanToLambdaBox/Upstream.lean`). The **below**-`env` form is what the conjunct has to be
   stated in: `IndInfo`, `IndArity`, `CtorOf` and `CasesOnShape` each bound their declaration
   list by `env₀ ≤ env` rather than by `env` itself, so a conjunct phrased at `env`'s own list
   (`FirstOrderInd`'s `HasInduct`, the special case `env₀ = env`) is not applicable at any
   consumer. The fork is free to derive it from the origin statement, where the recursor a block
   generates is what distinguishes two blocks declaring one former.

   Consumers: `ErasesEnv.blocks`' `IndDeclOf` conjunct — hence every rung's `ErasesEnv` — the
   derived `CasesOnShape.agree`, which is what pins `SEval.iota`'s parameter count to the rule's
   own block, and `CtorOf.ctorResult_at`, which is `ctor_saturated`'s and `fOFields_of_asks`'
   block uniqueness. They replace an ask W3R filed against the environment-translation relation
   and then withdrew: that relation is indexed by a `Lean.Environment`, so it cannot appear in a
   field of `UpstreamAsks env`, and its content for `firstOrderIndB_sound` is item 4 below.

3. **The seven kernel-generic declarations in `LeanToLambdaBox/CheckerAdequacy.lean`** —
   `VContext.ofMLCtx` with its three `@[simp]` projections, `VState.WF.initial`, `M.WF.run'`,
   and `kernelNGen`. They are about the checker, not about erasure; this repository's
   acceptance criteria forbid a `Lean4Lean`-namespace declaration here, and the oracle
   discharge needs them. They move to the fork with the pin bump (U3.1). Their statements, as
   they stand here in `namespace Lean4Lean.TypeChecker`:

   ```lean
   def kernelNGen : NameGenerator := { namePrefix := `_kernel_fresh, idx := 0 }

   def VContext.ofMLCtx {env : Environment} {ves : VEnvs} (wf : ves.WF env)
       (safety : DefinitionSafety := .safe) (lparams : List Name := [])
       (fuel : FuelConfig := {})
       (m : MLCtx) (mwf : m.WF (ves.venv safety) lparams) : VContext

   @[simp] theorem VContext.ofMLCtx_venv {env : Environment} {ves : VEnvs} (wf : ves.WF env)
       {safety : DefinitionSafety} {lparams : List Name} {fuel : FuelConfig}
       {m : MLCtx} (mwf : m.WF (ves.venv safety) lparams) :
       (VContext.ofMLCtx wf safety lparams fuel m mwf).venv = ves.venv safety

   @[simp] theorem VContext.ofMLCtx_lparams {env : Environment} {ves : VEnvs} (wf : ves.WF env)
       {safety : DefinitionSafety} {lparams : List Name} {fuel : FuelConfig}
       {m : MLCtx} (mwf : m.WF (ves.venv safety) lparams) :
       (VContext.ofMLCtx wf safety lparams fuel m mwf).lparams = lparams

   @[simp] theorem VContext.ofMLCtx_vlctx {env : Environment} {ves : VEnvs} (wf : ves.WF env)
       {safety : DefinitionSafety} {lparams : List Name} {fuel : FuelConfig}
       {m : MLCtx} (mwf : m.WF (ves.venv safety) lparams) :
       (VContext.ofMLCtx wf safety lparams fuel m mwf).vlctx = m.vlctx

   theorem VState.WF.initial {env : Environment} {ves : VEnvs} {wf : ves.WF env}
       {safety : DefinitionSafety} {lparams : List Name} {fuel : FuelConfig}
       {m : MLCtx} {mwf : m.WF (ves.venv safety) lparams}
       (hfresh : ∀ fv ∈ m.vlctx.fvars, kernelNGen.Reserves fv) :
       VState.WF (.ofMLCtx wf safety lparams fuel m mwf) {}

   theorem M.WF.run' {env : Environment} {ves : VEnvs} (wf : ves.WF env)
       {safety : DefinitionSafety} {lparams : List Name} {fuel : FuelConfig}
       {m : MLCtx} (mwf : m.WF (ves.venv safety) lparams)
       (hfresh : ∀ fv ∈ m.vlctx.fvars, kernelNGen.Reserves fv)
       {x : M α} {Q} (H : x.WF (.ofMLCtx wf safety lparams fuel m mwf) {} fun a _ => Q a) :
       (M.run env safety m.lctx lparams fuel x).WF Q
   ```

4. **A `TrEnv'` inversion on the `induct`/`AddInduct` clause** yielding
   `InductiveVal ↔ VInductDecl`, in the shape of `TrEnv.structure_rec`
   (`Verify/Environment/Lemmas.lean:644`) and `TrEnv'.pats_iota'` (`:674`). It would turn the
   `ind_adequate` field of this development's specification bundle from an assumed field into
   a theorem. Related and larger: the `inductDecl` case of `addDecl.WF`
   (`Verify/Environment.lean:208`) is `sorry` at the pinned revision — the lemma that would
   let the environment connection itself be derived rather than assumed.

   **It is also what would compose `ErasesEnv.tabled`'s two proved halves into one theorem.**
   `ErasesEnv.tabled` asks that a constant the compiler table gives a body for be a *plain*
   constant of `env`. Both halves are proved (`LeanToLambdaBox/Origin.lean`:
   `constants_of_tabled` and `constOrigin_of_constants`); what joins them is a transfer of the
   constant's **kind** from `lenv` to the model, and nothing at the pin performs it — no
   theorem spans the gap. Until item 4 lands, the exclusion is a premise of
   `SpecEnv.erasesEnv`.

   **This is also `firstOrderIndB_sound`'s blocker** (`LeanToLambdaBox/FirstOrderInd.lean`'s
   module header): the table-side half `firstOrderIndB_step` is proved, and the model-side half
   is exactly this inversion. W3R briefly filed a second ask for the same content
   (`TrEnv'.induct_block`) and withdrew it as a duplicate; until item 4 lands, `FirstOrderInd` is
   reached only through `FOModel.firstOrderInd_E` and `hfo` stays a rung binder.

5. **The `Quot.ind` divergence** between the theory (`Theory/Quot.lean:11` and its
   neighbours) and the executable checker.

6. **`VEnv.IsDefEqU.const_arity_inv`** — an application headed by an inductive **type former**
   is definitionally equal to neither a sort nor a Π. Home:
   `Theory/Typing/Injectivity.lean`, beside `sort_inv`, `forallE_inv_stratified` and
   `sort_forallE_inv`; all three are `sorry` at the pin and all three are already inherited here
   through `Erasable.app`, so the honest expectation is that this one lands the same way and its
   `sorryAx` root inherits into T5's ι and proj arms and into T7. Statement, in that file's
   idiom:

   ```lean
   theorem IsDefEqU.const_arity_inv {ds : List VDecl} {env : VEnv} {U : Nat} {Γ : List VExpr}
       (henv : env.WF' ds) (hΓ : OnCtx Γ (env.IsType U))
       {decl : VInductDecl} {t : VInductiveType} {us : List VLevel} {args : List VExpr}
       (hdecl : VDecl.induct decl ∈ ds) (htype : t ∈ decl.types)
       (hty : ∃ V, env.HasType U Γ (VExpr.mkApps (.const t.name us) args) V) :
       (∀ u, ¬ env.IsDefEqU U Γ (VExpr.mkApps (.const t.name us) args) (.sort u)) ∧
       (∀ A B, ¬ env.IsDefEqU U Γ (VExpr.mkApps (.const t.name us) args) (.forallE A B))
   ```

   The fork is free to sharpen the hypotheses (`hty` is there so that the over-applied case is
   excluded by typing rather than by a side condition). Consumers here, all theorems:
   `not_erasable_of_informative` (T5's ι arm, T5's proj arm, T7's `firstorder_no_box`), directly,
   and `fOFields_of_asks` (both T7 theorems), through `indSpine_ne_forallE`'s use inside
   `peel_piSpine`. It is
   **not** a consumer of the `SEval.ctorVal` arm any more: that arm carries `[S Fig. 12]`'s own
   `nargs ≤ cstr_arity` bound, read off `IndInfo`, so no-over-application is a premise of the
   source value relation rather than a kernel fact to be derived.

9. **`HasType.mkApps_inv`** — spine typing inversion. There is no lemma anywhere in
   `Lean4Lean/Theory/Typing/` about `HasType U Γ (VExpr.mkApps f args) V`; the tree needs one at
   four places. Stated with `OrderedStrong env` **explicit**, in `HasType.app_inv`'s own idiom
   (`Theory/Typing/Strong.lean:885`), so that the ask is `sorryAx`-free exactly as `app_inv` is
   (measured: `app_inv` is `[propext, Quot.sound]`). Home: at or below
   `Theory/Typing/UniqueTyping.lean`, beside `app_inv`.

   ```lean
   /-- Peeling a spine's typing, argument by argument. -/
   def Peel (env : VEnv) (U : Nat) (Γ : List VExpr) : VExpr → List VExpr → VExpr → Prop
     | T, [],      V => env.IsDefEqU U Γ T V
     | T, a :: as, V => ∃ A B, env.IsDefEqU U Γ T (.forallE A B) ∧ env.HasType U Γ a A ∧
                          Peel env U Γ (B.inst a) as V

   theorem HasType.mkApps_inv {env : VEnv} (henv : OrderedStrong env) {U Γ}
       (hΓ : OnCtx Γ (env.IsType U)) (args : List VExpr) {f V}
       (H : env.HasType U Γ (VExpr.mkApps f args) V) :
       ∃ T, env.HasType U Γ f T ∧ Peel env U Γ T args V
   ```

   Consumers, all theorems here: `indSpine_not_prop` alone (T5's ι and proj arms, inside
   `not_erasable_of_informative`). `elim_major`, `ctor_saturated` and `fOFields_of_asks` were
   filed as consumers and are **not**: all three read a spine reached through a `TrExprS`
   translation, and `TrExprS`'s `app` arm already carries the function's typing at a Π and the
   argument's at its domain, so `LeanToLambdaBox/Origin.lean`'s `trExprS_spine_peel` proves the
   peel for them outright — `fOFields_of_asks` consumes asks 2, 6 and 10 instead (items 2, 6
   and 10). The ask stays load-bearing for the one consumer whose spine is untranslated.
   Feasibility as measured: the forward half is ~40 lines
   from `HasType.app_inv` plus `IsDefEq.uniqU`; the second half needs `IsDefEqU.forallE_inv` and
   an instantiation lemma under a binder.

   **What it does not buy, said plainly.** Not sorry-freedom at the consumers. `app_inv` needs
   `OrderedStrong`, whose only introduction `VEnv.WF.orderedStrong` rests on
   `VEnv.WF.patsStrong := sorry` (`Theory/Typing/EnvLemmas.lean:334`), and `IsDefEq.uniqU` and
   `IsDefEqU.forallE_inv` are `sorry` at the pin as well. The consumers already inherit those
   roots — `not_erasable_of_informative` measures
   `[propext, sorryAx, Classical.choice, Quot.sound]` today — so this ask buys the statement, not
   the trust.

10. **`IsDefEqU.indSpine_inj`** — two spines headed by **inductively declared** type formers that
   are definitionally equal have the same head name. Home: `Theory/Typing/Injectivity.lean`,
   beside item 6.

   ```lean
   theorem IsDefEqU.indSpine_inj {env : VEnv} (henv : env.WF) {U Γ}
       (hΓ : OnCtx Γ (env.IsType U)) {I J : Name} {us vs iargs jargs}
       (hI : IndDeclOf env I) (hJ : IndDeclOf env J)
       (h : env.IsDefEqU U Γ (VExpr.mkApps (.const I us) iargs)
                             (VExpr.mkApps (.const J vs) jargs)) : I = J
   ```

   The `IndDeclOf` premises are load-bearing rather than decoration: without them the statement
   is **false**, since a `VDecl.def` named `Foo` with body `Nat` gives
   `IsDefEqU (.const Foo []) (.const Nat [])`. Consumers: `fOFields_of_asks` alone — it is the
   one theorem that must identify a constructor field's own type former with the value's;
   `ctor_saturated` was filed as a consumer and is not, since its `I` is given directly by its
   own `hi : IndInfo env I iid np nfs`, with no second former to identify it against.
   Honest expectation: the home file has three `sorry`s of four theorems (`sort_inv`,
   `forallE_inv_stratified`, `sort_forallE_inv`) and Church-Rosser itself is unproved
   (`ChurchRosser.lean:1193,1212`), so this ask lands with them and not before.

## Reported, not asked

7. *(Not an ask — a section. The running numbers continue through the file, which is why the
   asks W3R added are 9 and 10.)* Three findings about downstream consumers, recorded because
   theorems here are stated against them:

   * **MetaRocq's shipped `firstorder_ind` is `false` on `nat`.** The sort conjunct of
     `PCUICFirstorder.v:59` is not in `[S §7.3]`'s prose; it makes every theorem guarded by
     the predicate vacuously guarded. Reproduced three ways by `vm_compute`. This repository
     therefore cites the code as the origin of its own `FirstOrderInd` and does **not**
     transcribe it, and says so in `doc/rules-Erases.md`'s posture and in `doc/trust.md`.
   * **peregrine's `run_untyped_transforms` precondition obligation is `Admitted`**
     (`Transforms.v:375`), so the pass that consumes this frontend's output carries no proof
     of the precondition it requires.
   * **`peregrine validate` is `parse_ast ;; get_config ;; check_wf` only**
     (`Pipeline.v:245-248`, `CheckWf.v:182-183`) — no expandedness check. That is what makes
     `F-ETA` undetectable downstream, and why an `.ast` produced by a panicking run still
     validates (`doc/panics.md`).

## Proved here, filed for consolidation

8. Three facts about lean4lean's `VEnv.WF'`/`VInductDecl.WF` that are kernel-generic rather than
   about erasure. **No fork change is needed**: all three are proved here and `sorryAx`-free at
   the pin, in `LeanToLambdaBox/SourceEval.lean`, for want of a dedicated home. They are the
   constructor-side twins of `wf'_induct_origin` and `IndInfo.constant_isArity`
   (`LeanToLambdaBox/ErasesTotal.lean`), which make the same argument from the type-former side;
   the natural home for all five, on this side of the boundary, is `LeanToLambdaBox/Origin.lean`.

   ```lean
   theorem IsArity.piBody_sort {A : VExpr} (h : IsArity A) : ∃ u, A.piBody = .sort u

   theorem CtorOf.constant_ctorResult {env : VEnv} {c I : Name} {k : Nat} (h : CtorOf env c I k) :
       ∃ ci np nf nind, env.constants c = some ci ∧ ci.type.CtorResult I np nf nind

   theorem CtorOf.not_indInfo {env : VEnv} {c I : Name} {k : Nat} {iid : InductiveId}
       {np : Nat} {nfs : List Nat} (hc : CtorOf env c I k) : ¬ IndInfo env c iid np nfs
   ```
