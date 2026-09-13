# 08 — W6, the closing round

W5 delivered eight green rungs, the world-indexed run induction, the reduced `ErasureBridge` and
`bridgeEnv_of_regInv`, and left two class-**C** binders standing on `shipping_erase_correct_firstorder`:
`hve : VisitExprRunConcl` and `hbridge`, the latter with five fields. This document settles what
W6 does with each, with the measurement behind every decision, and re-plans the wave as the
closing round.

Every signature below is the one W6 lands. Probe files elaborate at this toolchain against the
tree at the W5 checkpoint (`lake build`, 173 jobs); they live outside the repository under
`amend6/` and are cited by basename.

## 0. The findings, and the decision each takes

| # | Finding (source) | Decision |
|---|---|---|
| F1 | `VisitExprRunConcl` is not provable as defined: its only configuration premise is `remove_irrel_constr_args = false`, while `visitExpr` reaches `prepare_erasure` through `visitMutual`'s `@[csimp]` branch and `run_prepare_erasure_ok` needs `csimp = false` (U5.1 obstruction 2) | the `def` is **deleted**; `visitExpr_runConcl` proves its conclusion outright under `ConfigPinned ctx.config`, and `step6`/`run_visitMutual_registers` call it (§1) |
| F2 | `SpecContent.defns` names *some* erasure of the compiler body, `RegInvShape'.defs` demands the emitted body be the `Lower` image of *that* one, and `Erases` is not deterministic outside the first-order fragment (U5.1 obstruction 1b) | the two clauses merge into one, `RegContent`, with the witness shared; the specification environment is threaded as an **output** of the refinement, not quantified first (§2) |
| F3 | `ConstExt` records no converse: nothing says a registered constant has a `gdecls` entry at its canonical kername (U5.1 obstruction 3) | **no new field is needed** — `ConstExt.gdecls` already records each prefix key as `toKername m` for an `m` the extended registry knows, so `RegKeyed` preservation is a theorem, `ConstExt.regKeyed` (§2.2) |
| F4 | Nothing produces `RegInvShape'` at a run's final state, so `erasesEnv`/`lowerEnv` have no argument (U5.2 blocker 1) | **not closed in W6**, for three independently measured reasons — the fixed level scope, the α gap, and the ∀-`Γspec` shape of `RunRefines` (§2.3); the two fields stay, and `hbridge` shrinks from five to two |
| F5 | `wf : LBWfPeregrine Γ t` has no supplier for ten of its twelve clauses (U5.2 blocker 2) | `LBWfPeregrine` is decided by a Boolean checker and every clause holds at every rung by `decide +kernel` in about a second; `wf` leaves the bundle and becomes a per-rung checked term (§3) |
| F6 | new, this round: `LBWfPeregrine.asciiNames` is **false** at five of the eight rungs — 1 offending binder name at G2/G3/G4, 34 at G7/G8 — and is not what peregrine's reader requires (§3.1) | `AsciiBinderName` is restated at the condition the quoted `(nNamed "…")` atom needs; the alphanumeric class is `cleanIdent`'s, a condition on kername identifiers, and belongs nowhere near a binder name (§3.1) |
| F7 | `noBox` needs the constructor-tree shape `firstorder_erases_core` computes and does not export, and the naive transport along `Lower` is false (U5.2 blocker 4) | `firstorder_erases_core` concludes `FOSpine t`; `FOSpine.lower` transports it; `noBox` is **retired** (§4) |
| F8 | `simulate`'s two ∀-premises are false at any `Γspec` for a constant-spine subject, so `simulate_of_erases_correct` cannot discharge the field (U5.2 blocker 3) | the field is **retired**: the capstone applies `erases_correct` once, at the spine, with `ErasesEnv.mkApps`; the two premises become per-argument premises of the observable clause, vacuous at every rung (§5) |
| F9 | `Alpha.lean` is 99 proved declarations outside the closure with no consumer and no scheduled W6 consumer (U5.5 obstruction 4, 07-STATUS §4) | **deleted**; it is the α-transport kit for `ReifiedDecl.Prepared`, whose only consumer is F4's deferred content clause, and `01-DESIGN.md` §9.6 admits no exception row without a scheduled consumer (§6) |
| F10 | `hcb : CompilerBodies` is a binder at G2–G8 | upstream, and stays so: 10 of G7's 30 tabled bodies carry an `Expr.proj` and `TrExprS` at a `.proj` routes through lean4lean's `TrProj`, entirely unproven at the pin (§7) |
| F11 | new, this round: T5 — `erases_correct`, the simulation — is **outside** the `Green.lean` ∪ `Capstone.lean` closure, together with its three arms (`lake exe hygiene --dead`) | F8's decision puts it inside: the capstone applies it, so the simulation and the arms it composes become live code (§5.3) |

## 1. `hve`, discharged

`VisitExprRunConcl` (`VisitExprRefines/Step/Env.lean:91`) is a `def … : Prop` — the last premise
def in the step files, and BD20's own count. Its conclusion is provable; the definition is one
premise short. `visitExpr` reaches `Erasure.prepare_erasure` through `visitMutual`, whose
`@[csimp]` branch runs `Lean.Core.transform` at `EraseM`, and `ColdStartRun.run_prepare_erasure_ok`
takes `hcs : ctx.config.csimp = false`. `ConfigPinned` (`ErasureSpec.lean:43-45`) carries both that
and the pruning flag, and both consumers already hold it: `run_visitMutual_registers` takes `hcs`
and `hpru` separately at `Step/Env.lean:301-302`, and `step6` derives each by `rw [hinv.cfg]` from
the capstone's `hcfg`.

W6 deletes the `def` and lands the theorem instead. `runClosedW_indReg` is the third `RunClosedW`
instance — the registry conjunct — and the other two, `runClosedW_runConcl` and `runClosedW_gen`,
are U5.1's:

```lean
theorem runClosedW_indReg {lenv : Environment} {env : VEnv} {Us : List Name}
    {gw : Void IO.RealWorld → NameGenerator} (S : ErasureSpec lenv env Us gw)
    (E : EraserAsks lenv env Us gw) (s₀ : ErasureState) :
    RunClosedW ConfigPinned
      (fun s _ => IndRegistryModelled env s₀ → IndRegistryModelled env s)

theorem visitExpr_runConcl {lenv : Environment} {env : VEnv} {Us : List Name}
    {gw : Void IO.RealWorld → NameGenerator} (S : ErasureSpec lenv env Us gw)
    (E : EraserAsks lenv env Us gw) {e : Expr} {s : ErasureState} {ctx : ErasureContext}
    {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
    {t : LBTerm} {s₁ : ErasureState} {w₁ : Void IO.RealWorld}
    (hcfg : ConfigPinned ctx.config)
    (hrun : Erasure.visitExpr e s ctx cctx ref w = .ok (t, s₁) w₁) :
    RunConcl s s₁ ∧ gw w ≤ gw w₁ ∧ (IndRegistryModelled env s → IndRegistryModelled env s₁)
```

`reg`'s two provenance arms are what makes the instance go through: the left arm reads the
`Lean.getConstInfo` run through `pass_getConstInfo_core` and `LookupAdequate.constInfo`, the right
arm — `Erasure.visitCases`' two machine-numeral registrations — is refuted by `hcfg.2.2.1 : nat = .peano`.

Both consumers lose a parameter and collapse their two flag premises into one:

```lean
theorem run_visitMutual_registers … (P : ErasureSpec lenv env Us gw) (E : EraserAsks lenv env Us gw)
    (htbl : SourceTableAdequate lenv tbl) (hsafe : TableSafe lenv tbl)
    (htab : (tbl.decl? n).isSome) (hcfg : ConfigPinned ctx.config)
    (hind : IndRegistryModelled env s)
    (hrun : visitMutual n s ctx cctx ref w = .ok (u, s₁) w₁) :
    (s₁.constants.get? n).isSome ∧ RunConcl s s₁ ∧ gw w ≤ gw w₁ ∧ IndRegistryModelled env s₁

theorem step6 (E : EraserAsks lenv env Us gw) (hsafe : TableSafe lenv tbl) :
    Step6 lenv env Us tbl cfg gw
```

`erasure_bridge_of_run` and `shipping_erase_correct_firstorder` drop `(hve : VisitExprRunConcl env gw)`;
so do the eight rungs. `grep -rn "VisitExprRunConcl" --include='*.lean' LeanToLambdaBox/` is empty
afterwards, and `grep -nE "^def [A-Za-z0-9_']+ " LeanToLambdaBox/VisitExprRefines/Step/*.lean`
goes from 1 to 0.

Evidence: `amend6/p1_hve.lean` — the two theorems, verbatim, elaborating against
`LeanToLambdaBox.Capstone` at the W5 checkpoint, both `[propext, Classical.choice, Quot.sound]`,
no `sorry`.

## 2. The registry invariant: the statement, the correction, and why it is not W6's

### 2.1 The determinism gap, closed by restating the clause

U5.1's refutation is of a *shape*, not of a fact: `SpecContent.defns` and `RegInvShape'.defs` name
the erasure witness twice and independently, so a `Γspec` adequate for the table need not be the
one the run's output lowers from. The repair is one clause carrying both readings of a single
witness:

```lean
/-- The content clause of the registration invariant, with the erasure witness **shared**:
the emitted body is the `Lower Γspec` image of the same `b₀` the specification environment
declares for the constant and the compiler body erases to. -/
structure RegContent (env : VEnv) (bo : Name → Option Expr)
    (Γspec : GlobalDeclarations) (s : ErasureState) : Prop where
  defns : ∀ (n : Name) (b : Expr) (t : LBTerm), bo n = some b →
    DefnDecl s.gdecls (toKername n) t →
    ∃ (b₀ : LBTerm) (Us : List Name), DefnDecl Γspec (toKername n) b₀ ∧
      Erases env Us [] b b₀ ∧
      (Lower Γspec b₀ t ∨ ∃ kns bs defs j, LowerFix Γspec kns bs defs ∧
        kns[j]? = some (toKername n) ∧ t = .fix defs j)
```

`SpecContent.defns` and `RegInvShape'.defs` are then projections of it at a declared constant, and
`bridgeEnv_of_regInv` is unchanged. The invariant is preserved only if `Γspec` grows with the
state rather than being fixed:

```lean
/-- `Γ'` extends `Γ` by a prefix of fresh keys, so `LBTerm.envLookup` at every old key is
unchanged and `DefnDecl`, `RuntimeKey` and every `Lower` derivation over `Γ` survive. -/
def SpecGrow (Γ Γ' : GlobalDeclarations) : Prop :=
  ∃ pre : GlobalDeclarations, Γ' = pre ++ Γ ∧ ∀ p ∈ pre, ∀ q ∈ Γ, p.1 ≠ q.1

theorem visitExpr_regInv_all {lenv env Us gw tbl} (P : ErasureSpec lenv env Us gw)
    (E : EraserAsks lenv env Us gw) (htbl : SourceTableAdequate lenv tbl) :
    ∀ e s ctx cctx ref w t s' w', Erasure.visitExpr e s ctx cctx ref w = .ok (t, s') w' →
      ConfigPinned ctx.config →
      ∀ Γspec, RegInvShape' env tbl.body? Γspec s → RegContent env tbl.body? Γspec s →
        ∃ Γspec', SpecGrow Γspec Γspec' ∧
          RegInvShape' env tbl.body? Γspec' s' ∧ RegContent env tbl.body? Γspec' s'
```

That is the statement U5.1's obstruction 1b leaves standing. It is stateable, and the preservation
kit it needs at the registration primitives already exists — `RegInvShape'.{addAxiom_run,
constCons, recConst, axiomCons, blockCons, stateCongr, indsGrow, register_inductive_run}`
(`ColdStartShape.lean:212-680`), whose side conditions are read off the final state and are
discharged by construction once `Γspec` is built from `s'.gdecls`.

### 2.2 `ConstExt`'s converse is derivable, not missing

U5.1's obstruction 3 asks for a clause. None is needed. `ConstExt.gdecls`
(`ErasureRun.lean:1541-1543`) already records, for every entry of the prefix, that it is
`(toKername m, .constantDecl ⟨none⟩)` for an `m` the *extended* registry knows. That is exactly
what makes the registry-domain invariant maintainable, in the direction `RegSaturated` reads it:

```lean
/-- Every emitted key is a registered constant's canonical kername or a registered inductive's
block key: the bound on `s.gdecls` that turns `RegInvShape'`'s registry-scoped clauses into
`LowerEnv`'s unscoped ones. -/
def RegKeyed (s : ErasureState) : Prop :=
  ∀ kn, LBTerm.envLookup s.gdecls kn ≠ none →
    (∃ n, kn = toKername n ∧ (s.constants.get? n).isSome) ∨
    (∃ n iid np nfs, (s.inductives.get? n).isSome ∧ IndInfo env n iid np nfs ∧
      kn = iid.mutualBlockName)

theorem ConstExt.regKeyed {s s' : ErasureState} (h : ConstExt s s')
    (hind : ∀ n, (s.inductives.get? n).isSome → (s'.inductives.get? n).isSome)
    (H : RegKeyed s) : RegKeyed s'
```

With `Γspec` built from `s.gdecls`, `RegSaturated.consts` is `RegKeyed`'s first disjunct and
`RegInvShape'.defsTotal` is vacuous at an `addAxiom`-registered constant, whose `Γspec` entry is
`⟨none⟩` and so no `DefnDecl`. Both clauses stop being obligations and become bookkeeping. That is
the second reason to build `Γspec` from the output rather than quantify it.

### 2.3 Why W6 does not land it

Three obstructions, each measured, each independent.

**O1 — the level scope.** `Motive6` reports registration and nothing about content
(`VisitExprRefines/Motives.lean:152-160`) because `BridgeInv.lparams : ctx.lparams = Us`
(`Bridge.lean:322`) cannot be re-established across `Erasure.lean:889` and `:912`, both of which
run the member body under `withReader (… lparams := ci.levelParams)`. Measured at G7: `g7Table`
has 44 declarations, 28 of them polymorphic, and **16 of the 30 tabled bodies belong to a
polymorphic constant** (`amend6/p11_tbl.lean`). The fix is to quantify `Us` *inside* the eighteen
motives, which forces `P : ErasureSpec lenv env Us gw` and `E : EraserAsks lenv env Us gw` — both
indexed by `Us` — to become `∀ Us, …` at the capstone, and rewrites `Motives.lean` and all
eighteen step lemmas (4,404 lines under `VisitExprRefines/`).

**O2 — α.** Even at a monomorphic dependency the run erases `prepare_erasure (compilerValue lenv n)`,
which `ReifiedDecl.Prepared` (`Witness/SourceTable.lean:194-201`) pins to the tabled body only up
to `Expr.AlphaEq` — deliberately, since on equality the clause is uninhabited wherever
`inlineMatchers` fires. `RegContent.defns` reads the *tabled* body, because `SEval` does; `Erases`
copies the source binder name into its image, so the two erasures differ by a target renaming; and
`Lower` is not α-closed on its source (`Alpha.lean:1033`, `Lower.not_alpha`: the two `fix` arms
read a declared body out of `Γ` by equality). Measured: `lake exe reify --check` reports five of
G7/G8's bodies matching only up to binder names — `Nat.add`, `Nat.mul`, `Nat.pow`, `Nat.pred`,
`Nat.sub` — and `SourceTableAdequate.body?_prepared`, the transport that would spend the clause,
has **no consumer anywhere in the tree**.

**O3 — the ∀-`Γspec` shape.** `RunRefines` (`Motives.lean:38-41`) reads content at *every*
`SpecEnv` of the final state. §2.1's threading is the opposite shape — one environment, produced.
The two cannot be proved in one induction without restating all eighteen motives.

**Verdict.** `erasesEnv` and `lowerEnv` stay as `hbridge`'s two fields. `bridgeEnv_of_regInv`
(`Capstone.lean:145-155`, proved, nine axioms, no `sorryAx`) remains the interface they plug into,
and §2.1–§2.2 are the statement and the two lemmas a later round starts from. `hbridge` is
recorded in `doc/trust.md` as one binder with two fields and this section as its discharge story.

## 3. `wf`, as a checked term

### 3.1 F6: `asciiNames` is refuted on the emitted output

`LBWfPeregrine.asciiNames` reads `AsciiBinders`, whose per-name condition is
`∀ c ∈ s.toList, c.isAlphanum ∨ c = '_'` (`Output.lean:177-190`) — `Basic.cleanIdent`'s character
class. Measured occurrences of names outside that class, per rung
(`amend6/p9_ascii.lean`, `amend6/p9c.lean`):

| rung | G1 | G2 | G3 | G4 | G5 | G6 | G7 | G8 |
|---|---|---|---|---|---|---|---|---|
| offending binder names | 0 | 1 | 1 | 1 | 0 | 0 | 34 (32 distinct) | 34 |

G2/G3/G4's single offender is `x._@.Init.Prelude.1822880135._hygCtx._hyg.3`, `instOfNatNat`'s
binder; G7/G8 add the four `.fix` definition names `Nat.add`, `Nat.mul`, `Nat.pow`, `Nat.sub` and
the twenty-eight hygienic binders the matcher inlining introduces. So `LBWfPeregrine Γ t` is false
at five of eight rungs, and at those five `hbridge`'s `wf` field is unsatisfiable: `green_G2`,
`green_G3`, `green_G4`, `green_G7` and `green_G8` are **vacuous as they stand**.

The clause is wrong, not the eraser. `cleanIdent` is applied by `toKername`/`rootKername`
(`Basic.lean:35-42`) to **kername identifiers**, and never to a binder name;
`Printing.lean:25-28` emits a binder name as a quoted atom, `(nNamed "…")`; and peregrine's
`Deserialize_ident` accepts any `Str` atom
(`peregrine-tool/theories/serialization/DeserializeCommon.v:13-18`). The condition the format
actually imposes is that the name closes no atom — `quote_atom` escapes nothing.

```lean
/-- A binder name the λ□ printer can emit. `Printing.lean`'s `quote_atom` wraps the name in
`"…"` and escapes nothing, and peregrine's `Deserialize_ident` accepts any `Str` atom, so the
condition is that the name contains neither of the two characters that would close or escape
the atom. `Basic.cleanIdent`'s alphanumeric class is a condition on **kername identifiers**,
which `toKername` establishes by construction; on a binder name it is false — the eraser emits
`x._@.Init.Prelude.1822880135._hygCtx._hyg.3` at three rungs and thirty-two such names at two
more. -/
def PrintableBinderName : BinderName → Prop
  | .named s => ∀ c ∈ s.toList, c ≠ '"' ∧ c ≠ '\\'
  | .anon => True

theorem hygienic_binder_not_alphanum :
    ¬ ∀ c ∈ "x._@.Init.Prelude.1822880135._hygCtx._hyg.3".toList, c.isAlphanum ∨ c = '_' := by
  decide
```

`AsciiBinders` becomes `PrintableBinders` with the same four `SubTerm` clauses, and
`LBWfPeregrine.asciiNames` becomes `printableNames`. Restated, the clause holds at all eight
rungs: 0 offenders everywhere (`amend6/p9c.lean`).

### 3.2 The checker

Every clause of `LBWfPeregrine` is a bounded quantifier once `OnProgram`'s `∀ kn` is read as a
fold over `Γ` and `SubTerm` as a structural walk, so the predicate has a Boolean twin. `decide`
alone does not reach it — `declsWf`'s `∀ kn body, LBTerm.envLookup Γ kn = …` is not a `Decidable`
proposition, measured — so W6 lands the checker and its soundness lemma:

```lean
def subtermAll (p : LBTerm → Bool) : LBTerm → Bool          -- + Args/Alts/Defs, structural
theorem subtermAll_sound {p : LBTerm → Bool} {t u : LBTerm}
    (h : subtermAll p t = true) (hu : SubTerm u t) : p u = true

def onProgramB (Γ : GlobalDeclarations) (t : LBTerm) (p : LBTerm → Bool) : Bool
theorem onProgramB_sound {Γ : GlobalDeclarations} {t : LBTerm} {p : LBTerm → Bool}
    {P : LBTerm → Prop} (hp : ∀ u, (∀ v, SubTerm v u → p v = true) → P u)
    (h : onProgramB Γ t p = true) : OnProgram Γ t P

def lbWfPeregrineB (Γ : GlobalDeclarations) (t : LBTerm) : Bool
theorem lbWfPeregrine_of_check {Γ : GlobalDeclarations} {t : LBTerm}
    (h : lbWfPeregrineB Γ t = true) : LBWfPeregrine Γ t
```

with one per-node Boolean per clause — `keysDistinctB`, `declsWfB`, `lbClosedB`, `noBlockB`,
`noDanglingNode`, `ctorsDeclaredNode`, `casesExhNode`, `projDeclNode`, `fixLambdaNode`,
`printableNode` — and, for the two saturation clauses, `spineInfo` plus the four-function
`ctorSatB` family, whose `ctorSatBFn` arm is what implements `ConstructSpine`'s
maximal-application-depth guard.

**Measured, at the W5 checkpoint, on `Green.g1Env`…`Green.g8Env`** (`amend6/p10_wfall.lean`): all
twelve clauses, all eight rungs, `by decide +kernel`, whole file 11.8 s. The per-clause probes are
`amend6/p5_wf.lean` (`keys`, `declsWf`), `amend6/p6_walk.lean` (`constsOk`, `fixLambda`),
`amend6/p7_ctorsat.lean` (`etaCtorsEnv`/`etaCtorsTm` at G1, G4, G7), `amend6/p8_rest.lean`
(`casesExh`, `projDecl`, `closed`, `ctorApplied`).

**One mechanical rule the unit spec carries, because it cost a probe:** every checker must be
**structurally** recursive. A catch-all arm that recurses at the same argument (`| t => ctorSatB Γ t`)
compiles by well-founded recursion, and a well-founded definition does not reduce in the kernel —
`decide +kernel` reports the instance stuck rather than failing.

### 3.3 Where `wf` goes

`LBWfPeregrine Γ t` is a statement about `Γ` and `t` alone; nothing in the bundle's other two
fields is needed for it, and nothing in it is needed for them. It leaves `ErasureBridge` and
becomes a binder of the capstone, `hwf : LBWfPeregrine Γ t`, discharged at every rung by
`lbWfPeregrine_of_check (by decide +kernel)` — the same shape as `hnb : NoBodylessRefs Γ t`,
which is already a binder discharged by kernel computation at all eight rungs. The relocation
neither strengthens nor weakens the theorem; what it buys is that the rungs stop assuming it.

## 4. `noBox`, retired

`firstorder_erases_core` (`FirstOrderInd.lean:448`) computes the shape it needs in its `ctor` arm —
`hshape` proves every erasure of the value is `LBTerm.mkApps (.construct iid k []) ts` with each
argument's erasure handled by the induction hypothesis — and then throws it away, concluding
`NoBox t`. W6 exports it:

```lean
/-- The λ□ image of a first-order value: an applied-form constructor tree. `.construct` nodes
carry no arguments (F-ETA2), so the tree is built by `.app`. -/
inductive FOSpine : LBTerm → Prop
  | ctor {iid : InductiveId} {k : Nat} : FOSpine (.construct iid k [])
  | app {f a : LBTerm} : FOSpine f → FOSpine a → FOSpine (.app f a)

theorem FOSpine.noBox {t : LBTerm} (h : FOSpine t) : NoBox t
theorem FOSpine.mkApps {iid : InductiveId} {k : Nat} {ts : List LBTerm}
    (h : ∀ x ∈ ts, FOSpine x) : FOSpine (LBTerm.mkApps (.construct iid k []) ts)
theorem spineHead_mkApps (f : LBTerm) (l : List LBTerm) :
    LBTerm.spineHead (LBTerm.mkApps f l) = LBTerm.spineHead f
theorem FOSpine.spineHead {t : LBTerm} (h : FOSpine t) :
    ∃ iid k, LBTerm.spineHead t = .construct iid k []
theorem FOSpine.lower {Γ : GlobalDeclarations} {s t : LBTerm}
    (hs : FOSpine s) (h : Lower Γ s t) : FOSpine t
theorem noBox_lower_of_foSpine {Γspec : GlobalDeclarations} {tv₀ tv : LBTerm}
    (hfo : FOSpine tv₀) (hlow : Lower Γspec tv₀ tv) : NoBox tv
```

and `firstorder_erases_core`'s conclusion becomes `FOSpine t ∧ ∀ t', Erases env Us [] v t' → t' = t`.
`firstorder_no_box`'s statement does not move — it has a `test/Ledger.lean` row — only its proof,
from `.1` to `.1.noBox`.

`FOSpine.lower` is the guard `noBox_lower_needs_noFix` (`LowerFix.lean:1050`) says any transport
needs, and it is not ad hoc: the `.construct` arm goes through `Lower.source_construct`
(`Lower.lean:1958`), which rules out the two `fix` arms by `Lower.ne_fix_of_block` because a
constructor node is neither a constant nor a λ; the `.app` arm goes through `Lower.source_app`
(`ErasesCorrect/Steps.lean:272`), whose `elimApp` disjunct is refuted on the spine head — a
`FOSpine`'s `spineHead` is a `.construct`, the disjunct's is a `.const`. The nullary route
`Lower.source_construct_nil` (`Lower.lean:2064`), which keeps a `.fix` disjunct, is not used.

Evidence: `amend6/p2_nobox.lean` — every theorem above proved, no `sorry`,
`[propext, Classical.choice, Quot.sound]`.

## 5. `simulate`, retired

### 5.1 The field is used once

`ErasureBridge.simulate` quantifies over every source term, and the capstone applies it at exactly
one: `B.simulate hspine hlowspine hevp` (`Capstone.lean:232`), at `s := mkApps pe args`. U5.2's
blocker 3 is a consequence of that over-generality — `simulate_of_erases_correct`'s `hsp` is false
at any `Γspec` because it quantifies over terms the environment does not declare. At the one
instance the capstone needs, both premises are supplyable, and the theorem that supplies them is
`erases_correct` itself (`ErasesCorrect/Close.lean:29`), applied directly.

### 5.2 What the capstone needs, and where it comes from

`erases_correct henv hwt hev her hlow hspec henvL A` needs, at the spine:

* `TrExprS env [] [] (mkApps pe args) vs`. Not derivable from the subject's translation and the
  arguments' — `TrExprS.app` carries typing side conditions — so it becomes a premise of the
  observable clause. At `args = []` it is `mkApps pe [] = pe` by `rfl`, i.e. the capstone's own
  `hwt`, so every rung discharges it with the term it already passes.
* `ErasesEnv env tbl.body? Γspec (LBTerm.mkApps t₀ a₀s)`. This one composes:

```lean
theorem ReachableFrom.mkApps_inv {Γ : GlobalDeclarations} {f : LBTerm} {kn : Kername}
    {l : List LBTerm} (h : ReachableFrom Γ (LBTerm.mkApps f l) kn) :
    ReachableFrom Γ f kn ∨ ∃ x ∈ l, ReachableFrom Γ x kn

theorem ErasesEnv.mkApps {env : VEnv} {bo : Name → Option Expr}
    {Γspec : GlobalDeclarations} {f : LBTerm} {l : List LBTerm}
    (hf : ErasesEnv env bo Γspec f) (hl : ∀ x ∈ l, ErasesEnv env bo Γspec x) :
    ErasesEnv env bo Γspec (LBTerm.mkApps f l)
```

  from `hbridge`'s `erasesEnv` at the head and a per-argument premise at the arguments. The
  observable clause's argument premise therefore reads

```lean
          (∀ i, i < args.length → ∃ a₀, Erases env [] [] args[i]! a₀ ∧
            Lower Γspec a₀ targs[i]! ∧ ErasesEnv env tbl.body? Γspec a₀) →
```

  which is `ErasesLB` unfolded with one conjunct added. At `args = []` it is
  `fun i hi => absurd hi (by simp)`, unchanged from what the eight rungs pass today.

Both are recorded weakenings of the conclusion at `args ≠ []`, and both are what MetaRocq's own
statement requires of a spine. They replace a field that nothing discharges, so no rung's
statement loses anything and every rung's `hbridge` loses a field.

`simulate_of_erases_correct` and its `test/Ledger.lean` row go with the field: the lemma's whole
content was the two ∀-premises, and they are false.

Evidence: `amend6/p3_erasesenv.lean` (both theorems proved, three axioms) and
`amend6/p4_capstone.lean` (the capstone's whole proof re-run with `simulate` and `noBox` gone from
the bundle, the two new premises in place, and the 33-name cluster unchanged).

### 5.3 F11: the simulation joins the closure

`lake exe hygiene --dead` at the W5 checkpoint reports `erases_correct`, `erases_correct_lb` and
`simulate_of_erases_correct` — all three of `ErasesCorrect/Close.lean` — as outside the
`Green.lean` ∪ `Capstone.lean` closure, and with them the arms they compose (`ErasesCorrect/Iota`
18, `Proj` 11, `Delta` 9, `ErasesCorrect.lean` 8, `ErasesUniform` 19, `IotaBridge` 4). T5 — the
simulation, the wave's largest single result — is not reachable from the shipping theorem. §5.2's
decision fixes that: the capstone applies `erases_correct`, so T5 and the arms it reaches become
live code. The gate re-measures `--dead` rather than predicting it; the two named movements are
Alpha's 99 leaving and the T5 closure entering.

## 6. `Alpha.lean`, deleted

99 declarations, 1,050 lines, the single largest block in `--dead`'s 315 and outside the closure
since it landed. What it is: the α-transport kit for `ReifiedDecl.Prepared` — `Expr.AlphaEq.refl`,
`TrExprS.alpha`, `Erases.alpha`, `SEval.alpha`, `StepDefeq.alpha` and the `LBTerm.AlphaEq`
congruence and decision procedure. Its only possible consumer is §2.3's O2, the content clause at a
run-built `Γspec`, which W6 does not schedule; U5.0's expected consumer, green-check up to α, did
not materialise, because byte-exact transcription turned out to be maintainable (U5.3 obstruction 5),
and `SourceTableAdequate.body?_prepared` — the theorem that would spend the α clause — is itself
consumed nowhere.

`01-DESIGN.md` §9.6 admits an exception row only with a scheduled consumer, and W6 is the closing
round, so there is none to name. The file is deleted; git holds it at the W5 checkpoint commit and
the round that lands §2.1 re-lands it verbatim. The aggregator's `import LeanToLambdaBox.Alpha`
(`LeanToLambdaBox.lean:62`) is the gate's, under N3a.

## 7. `hcb` at G2–G8: upstream

`CompilerBodies lenv env bo` demands `TrExprS env ci.levelParams [] b vb` per tabled body — a
translation, not a typing. Measured on `g7Table` (`amend6/p12_proj.lean`): 30 of 44 declarations
carry a body and **10 of those bodies contain an `Expr.proj`** — `Add.add`, `HAdd.hAdd`, `HMul.hMul`,
`HPow.hPow`, `HSub.hSub`, `Mul.mul`, `NatPow.pow`, `OfNat.ofNat`, `Pow.pow`, `Sub.sub`, the class
projections. `TrExprS` at a `.proj` routes through lean4lean's `TrProj`, which the pin
(`20ec229f1a8c6358f3b3852c4e27d2be523d1b87`) leaves entirely unproven. `g1Table` has 0 such bodies,
which is why `g1_compilerBodies` exists and no sibling does; independently, 28 of G7's 44
declarations are polymorphic, which `g1_compilerBodies`' monomorphic route does not reach at all.

`hcb` is therefore a class-**C** binder blocked on an upstream fact, at G2–G8, and W6 changes
nothing about it. It retires with a pin bump the fork accepts; `doc/upstream-asks.md` is this
side's register.

## 8. What W6 lands, and what `hbridge` still carries

`ErasureBridge` goes from five fields to two:

```lean
/-- What the capstone assumes beyond the erasure half: the two environment results the
specification environment of the run's final state carries. Both are derived by
`bridgeEnv_of_regInv` from `RegInvShape'` and `RegSaturated` at that state, and no theorem
produces that invariant for a run of the shipping eraser — `08-REPAIRS-W5.md` §2 is the
statement that would, and the three obstructions in the way. -/
structure ErasureBridge (env : VEnv) (bo : Name → Option Expr)
    (Γspec Γ : GlobalDeclarations) (t₀ : LBTerm) : Prop where
  erasesEnv : ErasesEnv env bo Γspec t₀
  lowerEnv : LowerEnv Γspec Γ
```

and the capstone's binder list loses `hve` and gains `hwf`:

```lean
theorem shipping_erase_correct_firstorder
    {lenv : Lean.Environment} {env : VEnv} {gw : Void IO.RealWorld → NameGenerator}
    {tbl : SourceTable} {cfg : ErasureConfig} {e pe : Expr} {ve : VExpr}
    {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
    {w wp w' : Void IO.RealWorld}
    {Γ : GlobalDeclarations} {t : LBTerm} {inls : List Kername}
    (P : ErasureSpec lenv env [] gw)                        -- class D
    (E : EraserAsks lenv env [] gw)                         -- class C
    (A : UpstreamAsks env)                                   -- upstream; dies with the pin bump
    (htbl : SourceTableAdequate lenv tbl)                    -- class D, `reify --check`
    (hsafe : TableSafe lenv tbl)                             -- class D, `reify --check`
    (hblk : TableBlocks lenv env tbl)                        -- class D, `reify --blocks`
    (hcfg : ConfigPinned cfg)                                -- checked term at every rung
    (hcb : CompilerBodies lenv env tbl.body?)                -- class C; upstream `TrProj` at G2–G8
    (hwt : TrExprS env [] [] pe ve)                          -- checked term at every rung
    (hsup : Supported env tbl pe)                            -- checked term at every rung
    (hprep : Erasure.prepare_erasure e {} { «config» := cfg } cctx ref w = .ok (pe, {}) wp)
    (hrun : Erasure.erase e cfg cctx ref w = .ok (.untyped Γ (some t), inls) w')
    (hnb : NoBodylessRefs Γ t)                               -- `by decide +kernel` per rung
    (hwf : LBWfPeregrine Γ t)                                -- `lbWfPeregrine_of_check` per rung
    (hbridge : ∀ (sf : ErasureState) (wt : Void IO.RealWorld),
      Erasure.visitExpr pe {} { «config» := cfg } cctx ref wp = .ok (t, sf) wt →
      ∃ Γspec : GlobalDeclarations, SpecEnv env tbl.body? sf Γspec ∧
        ∀ t₀ : LBTerm, Erases env [] [] pe t₀ → Lower Γspec t₀ t →
          ErasureBridge env tbl.body? Γspec Γ t₀) :
    ∃ (Γspec : GlobalDeclarations) (t₀ : LBTerm),
      Erasure.prepare_erasure e {} { «config» := cfg } cctx ref w = .ok (pe, {}) wp
      ∧ Erases env [] [] pe t₀
      ∧ ErasesEnv env tbl.body? Γspec t₀
      ∧ Lower Γspec t₀ t
      ∧ LowerEnv Γspec Γ
      ∧ LBWfPeregrine Γ t
      ∧ ∀ (args : List Expr) (targs : List LBTerm) (I : Name) (us : List VLevel)
          (idx : List VExpr) (v : Expr) (vv vs : VExpr),
          targs.length = args.length →
          (∀ i, i < args.length → ∃ a₀, Erases env [] [] args[i]! a₀ ∧
            Lower Γspec a₀ targs[i]! ∧ ErasesEnv env tbl.body? Γspec a₀) →
          TrExprS env [] [] (mkApps pe args) vs →
          SEval env tbl.body? [] fullFlags [] (mkApps e args) v →
          TrExprS env [] [] v vv →
          env.HasType 0 [] vv (VExpr.mkApps (.const I us) idx) →
          FirstOrderInd env I →
          ∃ tv₀ tv, Erases env [] [] v tv₀ ∧ Lower Γspec tv₀ tv ∧ NoBox tv
            ∧ (∀ tv', Erases env [] [] v tv' → tv' = tv₀)
            ∧ WcbvEval Γ eraseFlags (LBTerm.mkApps t targs) tv
```

Answering the round's question directly: `hve` is discharged; of `hbridge`'s five fields, `wf`,
`simulate` and `noBox` are discharged or retired; `erasesEnv` and `lowerEnv` are **not** closed,
and §2.3 names the three measured reasons. `green_G1`–`green_G8` afterwards carry: `P`, `E`, `A`,
`htbl`, `hsafe`, `hblk`, `hcb`, `hbridge`, and the four Π-bound hypotheses of the observable
clause (`hev`, `hvwt`, `hty`, `hfo`) — the standing class-C/D set, plus `hbridge`'s two fields.

## 9. Measurements taken for this document

| Claim | Command / probe | Result |
|---|---|---|
| the `hve` recipe compiles at HEAD | `lake env lean amend6/p1_hve.lean` | two theorems, 3 axioms each, no `sorry` |
| the `Lower` transport of box-freedom | `amend6/p2_nobox.lean` | 7 declarations, proved, 3 axioms |
| `ErasesEnv` at a spine | `amend6/p3_erasesenv.lean` | 2 theorems, proved, 3 axioms |
| the capstone without `simulate`/`noBox` | `amend6/p4_capstone.lean` | proof closes; footprint the 33-name cluster plus the three probe stand-ins |
| `keys`, `declsWf` at G7 | `amend6/p5_wf.lean` | `decide +kernel`, < 1 s |
| `constsOk`, `fixLambda` at G7 | `amend6/p6_walk.lean` | `decide +kernel`, ~1 s |
| `etaCtors*` at G1, G4, G7 | `amend6/p7_ctorsat.lean` | `decide +kernel`, ~1 s |
| `casesExh`, `projDecl`, `closed`, `ctorApplied` at G7 | `amend6/p8_rest.lean` | `decide +kernel`, ~1.4 s |
| `asciiNames` refuted, per rung | `amend6/p9_ascii.lean`, `amend6/p9c.lean` | 0/1/1/1/0/0/34/34; restated clause 0 everywhere |
| all twelve clauses, all eight rungs | `amend6/p10_wfall.lean` | `decide +kernel`, 11.8 s for the file |
| G7's polymorphic and bodied declarations | `amend6/p11_tbl.lean` | 44 decls, 30 bodied, 28 polymorphic, 16 both |
| G7's projection-carrying bodies | `amend6/p12_proj.lean` | 10, all class projections; G1: 0 |
| `--dead` composition | `lake exe hygiene --dead` | 315 total; Alpha 99; `erases_correct` and both siblings dead |
