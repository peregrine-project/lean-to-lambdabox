import LeanToLambdaBox.VisitExprRefines.Motives

/-!
# The environment-facing steps of the bridge induction

`Erasure.visitConst` resolves a constant head, `Erasure.get_constant_kername` looks its
kername up, and `Erasure.visitMutual` registers the declaration behind it. These are the three
members that write the erasure state's constant registry, and their motives are the ones that
report registration rather than a term relation.

* `step5` and `step6` are the two registration steps, discharged in full.
* `visitConst_refines` is step 4's content and `step_visitConst` is its step interface:
  `Motive4` carries the constructor and type-former exclusions `Erases.const` needs, so the
  interface is `Step4` on the nose.
* `blockKeyed_install` proves the four conditions of the reader description at the pair
  `Erasure.visitMutual` installs.
* `visitExpr_runConcl` is the term walk's own state, generator and registry conclusion, which
  the two registration steps spend at the dependency bodies `Erasure.visitMutual` erases.

`Motive6` reports registration and nothing about the block's content. The sub-runs erase a
dependency at its own `levelParams`, where `BridgeInv.lparams` — the reader's level scope is
the ambient one — is unsatisfiable at a polymorphic dependency of a closed subject, so the
block's content is read off the final state by `SpecEnv` instead. That is a restriction of the
motive's shape rather than a premise, and it is why `blockKeyed_install` has no consumer
here.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean Erasure Witness Lean.Order

set_option synthInstance.maxSize 4000

/-! ## Registry plumbing -/

/-- A `Std.HashMap` `get!` at a key the `get?` finds: what turns the `panic!`-defaulting lookup
of `Erasure.get_constant_kername`'s miss branch into the kername the registry holds. -/
theorem hashMap_get!_of_get? {m : Std.HashMap Name Kername} {k : Name} {v : Kername}
    (h : m.get? k = some v) : m[k]! = v := by
  rw [Std.HashMap.getElem!_eq_get!_getElem?, show m[k]? = some v from h]
  rfl

/-- The block registration loop writes the constant registry and `gdecls` only, so a modelled
inductive registry survives it. -/
theorem indRegistryModelled_recConstState {env : VEnv} (names : List Name)
    (defs : List (@FixDef LBTerm)) {s : ErasureState} (h : IndRegistryModelled env s) :
    IndRegistryModelled env (recConstState names defs s) := by
  rw [recConstState_eq]
  have key : ∀ (l : List (Name × Nat)) (s' : ErasureState), IndRegistryModelled env s' →
      IndRegistryModelled env (l.foldl (recConstStep defs) s') := by
    intro l
    induction l with
    | nil => exact fun _ h' => h'
    | cons _ _ ih => exact fun s' h' => ih _ h'
  exact key _ _ h

/-! ## The preparation pass, run

`Erasure.prepare_erasure` is four `CoreM`-lifted passes and a `@[csimp]` walk the pinned
configuration closes. Its state half is a theorem of the run decomposition; its generator half
is `EraserAsks.passes_monotone`, one application per call.
-/

/-- **The preparation pass leaves the erasure state alone and only advances the generator.**
With the `@[csimp]` gate closed the run is exactly the four lifted calls
`run_prepare_erasure_ok` exposes, and each of the three functions it calls is a member of
`preparePasses`. -/
theorem run_prepare_erasure_concl {lenv : Environment} {env : VEnv} {Us : List Name}
    {gw : Void IO.RealWorld → NameGenerator} (E : EraserAsks lenv env Us gw) {e : Expr}
    {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
    {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld} {pe : Expr}
    {s₁ : ErasureState} {w₁ : Void IO.RealWorld} (hcs : ctx.config.csimp = false)
    (hrun : prepare_erasure e s ctx cctx ref w = .ok (pe, s₁) w₁) :
    s₁ = s ∧ gw w ≤ gw w₁ := by
  obtain ⟨rfl, e₁, e₂, e₃, v₁, v₂, v₃, h1, h2, h3, h4⟩ := run_prepare_erasure_ok hcs hrun
  refine ⟨rfl, NameGenerator.LE.trans
    (E.passes_monotone _ (by simp [preparePasses]) _ _ _ _ _ _ _ _ _ h1)
    (NameGenerator.LE.trans
      (E.passes_monotone _ (by simp [preparePasses]) _ _ _ _ _ _ _ _ _ h2)
      (NameGenerator.LE.trans
        (E.passes_monotone _ (by simp [preparePasses]) _ _ _ _ _ _ _ _ _ h3)
        (E.passes_monotone _ (by simp [preparePasses]) _ _ _ _ _ _ _ _ _ h4)))⟩

/-! ## The term walk's run conclusion

`Erasure.visitExpr` leaves the erasure state extended, the name generator advanced and a
modelled inductive registry modelled. The three facts are one `RunClosedW` instance each,
composed by `RunClosedW.and` and spent by `visitExpr_shapeW`; the pinned configuration is
what closes the `@[csimp]` branch of `Erasure.prepare_erasure` and refutes the machine-numeral
registrations of `Erasure.visitCases`.

The registration loop's own two facts come from elsewhere. That
`Lean.Compiler.LCNF.getDeclInfo?` answers at a tabled head is
`ErasureSpec.LookupAdequate.declInfo`'s `r = none` arm read against
`Witness.SourceTableAdequate`'s pin; that the head is not an `_unsafe_rec` companion is
`TableSafe.notUnsafeRec`.
-/

/-- **The registry conjunct as a `RunClosedW` instance.** Every primitive leaves the state
alone; the registration reader's two provenance arms are the `Lean.getConstInfo` run, read
through `ErasureSpec.LookupAdequate.constInfo` into `run_register_inductive_models`, and the
machine-numeral registrations, refuted by `nat = .peano`. -/
theorem runClosedW_indReg {lenv : Environment} {env : VEnv} {Us : List Name}
    {gw : Void IO.RealWorld → NameGenerator} (S : ErasureSpec lenv env Us gw)
    (E : EraserAsks lenv env Us gw) (s₀ : ErasureState) :
    RunClosedW ConfigPinned
      (fun s _ => IndRegistryModelled env s₀ → IndRegistryModelled env s) where
  oracle h hq := by rw [run_liftMetaM_state _ _ _ _ _ h]; exact hq
  inferType h hq := by rw [run_liftMetaM_state _ _ _ _ _ h]; exact hq
  constInfo h hq := by rw [run_getConstInfo_state _ _ _ _ _ h]; exact hq
  getEnv h hq := by rw [run_getEnv_state _ _ _ _ _ h]; exact hq
  logInfo h hq := by rw [run_logInfo_state _ _ _ _ _ h]; exact hq
  isInstance h hq := by rw [run_liftCoreM_state _ _ _ _ _ h]; exact hq
  fresh h hq := by rw [run_mkFreshFVarId_state _ _ _ _ _ h]; exact hq
  declInfo h hq := by rw [run_liftCoreM_state _ _ _ _ _ h]; exact hq
  ctorArity h hq := by rw [run_liftCoreM_state _ _ _ _ _ h]; exact hq
  casesInfo h hq := by rw [run_liftCoreM_state _ _ _ _ _ h]; exact hq
  inl hq := hq
  ax h hq := by rw [(run_addAxiom_ok h).1]; exact hq
  reg := by
    intro ii s ctx cctx ref w r s' w' hprov hc h hq h0
    rcases hprov with ⟨hd, sa, sb, wa, wb, hci⟩ | hmach
    · exact run_register_inductive_models S
        (S.lookup_adequate.constInfo hd cctx ref wa _ wb (pass_getConstInfo_core hci)).2
        hc (hq h0) h
    · exact absurd (hc.2.2.1.symm.trans hmach) (by simp)
  prep hc h hq := by rw [(run_prepare_erasure_concl E hc.1 h).1]; exact hq
  nrc hq _ _ _ := hq
  rc hq _ _ := fun h0 => indRegistryModelled_recConstState _ _ (hq h0)

/-- **The term walk's state, generator and registry conclusion.** The three `RunClosedW`
instances the pinned configuration admits, composed and spent at one run of
`Erasure.visitExpr`. -/
theorem visitExpr_runConcl {lenv : Environment} {env : VEnv} {Us : List Name}
    {gw : Void IO.RealWorld → NameGenerator} (S : ErasureSpec lenv env Us gw)
    (E : EraserAsks lenv env Us gw) {e : Expr} {s : ErasureState} {ctx : ErasureContext}
    {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
    {t : LBTerm} {s₁ : ErasureState} {w₁ : Void IO.RealWorld}
    (hcfg : ConfigPinned ctx.config)
    (hrun : Erasure.visitExpr e s ctx cctx ref w = .ok (t, s₁) w₁) :
    RunConcl s s₁ ∧ gw w ≤ gw w₁ ∧
      (IndRegistryModelled env s → IndRegistryModelled env s₁) := by
  have K := (visitExpr_shapeW
    (((runClosedW_runConcl (Cfg := ConfigPinned) s
        (fun hc h => (run_prepare_erasure_concl E hc.1 h).1)).and
      (runClosedW_gen S w (fun hc h => (run_prepare_erasure_concl E hc.1 h).2)
        (fun hc h => run_register_inductive_gen S hc h))).and
      (runClosedW_indReg S E s))).1
    _ _ _ _ _ _ _ _ _ hrun ⟨⟨RunConcl.rfl' s, NameGenerator.LE.rfl⟩, id⟩ hcfg
  exact ⟨K.1.1.1, K.1.1.2, K.1.2⟩

/-! ## The registration exits, decomposed

`Erasure.visitMutual` has four exits and every one of them registers the name it was called
at. The Hoare rules of `ErasureRun.lean` propagate a predicate that already holds at the
call's entry, and "`n` is in the registry" does not; so the two term-producing exits are
decomposed here, at the abstract eraser the induction hands the step.
-/

section Exits

variable {lenv : Environment} {env : VEnv} {Us : List Name}
  {gw : Void IO.RealWorld → NameGenerator} {n : Name}
  {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}

/-- **The non-recursive exit registers its name.** The body erasure and the `@[inline]`
bookkeeping tail only grow the state; the `modify` between them is the registration. -/
theorem run_nonrec_exit_reg {vE : Expr → EraseM LBTerm}
    {f : ErasureContext → ErasureContext} {e : Expr}
    {b1 b2 : ErasureContext → LBTerm → Bool} {msg1 msg2 : MessageData}
    (hpm : PrimMonotone gw) (E : EraserAsks lenv env Us gw)
    (hvE : ∀ (e' : Expr) (s' : ErasureState) (ctx' : ErasureContext)
        (w' : Void IO.RealWorld) (t : LBTerm) (s'' : ErasureState) (w'' : Void IO.RealWorld),
      ConfigPinned ctx'.config →
      vE e' s' ctx' cctx ref w' = .ok (t, s'') w'' →
      RunConcl s' s'' ∧ gw w' ≤ gw w'' ∧
        (IndRegistryModelled env s' → IndRegistryModelled env s''))
    {s : ErasureState} {ctx : ErasureContext} {w : Void IO.RealWorld}
    {u : Unit} {s₁ : ErasureState} {w₁ : Void IO.RealWorld}
    (hrun : (do
        let t ← withReader f (do let pe ← prepare_erasure e; vE pe)
        modify (fun s => { s with
          constants := s.constants.insert n (toKername n),
          gdecls := (toKername n, .constantDecl ⟨some t⟩) :: s.gdecls })
        let c ← read
        if b1 c t = true then do
          let isInst ← liftM (Lean.Meta.isInstance n)
          if isInst = true then do
            logInfo msg1
            modify (fun s => { s with inlinings := toKername n :: s.inlinings })
          else if b2 c t = true then do
            logInfo msg2
            modify (fun s => { s with inlinings := toKername n :: s.inlinings })
          else pure ()
        else pure () : EraseM Unit) s ctx cctx ref w = .ok (u, s₁) w₁)
    (hcfg : ConfigPinned ctx.config)
    (hind : IndRegistryModelled env s)
    (hf : ∀ c : ErasureContext, (f c).config = c.config) :
    (s₁.constants.get? n).isSome ∧ RunConcl s s₁ ∧ gw w ≤ gw w₁ ∧
      IndRegistryModelled env s₁ := by
  rw [run_bind_ok] at hrun
  obtain ⟨t, st, wt, hvis, hrun⟩ := hrun
  rw [run_withReader, run_bind_ok] at hvis
  obtain ⟨pe, sp, wp, hpr, hvis⟩ := hvis
  obtain ⟨hsp, hlep⟩ := run_prepare_erasure_concl E (by rw [hf]; exact hcfg.1) hpr
  subst hsp
  obtain ⟨hrct, hlet, hindt⟩ := hvE _ _ _ _ _ _ _ (by rw [hf]; exact hcfg) hvis
  rw [run_bind_ok] at hrun
  obtain ⟨u2, sm, wm, hmod, hrun⟩ := hrun
  rw [run_modify] at hmod
  cases hmod
  rw [run_bind_ok] at hrun
  obtain ⟨c2, sc, wc, hread, hrun⟩ := hrun
  rw [run_read] at hread
  cases hread
  have hP := run_inline_tail_ok' (n := n) (cctx := cctx) (ref := ref)
    (P := fun s' w' => RunConcl (nonrecConstState n t st) s' ∧ gw wt ≤ gw w' ∧
      IndRegistryModelled env s')
    (fun {s' w' kn} h => ⟨h.1.trans (runConcl_inlinings s' kn), h.2.1, h.2.2⟩)
    (fun {m u' s' s'' ctx' w' w''} hl h => by
      obtain rfl := run_logInfo_state _ _ cctx ref _ hl
      exact ⟨h.1, NameGenerator.LE.trans h.2.1 (hpm.logInfo _ _ _ _ _ _ _ _ _ hl), h.2.2⟩)
    (fun {m b s' s'' ctx' w' w''} hi h => by
      obtain rfl := run_liftCoreM_state (x := (Lean.Meta.isInstance m : CoreM Bool)) _ _ cctx ref _ hi
      exact ⟨h.1, NameGenerator.LE.trans h.2.1 (hpm.isInstance _ _ _ _ _ _ _ _ _ hi), h.2.2⟩)
    ⟨RunConcl.rfl' _, NameGenerator.LE.rfl, hindt hind⟩ hrun
  refine ⟨hP.1.le.consts (nonrecConstState_get? n t st), ?_, ?_, hP.2.2⟩
  · exact (hrct.trans (runConcl_nonrecConstState n t st)).trans hP.1
  · exact NameGenerator.LE.trans (NameGenerator.LE.trans hlep hlet) hP.2.1

/-- **The block exit registers every name of the block.** The identifier loop leaves the state
alone, the sibling loop only grows it, and the registration loop is `recConstState`. -/
theorem run_rec_exit_reg {vE : Expr → EraseM LBTerm} {names fixnames : List Name}
    {f : List FVarId → ErasureContext → ErasureContext}
    {g : ConstantInfo → ErasureContext → ErasureContext} {val : ConstantInfo → Expr}
    (E : EraserAsks lenv env Us gw)
    (hfresh : ∀ (s' : ErasureState) (ctx' : ErasureContext) (w' : Void IO.RealWorld)
        (x : FVarId) (s'' : ErasureState) (w'' : Void IO.RealWorld),
      (mkFreshFVarId : EraseM FVarId) s' ctx' cctx ref w' = .ok (x, s'') w'' → gw w' ≤ gw w'')
    (hci : ∀ (m : Name) (s' : ErasureState) (ctx' : ErasureContext) (w' : Void IO.RealWorld)
        (ci : ConstantInfo) (s'' : ErasureState) (w'' : Void IO.RealWorld),
      (getConstInfo m : EraseM ConstantInfo) s' ctx' cctx ref w' = .ok (ci, s'') w'' →
        gw w' ≤ gw w'')
    (hvE : ∀ (e' : Expr) (s' : ErasureState) (ctx' : ErasureContext)
        (w' : Void IO.RealWorld) (t : LBTerm) (s'' : ErasureState) (w'' : Void IO.RealWorld),
      ConfigPinned ctx'.config →
      vE e' s' ctx' cctx ref w' = .ok (t, s'') w'' →
      RunConcl s' s'' ∧ gw w' ≤ gw w'' ∧
        (IndRegistryModelled env s' → IndRegistryModelled env s''))
    (hmem : n ∈ fixnames)
    {s : ErasureState} {ctx : ErasureContext} {w : Void IO.RealWorld}
    {u : Unit} {s₁ : ErasureState} {w₁ : Void IO.RealWorld}
    (hrun : (do
        let ids ← names.mapM (fun _ => mkFreshFVarId)
        withReader (f ids) (do
          let defs ← names.mapM (fun m => do
            let ci ← getConstInfo m
            let t ← withReader (g ci) (do let pe ← prepare_erasure (val ci); vE pe)
            mkDef (remove_unsafe_rec m) fixnames t)
          for p in fixnames.zipIdx do
            modify (fun s => { s with
              constants := s.constants.insert p.1 (toKername p.1),
              gdecls := (toKername p.1, .constantDecl ⟨some (.fix defs p.2)⟩) :: s.gdecls })
          pure ()) : EraseM Unit) s ctx cctx ref w = .ok (u, s₁) w₁)
    (hcfg : ConfigPinned ctx.config)
    (hind : IndRegistryModelled env s)
    (hf : ∀ (ids : List FVarId) (c : ErasureContext), (f ids c).config = c.config)
    (hg : ∀ (ci : ConstantInfo) (c : ErasureContext), (g ci c).config = c.config) :
    (s₁.constants.get? n).isSome ∧ RunConcl s s₁ ∧ gw w ≤ gw w₁ ∧
      IndRegistryModelled env s₁ := by
  rw [run_bind_ok] at hrun
  obtain ⟨ids, sid, wid, hids, hrun⟩ := hrun
  have hid := run_list_mapM_ok _ cctx ref
    (P := fun (_ : List Name) (_ : List FVarId) (s' : ErasureState) (w' : Void IO.RealWorld) =>
      s' = s ∧ gw w ≤ gw w')
    ⟨rfl, NameGenerator.LE.rfl⟩
    (fun _ _ _ _ _ _ _ _ _ _ hPa hb => by
      obtain ⟨rfl, hle⟩ := hPa
      obtain rfl := run_mkFreshFVarId_state _ _ cctx ref _ hb
      exact ⟨rfl, NameGenerator.LE.trans hle (hfresh _ _ _ _ _ _ hb)⟩)
    hids
  obtain ⟨hsid, hleid⟩ := hid
  rw [run_withReader, run_bind_ok] at hrun
  obtain ⟨defs, sd, wd, hdefs, hrun⟩ := hrun
  have hsib := run_list_mapM_ok _ cctx ref
    (P := fun (_ : List Name) (_ : List (@FixDef LBTerm)) (s' : ErasureState)
        (w' : Void IO.RealWorld) => RunConcl sid s' ∧ gw wid ≤ gw w' ∧
          IndRegistryModelled env s')
    ⟨RunConcl.rfl' _, NameGenerator.LE.rfl, by rw [hsid]; exact hind⟩
    (fun _ _ _ _ _ _ _ _ _ _ hPa hb => by
      obtain ⟨hrc, hle, hindp⟩ := hPa
      rw [run_bind_ok] at hb
      obtain ⟨ci, s2, w2, hciR, hb⟩ := hb
      have hleci := hci _ _ _ _ _ _ _ hciR
      obtain hs2 := run_getConstInfo_state _ _ cctx ref _ hciR
      subst hs2
      rw [run_bind_ok] at hb
      obtain ⟨t2, s4, w4, hvis, hb⟩ := hb
      rw [run_withReader, run_bind_ok] at hvis
      obtain ⟨pe2, s3, w3, hpr, hvis⟩ := hvis
      obtain ⟨rfl, hlep⟩ := run_prepare_erasure_concl E (by rw [hg, hf]; exact hcfg.1) hpr
      obtain ⟨hrc2, hle2, hind2⟩ := hvE _ _ _ _ _ _ _ (by rw [hg, hf]; exact hcfg) hvis
      obtain ⟨-, -, rfl, rfl⟩ := run_mkDef_ok hb
      exact ⟨hrc.trans hrc2, NameGenerator.LE.trans hle
        (NameGenerator.LE.trans hleci
          (NameGenerator.LE.trans hlep hle2)), hind2 hindp⟩)
    hdefs
  rw [run_bind_ok] at hrun
  obtain ⟨u4, sf, wf, hloop, hrun⟩ := hrun
  obtain ⟨hsf, rfl⟩ := run_modify_forIn_ok hloop
  rw [run_pure] at hrun
  cases hrun
  have hreg : s₁ = recConstState fixnames defs sd := by rw [hsf]; rfl
  subst hreg
  refine ⟨recConstState_get? hmem, ?_, ?_, indRegistryModelled_recConstState _ _ hsib.2.2⟩
  · exact (hsid ▸ hsib.1 : RunConcl s sd).trans (runConcl_recConstState fixnames defs sd)
  · exact NameGenerator.LE.trans hleid hsib.2.1

/-- The registration conclusion, composed across a prefix that registered nothing. -/
theorem reg_compose {s s' s₁ : ErasureState} {w w' w₁ : Void IO.RealWorld}
    (hrc : RunConcl s s') (hle : gw w ≤ gw w')
    (h : (s₁.constants.get? n).isSome ∧ RunConcl s' s₁ ∧ gw w' ≤ gw w₁ ∧
      IndRegistryModelled env s₁) :
    (s₁.constants.get? n).isSome ∧ RunConcl s s₁ ∧ gw w ≤ gw w₁ ∧
      IndRegistryModelled env s₁ :=
  ⟨h.1, hrc.trans h.2.1, NameGenerator.LE.trans hle h.2.2.1, h.2.2.2⟩

set_option maxHeartbeats 2000000 in
theorem run_visitMutual_registers {lenv : Environment} {env : VEnv} {Us : List Name}
    {tbl : SourceTable} {s : ErasureState} {ctx : ErasureContext} {w : Void IO.RealWorld}
    {u : Unit} {s₁ : ErasureState} {w₁ : Void IO.RealWorld}
    (P : ErasureSpec lenv env Us gw) (E : EraserAsks lenv env Us gw)
    (htbl : SourceTableAdequate lenv tbl) (hsafe : TableSafe lenv tbl)
    (htab : (tbl.decl? n).isSome) (hcfg : ConfigPinned ctx.config)
    (hind : IndRegistryModelled env s)
    (hrun : visitMutual n s ctx cctx ref w = .ok (u, s₁) w₁) :
    (s₁.constants.get? n).isSome ∧ RunConcl s s₁ ∧ gw w ≤ gw w₁ ∧
      IndRegistryModelled env s₁ := by
  have hvE : ∀ (e' : Expr) (s' : ErasureState) (ctx' : ErasureContext)
      (w' : Void IO.RealWorld) (t : LBTerm) (s'' : ErasureState) (w'' : Void IO.RealWorld),
      ConfigPinned ctx'.config →
      visitExpr e' s' ctx' cctx ref w' = .ok (t, s'') w'' →
      RunConcl s' s'' ∧ gw w' ≤ gw w'' ∧
        (IndRegistryModelled env s' → IndRegistryModelled env s'') :=
    fun _ _ _ _ _ _ _ hc h => visitExpr_runConcl P E hc h
  have hfresh : ∀ (s' : ErasureState) (ctx' : ErasureContext) (w' : Void IO.RealWorld)
      (x : FVarId) (s'' : ErasureState) (w'' : Void IO.RealWorld),
      (mkFreshFVarId : EraseM FVarId) s' ctx' cctx ref w' = .ok (x, s'') w'' → gw w' ≤ gw w'' :=
    fun s' ctx' w' x s'' w'' h => (P.fresh_names s' ctx' cctx ref w' x s'' w'' h).2.2.1
  have hciM : ∀ (m : Name) (s' : ErasureState) (ctx' : ErasureContext) (w' : Void IO.RealWorld)
      (ci : ConstantInfo) (s'' : ErasureState) (w'' : Void IO.RealWorld),
      (getConstInfo m : EraseM ConstantInfo) s' ctx' cctx ref w' = .ok (ci, s'') w'' →
        gw w' ≤ gw w'' := by
    intro m s' ctx' w' ci s'' w'' h
    unfold Lean.getConstInfo at h
    rw [run_bind_ok] at h
    obtain ⟨e, s₂, w₂, henv, hk⟩ := h
    have hle := P.prim_monotone.getEnv _ _ _ _ _ _ _ _ henv
    cases hfind : e.find? m with
    | some info =>
      rw [hfind] at hk
      simp only [] at hk
      rw [run_pure] at hk
      cases hk
      exact hle
    | none =>
      rw [hfind] at hk
      simp only [] at hk
      unfold Lean.throwUnknownConstant at hk
      refine absurd hk (run_bind_ne_ok _ ctx' cctx ref w₂ ?_ _ _ _)
      intro a s₃ w₃ b s₄ w₄
      unfold Lean.throwUnknownConstantAt Lean.throwUnknownIdentifierAt
      refine run_bind_ne_ok _ ctx' cctx ref w₃ ?_ _ _ _
      intro a' s₅ w₅ b' s₆ w₆
      unfold Lean.throwErrorAt Lean.withRef
      refine run_bind_ne_ok _ ctx' cctx ref w₅ ?_ _ _ _
      intro a'' s₇ w₇ b'' s₈ w₈
      rw [run_monadRefWithRef]
      exact run_throwError_ne_ok s₇ ctx' _ ref w₇ _ _ _ _
  unfold visitMutual at hrun
  simp only [] at hrun
  rw [run_bind_ok] at hrun
  obtain ⟨di, sa, wa, hdi, hrun⟩ := hrun
  have hsa := run_liftCoreM_state (x := (Compiler.LCNF.getDeclInfo? n : CoreM _))
    _ _ cctx ref _ hdi
  subst hsa
  have hdiC := ((run_liftCoreM_ok _ _ cctx ref _).mp hdi).1
  have hmem : n ∈ di.get!.all.map remove_unsafe_rec := by
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp htab
    obtain ⟨⟨ci₁, hfind₁, -, -⟩, -⟩ :=
      htbl.decls n d (mem_of_lookup (by rwa [SourceTable.decl?] at hd))
    obtain ⟨ci₀, hci₀⟩ : ∃ ci₀, di = some ci₀ := by
      cases hdisome : di with
      | some ci₀ => exact ⟨ci₀, rfl⟩
      | none =>
        have := (P.lookup_adequate.declInfo n cctx ref w di wa hdiC).2.2 hdisome
        rw [hfind₁] at this; exact absurd this (by simp)
    have hb := ((P.lookup_adequate.declInfo n cctx ref w di wa hdiC).2.1 ci₀ hci₀).2
      (hsafe.notUnsafeRec n htab)
    simpa [hci₀] using hb
  have hlea : gw w ≤ gw wa := (P.lookup_adequate.declInfo n cctx ref w di wa hdiC).1
  rw [run_bind_ok] at hrun
  obtain ⟨env0, sb, wb, henv0, hrun⟩ := hrun
  have hsb := run_getEnv_state _ _ cctx ref _ henv0
  subst hsb
  have hleb : gw w ≤ gw wb :=
    NameGenerator.LE.trans hlea (P.prim_monotone.getEnv _ _ _ _ _ _ _ _ henv0)
  clear hdi henv0
  refine reg_compose (RunConcl.rfl' _) hleb ?_
  split at hrun
  case isFalse =>
    split at hrun
    · exact run_nonrec_exit_reg P.prim_monotone E hvE hrun hcfg hind (fun _ => rfl)
    · exact run_rec_exit_reg E hfresh hciM hvE hmem hrun hcfg hind (fun _ _ => rfl)
        (fun _ _ => rfl)
  case isTrue =>
    obtain ⟨s₀, w₀, u₀, hpre, hm⟩ := run_inline_prefix_decomp' hrun
    have hpc : RunConcl sb s₀ ∧ gw wb ≤ gw w₀ ∧ IndRegistryModelled env s₀ := by
      rcases hpre with ⟨rfl, rfl⟩ | ⟨u', hlog, rfl⟩
      · exact ⟨RunConcl.rfl' _, NameGenerator.LE.rfl, hind⟩
      · exact ⟨runConcl_inlinings _ _, P.prim_monotone.logInfo _ _ _ _ _ _ _ _ _ hlog, hind⟩
    refine reg_compose hpc.1 hpc.2.1 ?_
    rw [run_bind_ok] at hm
    obtain ⟨env2, se, we, henv2, hm⟩ := hm
    have hse := run_getEnv_state _ _ cctx ref _ henv2
    subst hse
    have hlee : gw w₀ ≤ gw we := P.prim_monotone.getEnv _ _ _ _ _ _ _ _ henv2
    rw [run_bind_ok] at hm
    obtain ⟨c1, sr, wr, hread, hm⟩ := hm
    rw [run_read] at hread
    cases hread
    cases hval : di.get!.value? (allowOpaque := true) <;>
      cases hext : isExtern env2 n <;>
        cases hcfgx : ctx.config.extern <;>
          simp only [hval, hext, hcfgx] at hm
    all_goals
      try
        (rw [run_bind_ok] at hm
         obtain ⟨u3, s3, w3, hlogr, hm⟩ := hm
         have hz2 := run_logInfo_state _ _ cctx ref _ hlogr
         subst hz2
         replace hlee := NameGenerator.LE.trans hlee
           (P.prim_monotone.logInfo _ _ _ _ _ _ _ _ _ hlogr))
    all_goals
      first
        | (obtain ⟨hstA, hwA⟩ := run_addAxiom_ok hm
           subst hstA
           subst hwA
           exact ⟨addAxiomState_get? n _, runConcl_addAxiomState n _, hlee, hpc.2.2⟩)
        | (refine reg_compose (RunConcl.rfl' _) hlee ?_
           split at hm
           · exact run_nonrec_exit_reg P.prim_monotone E hvE hm hcfg hpc.2.2
               (fun _ => rfl)
           · exact run_rec_exit_reg E hfresh hciM hvE hmem hm hcfg hpc.2.2
               (fun _ _ => rfl) (fun _ _ => rfl))

end Exits

/-! ## The installed block's keying -/

/-- **The pair `Erasure.visitMutual` installs is `BlockKeyed`.** The reader equation is the
`withReader` the block branch runs under, the length is the identifier loop's, the distinctness
is `EraserAsks.block_keys_distinct` read back through `toKername`, and the separation is the
table's own key separation against `TableBlocks.members`. `hfb` is the correspondence between
the run's `Lean.Compiler.LCNF.getDeclInfo?` answer and `Witness.fixBlock?`, which no clause of
the specification bundle supplies. -/
theorem blockKeyed_install {lenv : Environment} {env : VEnv} {Us : List Name}
    {gw : Void IO.RealWorld → NameGenerator} {tbl : SourceTable} {ctx : ErasureContext}
    {n : Name} {e : Expr} {ci : ConstantInfo} {ids : List FVarId} {cctx : Core.Context}
    {ref : ST.Ref IO.RealWorld Core.State} {w w₁ : Void IO.RealWorld}
    (E : EraserAsks lenv env Us gw) (hblk : TableBlocks lenv env tbl)
    (hsup : Supported env tbl e) (htab : (tbl.decl? n).isSome)
    (hdi : (Lean.Compiler.LCNF.getDeclInfo? n : CoreM (Option ConstantInfo)) cctx ref w
      = .ok (some ci) w₁)
    (hfb : fixBlock? lenv n = some (ci.all.map remove_unsafe_rec))
    (hlen : ids.length = ci.all.length)
    (hfx : ctx.fixvars = some (fixvarMap (ci.all.map remove_unsafe_rec) ids)) :
    BlockKeyed tbl ctx (ci.all.map remove_unsafe_rec) ids := by
  refine ⟨hfx, by simp [hlen], List.Pairwise.of_map toKername
    (fun _ _ hne hab => hne (congrArg toKername hab))
    (E.block_keys_distinct n cctx ref w ci w₁ hdi), ?_⟩
  intro m htm hin
  obtain ⟨m', hm', hkey⟩ := List.mem_map.mp hin
  have heq : m = m' := hsup.kernames m m' htm (hblk.members n _ htab hfb m' hm') hkey.symm
  rw [heq]
  exact hm'

/-! ## The two registration steps -/

section Steps

variable {lenv : Environment} {env : VEnv} {Us : List Name} {tbl : SourceTable}
  {cfg : ErasureConfig} {gw : Void IO.RealWorld → NameGenerator}

/-- **Step 5.** The hit branch reads the registry, whose kernames are canonical by the
invariant; the miss branch registers the name through `Erasure.visitMutual` and then reads it
back, which is what makes the `panic!`-defaulting lookup total and canonical. -/
theorem step5 : Step5 lenv env Us tbl cfg gw := by
  intro _P _htbl _hcfg _hcb vMut m6
  refine ⟨?_, bodyLe5 m6.2⟩
  intro n s ctx cctx ref w kn s' w' hrun Δ hinv hsup htab
  unfold getConstantKernameBody at hrun
  rw [run_bind_ok] at hrun
  obtain ⟨s₀, sa, wa, hget, hk⟩ := hrun
  rw [run_get] at hget
  cases hget
  cases hc : s.constants.get? n with
  | some kn₀ =>
      rw [hc] at hk
      simp only [] at hk
      rw [run_pure] at hk
      cases hk
      exact ⟨hinv.canon hc, by rw [hc]; simp, RunConcl.rfl' _, hinv.indcanon,
        NameGenerator.LE.rfl⟩
  | none =>
      rw [hc] at hk
      simp only [] at hk
      rw [run_bind_ok] at hk
      obtain ⟨uu, sb, wb, hvm, hk2⟩ := hk
      rw [run_bind_ok] at hk2
      obtain ⟨sc, sd, wd, hget2, hp⟩ := hk2
      rw [run_get] at hget2
      cases hget2
      rw [run_pure] at hp
      cases hp
      obtain ⟨hdom, hrc, hreg, hle⟩ := m6.1 _ _ _ _ _ _ _ _ _ hvm Δ hinv hsup htab
      obtain ⟨kn₀, hkn₀⟩ := Option.isSome_iff_exists.mp hdom
      exact ⟨by rw [hashMap_get!_of_get? hkn₀]; exact hrc.canon hinv.canon hkn₀, hdom, hrc,
        hreg, hle⟩

/-- **Step 6.** All four exits of `Erasure.visitMutual` register the name it was called at, and
the term walk's own run conclusion is what carries the state and generator facts across the
body erasures. `Motive1`'s refinement half is not consumed: what the motive reports is
registration, and the fragment and translation premises a body erasure would need are not
available at a dependency's own level scope. -/
theorem step6 (E : EraserAsks lenv env Us gw) (hsafe : TableSafe lenv tbl) :
    Step6 lenv env Us tbl cfg gw := by
  intro P htbl hcfg _hcb vExpr m1
  refine ⟨?_, bodyLe6 m1.2⟩
  intro n s ctx cctx ref w u s' w' hrun Δ hinv _hsup htab
  have hrun' := run_ok_of_le₁ (bodyLe6 m1.2) hrun
  obtain ⟨hdom, hrc, hle, hreg⟩ := run_visitMutual_registers P E htbl hsafe htab
    (by rw [hinv.cfg]; exact hcfg) hinv.indcanon hrun'
  exact ⟨hdom, hrc, hreg, hle⟩

end Steps

/-! ## The environment gap at a tabled constant -/

/-- **A constant the compiler table gives a body for is a plain constant of the model.**
Composed from the two halves that surround the gap ask 4 leaves open: `constants_of_tabled`
puts the name in the model, `constOrigin_of_constants` classifies it. The two exclusions are
premises because no theorem at the pin transfers a constant's *kind* from `lenv` to the model
(`doc/upstream-asks.md` item 4); that is the same place `SpecEnv.erasesEnv`'s `htab` stands. -/
theorem env_motive_tabled {lenv : Environment} {env : VEnv} {Us : List Name}
    {gw : Void IO.RealWorld → NameGenerator} {tbl : SourceTable}
    (P : ErasureSpec lenv env Us gw) (ht : SourceTableAdequate lenv tbl)
    (hsafe : TableSafe lenv tbl) (A : UpstreamAsks env) {c : Name} {b : Expr}
    (hnc : ∀ I k, ¬ CtorOf env c I k) (hni : ∀ iid np nfs, ¬ IndInfo env c iid np nfs)
    (hb : tbl.body? c = some b) : ConstOrigin env c := by
  obtain ⟨vc, hvc⟩ := constants_of_tabled P ht hsafe hb
  exact constOrigin_of_constants A hvc hnc hni

/-! ## What a specification environment says about a runtime key -/

/-- **A runtime key belongs to a `casesOn` constant**, read off the entries rather than off a
program's reachability: a tabled constant's entry is an erasure image and no erasure image is
an `ElimBody`, and a body-less non-eliminator's entry is `⟨none⟩`. The `ErasesEnv` twin is
`ErasesEnv.runtimeKey_isCasesOn`; this is the `SpecContent` one, which is what a motive holding
a `SpecEnv` and no program has. -/
theorem SpecContent.runtimeKey_isCasesOn {env : VEnv} {bo : Name → Option Expr}
    {lp : Name → List Name} {Γspec : GlobalDeclarations} (H : SpecContent env bo lp Γspec)
    {c : Name}
    (hco : ConstOrigin env c) (hrk : RuntimeKey Γspec (toKername c)) :
    isCasesOnName c = true := by
  obtain ⟨iid, np, dp, nfs, ⟨body, hlook, helim⟩, -⟩ := hrk
  by_cases hb : ∃ b, bo c = some b
  · obtain ⟨b, hb⟩ := hb
    obtain ⟨b₀, hlook', her⟩ := H.defns c b hb (by rw [hlook]; simp)
    rw [hlook] at hlook'
    cases hlook'
    exact absurd (erases_ne_elimBody her (iid := iid) (np := np) (dp := dp) (nfs := nfs))
      (by simpa using helim)
  · have hnone : bo c = none := by
      cases hbo : bo c with
      | none => rfl
      | some b => exact absurd ⟨b, hbo⟩ hb
    by_cases hcas : isCasesOnName c = true
    · exact hcas
    · have := H.axioms c hnone hco (by simpa using hcas) (by rw [hlook]; simp)
      rw [hlook] at this
      exact absurd this (by simp)

/-- A plain constant of the fragment is not a runtime key of any specification environment. -/
theorem specEnv_not_runtimeKey {env : VEnv} {bo : Name → Option Expr}
    {lp : Name → List Name} {Γspec : GlobalDeclarations} (H : SpecContent env bo lp Γspec)
    {c : Name}
    (hco : ConstOrigin env c) (hcas : isCasesOnName c = false) :
    ¬ RuntimeKey Γspec (toKername c) := by
  intro hrk
  rw [H.runtimeKey_isCasesOn hco hrk] at hcas
  exact absurd hcas (by simp)

/-! ## Step 4

`Erases.const` asks for `ConstOrigin`, which `KnownHead`'s three columns do not settle: the
constructor and type-former columns are ruled out by `Motive4`'s own exclusions, which the
run's callers produce — the constructor one from `Erasure.visitConstApp`'s
`Lean.Compiler.LCNF.getCtorArity?` miss, the type-former one from the relevance oracle's
`false` verdict. `visitConst_refines` is the content, at the model facts the constant branch
reads; `step_visitConst` is the step interface.
-/

/-- **Step 4's content.** The block branch returns the member's fix variable, which is
`ErasesLBFix.fixvar`; the plain branch returns the canonical kername, which is `Erases.const`
composed with `Lower.const` — and inside a block, with `ConstToFVar.miss`. -/
theorem visitConst_refines {env : VEnv} {Us : List Name} {tbl : SourceTable}
    {cfg : ErasureConfig} {gw : Void IO.RealWorld → NameGenerator}
    {vGck : Name → EraseM Kername} (m5 : Motive5 env Us tbl cfg gw vGck) :
    ∀ (e : Expr) (s : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
      (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) (t : LBTerm)
      (s' : ErasureState) (w' : Void IO.RealWorld),
      visitConstBody vGck e s ctx cctx ref w = .ok (t, s') w' →
      ∀ (Δ : VLCtx) (n : Name) (us : List Level) (ci : VConstant),
        BridgeInv env Us tbl cfg (gw w) ctx s Δ → e = .const n us →
        isCasesOnName n = false → env.constants n = some ci → ConstOrigin env n →
        (tbl.decl? n).isSome → Supported env tbl e →
        RunConcl s s' ∧ IndRegistryModelled env s' ∧ gw w ≤ gw w' ∧
          ∀ Γspec, SpecEnv env tbl.body? tbl.levels? s' Γspec →
            ErasesLBMode tbl ctx env Us Γspec Δ e t := by
  intro e s ctx cctx ref w t s' w' hrun Δ n us ci hinv he hcas hcst hco htab hsup
  subst he
  have hsupc : Supported env tbl (.const n []) :=
    hsup.subterm (by simp [constNames]) (by
      cases hsup.term with
      | const hp hc hr hs hk => exact .const hp hc hr (by simpa [CtorSaturated] using hs) hk
      | casesApp _ _ _ _ harity => simp at harity)
  simp only [visitConstBody] at hrun
  rw [run_bind_ok] at hrun
  obtain ⟨c, s₁, w₁, hrd, hk⟩ := hrun
  rw [run_read] at hrd
  cases hrd
  cases hopt : ctx.fixvars.bind (fun hmap => hmap[n]?) with
  | some id =>
      rw [hopt] at hk
      simp only [] at hk
      rw [run_pure] at hk
      cases hk
      refine ⟨RunConcl.rfl' _, hinv.indcanon, NameGenerator.LE.rfl,
        fun Γspec hspec => ⟨?_, ?_⟩⟩
      · intro hnone; rw [hnone] at hopt; simp at hopt
      · intro nms ids hbk
        rw [hbk.1] at hopt
        simp only [Option.bind_some] at hopt
        obtain ⟨j, hj1, hj2⟩ := fixvarMap_get?_some hopt
        exact ErasesLBFix.fixvar (by rw [List.getElem?_map, hj1]; rfl) hj2
          (specEnv_not_runtimeKey hspec.spec hco hcas) hcst hco
  | none =>
      rw [hopt] at hk
      simp only [] at hk
      rw [run_bind_ok] at hk
      obtain ⟨kn, s₂, w₂, hgck, hp⟩ := hk
      rw [run_pure] at hp
      cases hp
      obtain ⟨hkn, hdom, hrc, hreg, hle⟩ := m5.1 _ _ _ _ _ _ _ _ _ hgck Δ hinv hsupc htab
      subst hkn
      refine ⟨hrc, hreg, hle, fun Γspec hspec => ⟨?_, ?_⟩⟩
      · intro _
        exact ⟨.const (toKername n), .const hcst hco,
          .const (specEnv_not_runtimeKey hspec.spec hco hcas)⟩
      · intro nms ids hbk
        refine ErasesLBFix.of_erasesLB ⟨.const (toKername n), .const hcst hco,
          .const (specEnv_not_runtimeKey hspec.spec hco hcas)⟩ (.miss ?_)
        intro hin
        rw [hbk.1] at hopt
        simp only [Option.bind_some] at hopt
        exact fixvarMap_get?_none (Nat.le_of_eq hbk.2.1) hopt (hbk.2.2.2 n htab hin)

/-- **Step 4.** With `Motive4`'s two exclusions the head is the `defn` column of `KnownHead`,
whose `VEnv.contains` and `SourceTable.decl?` are exactly what `visitConst_refines` reads. -/
theorem step_visitConst {lenv : Environment} {env : VEnv} {Us : List Name}
    {tbl : SourceTable} {cfg : ErasureConfig} {gw : Void IO.RealWorld → NameGenerator}
    (A : UpstreamAsks env) : Step4 lenv env Us tbl cfg gw := by
  intro _P _htbl _hcfg _hcb vGck m5
  refine ⟨?_, bodyLe4 m5.2⟩
  intro e s ctx cctx ref w t s' w' hrun Δ nm us hinv he _hplain hcas hkn hsup hnc hni
  obtain ⟨vc, hvc, hco, htab⟩ :
      ∃ vc, env.constants nm = some vc ∧ ConstOrigin env nm ∧ (tbl.decl? nm).isSome := by
    cases hkn with
    | indType _ hm => obtain ⟨iid, np, nfs, h⟩ := hm; exact absurd h (hni iid np nfs)
    | ctor _ hm => obtain ⟨I, k, h⟩ := hm; exact absurd h (hnc I k)
    | defn hd hm =>
        obtain ⟨vc, hvc⟩ := hm
        exact ⟨vc, hvc, constOrigin_of_constants A hvc hnc hni, by rw [hd]; simp⟩
  exact visitConst_refines m5 e s ctx cctx ref w t s' w' hrun Δ nm us vc hinv he hcas hvc hco
    htab hsup

/-! ## Why the block conjunct is keyed

The unkeyed conjunct is read at **every** pair of lists `fixvarMap` re-assembles the reader's
map from, and `List.zip` truncates, so a name list one longer than the identifier list presents
the same map. At that pair the last kername has no identifier, so `ConstToFVar` relates nothing
to a constant target: the unkeyed conjunct is unsatisfiable whenever the emitted term is a
`.const`, which is what the plain branch of `Erasure.visitConst` emits. `BlockKeyed` excludes
that pair by its length condition, and its separation conjunct is restricted to the tabled
names because `toKername` is not injective.
-/

/-- **The unkeyed block conjunct is unsatisfiable at a constant target.** At the pair that
appends the target's own name to the name list, the emitted `.const` is neither a `hit` — there
is no identifier at that index — nor a `miss` — the kername is in the list. It is the reason
`BlockKeyed`'s **length** condition is there, and `blockKeyed_append_absurd` is that condition
excluding this pair. -/
theorem erasesLBMode_block_refuted {env : VEnv} {Us : List Name}
    {Γspec : GlobalDeclarations} {Δ : VLCtx} {ctx : ErasureContext} {e : Expr}
    {nms : List Name} {ids : List FVarId} (c : Name) (hlen : ids.length ≤ nms.length)
    (hfx : ctx.fixvars = some (fixvarMap nms ids)) :
    ¬ ∀ (nms' : List Name) (ids' : List FVarId),
        ctx.fixvars = some (fixvarMap nms' ids') →
        ErasesLBFix env Us Γspec (nms'.map toKername) ids' Δ e (.const (toKername c)) := by
  intro h
  obtain ⟨t₀, t₁, -, -, hc⟩ :=
    h (nms ++ [c]) ids (by rw [hfx, fixvarMap_append_left c hlen])
  cases hc with
  | miss hnm => exact hnm (by simp)

/-- **The refuting pair is not `BlockKeyed`.** Its name list is one longer than its identifier
list, so `BlockKeyed`'s length condition excludes it and `erasesLBMode_block_refuted` does not
reach the keyed conjunct. -/
theorem blockKeyed_append_absurd {tbl : SourceTable} {ctx : ErasureContext} {nms : List Name}
    {ids : List FVarId} (c : Name) (hlen : ids.length ≤ nms.length) :
    ¬ BlockKeyed tbl ctx (nms ++ [c]) ids := by
  intro h
  have hl := h.2.1
  simp only [List.length_append, List.length_cons, List.length_nil] at hl
  omega

/-- **`toKername` is not injective**, so a name outside the block can still carry a block
member's kername. That is why `BlockKeyed`'s separation conjunct is quantified over the tabled
names, and it is a finding about the shipping printer: two Lean constants with one λ□ key
shadow each other in the emitted environment. -/
theorem toKername_not_injective :
    toKername (.num .anonymous 5) = toKername (.str .anonymous "5") ∧
      (Name.num .anonymous 5) ≠ (Name.str .anonymous "5") :=
  ⟨rfl, by decide⟩

end LeanToLambdaBox
