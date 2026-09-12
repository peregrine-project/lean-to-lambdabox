import LeanToLambdaBox.VisitExprRefines.Motives

/-!
# The environment-facing steps of the bridge induction

`Erasure.visitConst` resolves a constant head, `Erasure.get_constant_kername` looks its
kername up, and `Erasure.visitMutual` registers the declaration behind it. These are the three
members that write the erasure state's constant registry, and their motives are the ones that
report registration rather than a term relation.

* `step5` and `step6` are the two registration steps, discharged in full.
* `visitConst_refines` is step 4's content. `Step4` itself is **not** delivered: `Motive4` is
  false as stated — at a constructor or type-former head, and at every block reader
  (`erasesLBMode_block_refuted`) — so the content is delivered with those gaps as explicit
  premises.
* Four facts about impure primitives that no clause of `ErasureSpec` carries are named here and
  taken as premises; each docstring says what it would be as an `ErasureSpec` field.
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

/-! ## The primitives the specification bundle does not carry

`ErasureSpec` specifies the four environment queries, the fresh-name source and the relevance
oracle. `Erasure.visitMutual`'s registration path calls four more impure things, and each of
the four facts below is what an `ErasureSpec` field for it would say. They are premises of the
step lemmas that need them, in the idiom `InferTypeMonotone` uses for `Lean.Meta.inferType`.
-/

/-- The three state-transparent `CoreM` calls on the registration path — `Lean.getEnv`,
`Lean.logInfo` and `Lean.Meta.isInstance` — only advance the name generator. Class **D**: the
generator is read out of `IO.RealWorld`, which no term denotes. -/
def CoreCallsMonotone (gw : Void IO.RealWorld → NameGenerator) : Prop :=
  (∀ (s : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
      (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) (e : Environment)
      (s₁ : ErasureState) (w₁ : Void IO.RealWorld),
      (getEnv : EraseM Environment) s ctx cctx ref w = .ok (e, s₁) w₁ → gw w ≤ gw w₁) ∧
  (∀ (m : MessageData) (s : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
      (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) (u : Unit)
      (s₁ : ErasureState) (w₁ : Void IO.RealWorld),
      (logInfo m : EraseM Unit) s ctx cctx ref w = .ok (u, s₁) w₁ → gw w ≤ gw w₁) ∧
  (∀ (nm : Name) (s : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
      (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) (b : Bool)
      (s₁ : ErasureState) (w₁ : Void IO.RealWorld),
      (liftM (Lean.Meta.isInstance nm) : EraseM Bool) s ctx cctx ref w = .ok (b, s₁) w₁ →
        gw w ≤ gw w₁)

/-- `Erasure.prepare_erasure` leaves the erasure state alone and only advances the generator.
Class **D**: its `csimp` branch runs `Lean.Core.transform` at `EraseM` through
`MonadControlT`, so its state transparency does not follow from the `liftM` run lemmas. -/
def PrepareRunConcl (gw : Void IO.RealWorld → NameGenerator) : Prop :=
  ∀ (e : Expr) (s : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) (pe : Expr)
    (s₁ : ErasureState) (w₁ : Void IO.RealWorld),
    prepare_erasure e s ctx cctx ref w = .ok (pe, s₁) w₁ → s₁ = s ∧ gw w ≤ gw w₁

/-- The term walk's state and generator conclusion, unconditionally. This is the
`Erasure.visitExpr` half of the unconditional shape induction (`erase_run_ok`), which is a
second induction over the same eighteen-member family; it is a premise here so that the
registration step does not depend on the order the two inductions land in. -/
def VisitExprRunConcl (gw : Void IO.RealWorld → NameGenerator) : Prop :=
  ∀ (e : Expr) (s : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) (t : LBTerm)
    (s₁ : ErasureState) (w₁ : Void IO.RealWorld),
    Erasure.visitExpr e s ctx cctx ref w = .ok (t, s₁) w₁ → RunConcl s s₁ ∧ gw w ≤ gw w₁

/-- The code generator answers for a name of the fragment, and the block it reports contains
that name, modulo the `_unsafe_rec` renaming `Erasure.remove_unsafe_rec` undoes. Class **D**,
and the clause `ErasureSpec.LookupAdequate.declInfo` is missing: `declInfo` pins only that a
non-`none` answer is a name `lenv` knows, while the registration conclusion of
`Erasure.visitMutual`'s block exit is about the names the block registers. -/
def DeclBlockMember (env : VEnv) (tbl : SourceTable) : Prop :=
  ∀ (n : Name) (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld) (r : Option ConstantInfo) (w₁ : Void IO.RealWorld),
    KnownHead env tbl n →
    (Lean.Compiler.LCNF.getDeclInfo? n : CoreM (Option ConstantInfo)) cctx ref w = .ok r w₁ →
      n ∈ r.get!.all.map remove_unsafe_rec


/-! ## The registration exits, decomposed

`Erasure.visitMutual` has four exits and every one of them registers the name it was called
at. The Hoare rules of `ErasureRun.lean` propagate a predicate that already holds at the
call's entry, and "`n` is in the registry" does not; so the two term-producing exits are
decomposed here, at the abstract eraser the induction hands the step.
-/

section Exits

variable {gw : Void IO.RealWorld → NameGenerator} {n : Name}
  {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}

/-- **The non-recursive exit registers its name.** The body erasure and the `@[inline]`
bookkeeping tail only grow the state; the `modify` between them is the registration. -/
theorem run_nonrec_exit_reg {vE : Expr → EraseM LBTerm}
    {f : ErasureContext → ErasureContext} {e : Expr}
    {b1 b2 : ErasureContext → LBTerm → Bool} {msg1 msg2 : MessageData}
    (hbk : CoreCallsMonotone gw) (hprep : PrepareRunConcl gw)
    (hvE : ∀ (e' : Expr) (s' : ErasureState) (ctx' : ErasureContext)
        (w' : Void IO.RealWorld) (t : LBTerm) (s'' : ErasureState) (w'' : Void IO.RealWorld),
      vE e' s' ctx' cctx ref w' = .ok (t, s'') w'' → RunConcl s' s'' ∧ gw w' ≤ gw w'')
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
        else pure () : EraseM Unit) s ctx cctx ref w = .ok (u, s₁) w₁) :
    (s₁.constants.get? n).isSome ∧ RunConcl s s₁ ∧ gw w ≤ gw w₁ := by
  rw [run_bind_ok] at hrun
  obtain ⟨t, st, wt, hvis, hrun⟩ := hrun
  rw [run_withReader, run_bind_ok] at hvis
  obtain ⟨pe, sp, wp, hpr, hvis⟩ := hvis
  obtain ⟨hsp, hlep⟩ := hprep _ _ _ _ _ _ _ _ _ hpr
  subst hsp
  obtain ⟨hrct, hlet⟩ := hvE _ _ _ _ _ _ _ hvis
  rw [run_bind_ok] at hrun
  obtain ⟨u2, sm, wm, hmod, hrun⟩ := hrun
  rw [run_modify] at hmod
  cases hmod
  rw [run_bind_ok] at hrun
  obtain ⟨c2, sc, wc, hread, hrun⟩ := hrun
  rw [run_read] at hread
  cases hread
  have hP := run_inline_tail_ok' (n := n) (cctx := cctx) (ref := ref)
    (P := fun s' w' => RunConcl (nonrecConstState n t st) s' ∧ gw wt ≤ gw w')
    (fun {s' w' kn} h => ⟨h.1.trans (runConcl_inlinings s' kn), h.2⟩)
    (fun {m u' s' s'' ctx' w' w''} hl h => by
      obtain rfl := run_logInfo_state _ _ cctx ref _ hl
      exact ⟨h.1, NameGenerator.LE.trans h.2 (hbk.2.1 _ _ _ _ _ _ _ _ _ hl)⟩)
    (fun {m b s' s'' ctx' w' w''} hi h => by
      obtain rfl := run_liftCoreM_state (x := (Lean.Meta.isInstance m : CoreM Bool)) _ _ cctx ref _ hi
      exact ⟨h.1, NameGenerator.LE.trans h.2 (hbk.2.2 _ _ _ _ _ _ _ _ _ hi)⟩)
    ⟨RunConcl.rfl' _, NameGenerator.LE.rfl⟩ hrun
  refine ⟨hP.1.le.consts (nonrecConstState_get? n t st), ?_, ?_⟩
  · exact (hrct.trans (runConcl_nonrecConstState n t st)).trans hP.1
  · exact NameGenerator.LE.trans (NameGenerator.LE.trans hlep hlet) hP.2

/-- **The block exit registers every name of the block.** The identifier loop leaves the state
alone, the sibling loop only grows it, and the registration loop is `recConstState`. -/
theorem run_rec_exit_reg {vE : Expr → EraseM LBTerm} {names fixnames : List Name}
    {f : List FVarId → ErasureContext → ErasureContext}
    {g : ConstantInfo → ErasureContext → ErasureContext} {val : ConstantInfo → Expr}
    (hprep : PrepareRunConcl gw)
    (hfresh : ∀ (s' : ErasureState) (ctx' : ErasureContext) (w' : Void IO.RealWorld)
        (x : FVarId) (s'' : ErasureState) (w'' : Void IO.RealWorld),
      (mkFreshFVarId : EraseM FVarId) s' ctx' cctx ref w' = .ok (x, s'') w'' → gw w' ≤ gw w'')
    (hci : ∀ (m : Name) (s' : ErasureState) (ctx' : ErasureContext) (w' : Void IO.RealWorld)
        (ci : ConstantInfo) (s'' : ErasureState) (w'' : Void IO.RealWorld),
      (getConstInfo m : EraseM ConstantInfo) s' ctx' cctx ref w' = .ok (ci, s'') w'' →
        gw w' ≤ gw w'')
    (hvE : ∀ (e' : Expr) (s' : ErasureState) (ctx' : ErasureContext)
        (w' : Void IO.RealWorld) (t : LBTerm) (s'' : ErasureState) (w'' : Void IO.RealWorld),
      vE e' s' ctx' cctx ref w' = .ok (t, s'') w'' → RunConcl s' s'' ∧ gw w' ≤ gw w'')
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
          pure ()) : EraseM Unit) s ctx cctx ref w = .ok (u, s₁) w₁) :
    (s₁.constants.get? n).isSome ∧ RunConcl s s₁ ∧ gw w ≤ gw w₁ := by
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
        (w' : Void IO.RealWorld) => RunConcl sid s' ∧ gw wid ≤ gw w')
    ⟨RunConcl.rfl' _, NameGenerator.LE.rfl⟩
    (fun _ _ _ _ _ _ _ _ _ _ hPa hb => by
      obtain ⟨hrc, hle⟩ := hPa
      rw [run_bind_ok] at hb
      obtain ⟨ci, s2, w2, hciR, hb⟩ := hb
      have hleci := hci _ _ _ _ _ _ _ hciR
      obtain hs2 := run_getConstInfo_state _ _ cctx ref _ hciR
      subst hs2
      rw [run_bind_ok] at hb
      obtain ⟨t2, s4, w4, hvis, hb⟩ := hb
      rw [run_withReader, run_bind_ok] at hvis
      obtain ⟨pe2, s3, w3, hpr, hvis⟩ := hvis
      obtain ⟨rfl, hlep⟩ := hprep _ _ _ _ _ _ _ _ _ hpr
      obtain ⟨hrc2, hle2⟩ := hvE _ _ _ _ _ _ _ hvis
      obtain ⟨-, -, rfl, rfl⟩ := run_mkDef_ok hb
      exact ⟨hrc.trans hrc2, NameGenerator.LE.trans hle
        (NameGenerator.LE.trans hleci
          (NameGenerator.LE.trans hlep hle2))⟩)
    hdefs
  rw [run_bind_ok] at hrun
  obtain ⟨u4, sf, wf, hloop, hrun⟩ := hrun
  obtain ⟨hsf, rfl⟩ := run_modify_forIn_ok hloop
  rw [run_pure] at hrun
  cases hrun
  have hreg : s₁ = recConstState fixnames defs sd := by rw [hsf]; rfl
  subst hreg
  refine ⟨recConstState_get? hmem, ?_, ?_⟩
  · exact (hsid ▸ hsib.1 : RunConcl s sd).trans (runConcl_recConstState fixnames defs sd)
  · exact NameGenerator.LE.trans hleid hsib.2

/-- The registration conclusion, composed across a prefix that registered nothing. -/
theorem reg_compose {s s' s₁ : ErasureState} {w w' w₁ : Void IO.RealWorld}
    (hrc : RunConcl s s') (hle : gw w ≤ gw w')
    (h : (s₁.constants.get? n).isSome ∧ RunConcl s' s₁ ∧ gw w' ≤ gw w₁) :
    (s₁.constants.get? n).isSome ∧ RunConcl s s₁ ∧ gw w ≤ gw w₁ :=
  ⟨h.1, hrc.trans h.2.1, NameGenerator.LE.trans hle h.2.2⟩

set_option maxHeartbeats 2000000 in
theorem run_visitMutual_registers {lenv : Environment} {env : VEnv} {Us : List Name}
    {tbl : SourceTable} {s : ErasureState} {ctx : ErasureContext} {w : Void IO.RealWorld}
    {u : Unit} {s₁ : ErasureState} {w₁ : Void IO.RealWorld}
    (P : ErasureSpec lenv env Us gw) (hbk : CoreCallsMonotone gw)
    (hprep : PrepareRunConcl gw) (hve : VisitExprRunConcl gw)
    (hblk : DeclBlockMember env tbl) (hkn : KnownHead env tbl n)
    (hrun : visitMutual n s ctx cctx ref w = .ok (u, s₁) w₁) :
    (s₁.constants.get? n).isSome ∧ RunConcl s s₁ ∧ gw w ≤ gw w₁ := by
  have hvE : ∀ (e' : Expr) (s' : ErasureState) (ctx' : ErasureContext)
      (w' : Void IO.RealWorld) (t : LBTerm) (s'' : ErasureState) (w'' : Void IO.RealWorld),
      visitExpr e' s' ctx' cctx ref w' = .ok (t, s'') w'' → RunConcl s' s'' ∧ gw w' ≤ gw w'' :=
    fun e' s' ctx' w' t s'' w'' h => hve _ _ _ _ _ _ _ _ _ h
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
    have hle := hbk.1 _ _ _ _ _ _ _ _ henv
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
  have hmem : n ∈ di.get!.all.map remove_unsafe_rec := hblk _ _ _ _ _ _ hkn hdiC
  have hlea : gw w ≤ gw wa := (P.lookup_adequate.declInfo n cctx ref w di wa hdiC).1
  rw [run_bind_ok] at hrun
  obtain ⟨env0, sb, wb, henv0, hrun⟩ := hrun
  have hsb := run_getEnv_state _ _ cctx ref _ henv0
  subst hsb
  have hleb : gw w ≤ gw wb :=
    NameGenerator.LE.trans hlea (hbk.1 _ _ _ _ _ _ _ _ henv0)
  clear hdi henv0
  refine reg_compose (RunConcl.rfl' _) hleb ?_
  split at hrun
  case isFalse =>
    split at hrun
    · exact run_nonrec_exit_reg hbk hprep hvE hrun
    · exact run_rec_exit_reg hprep hfresh hciM hvE hmem hrun
  case isTrue =>
    obtain ⟨s₀, w₀, u₀, hpre, hm⟩ := run_inline_prefix_decomp' hrun
    have hpc : RunConcl sb s₀ ∧ gw wb ≤ gw w₀ := by
      rcases hpre with ⟨rfl, rfl⟩ | ⟨u', hlog, rfl⟩
      · exact ⟨RunConcl.rfl' _, NameGenerator.LE.rfl⟩
      · exact ⟨runConcl_inlinings _ _, hbk.2.1 _ _ _ _ _ _ _ _ _ hlog⟩
    refine reg_compose hpc.1 hpc.2 ?_
    rw [run_bind_ok] at hm
    obtain ⟨env2, se, we, henv2, hm⟩ := hm
    have hse := run_getEnv_state _ _ cctx ref _ henv2
    subst hse
    have hlee : gw w₀ ≤ gw we := hbk.1 _ _ _ _ _ _ _ _ henv2
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
           (hbk.2.1 _ _ _ _ _ _ _ _ _ hlogr))
    all_goals
      first
        | (obtain ⟨hstA, hwA⟩ := run_addAxiom_ok hm
           subst hstA
           subst hwA
           exact ⟨addAxiomState_get? n _, runConcl_addAxiomState n _, hlee⟩)
        | (refine reg_compose (RunConcl.rfl' _) hlee ?_
           split at hm
           · exact run_nonrec_exit_reg hbk hprep hvE hm
           · exact run_rec_exit_reg hprep hfresh hciM hvE hmem hm)

end Exits

/-! ## The two registration steps -/

section Steps

variable {lenv : Environment} {env : VEnv} {Us : List Name} {tbl : SourceTable}
  {cfg : ErasureConfig} {gw : Void IO.RealWorld → NameGenerator}

/-- A constant at the empty spine is a plain head: the `casesApp` rule needs a spine long
enough for the eliminator's own arity, so it does not apply. -/
theorem knownHead_of_supported_const {env : VEnv} {tbl : SourceTable} {n : Name}
    {us : List Level} (h : SupportedTm env tbl (.const n us) []) :
    KnownHead env tbl n ∧ PlainHead n ∧ isCasesOnName n = false := by
  cases h with
  | const hp hc _ _ hk => exact ⟨hk, hp, hc⟩
  | casesApp _ _ _ _ harity => simp at harity

/-- **Step 5.** The hit branch reads the registry, whose kernames are canonical by the
invariant; the miss branch registers the name through `Erasure.visitMutual` and then reads it
back, which is what makes the `panic!`-defaulting lookup total and canonical. -/
theorem step5 : Step5 lenv env Us tbl cfg gw := by
  intro _P _htbl _hcfg _hcb vMut m6
  refine ⟨?_, bodyLe5 m6.2⟩
  intro n s ctx cctx ref w kn s' w' hrun Δ hinv hsup
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
      exact ⟨hinv.canon hc, by rw [hc]; simp, RunConcl.rfl' _, NameGenerator.LE.rfl⟩
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
      obtain ⟨hdom, hrc, hle⟩ := m6.1 _ _ _ _ _ _ _ _ _ hvm Δ hinv hsup
      obtain ⟨kn₀, hkn₀⟩ := Option.isSome_iff_exists.mp hdom
      exact ⟨by rw [hashMap_get!_of_get? hkn₀]; exact hrc.canon hinv.canon hkn₀, hdom, hrc, hle⟩

/-- **Step 6.** All four exits of `Erasure.visitMutual` register the name it was called at, and
the term walk's own run conclusion is what carries the state and generator facts across the
body erasures. `Motive1`'s refinement half is not consumed: what the motive reports is
registration, and the fragment and translation premises a body erasure would need are not
available at a dependency's own level scope. -/
theorem step6 (hbk : CoreCallsMonotone gw) (hprep : PrepareRunConcl gw)
    (hve : VisitExprRunConcl gw) (hblk : DeclBlockMember env tbl) :
    Step6 lenv env Us tbl cfg gw := by
  intro P _htbl _hcfg _hcb vExpr m1
  refine ⟨?_, bodyLe6 m1.2⟩
  intro n s ctx cctx ref w u s' w' hrun Δ _hinv hsup
  exact run_visitMutual_registers P hbk hprep hve hblk
    (knownHead_of_supported_const hsup.term).1
    (run_ok_of_le₁ (bodyLe6 m1.2) hrun)

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
    {Γspec : GlobalDeclarations} (H : SpecContent env bo Γspec) {c : Name}
    (hco : ConstOrigin env c) (hrk : RuntimeKey Γspec (toKername c)) :
    isCasesOnName c = true := by
  obtain ⟨iid, np, dp, nfs, ⟨body, hlook, helim⟩, -⟩ := hrk
  by_cases hb : ∃ b, bo c = some b
  · obtain ⟨b, hb⟩ := hb
    obtain ⟨b₀, Us, hlook', her⟩ := H.defns c b hb (by rw [hlook]; simp)
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
    {Γspec : GlobalDeclarations} (H : SpecContent env bo Γspec) {c : Name}
    (hco : ConstOrigin env c) (hcas : isCasesOnName c = false) :
    ¬ RuntimeKey Γspec (toKername c) := by
  intro hrk
  rw [H.runtimeKey_isCasesOn hco hrk] at hcas
  exact absurd hcas (by simp)

/-! ## The reader's fixvar map, read as index lists

`ErasesLBFix` is indexed by a kername list and an identifier list read positionally, while the
reader carries a `Std.HashMap`. These three lemmas cross the gap.
-/

/-- The map the block reader installs, read as a right-biased lookup in the zipped list. -/
theorem fixvarMap_getElem? (nms : List Name) (ids : List FVarId) (m : Name) :
    (fixvarMap nms ids)[m]? =
      List.findSome? (fun p => if p.1 == m then some p.2 else none) (nms.zip ids).reverse := by
  rw [fixvarMap,
    show (Std.HashMap.ofList (nms.zip ids))
        = (∅ : Std.HashMap Name FVarId).insertMany (nms.zip ids) from rfl,
    Std.HashMap.getElem?_insertMany_list]
  simp

/-- A hit in the reader's map is a hit at one index of both lists: the last pair the zipped
list holds for the key, which is the one `Std.HashMap.ofList` keeps. -/
theorem fixvarMap_get?_some {nms : List Name} {ids : List FVarId} {m : Name} {x : FVarId}
    (h : (fixvarMap nms ids)[m]? = some x) :
    ∃ j : Nat, nms[j]? = some m ∧ ids[j]? = some x := by
  rw [fixvarMap_getElem?] at h
  obtain ⟨l₁, a, l₂, hsplit, hfa, -⟩ := List.findSome?_eq_some_iff.mp h
  have hmem : a ∈ nms.zip ids := by
    rw [← List.mem_reverse, hsplit]; simp
  have ha : a.1 = m ∧ a.2 = x := by
    by_cases hb : a.1 == m
    · simp only [hb, if_pos] at hfa
      exact ⟨by simpa using hb, by simpa using hfa⟩
    · simp only [hb, Bool.false_eq_true, if_false] at hfa
      exact absurd hfa (by simp)
  obtain ⟨j, hj, hja⟩ := List.getElem_of_mem hmem
  have hjn : j < nms.length := by
    have := List.length_zip (l₁ := nms) (l₂ := ids); omega
  have hji : j < ids.length := by
    have := List.length_zip (l₁ := nms) (l₂ := ids); omega
  refine ⟨j, ?_, ?_⟩
  · rw [List.getElem?_eq_getElem hjn]
    congr 1
    rw [← ha.1, ← hja, List.getElem_zip]
  · rw [List.getElem?_eq_getElem hji]
    congr 1
    rw [← ha.2, ← hja, List.getElem_zip]

/-- A miss in the reader's map is a miss in the name list, provided the identifier list is long
enough that `List.zip` truncates none of it. -/
theorem fixvarMap_get?_none {nms : List Name} {ids : List FVarId} {m : Name}
    (hlen : nms.length ≤ ids.length) (h : (fixvarMap nms ids)[m]? = none) : m ∉ nms := by
  rw [fixvarMap_getElem?] at h
  intro hm
  obtain ⟨j, hj, hjm⟩ := List.getElem_of_mem hm
  have hjz : j < (nms.zip ids).length := by
    rw [List.length_zip]; omega
  have hmem : (m, ids[j]'(by omega)) ∈ nms.zip ids := by
    have : (nms.zip ids)[j] = (nms[j], ids[j]'(by omega)) := List.getElem_zip
    rw [hjm] at this
    exact this ▸ List.getElem_mem hjz
  have := List.findSome?_eq_none_iff.mp h (m, ids[j]'(by omega)) (by rwa [List.mem_reverse])
  simp at this

/-! ## Step 4's content

`Step4` itself is **not** delivered: `Motive4` is false as stated. Two independent reasons, both
recorded by a lemma below. The content is delivered here with the two gaps as premises —
`ConstOrigin env n` at the visited head, and the two conditions under which the reader's map is
faithfully described by the index lists `ErasesLBFix` is stated at.
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
        BridgeInv env Us cfg (gw w) ctx s Δ → e = .const n us →
        isCasesOnName n = false → env.constants n = some ci → ConstOrigin env n →
        Supported env tbl e →
        RunConcl s s' ∧ gw w ≤ gw w' ∧
          ∀ Γspec, SpecEnv env tbl.body? s' Γspec →
            (ctx.fixvars = none → ErasesLB env Us Γspec Δ e t) ∧
            ∀ (nms : List Name) (ids : List FVarId),
              ctx.fixvars = some (fixvarMap nms ids) → nms.length ≤ ids.length →
              (∀ m : Name, toKername m ∈ nms.map toKername → m ∈ nms) →
              ErasesLBFix env Us Γspec (nms.map toKername) ids Δ e t := by
  intro e s ctx cctx ref w t s' w' hrun Δ n us ci hinv he hcas hcst hco hsup
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
      refine ⟨RunConcl.rfl' _, NameGenerator.LE.rfl, fun Γspec hspec => ⟨?_, ?_⟩⟩
      · intro hnone; rw [hnone] at hopt; simp at hopt
      · intro nms ids hfx hlen hsep
        rw [hfx] at hopt
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
      obtain ⟨hkn, hdom, hrc, hle⟩ := m5.1 _ _ _ _ _ _ _ _ _ hgck Δ hinv hsupc
      subst hkn
      refine ⟨hrc, hle, fun Γspec hspec => ⟨?_, ?_⟩⟩
      · intro _
        exact ⟨.const (toKername n), .const hcst hco,
          .const (specEnv_not_runtimeKey hspec.spec hco hcas)⟩
      · intro nms ids hfx hlen hsep
        refine ErasesLBFix.of_erasesLB ⟨.const (toKername n), .const hcst hco,
          .const (specEnv_not_runtimeKey hspec.spec hco hcas)⟩ (.miss ?_)
        intro hin
        rw [hfx] at hopt
        simp only [Option.bind_some] at hopt
        exact fixvarMap_get?_none hlen hopt (hsep n hin)

/-! ## Why `Step4` is not delivered

`ErasesLBMode`'s block conjunct is read at **every** pair of lists `fixvarMap` re-assembles the
reader's map from, and `List.zip` truncates, so a name list one longer than the identifier list
presents the same map. At that pair the last kername has no identifier, so `ConstToFVar`
relates nothing to a constant target: the conjunct is unsatisfiable whenever the emitted term
is a `.const`, which is what the plain branch of `Erasure.visitConst` emits. The repair is in
`Bridge.lean`: read the conjunct at the decompositions `BridgeInv.fixvars` provides — length
matched, and separated under `toKername`, which `toKername_not_injective` shows is a real
condition and not a formality.
-/

/-- Appending a name past the end of the identifier list does not change the reader's map. -/
theorem fixvarMap_append_left {nms : List Name} {ids : List FVarId} (c : Name)
    (hlen : ids.length ≤ nms.length) :
    fixvarMap (nms ++ [c]) ids = fixvarMap nms ids := by
  rw [fixvarMap, fixvarMap]
  congr 1
  induction nms generalizing ids with
  | nil =>
      have : ids = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst this; rfl
  | cons a as ih =>
      cases ids with
      | nil => rfl
      | cons x xs =>
          simp only [List.cons_append, List.zip_cons_cons]
          rw [ih (by simpa using hlen)]

/-- **The block conjunct is unsatisfiable at a constant target.** At the decomposition that
appends the target's own name to the name list, the emitted `.const` is neither a `hit` — there
is no identifier at that index — nor a `miss` — the kername is in the list. So no motive
concluding `ErasesLBMode` at a block reader holds of a run that emits a bare constant, which
is every plain constant head inside a mutual block. -/
theorem erasesLBMode_block_refuted {env : VEnv} {Us : List Name}
    {Γspec : GlobalDeclarations} {Δ : VLCtx} {ctx : ErasureContext} {e : Expr}
    {nms : List Name} {ids : List FVarId} (c : Name) (hlen : ids.length ≤ nms.length)
    (hfx : ctx.fixvars = some (fixvarMap nms ids)) :
    ¬ ErasesLBMode ctx env Us Γspec Δ e (.const (toKername c)) := by
  intro h
  obtain ⟨t₀, t₁, -, -, hc⟩ :=
    h.2 (nms ++ [c]) ids (by rw [hfx, fixvarMap_append_left c hlen])
  cases hc with
  | miss hnm => exact hnm (by simp)

/-- **`toKername` is not injective**, so a name outside the block can still carry a block
member's kername. That is the second condition `visitConst_refines` takes as a premise, and a
finding about the shipping printer: two Lean constants with one λ□ key shadow each other in the
emitted environment. -/
theorem toKername_not_injective :
    toKername (.num .anonymous 5) = toKername (.str .anonymous "5") ∧
      (Name.num .anonymous 5) ≠ (Name.str .anonymous "5") :=
  ⟨rfl, by decide⟩

end LeanToLambdaBox
