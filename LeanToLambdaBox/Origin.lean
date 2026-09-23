import LeanToLambdaBox.Upstream
import LeanToLambdaBox.SubjectReduction
import LeanToLambdaBox.Supported

/-!
# The origin corollaries, conditional on the upstream asks

`Erases` reads `Expr.const` three ways — a constructor (`CtorOf`), an inductive type name
(`IndInfo`), a plain constant (`ConstOrigin`) — and each reading exhibits a declaration list of
`VEnv.WF'` below `env`. Introduction sites need only the positive reading they already have. The
*exclusion* and *uniqueness* directions are a fact about `VEnv.WF'` and not about erasure, filed
as `doc/upstream-asks.md` item 2; until the pin moves they are the `constsOrigin` field of
`UpstreamAsks`, and this module unpacks that field into the named facts the tree consumes.

Beside them sit the four kernel corollaries the ι and projection arms and T7 read, each stated
without mentioning an ask: `indSpine_not_prop` (a relevant inductive spine is not a
proposition), `not_erasable_of_informative` (a value of one is neither a proof nor a
type-former), `elim_major` (the major premise of a saturated `casesOn` spine is typed at its own
inductive) and `ctor_saturated` (a constructor spine typed at its own inductive is saturated),
together with `CasesOnShape.agree`, which pins `SEval.iota`'s parameter count to the
eliminator's own block.

The corollaries that rest on an ask take `(A : UpstreamAsks env)` explicitly; the spine and
major-premise lemmas beside them need no ask. Once the fork holds the four asked theorems the
binder is discharged by the pin bump and no statement below changes shape.
-/
namespace LeanToLambdaBox

open Lean Lean4Lean

variable {env : VEnv} {c I I' : Name} {k k' dp nm dp' nm' np np' : Nat}
  {iid iid' : InductiveId} {nfs nfs' : List Nat}

/-- A name declared as a plain constant is not a constructor. -/
theorem constOrigin_not_ctorOf (A : UpstreamAsks env) (h : ConstOrigin env c) :
    ∀ I k, ¬ CtorOf env c I k :=
  (A.constsOrigin.2.2.2.2.2.1 c h).1

/-- A name declared as a plain constant is not an inductive type name. -/
theorem constOrigin_not_indInfo (A : UpstreamAsks env) (h : ConstOrigin env c) :
    ∀ iid np nfs, ¬ IndInfo env c iid np nfs :=
  (A.constsOrigin.2.2.2.2.2.1 c h).2

/-- The block declaring a given type former is unique, so its λ□ coordinates are. -/
theorem IndInfo.inj (A : UpstreamAsks env) (h : IndInfo env I iid np nfs)
    (h' : IndInfo env I iid' np' nfs') : iid = iid' ∧ np = np' ∧ nfs = nfs' :=
  A.constsOrigin.2.2.1 I iid np nfs iid' np' nfs' h h'

/-- A constructor belongs to one type at one index. -/
theorem CtorOf.inj (A : UpstreamAsks env) (h : CtorOf env c I k) (h' : CtorOf env c I' k') :
    I = I' ∧ k = k' :=
  A.constsOrigin.2.1 c I k I' k' h h'

/-- The segmentation an eliminator's own block fixes is unique. -/
theorem CasesOnShape.inj (A : UpstreamAsks env) (h : CasesOnShape env c I dp nm)
    (h' : CasesOnShape env c I dp' nm') : dp = dp' ∧ nm = nm' :=
  A.constsOrigin.2.2.2.1 c I dp nm dp' nm' h h'

/-- Totality of the three readings: a declared constant is a constructor, an inductive type name
or a plain constant. This is `Erases.exists_of_trExprS_of_projInfo`'s `hclass`. -/
theorem consts_classified (A : UpstreamAsks env) (_hwf : env.WF) : ∀ c ci,
    env.constants c = some ci →
    (∃ I k, CtorOf env c I k) ∨ (∃ iid np nfs, IndInfo env c iid np nfs) ∨ ConstOrigin env c :=
  A.constsOrigin.2.2.2.2.1

/-- A block below `env` that declares `I` is matched by a block of `env`'s own declaration
list. `ErasesEnv.blocks`' `IndDeclOf` conjunct. -/
theorem IndInfo.indDeclOf (A : UpstreamAsks env) (h : IndInfo env I iid np nfs) :
    IndDeclOf env I :=
  A.constsOrigin.2.2.2.2.2.2.1 I iid np nfs h

/-- Two blocks below `env` that declare the type former `I` are the same block. -/
theorem indBlock_uniq (A : UpstreamAsks env) {decl decl' : VInductDecl}
    (h : IndBlockBelow env decl) (h' : IndBlockBelow env decl')
    (ht : ∃ t ∈ decl.types, t.name = I) (ht' : ∃ t ∈ decl'.types, t.name = I) : decl = decl' :=
  A.constsOrigin.2.2.2.2.2.2.2 I decl decl' h h' ht ht'

/-! ## Level relevance under instantiation -/

/-- Never-zero-ness survives level instantiation: `VLevel.eval_inst` reads the instantiated
level's value off the original at the instantiated arguments. -/
theorem isNeverZero_inst {l : VLevel} {us : List VLevel} (h : l.IsNeverZero) :
    (l.inst us).IsNeverZero := fun ls hz => h _ (by rwa [VLevel.eval_inst] at hz)

/-- A Π-telescope's result sort is read through level instantiation. -/
theorem vResultSort_instL {T : VExpr} {l : VLevel} {us : List VLevel}
    (h : vResultSort T = some l) : vResultSort (T.instL us) = some (l.inst us) := by
  induction T with
  | sort u => cases h; rfl
  | forallE _ _ _ ih => exact ih h
  | _ => simp [vResultSort] at h

/-- A Π-telescope's result sort is read through term instantiation: the result is a `.sort`,
which carries no de Bruijn variable. -/
theorem vResultSort_inst {T : VExpr} {l : VLevel} :
    ∀ {a : VExpr} {k : Nat}, vResultSort T = some l → vResultSort (T.inst a k) = some l := by
  induction T with
  | sort u => intro _ _ h; cases h; rfl
  | forallE _ _ _ ih => intro _ _ h; exact ih h
  | _ => intro _ _ h; simp [vResultSort] at h

/-! ## Spine typing at a relevant inductive type former -/

/-- Level equivalence is reflexive pointwise along a list. -/
theorem forall₂_equiv_refl : ∀ (us : List VLevel), List.Forall₂ (· ≈ ·) us us
  | [] => .nil
  | _ :: us => .cons rfl (forall₂_equiv_refl us)

/-- A constant reference is typed at its declared type, instantiated at the reference's own
levels. `VEnv.HasType.const_inv` supplies the two side conditions. -/
theorem hasType_const {env : VEnv} {U : Nat} {Γ : List VExpr} {c : Name} {ci : VConstant}
    {us : List VLevel} (hci : env.constants c = some ci) (hus : ∀ l ∈ us, l.WF U)
    (hlen : us.length = ci.uvars) : env.HasType U Γ (.const c us) (ci.type.instL us) :=
  .constDF hci hus hus hlen (forall₂_equiv_refl us)

/-- Peeling a type whose result sort never evaluates to zero can never end at `Prop`: every
peel step keeps the two types definitionally equal, and the telescope's tail is a sort that
`IsDefEqU.sort_inv` would have to equate with `.zero`. -/
theorem peel_ne_prop {env : VEnv} (henv : env.WF) {U : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) {l : VLevel} (hl : l.IsNeverZero) :
    ∀ (args : List VExpr) {T S : VExpr}, vResultSort S = some l →
      env.IsDefEqU U Γ T S → ¬ Peel env U Γ T args (.sort .zero) := by
  intro args
  induction args with
  | nil =>
    intro T S hS hTS hP
    have hSz : env.IsDefEqU U Γ S (.sort .zero) := VEnv.IsDefEqU.trans henv hΓ hTS.symm hP
    match S, hS with
    | .sort u, hS =>
      cases hS
      exact hl [] (VLevel.equiv_def.1 (VEnv.IsDefEqU.sort_inv henv hΓ hSz) [])
    | .forallE _ _, _ => exact VEnv.IsDefEqU.sort_forallE_inv henv hΓ hSz.symm
  | cons a as ih =>
    intro T S hS hTS hP
    obtain ⟨A, B, hTf, ha, hrest⟩ := hP
    have hSf : env.IsDefEqU U Γ S (.forallE A B) := VEnv.IsDefEqU.trans henv hΓ hTS.symm hTf
    match S, hS with
    | .sort _, _ => exact VEnv.IsDefEqU.sort_forallE_inv henv hΓ hSf
    | .forallE A₀ B₀, hS =>
      obtain ⟨⟨_, hA⟩, _, hB⟩ := VEnv.IsDefEqU.forallE_inv henv hΓ hSf
      have ha₀ : env.HasType U Γ a A₀ :=
        VEnv.HasType.defeqU_r henv hΓ ⟨_, hA.symm⟩ ha
      have hinst : env.IsDefEqU U Γ (B₀.inst a) (B.inst a) :=
        VEnv.IsDefEqU.instN henv.ordered .zero ⟨_, hB⟩ ha₀
      have hS' : vResultSort B₀ = some l := hS
      exact ih (vResultSort_inst hS') hinst.symm hrest

/-- A spine headed by a relevant inductive type former is not a proposition. Ask 9 peels the
spine's typing onto the former's declared type, whose result sort is never zero. -/
theorem indSpine_not_prop {env : VEnv} (henv : env.WF) (A : UpstreamAsks env) {U : Nat}
    {Γ : List VExpr} {I : Name} {us : List VLevel} {args : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) (hinf : InformativeInd env I) :
    ¬ env.HasType U Γ (VExpr.mkApps (.const I us) args) (.sort .zero) := by
  intro hty
  obtain ⟨ci, hci, l, hl, hnz⟩ := hinf
  obtain ⟨T, hhead, hpeel⟩ := A.mkAppsInv henv.orderedStrong hΓ args hty
  obtain ⟨ci₂, hci₂, hus, hlen⟩ := VEnv.HasType.const_inv henv.orderedStrong hΓ hhead
  rw [Option.some.inj (hci₂.symm.trans hci)] at hlen
  have hconst : env.HasType U Γ (.const I us) (ci.type.instL us) := hasType_const hci hus hlen
  exact peel_ne_prop henv hΓ (isNeverZero_inst hnz) args (vResultSort_instL hl)
    (VEnv.IsDefEq.uniqU henv hΓ hhead hconst) hpeel


/-- **A value of a relevant inductive is neither a proof nor a type-former**, so the box rule
does not reach it. The type-former disjunct is ask 6; the proof disjunct is
`indSpine_not_prop`, i.e. ask 9 against the former's never-zero result sort. -/
theorem not_erasable_of_informative {env : VEnv} (henv : env.WF) (A : UpstreamAsks env)
    {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    {I : Name} (hdec : IndDeclOf env I) (hinf : InformativeInd env I)
    {e : VExpr} {us : List VLevel} {args : List VExpr}
    (hty : env.HasType U Γ e (VExpr.mkApps (.const I us) args)) :
    ¬ Erasable env U Γ e := by
  obtain ⟨ds, decl, tp, hds, hdecl, htype, rfl⟩ := hdec
  rintro ⟨T, hT, hcase⟩
  have hTeq : env.IsDefEqU U Γ T (VExpr.mkApps (.const tp.name us) args) :=
    VEnv.IsDefEq.uniqU henv hΓ hT hty
  have hisT : ∃ V, env.HasType U Γ (VExpr.mkApps (.const tp.name us) args) V := by
    obtain ⟨u, hu⟩ := hty.isType henv hΓ
    exact ⟨_, hu⟩
  cases hcase with
  | inl hp =>
      exact indSpine_not_prop henv A hΓ hinf (VEnv.HasType.defeqU_l henv hΓ hTeq hp)
  | inr har =>
      obtain ⟨T', hdef', harity⟩ := har
      have hspine : env.IsDefEqU U Γ (VExpr.mkApps (.const tp.name us) args) T' :=
        VEnv.IsDefEqU.trans henv hΓ (VEnv.IsDefEqU.symm hTeq) hdef'
      obtain ⟨hns, hnf⟩ := VEnv.IsDefEqU.const_arity_inv hds hΓ hdecl htype hisT
      cases harity with
      | sort u => exact hns u hspine
      | forallE A' B' _ => exact hnf A' B' hspine


/-! ## The block a spine's head belongs to -/

/-- A successful `addConst` fold has injective names: the second registration of a name finds
it already bound and fails. Kernel-generic, and proved here for want of a home upstream. -/
theorem addConst_foldlM_name_inj {α : Type _} {nm : α → Name} {ci : α → VConstant} :
    ∀ {l : List α} {init final : VEnv},
      l.foldlM (fun (e : VEnv) a => e.addConst (nm a) (ci a)) init = some final →
      ∀ a ∈ l, ∀ b ∈ l, nm a = nm b → a = b
  | [], _, _, _, _, ha, _, _, _ => absurd ha (List.not_mem_nil)
  | x :: xs, init, final, h, a, ha, b, hb, hnm => by
    simp only [List.foldlM] at h
    obtain ⟨e1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨-, hset, -⟩ := VEnv.addConst_eq h1
    have hfresh : ∀ y ∈ xs, nm y ≠ nm x := fun y hy hxy => by
      have := VEnv.addConst_foldlM_fresh h2 y hy
      rw [hxy, hset] at this; exact Option.some_ne_none _ this
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · rfl
    · exact absurd hnm.symm (hfresh b hb')
    · exact absurd hnm (hfresh a ha')
    · exact addConst_foldlM_name_inj h2 a ha' b hb' hnm

/-- A block declares each of its type formers under one name, so the block and the name pin
the former. The names are those `VInductDecl.addTypes` registers. -/
theorem indBlockBelow_type_uniq {env : VEnv} {decl : VInductDecl} (h : IndBlockBelow env decl)
    {t t' : VInductiveType} (ht : t ∈ decl.types) (ht' : t' ∈ decl.types)
    (hn : t.name = t'.name) : t = t' := by
  obtain ⟨ds, env₀, hds, -, hd⟩ := h
  obtain ⟨e₀, e₁, -, hadd, -⟩ := VEnv.WF'.induct_origin hds hd
  obtain ⟨envT, -, -, hT, -, -, -⟩ := VEnv.addInduct_stages hadd
  exact addConst_foldlM_name_inj hT t ht t' ht' hn

/-- The block `CasesOnShape` exhibits, with the segmentation it fixes. -/
theorem CasesOnShape.indBlockBelow (h : CasesOnShape env c I dp nm) :
    ∃ decl, IndBlockBelow env decl ∧ ∃ t ∈ decl.types, t.name = I ∧
      dp = decl.nparams + 1 + (t.type.piArity - decl.nparams) ∧ nm = t.ctors.length :=
  let ⟨_, _, _, ds, env₀, decl, t, hds, hd, hle, ht, hname, hdp, hnm⟩ := h
  ⟨decl, ⟨ds, env₀, hds, hle, hd⟩, t, ht, hname, hdp, hnm⟩

/-- The block `IndArity` exhibits, with its arity data. -/
theorem IndArity.indBlockBelow (h : IndArity env I np nfs) :
    ∃ decl, IndBlockBelow env decl ∧ ∃ t ∈ decl.types, t.name = I ∧
      decl.nparams = np ∧ ctorFieldCounts np t = nfs :=
  let ⟨ds, env₀, decl, t, hds, hd, hle, ht, hname, hnp, hnfs⟩ := h
  ⟨decl, ⟨ds, env₀, hds, hle, hd⟩, t, ht, hname, hnp, hnfs⟩

/-- **`SEval.iota`'s block is the eliminator's block.** `CasesOnShape` and `IndArity` each
exhibit a `WF'` list below `env`; ask 2's declaration-level uniqueness identifies them, and a
block names its type formers injectively. -/
theorem CasesOnShape.agree (A : UpstreamAsks env) (hsh : CasesOnShape env c I dp nm)
    (hnp : IndArity env I np nfs) : dp = np + 1 + (dp - np - 1) ∧ nm = nfs.length := by
  obtain ⟨decl, hblk, t, ht, hname, hdp, hnm⟩ := hsh.indBlockBelow
  obtain ⟨decl', hblk', t', ht', hname', hnp', hnfs⟩ := hnp.indBlockBelow
  obtain rfl : decl = decl' :=
    indBlock_uniq A hblk hblk' ⟨t, ht, hname⟩ ⟨t', ht', hname'⟩
  obtain rfl : t = t' := indBlockBelow_type_uniq hblk ht ht' (hname.trans hname'.symm)
  subst hnp'; subst hnfs
  refine ⟨by omega, ?_⟩
  simp [ctorFieldCounts, hnm]

/-- **A type former has one arity.** The `IndArity` twin of `IndInfo.inj`; the same route as
`CasesOnShape.agree`, at two `IndArity`s. -/
theorem IndArity.inj {env : VEnv} (A : UpstreamAsks env) {I : Name} {np np' : Nat}
    {nfs nfs' : List Nat} (h : IndArity env I np nfs) (h' : IndArity env I np' nfs') :
    np = np' ∧ nfs = nfs' := by
  obtain ⟨decl, hblk, t, ht, hname, hnp, hnfs⟩ := h.indBlockBelow
  obtain ⟨decl', hblk', t', ht', hname', hnp', hnfs'⟩ := h'.indBlockBelow
  obtain rfl : decl = decl' :=
    indBlock_uniq A hblk hblk' ⟨t, ht, hname⟩ ⟨t', ht', hname'⟩
  obtain rfl : t = t' := indBlockBelow_type_uniq hblk ht ht' (hname.trans hname'.symm)
  subst hnp; subst hnp'; subst hnfs; subst hnfs'
  exact ⟨rfl, rfl⟩


/-! ## Peeling a translated spine

The `app` arm of `TrExprS` already carries the typing of the function at a Π and of the
argument at its domain, so a *translated* spine peels without ask 9. Ask 9 is what the
untranslated spine of `indSpine_not_prop` needs.
-/

/-- The typing of a translated spine peels argument by argument off the head's type. -/
theorem trExprS_spine_peel {env : VEnv} {Us : List Name} {Δ : VLCtx} (henv : env.WF)
    (hΔ : VLCtx.WF env Us.length Δ) :
    ∀ (args : List Expr) {hd : Expr} {hve T ve : VExpr},
      TrExprS env Us Δ hd hve → env.HasType Us.length Δ.toCtx hve T →
      TrExprS env Us Δ (mkApps hd args) ve →
      ∃ V vargs, vargs.length = args.length ∧
        (∀ i, i < args.length → TrExprS env Us Δ args[i]! vargs[i]!) ∧
        env.HasType Us.length Δ.toCtx ve V ∧ Peel env Us.length Δ.toCtx T vargs V := by
  have hΓ := hΔ.toCtx
  intro args
  induction args with
  | nil =>
    intro hd hve T ve hhd hT htr
    have hdefeq : env.IsDefEqU Us.length Δ.toCtx hve ve :=
      VEnv.IsDefEqU.symm (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htr hhd)
    obtain ⟨u, hu⟩ := hT.isType henv hΓ
    exact ⟨T, [], rfl, fun i hi => absurd hi (by simp),
      VEnv.HasType.defeqU_l henv hΓ hdefeq hT, ⟨_, hu⟩⟩
  | cons a as ih =>
    intro hd hve T ve hhd hT htr
    rw [mkApps_cons] at htr
    obtain ⟨wapp, htrapp⟩ := trExprS_spine_head as htr
    cases htrapp with
    | app h1 h2 h3 h4 =>
      have hfeq : env.IsDefEqU Us.length Δ.toCtx hve _ :=
        TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) hhd h3
      have hhveF := VEnv.HasType.defeqU_l henv hΓ (VEnv.IsDefEqU.symm hfeq) h1
      have hTF := VEnv.IsDefEq.uniqU henv hΓ hT hhveF
      obtain ⟨V, vargs, hlen, hall, hveV, hpeel⟩ :=
        ih (.app h1 h2 h3 h4) (VEnv.IsDefEq.appDF h1 h2) htr
      refine ⟨V, _ :: vargs, by simp [hlen], fun i hi => ?_, hveV, _, _, hTF, h2, hpeel⟩
      match i, hi with
      | 0, _ => simpa using h4
      | i + 1, hi => simpa using hall i (by simpa using hi)


/-! ## The major premise of an eliminator spine -/

/-- A bare type former at binder `i` of a Π-telescope is a major premise of that former at
position `i`: `MajorPremiseAt`'s spine is the empty application. -/
theorem majorPremiseAt_of_piBinders {J : Name} {jus : List VLevel} :
    ∀ {i : Nat} {T : VExpr}, T.piBinders[i]? = some (.const J jus) → MajorPremiseAt J i T
  | 0, .forallE _ B, h => by
      simp only [VExpr.piBinders, List.getElem?_cons_zero, Option.some.injEq] at h
      exact ⟨_, B, jus, [], rfl, h⟩
  | _ + 1, .forallE A _, h => by
      simp only [VExpr.piBinders, List.getElem?_cons_succ] at h
      exact ⟨A, _, rfl, majorPremiseAt_of_piBinders h⟩
  | _, .bvar .., h | _, .sort .., h | _, .const .., h | _, .app .., h | _, .lam .., h => by
      simp [VExpr.piBinders] at h

/-- The major-premise position survives instantiation: the domain is a spine headed by `I`,
and `VExpr.mkApps_inst` pushes the substitution into its arguments. -/
theorem MajorPremiseAt.inst {I : Name} : ∀ {n : Nat} {T a : VExpr} {k : Nat},
    MajorPremiseAt I n T → MajorPremiseAt I n (T.inst a k)
  | 0, _, a, k, ⟨_, _, ius, iargs, rfl, rfl⟩ =>
      ⟨_, _, ius, iargs.map (·.inst a k), rfl, VExpr.mkApps_inst⟩
  | _ + 1, _, _, _, ⟨_, _, rfl, h⟩ => ⟨_, _, rfl, h.inst⟩

/-- The major-premise position survives level instantiation, as `MajorPremiseAt.inst` survives
term instantiation. -/
theorem MajorPremiseAt.instL {I : Name} {ls : List VLevel} : ∀ {n : Nat} {T : VExpr},
    MajorPremiseAt I n T → MajorPremiseAt I n (T.instL ls)
  | 0, _, ⟨_, _, ius, iargs, rfl, rfl⟩ =>
      ⟨_, _, ius.map (VLevel.inst ls), iargs.map (·.instL ls), rfl, VExpr.mkApps_instL⟩
  | _ + 1, _, ⟨_, _, rfl, h⟩ => ⟨_, _, rfl, h.instL⟩

/-- Peeling a type whose `n`-th binder is a major premise of `I` types the `n`-th argument at
an `I`-spine. -/
theorem peel_major {env : VEnv} (henv : env.WF) {U : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) {I : Name} :
    ∀ (n : Nat) (vargs : List VExpr) {T S V : VExpr},
      MajorPremiseAt I n S → env.IsDefEqU U Γ T S → Peel env U Γ T vargs V →
      n < vargs.length →
      ∃ ius iargs, env.HasType U Γ vargs[n]! (VExpr.mkApps (.const I ius) iargs) := by
  intro n
  induction n with
  | zero =>
    intro vargs T S V hM hTS hP hlt
    obtain ⟨_, _, ius, iargs, rfl, rfl⟩ := hM
    cases vargs with
    | nil => simp at hlt
    | cons a rest =>
      obtain ⟨_, _, hTf, ha, -⟩ := hP
      obtain ⟨⟨_, hA⟩, -⟩ := VEnv.IsDefEqU.forallE_inv henv hΓ
        (VEnv.IsDefEqU.trans henv hΓ (VEnv.IsDefEqU.symm hTS) hTf)
      exact ⟨ius, iargs, by simpa using VEnv.HasType.defeqU_r henv hΓ ⟨_, hA.symm⟩ ha⟩
  | succ n ih =>
    intro vargs T S V hM hTS hP hlt
    obtain ⟨A₀, B₀, rfl, hM'⟩ := hM
    cases vargs with
    | nil => simp at hlt
    | cons a rest =>
      obtain ⟨_, B', hTf, ha, hrest⟩ := hP
      obtain ⟨⟨_, hA⟩, _, hB⟩ := VEnv.IsDefEqU.forallE_inv henv hΓ
        (VEnv.IsDefEqU.trans henv hΓ (VEnv.IsDefEqU.symm hTS) hTf)
      have ha₀ : env.HasType U Γ a A₀ := VEnv.HasType.defeqU_r henv hΓ ⟨_, hA.symm⟩ ha
      have hinst : env.IsDefEqU U Γ (B₀.inst a) (B'.inst a) :=
        VEnv.IsDefEqU.instN henv.ordered .zero ⟨_, hB⟩ ha₀
      simpa using
        ih rest hM'.inst (VEnv.IsDefEqU.symm hinst) hrest (by simpa using hlt)

/-- **The major premise of a well-typed saturated `casesOn` spine is typed at its own
inductive.** `CasesOnShape`'s type clause places the major premise at position `dp` of the
declared type, and the translated spine peels the typing onto it. -/
theorem elim_major {env : VEnv} {Us : List Name} (henv : env.WF)
    {c I : Name} {dp nm : Nat} {us : List Level} {pre minors extra : List Expr}
    {disc : Expr} {ve w : VExpr}
    (hsh : CasesOnShape env c I dp nm) (hpre : pre.length = dp) (_hmin : minors.length = nm)
    (hwt : TrExprS env Us [] (mkApps (.const c us) (pre ++ disc :: minors ++ extra)) ve)
    (hdisc : TrExprS env Us [] disc w) :
    ∃ (ius : List VLevel) (iargs : List VExpr),
      env.HasType Us.length [] w (VExpr.mkApps (.const I ius) iargs) := by
  obtain ⟨-, -, ⟨ci, hci, hmaj⟩, -⟩ := hsh
  have hΔ : VLCtx.WF env Us.length ([] : VLCtx) := trivial
  have hΓ : OnCtx (VLCtx.toCtx ([] : VLCtx)) (env.IsType Us.length) := hΔ.toCtx
  obtain ⟨_, htrhead⟩ := trExprS_spine_head _ hwt
  cases htrhead with
  | const hci₂ hmap hlen =>
    obtain rfl : ci = _ := Option.some.inj (hci.symm.trans hci₂)
    have hlen' : _ = ci.uvars := ((List.mapM_eq_some.1 hmap).length_eq).symm.trans hlen
    have hT := hasType_const (Γ := VLCtx.toCtx ([] : VLCtx)) hci
      (VLevel.WF.of_mapM_ofLevel hmap) hlen'
    obtain ⟨_, vargs, hvlen, hvarg, -, hpeel⟩ :=
      trExprS_spine_peel henv hΔ _ (.const hci₂ hmap hlen) hT hwt
    obtain ⟨u, hu⟩ := hT.isType henv hΓ
    have hlt : dp < vargs.length := by
      rw [hvlen]; simp only [List.length_append, List.length_cons]; omega
    obtain ⟨ius, iargs, hty⟩ :=
      peel_major henv hΓ dp vargs (hmaj _) ⟨_, hu⟩ hpeel hlt
    have hdiscIdx : (pre ++ disc :: (minors ++ extra))[dp]! = disc := by
      subst hpre; simp
    have htrd := hvarg dp (by simp only [List.length_append, List.length_cons]; omega)
    rw [show pre ++ disc :: minors ++ extra = pre ++ disc :: (minors ++ extra) by simp,
      hdiscIdx] at htrd
    exact ⟨ius, iargs, VEnv.HasType.defeqU_l henv hΓ
      (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrd hdisc) hty⟩


/-! ## Saturation of a constructor value -/

/-- `T` is a Π-telescope of `n` binders whose body is a spine headed by `I` — the shape
`VExpr.CtorResult` pins for a constructor's declared type. -/
def PiSpine (I : Name) : Nat → VExpr → Prop
  | 0,     T => ∃ us args, T = VExpr.mkApps (.const I us) args
  | n + 1, T => ∃ A B, T = .forallE A B ∧ PiSpine I n B

theorem PiSpine.instL {I : Name} : ∀ {n : Nat} {T : VExpr} {ls : List VLevel},
    PiSpine I n T → PiSpine I n (T.instL ls)
  | 0, _, ls, ⟨us, args, rfl⟩ =>
      ⟨us.map (VLevel.inst ls), args.map (·.instL ls), VExpr.mkApps_instL⟩
  | _ + 1, _, _, ⟨_, _, rfl, h⟩ => ⟨_, _, rfl, h.instL⟩

theorem PiSpine.inst {I : Name} : ∀ {n : Nat} {T a : VExpr} {k : Nat},
    PiSpine I n T → PiSpine I n (T.inst a k)
  | 0, _, a, k, ⟨us, args, rfl⟩ => ⟨us, args.map (·.inst a k), VExpr.mkApps_inst⟩
  | _ + 1, _, _, _, ⟨_, _, rfl, h⟩ => ⟨_, _, rfl, h.inst⟩

/-- A type of Π-arity `n` whose body is an `I`-spine is a `PiSpine`. -/
theorem piSpine_of_piBody {I : Name} : ∀ {ty : VExpr} {n : Nat}, ty.piArity = n →
    (∃ us args, ty.piBody = VExpr.mkApps (.const I us) args) → PiSpine I n ty
  | .forallE _ B, n, harity, hbody => by
      cases n with
      | zero => simp [VExpr.piArity] at harity
      | succ m =>
        refine ⟨_, B, rfl, piSpine_of_piBody ?_ hbody⟩
        simpa [VExpr.piArity] using harity
  | .bvar _, _, harity, hbody | .sort _, _, harity, hbody | .const .., _, harity, hbody
  | .app .., _, harity, hbody | .lam .., _, harity, hbody => by
      simp only [VExpr.piArity] at harity
      subst harity
      exact hbody

set_option linter.unusedVariables false in
/-- A spine headed by an inductively declared type former is definitionally equal to no Π.
Ask 6, with its declaration data read off `IndDeclOf` and its typing premise off the
equation itself. `A` is unused since the pin: the body now cites
`Lean4Lean.VEnv.IsDefEqU.const_arity_inv` directly rather than `A.constArityInv`, and the
parameter stays to keep `peel_piSpine`'s two call sites unchanged. -/
theorem indSpine_ne_forallE {env : VEnv} (A : UpstreamAsks env) {U : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) {I : Name} (hdec : IndDeclOf env I)
    {us : List VLevel} {args : List VExpr} {A' B' : VExpr} :
    ¬ env.IsDefEqU U Γ (VExpr.mkApps (.const I us) args) (.forallE A' B') := by
  intro h
  obtain ⟨ds, decl, t, hds, hdecl, ht, rfl⟩ := hdec
  obtain ⟨C, hC⟩ := h
  exact (VEnv.IsDefEqU.const_arity_inv hds hΓ hdecl ht ⟨C, hC.hasType.1⟩).2 _ _ ⟨C, hC⟩

/-- Peeling a constructor's declared type at a value typed in its own inductive exhausts the
telescope exactly: a short spine ends at a Π where an inductive spine is wanted, and a long
one asks an inductive spine to be a Π. -/
theorem peel_piSpine {env : VEnv} (henv : env.WF) (A : UpstreamAsks env) {U : Nat}
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) {I J : Name}
    (hdI : IndDeclOf env I) (hdJ : IndDeclOf env J) :
    ∀ (vargs : List VExpr) {T S V : VExpr} {n : Nat} {jus : List VLevel} {jargs : List VExpr},
      PiSpine I n S → env.IsDefEqU U Γ T S → Peel env U Γ T vargs V →
      env.IsDefEqU U Γ V (VExpr.mkApps (.const J jus) jargs) → vargs.length = n := by
  intro vargs
  induction vargs with
  | nil =>
    intro T S V n jus jargs hS hTS hP hV
    cases n with
    | zero => rfl
    | succ m =>
      obtain ⟨A₀, B₀, rfl, -⟩ := hS
      exact absurd (VEnv.IsDefEqU.symm (VEnv.IsDefEqU.trans henv hΓ
        (VEnv.IsDefEqU.trans henv hΓ (VEnv.IsDefEqU.symm hTS) hP) hV))
        (indSpine_ne_forallE A hΓ hdJ)
  | cons a as ih =>
    intro T S V n jus jargs hS hTS hP hV
    obtain ⟨A', B', hTf, ha, hrest⟩ := hP
    have hSf := VEnv.IsDefEqU.trans henv hΓ (VEnv.IsDefEqU.symm hTS) hTf
    cases n with
    | zero =>
      obtain ⟨_, _, rfl⟩ := hS
      exact absurd hSf (indSpine_ne_forallE A hΓ hdI)
    | succ m =>
      obtain ⟨A₀, B₀, rfl, hS'⟩ := hS
      obtain ⟨⟨_, hA⟩, _, hB⟩ := VEnv.IsDefEqU.forallE_inv henv hΓ hSf
      have ha₀ : env.HasType U Γ a A₀ := VEnv.HasType.defeqU_r henv hΓ ⟨_, hA.symm⟩ ha
      have hinst : env.IsDefEqU U Γ (B₀.inst a) (B'.inst a) :=
        VEnv.IsDefEqU.instN henv.ordered .zero ⟨_, hB⟩ ha₀
      simpa using ih hS'.inst (VEnv.IsDefEqU.symm hinst) hrest hV

/-- Peeling a Π-telescope to its end reaches the telescope's own result spine. `peel_piSpine`
says the spine of a well-typed constructor value has exactly the telescope's length; this says
what the type at that end is. -/
theorem peel_piSpine_head {env : VEnv} (henv : env.WF) {U : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) {I : Name} :
    ∀ (vargs : List VExpr) {T S V : VExpr} {n : Nat}, PiSpine I n S → vargs.length = n →
      env.IsDefEqU U Γ T S → Peel env U Γ T vargs V →
      ∃ us args, env.IsDefEqU U Γ V (VExpr.mkApps (.const I us) args) := by
  intro vargs
  induction vargs with
  | nil =>
    intro T S V n hS hlen hTS hP
    cases n with
    | zero =>
      obtain ⟨us, args, rfl⟩ := hS
      exact ⟨us, args, VEnv.IsDefEqU.trans henv hΓ (VEnv.IsDefEqU.symm hP) hTS⟩
    | succ m => simp at hlen
  | cons a as ih =>
    intro T S V n hS hlen hTS hP
    cases n with
    | zero => simp at hlen
    | succ m =>
      obtain ⟨A₀, B₀, rfl, hS'⟩ := hS
      obtain ⟨A', B', hTf, ha, hrest⟩ := hP
      obtain ⟨⟨_, hA⟩, _, hB⟩ := VEnv.IsDefEqU.forallE_inv henv hΓ
        (VEnv.IsDefEqU.trans henv hΓ (VEnv.IsDefEqU.symm hTS) hTf)
      have ha₀ : env.HasType U Γ a A₀ := VEnv.HasType.defeqU_r henv hΓ ⟨_, hA.symm⟩ ha
      have hinst : env.IsDefEqU U Γ (B₀.inst a) (B'.inst a) :=
        VEnv.IsDefEqU.instN henv.ordered .zero ⟨_, hB⟩ ha₀
      exact ih hS'.inst (by simpa using hlen) (VEnv.IsDefEqU.symm hinst) hrest

/-- A constructor's declared type, with the block's own parameter count and this
constructor's field count. `CtorOf` and `IndArity` each exhibit a block; ask 2's uniqueness
identifies them. -/
theorem CtorOf.ctorResult_at (A : UpstreamAsks env) {c I : Name} {k np : Nat}
    {nfs : List Nat} (hct : CtorOf env c I k) (hnp : IndArity env I np nfs) :
    ∃ ci nind, env.constants c = some ci ∧ ci.type.CtorResult I np nfs[k]! nind := by
  obtain ⟨ds, env₀, decl, t, ctor, hds, hd, hle, hmem, hname, hk, hcn⟩ := hct
  obtain ⟨decl', hblk', t', ht', hname', hnp', hnfs⟩ := hnp.indBlockBelow
  have hblk : IndBlockBelow env decl := ⟨ds, env₀, hds, hle, hd⟩
  obtain rfl : decl = decl' := indBlock_uniq A hblk hblk' ⟨t, hmem, hname⟩ ⟨t', ht', hname'⟩
  obtain rfl : t = t' := indBlockBelow_type_uniq hblk hmem ht' (hname.trans hname'.symm)
  obtain ⟨e₀, e₁, hdecl, hadd, hle₁⟩ := VEnv.WF'.induct_origin hds hd
  obtain ⟨envT, envC, envR, hT, hC, hR, hP⟩ := VEnv.addInduct_stages hadd
  have hctor : ctor ∈ t.ctors := List.mem_of_getElem? hk
  have hcmem' : ctor ∈ decl.types.flatMap (·.ctors) := List.mem_flatMap.2 ⟨t, hmem, hctor⟩
  have hfold : decl.consts.foldlM (fun (e : VEnv) b => e.addConst b.1 b.2) e₀ = some envR := by
    rw [← VInductDecl.addTypesCtorsRecs_eq]
    unfold VInductDecl.addTypesCtorsRecs VInductDecl.addTypesCtors
    simp [hT, hC, hR]
  have hcmem : (ctor.name, ctor.toVConstant) ∈ decl.consts :=
    List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hcmem'))
  have hfind := VEnv.addConst_foldlM_find (nm := Prod.fst) (ci := Prod.snd) hfold _ hcmem
  obtain ⟨nf, hres⟩ := hdecl.ctors_result t hmem ctor hctor
  have hidx : nfs[k]! = nf := by
    subst hnfs; subst hnp'
    have : ctor.type.piArity = decl.nparams + nf := hres.1
    simp only [ctorFieldCounts, List.getElem!_eq_getElem?_getD, List.getElem?_map, hk]
    simp [this]
  refine ⟨ctor.toVConstant, t.type.piArity - decl.nparams,
    hcn ▸ hle.constants (hle₁.constants ((VEnv.addRules_le hP).constants hfind)), ?_⟩
  rw [hidx, ← hnp']
  exact hname ▸ hres

/-- **A constructor spine typed at its own inductive is saturated.** -/
theorem ctor_saturated {env : VEnv} {Us : List Name} (henv : env.WF) (A : UpstreamAsks env)
    {ctor I : Name} {k : Nat} {iid : InductiveId} {np : Nat} {nfs : List Nat}
    {cus : List Level} {cargs : List Expr} {w : VExpr} {ius : List VLevel}
    {iargs : List VExpr} (hct : CtorOf env ctor I k) (hi : IndInfo env I iid np nfs)
    (hwt : TrExprS env Us [] (mkApps (.const ctor cus) cargs) w)
    (hty : env.HasType Us.length [] w (VExpr.mkApps (.const I ius) iargs)) :
    cargs.length = np + nfs[k]! := by
  have hΔ : VLCtx.WF env Us.length ([] : VLCtx) := trivial
  have hΓ : OnCtx (VLCtx.toCtx ([] : VLCtx)) (env.IsType Us.length) := hΔ.toCtx
  have hdec := IndInfo.indDeclOf A hi
  obtain ⟨cci, nind, hcci, hres⟩ := hct.ctorResult_at A hi.arity
  obtain ⟨_, htrhead⟩ := trExprS_spine_head _ hwt
  cases htrhead with
  | const hci₂ hmap hlen =>
    rename_i cus'
    obtain rfl : cci = _ := Option.some.inj (hcci.symm.trans hci₂)
    have hlen' : _ = cci.uvars := ((List.mapM_eq_some.1 hmap).length_eq).symm.trans hlen
    have hT := hasType_const (Γ := VLCtx.toCtx ([] : VLCtx)) hcci
      (VLevel.WF.of_mapM_ofLevel hmap) hlen'
    obtain ⟨V, vargs, hvlen, -, hveV, hpeel⟩ :=
      trExprS_spine_peel henv hΔ _ (.const hci₂ hmap hlen) hT hwt
    obtain ⟨u, hu⟩ := hT.isType henv hΓ
    have hspine : PiSpine I (np + nfs[k]!) (cci.type.instL cus') :=
      (piSpine_of_piBody hres.1 (by obtain ⟨us, idx, -, h⟩ := hres.2; exact ⟨us, _, h⟩)).instL
    rw [← hvlen]
    exact peel_piSpine henv A hΓ hdec hdec vargs hspine ⟨_, hu⟩ hpeel
      (VEnv.IsDefEq.uniqU henv hΓ hveV hty)


/-! ## A tabled constant in the model -/

/-- A constant the compiler table gives a body for is a constant of the model: the table pins
it in `lenv`, `TableSafe` gives its safety and `ErasureSpec.decl_adequate` translates it.
Class **D**, through `ErasureSpec`. -/
theorem constants_of_tabled {lenv : Environment} {env : VEnv} {Us : List Name}
    {gw : Void IO.RealWorld → NameGenerator} {tbl : Witness.SourceTable}
    (P : ErasureSpec lenv env Us gw) (ht : Witness.SourceTableAdequate lenv tbl)
    (hsafe : TableSafe lenv tbl) {c : Name} {b : Expr} (h : tbl.body? c = some b) :
    ∃ vc, env.constants c = some vc := by
  cases hd : tbl.decls.lookup c with
  | none =>
    rw [Witness.SourceTable.body?, Witness.SourceTable.decl?, hd] at h
    nomatch (show (none : Option Expr) = some b from h)
  | some d =>
    obtain ⟨ci, hfind, -, -⟩ := (ht.decls c d (Witness.mem_of_lookup hd)).1
    have hs := hsafe.decls c ci (by rw [Witness.SourceTable.decl?, hd]; rfl) hfind
    obtain ⟨vc, hvc, -⟩ := P.decl_adequate c ci hfind hs
    exact ⟨vc, hvc⟩

/-- **A declared constant that is neither a constructor nor an inductive type name is a plain
constant.** Ask 2's classification conjunct, with the two exclusions as premises. -/
theorem constOrigin_of_constants (A : UpstreamAsks env) {ci : VConstant}
    (hc : env.constants c = some ci) (hnc : ∀ I k, ¬ CtorOf env c I k)
    (hni : ∀ iid np nfs, ¬ IndInfo env c iid np nfs) : ConstOrigin env c := by
  rcases A.constsOrigin.2.2.2.2.1 c ci hc with ⟨I, k, h⟩ | ⟨iid, np, nfs, h⟩ | h
  · exact absurd h (hnc I k)
  · exact absurd h (hni iid np nfs)
  · exact h


end LeanToLambdaBox
