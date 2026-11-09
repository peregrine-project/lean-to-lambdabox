import EraseProof.Core.StepsCases

/-!
# The `□` and reduced branches of `visitCases`

Two branches of `visitCases` (`LeanToLambdaBox/Erasure.lean:870`) on a saturated spine of a
recognized `casesOn` constant do not build a λ□ `case`:
* a `casesOn` with as many universe parameters as its inductive eliminates only into `Prop`, and
  the spine is erased to `□`: its translation reduces to the recursor node at the motive level `0`
  (`SrcProof.casesOn_recr`), a proof (`isErasable_cases_box`);
* when the discriminant's sort may be zero and the inductive has one constructor, the spine is
  erased to the erased alternative applied to `□` for each field (`Erases.casesReduced`), which
  needs every field of a constructor node of the inductive to be erasable (`FieldsErasable`): the
  `casesOn` has a universe parameter more than its inductive, so the block eliminates into every
  sort, and the sort may be zero, so the block eliminates as a subsingleton, whose ordinary fields
  are at level `0` or index variables (`Ctor.Eligible`), and the latter are Lean index fields
  (`IndBlock.indexVars`), which a recognized `casesOn` has none of (`NoIndexFields`); its recursive
  fields are then at level `0` too (`fieldsErasable_reduced`).

Reference: `erases_tCase` with `Subsingleton` (`MR E/Extract.v:111`); the reduction at erasure
time is DV-25.
-/

open Lean Erasure
open Metalean (Defeq TypeEq EnvWF WHRedS)

namespace EraseProof

namespace StepsCases

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P : List ConstantInfo}
  {lps : List Name}

/-- An application spine on a head that is not special translates to the head's translation
applied to the arguments' translations. -/
theorem trM_spine {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    {as : List Expr} {as' : List (Metalean.Expr ζ lps.length n)}
    (has : List.Forall₂ (TrM E B lps Γ Δ) as as') :
    ∀ {f : Expr} {f' : Metalean.Expr ζ lps.length n}, ¬ SpecialHead B f →
      TrM E B lps Γ Δ f f' → TrM E B lps Γ Δ (mkAppN f as.toArray) (f'.appList as') := by
  induction has with
  | nil => intro f f' _ hf; exact hf
  | @cons a a' as as' ha _ ih =>
    intro f f' hns hf
    have hns' : ¬ SpecialHead B (.app f a) := fun ⟨c, us, b, h, hb, hs⟩ =>
      hns ⟨c, us, b, h, hb, hs⟩
    have h := ih hns' (.app hns hf ha)
    rw [mkAppN_toArray] at h ⊢
    exact h

/-- The head of a recognized `casesOn` spine is not special: the `casesOn` is a definition. -/
theorem casesOn_notSpecial {σ : EvalEnv} (henv : ProgEnv P ζ E B) (hsub : SubEnv σ.decls P)
    {c : Name} {us : List Level} {d : DefinitionVal}
    (hd : findDecl σ.decls c = some (.defnInfo d)) : ¬ SpecialHead B (.const c us) := by
  obtain ⟨η, hB, -⟩ := henv.lookup_def (SrcDefeq.findDecl_sub hsub hd)
  rintro ⟨c', us', b, hfn, hb, hs⟩
  cases hfn
  rw [hB] at hb; cases hb; cases hs

/-- A typed translation of a spine of a recognized `casesOn` with at least its arity of
arguments: the saturated prefix translates to a typed term `t₁` that reduces to the Metalean
recursor node on a translation of the major (`SrcProof.casesOn_recr`), and the whole spine's
translation is `t₁` applied to the remaining arguments' translations. -/
theorem cases_sat_split {σ : EvalEnv} (henv : ProgEnv P ζ E B) (hE : EnvWF E)
    (hsub : SubEnv σ.decls P) {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
    {Δ : MLCtx ζ lps.length n} (hΓ : E[Γ] ⊢ ok) {c : Name} {iv : InductiveVal}
    {d : DefinitionVal} {us : List Level} {as : List Expr} {t T : Metalean.Expr ζ lps.length n}
    (hcs : σ.casesOn? c = some iv) (hd : findDecl σ.decls c = some (.defnInfo d))
    (hsat : casesArity iv ≤ as.length)
    (he : TrM E B lps Γ Δ (mkAppN (.const c us) as.toArray) t) (ht : E[Γ] ⊢ t : T) :
    ∃ (t₁ F : Metalean.Expr ζ lps.length n) (xs : List (Metalean.Expr ζ lps.length n)),
      t = t₁.appList xs ∧ E[Γ] ⊢ t₁ : F ∧
      ∃ (ι : Metalean.IndSig) (η : Metalean.Head ζ (.inductive ι)) (s : Fin ι.nsorts)
        (L : Fin ι.nlevels → Metalean.Level lps.length) (l : Metalean.Level lps.length)
        (ps : Fin ι.nparams → Metalean.Expr ζ lps.length n)
        (ms : Fin ι.nsorts → Metalean.Expr ζ lps.length n)
        (mins : (t : Fin ι.nsorts) → Fin (ι.nctors t) → Metalean.Expr ζ lps.length n)
        (is : Fin (ι.nindices s) → Metalean.Expr ζ lps.length n)
        (m : Expr) (m'' : Metalean.Expr ζ lps.length n),
        as[casesMajor iv]? = some m ∧ B iv.name = some (.ind η s) ∧ TrM E B lps Γ Δ m m'' ∧
        E[Γ] ⊢ .recr η s L l ps ms mins is m'' : F ∧
        (∀ l₀, casesSortLevel iv us = some l₀ →
          TrLevel lps l₀ = some ((E.get η).block.level{L})) ∧
        (d.levelParams.length = iv.levelParams.length ↔ ¬ LeanLargeElim (E.get η).block) ∧
        (¬ LeanLargeElim (E.get η).block → l = .zero) := by
  have hns := casesOn_notSpecial (us := us) henv hsub hd
  obtain ⟨h', xs, hh, hxs, rfl⟩ := CasesWhred.trM_spine_inv hns as he
  have hlen := hxs.length_eq
  have happ : h'.appList xs =
      (h'.appList (xs.take (casesArity iv))).appList (xs.drop (casesArity iv)) := by
    rw [← TrApps.appList_append, List.take_append_drop]
  rw [happ] at ht
  obtain ⟨⟨F, hF⟩, -⟩ := InstPre.appList_inv ht
  have he₁ := trM_spine (List.forall₂_take (casesArity iv) hxs) hns hh
  have hmaj : casesMajor iv < (as.take (casesArity iv)).length := by
    simp only [List.length_take, casesArity, casesMajor] at hsat ⊢; omega
  have hm := List.getElem?_eq_getElem hmaj
  obtain ⟨ι, η, s, L, l, ps, ms, mins, is, m', hBT, hm', hred, hlv, hlp, hl0⟩ :=
    SrcProof.casesOn_recr henv hE hsub hcs (by simp only [List.length_take]; omega) hm he₁
  have hR := (WHRedS.defeq hE hΓ hred hF).right
  rw [List.getElem?_take_of_lt (by simp only [casesArity, casesMajor]; omega)] at hm
  exact ⟨_, F, _, happ, hF, ι, η, s, L, l, ps, ms, mins, is, _, m', hm, hBT, hm', hR, hlv,
    hlp d hd, hl0⟩

/-- A typed translation of a spine of a recognized `casesOn` with as many universe parameters as
its inductive, with at least its arity of arguments, is a proof: the saturated prefix reduces to
the recursor node at the motive level `0` (`SrcProof.casesOn_recr`), and applications of a proof
are proofs. Reference: the proof case of `erases_tCase` (`MR E/Extract.v:111`; `isErasable` of
the `tCase`, whose return type is in `Prop`). -/
theorem isErasable_cases_box {σ : EvalEnv} (henv : ProgEnv P ζ E B) (hE : EnvWF E)
    (hsub : SubEnv σ.decls P) {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
    {Δ : MLCtx ζ lps.length n} (hΓ : E[Γ] ⊢ ok) {c : Name} {iv : InductiveVal}
    {d : DefinitionVal} {us : List Level} {as : List Expr} {t T : Metalean.Expr ζ lps.length n}
    (hcs : σ.casesOn? c = some iv) (hd : findDecl σ.decls c = some (.defnInfo d))
    (hlp : d.levelParams.length = iv.levelParams.length) (hsat : casesArity iv ≤ as.length)
    (he : TrM E B lps Γ Δ (mkAppN (.const c us) as.toArray) t) (ht : E[Γ] ⊢ t : T) :
    IsErasable E Γ t := by
  obtain ⟨t₁, F, xs, rfl, hF, ι, η, s, L, l, ps, ms, mins, is, -, m'', -, -, -, hR, -, hlv,
    hl0⟩ := cases_sat_split henv hE hsub hΓ hcs hd hsat he ht
  refine ErasableAtom.IsErasable.appList hE hΓ xs ?_ ht
  rw [hl0 (hlv.1 hlp)] at hR
  obtain ⟨U, hU, hUe⟩ := SimInd.isErasable_recr_zero hR
  exact ⟨U, (Defeq.uniqTy hE hΓ hR hU).conv hF, hUe⟩

/-- Every field of a typed constructor node of the inductive of a recognized `casesOn` with more
universe parameters than its inductive is erasable, when the sort of the discriminant's type may
be zero (`u`, a level of the type of every typed translation of the major, is not never-zero): the
block eliminates into every sort (`IndBlock.recr`), not by being proof-relevant (its level is zero
under some assignment), so as a subsingleton (`ML.Inductive.LargeElim.singleton_of_eval_zero`), whose ordinary fields
are at level `0` or index variables (`Ctor.Eligible`); index variables are Lean index fields
(`IndBlock.indexVars`), which the constructors of a recognized `casesOn` have none of
(`NoIndexFields`); a recursive field forces the block's level to `0`, and its type is then a `Π`
into the block's sort (`Ctx.pi_prop`). Reference: `Subsingleton` (`MR P/PCUICElimination.v:45`);
`elim_only_at_universe_zero` (Lean's kernel, `src/kernel/inductive.cpp`); DV-25. -/
theorem fieldsErasable_reduced {σ : EvalEnv} (henv : ProgEnv P ζ E B) (hE : EnvWF E)
    (hsub : SubEnv σ.decls P) (hdc : DepClosed σ.decls) (hidx : NoIndexFields σ.decls)
    {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n} (hΓ : E[Γ] ⊢ ok)
    {c : Name} {ci : CasesInfo} {iv : InductiveVal} {d : DefinitionVal} {us : List Level}
    {as : List Expr} {t T : Metalean.Expr ζ lps.length n} {u : Level}
    (hci : casesInfo? σ.decls c = some ci) (hcs : σ.casesOn? c = some iv)
    (hd : findDecl σ.decls c = some (.defnInfo d))
    (hlp : d.levelParams.length ≠ iv.levelParams.length) (hsat : casesArity iv ≤ as.length)
    (he : TrM E B lps Γ Δ (mkAppN (.const c us) as.toArray) t) (ht : E[Γ] ⊢ t : T)
    (hlev : ∀ m m'', as[casesMajor iv]? = some m → TrM E B lps Γ Δ m m'' →
      (∃ M, E[Γ] ⊢ m'' : M) →
      ∃ l M, TrLevel lps u = some l ∧ E[Γ] ⊢ m'' : M ∧ E[Γ] ⊢ M : .sort l)
    (hu : u.isNeverZero = false) :
    FieldsErasable E B iv.name := by
  obtain ⟨t₁, F, xs, -, -, ι, η, s, L, l, ps, ms, mins, is, m, m'', hm, hBT, hm'', hR, -, hlv,
    -⟩ := cases_sat_split henv hE hsub hΓ hcs hd hsat he ht
  have hLE : (E.get η).block.LargeElim :=
    LeanLargeElim.toLargeElim (Classical.byContradiction fun h => hlp (hlv.2 h))
  obtain ⟨-, hps, -, -, his, hmaj⟩ := Defeq.recr_typed hE hΓ hR
  obtain ⟨l₁, M, hTr, hmM, hMl⟩ := hlev m m'' hm hm'' ⟨_, hmaj⟩
  -- the sort of the discriminant's type is the block's level at `L`, zero somewhere
  have hl₁ : l₁ = (E.get η).block.level{L} := by
    obtain ⟨l₂, hMI⟩ := TypeEq.sort_uniq hE hΓ (Defeq.uniqTy hE hΓ hmM hmaj)
    have h1 := TypeEq.sort_inj hE hΓ (Defeq.uniqTy hE hΓ hMI.left hMl)
    have h2 := TypeEq.sort_inj hE hΓ (Defeq.uniqTy hE hΓ hMI.right (Defeq.indDF hps his).left)
    rw [← h1, h2]
  obtain ⟨ν, hν⟩ : ∃ ν, l₁.eval ν = 0 := by
    by_contra hne
    have h := (TrLevel.isNeverZero_iff hTr).2 fun ν hν => hne ⟨ν, hν⟩
    rw [hu] at h
    cases h
  rw [hl₁] at hν
  -- the block's ctors have no index variable among their fields
  obtain ⟨lps₀, Is, Cs, Rs, orders, ⟨⟨_, _, _, _, hblk⟩, -, hfd, -, hind, -⟩, hix⟩ :=
    CasesWhred.ProgEnv.blockIdx henv η
  have hT := hind _ s hBT
  have hivd := SimInd.casesOn?_ind hcs
  have hI := hfd (.inductInfo (Is s)) (by simp [IndBlock.decls, List.mem_ofFn])
  rw [CasesWhred.name_inductInfo, ← hT, SrcDefeq.findDecl_sub hsub hivd] at hI
  cases hI
  obtain ⟨-, -, -, hpI, -, hcsI, -⟩ := hblk.ind s
  have hindI : findConst σ.decls ci.indName = some (.inductInfo (Is s)) := by
    have hcs' := hcs
    simp only [EvalEnv.casesOn?, hci] at hcs'
    split at hcs'
    · cases hcs'
      assumption
    · cases hcs'
  have hnoidx : ∀ (c' : Fin (ι.nctors s)) (i : Fin (ι.nindices s))
      (f : Fin (ι.ctors s c').nfields),
      (((E.get η).block.ctors s c').targetIndices i).isVar ≠ some (ι.nparams + f.val) := by
    intro c' i f hx
    have hany := hix s c' ⟨i, f, hx⟩
    have hmem : (Cs s c').name ∈ (Is s).ctors := by
      rw [hcsI]; exact List.mem_ofFn.mpr ⟨c', rfl⟩
    obtain ⟨ci₀, hci₀⟩ := Option.isSome_iff_exists.1
      ((hdc _ (findDecl_eq_some hivd).1).2.2.1 _ rfl _ hmem)
    have hC := hfd (.ctorInfo (Cs s c')) (by
      simp only [IndBlock.decls, List.mem_append, List.mem_flatten, List.mem_ofFn]
      exact .inl (.inr ⟨_, ⟨s, rfl⟩, List.mem_ofFn.mpr ⟨c', rfl⟩⟩))
    rw [CasesWhred.name_ctorInfo, SrcDefeq.findDecl_sub hsub hci₀] at hC
    cases hC
    have hall := hidx c ci (Is s) hci hindI _ hmem _ hci₀
    rw [hpI, List.all_eq_true] at hall
    obtain ⟨x, hx, hxs⟩ := List.any_eq_true.1 hany
    have := hall x hx
    cases x <;> simp_all
  -- the fields of a typed constructor node
  intro ι' η' s' hB' ℓ' n' Γ' c' ls ps' fds recFds _ hΓ' ⟨U, hU⟩
  rw [hBT] at hB'
  cases hB'
  have helig : ((E.get η).block.ctors s c').Eligible (E.get η).block.level := by
    exact (ML.Inductive.LargeElim.singleton_of_eval_zero hLE L hν c').2
  have hct := Metalean.Defeq.ctor_typed hE hU
  have hctor := (hE.entryWF η).block.ctors s c'
  refine ⟨fun f => ?_, fun f => ?_⟩
  · rcases helig.ordinary f with hz | ⟨i, hi⟩
    · have hs := hctor.ordinaryFieldExpr f hct.1 hct.2.1
      rw [hz, Metalean.Level.inst_zero] at hs
      exact ⟨_, hct.2.1 f, .inr hs⟩
    · exact absurd hi (hnoidx c' i f)
  · have hz := helig.recursive f
    obtain ⟨v, hv⟩ := hctor.recursiveFieldExpr rfl f hΓ' hct.1 hct.2.1
    rw [Metalean.Ctor.recursiveFieldExpr_eq] at hv
    obtain ⟨hΓt, w, hindw⟩ := Metalean.Ctx.pi_isType_inv _ hΓ' hv
    obtain ⟨-, -, -, -, hsort⟩ := Metalean.Defeq.ind_inv hindw
    have hindp := hsort.conv hindw
    rw [hz, Metalean.Level.inst_zero] at hindp
    have hpi := Metalean.Ctx.pi_prop _ hΓt hindp
    rw [← Metalean.Ctor.recursiveFieldExpr_eq] at hpi
    exact ⟨_, hct.2.2 f, .inr hpi⟩

end

/-! ## The runs of `visitCases` up to its branches -/

section
variable {pc : PureCtx} {tc : TravCtx} {st : ErasureState} {ps : PureState}

open TravFrame

/-- `getConst` on a constant of the declarations returns it, without changing the states. -/
theorem getConst_run {n : Name} {ci : ConstantInfo} (h : findConst pc.decls n = some ci) :
    (getConst (m := PureM) n).runPure st tc pc ps = .ok ((ci, st), ps) := by
  unfold Erasure.getConst
  rw [runPure_bind]
  show (Except.ok ((findConst pc.decls n, st), ps) >>= _) = _
  rw [h]
  rfl

/-- `getOrFail` on a value returns it, without changing the states. -/
theorem getOrFail_run {γ : Type} [Inhabited γ] {o : Option γ} {a : γ} {msg : String}
    (h : o = some a) : (getOrFail (m := PureM) o msg).runPure st tc pc ps = .ok ((a, st), ps) := by
  subst h
  rfl

end

/-- A recognized `casesOn` is the definition named `c`, of the inductive `ci.indName` of the
declarations, and its discriminant is the major premise. -/
theorem casesInfo?_names {decls : List ConstantInfo} {c : Name} {ci : CasesInfo}
    (h : casesInfo? decls c = some ci) :
    ci.declName = c ∧ ∃ iv, findDecl decls ci.indName = some (.inductInfo iv) ∧
      ci.discrPos = casesMajor iv := by
  unfold casesInfo? at h
  split at h
  next T =>
    split at h
    next d I R hd hI hR =>
      dsimp only at h
      split at h
      next j body alts before hj hb ha hbe =>
        split at h
        next hok =>
          cases h
          exact ⟨rfl, I, hI, rfl⟩
        next => cases h
      next => cases h
    next => cases h
  next => cases h

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P : List ConstantInfo}
  {lps : List Name} {view : EnvView} {cfg : ErasureConfig} {decls : List ConstantInfo}

open Steps

/-- What the recognizer gives about a recognized `casesOn` `c` in the evaluation environment:
its inductive `iv` and definition `cd`, the arity and the discriminant's position. -/
theorem casesInfo?_eval {c : Name} {ci : CasesInfo} (hci : casesInfo? decls c = some ci) :
    ∃ iv cd, findDecl decls ci.indName = some (.inductInfo iv) ∧
      findDecl decls c = some (.defnInfo cd) ∧ ci.declName = c ∧
      (evalEnvOf view cfg decls).casesOn? c = some iv ∧ ci.arity = casesArity iv ∧
      ci.discrPos = casesMajor iv := by
  obtain ⟨iv, cd, hiv, hd, har, -⟩ := casesInfo?_arity hci
  obtain ⟨hdn, iv', hiv', hdp⟩ := casesInfo?_names hci
  rw [hiv] at hiv'
  cases hiv'
  exact ⟨iv, cd, hiv, hd, hdn, by simp [EvalEnv.casesOn?, evalEnvOf, hci, hiv], har, hdp⟩

/-- The `□` branch of `visitCases` (`LeanToLambdaBox/Erasure.lean:878`): on a saturated spine of a
recognized `casesOn` with as many universe parameters as its inductive, a successful run returns
`□` without changing the states, and `□` erases the spine (`isErasable_cases_box`). Reference: the
proof case of `erases_tCase` (`MR E/Extract.v:111`), by `erases_box` (`MR E/Extract.v:131`). -/
theorem casesSat_box (hG : CoreEnv E B P decls view cfg) {j : Nat} {c : Name} {ci : CasesInfo}
    (hci : casesInfo? decls c = some ci) {cd : DefinitionVal} {iv : InductiveVal}
    (hd : findDecl decls c = some (.defnInfo cd))
    (hiv : findDecl decls ci.indName = some (.inductInfo iv))
    (hlp : cd.levelParams.length = iv.levelParams.length) {n : Nat}
    {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n} {S : Name → Prop}
    {us : List Level} {as : List Expr} {t : Metalean.Expr ζ lps.length n} {st : ErasureState}
    {tc : TravCtx} {ps : PureState} {r : LBTerm} {st' : ErasureState} {ps' : PureState}
    (hctx : CtxOK E B lps Γ Δ cfg tc ps) (hok : StateOK E B (evalEnvOf view cfg decls) st)
    (he : TrM E B lps Γ Δ (mkAppN (.const c us) as.toArray) t) (ht : ∃ T, E[Γ] ⊢ t : T)
    (hsat : ci.arity ≤ as.length)
    (hrun : (visitCases (m := PureM) j ci as.toArray).runPure st tc ⟨decls, view⟩ ps =
      .ok ((r, st'), ps')) :
    Erases E B lps (evalEnvOf view cfg decls) Γ Δ (mkAppN (.const c us) as.toArray) r ∧
      ErasesDeps E B (evalEnvOf view cfg decls) st'.gdecls r ∧
      Grows E B (evalEnvOf view cfg decls) S st st' ps ps' := by
  obtain ⟨iv', cd', hiv', hd', hdn, hcs, har, hdp⟩ := casesInfo?_eval (view := view) (cfg := cfg) hci
  rw [hiv] at hiv'; cases hiv'
  rw [hd] at hd'; cases hd'
  obtain ⟨T, hT⟩ := ht
  have hbox : Erases E B lps (evalEnvOf view cfg decls) Γ Δ (mkAppN (.const c us) as.toArray)
      .box :=
    .box ⟨t, he, isErasable_cases_box hG.prog hG.wf hG.sub hctx.wf hcs hd hlp (by omega) he hT⟩
  cases j with
  | zero => rw [visitCases] at hrun; cases hrun
  | succ j =>
  have hdisc : as.toArray[ci.discrPos]? = some (as[casesMajor iv]'(by
      simp only [casesArity] at har; omega)) := by
    rw [hdp]; simp
  rw [visitCases, TravFrame.runPure_bind, getOrFail_run hdisc, Steps.ok_bind'] at hrun
  dsimp only at hrun
  rw [TravFrame.runPure_bind, getConst_run (pc := ⟨decls, view⟩) (show findConst decls _ = _ from hiv), Steps.ok_bind'] at hrun
  dsimp only at hrun
  rw [TravFrame.runPure_bind, hdn, getConst_run (pc := ⟨decls, view⟩) (show findConst decls _ = _ from hd), Steps.ok_bind'] at hrun
  dsimp only at hrun
  simp only [show (cd.levelParams.length == iv.levelParams.length) = true by simpa using hlp,
    ↓reduceIte] at hrun
  cases hrun
  exact ⟨hbox, .box, .refl hok⟩


/-- A recognized `casesOn` gives its alternatives (one per constructor) and their range. -/
theorem casesInfo?_alts {decls : List ConstantInfo} {c : Name} {ci : CasesInfo} {iv : InductiveVal}
    (h : casesInfo? decls c = some ci) (hiv : findDecl decls ci.indName = some (.inductInfo iv)) :
    ∃ alts, ctorAlts decls iv.ctors = some alts ∧ ci.altNumParams = alts.toArray ∧
      ci.altsRange = (casesMajor iv + 1)...(casesArity iv) := by
  unfold casesInfo? at h
  split at h
  next T =>
    split at h
    next d I R hd hI hR =>
      dsimp only at h
      split at h
      next j body alts before hj hb ha hbe =>
        split at h
        next hok =>
          cases h
          rw [show findDecl decls T = findConst decls T from rfl, hI] at hiv
          cases hiv
          exact ⟨alts, ha, rfl, rfl⟩
        next => cases h
      next => cases h
    next => cases h
  next => cases h

/-- `List.foldl` of λ□ applications is `mkApps`. -/
theorem foldl_app_mkApps (l : List LBTerm) : ∀ t : LBTerm, l.foldl .app t = mkApps t l := by
  induction l with
  | nil => intro t; rfl
  | cons a l ih => intro t; exact ih (.app t a)

/-- `visitAppArgs (j + 1) tf args`, from `visitExpr` at `j`: the head applied to erasures of the
arguments, in order. -/
theorem visitAppArgs_run {j : Nat} (ih : ∀ e, ExprSpec E B view cfg decls j e)
    {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    {S : Name → Prop} {st st' : ErasureState} {tc : TravCtx} {ps ps' : PureState}
    {r tf : LBTerm} {args : List Expr}
    (hctx : CtxOK E B lps Γ Δ cfg tc ps) (hsc : ScopeOK decls S)
    (hargs : ∀ a ∈ args, (∀ d, nameOccurs d a = true → S d) ∧ MachineFree cfg a ∧
      NatPlain cfg a ∧ RecShaped cfg decls a ∧ ∃ a', TrM E B lps Γ Δ a a' ∧ ∃ A, E[Γ] ⊢ a' : A)
    (hok : StateOK E B (evalEnvOf view cfg decls) st)
    (hdf : ErasesDeps E B (evalEnvOf view cfg decls) st.gdecls tf)
    (hrun : (visitAppArgs (m := PureM) (j + 1) tf args.toArray).runPure st tc ⟨decls, view⟩ ps =
      .ok ((r, st'), ps')) :
    ∃ args', List.Forall₂ (Erases E B lps (evalEnvOf view cfg decls) Γ Δ) args args' ∧
      r = mkApps tf args' ∧ ErasesDeps E B (evalEnvOf view cfg decls) st'.gdecls r ∧
      Grows E B (evalEnvOf view cfg decls) S st st' ps ps' := by
  rw [visitAppArgs, ← Array.foldlM_toList, List.toList_toArray] at hrun
  induction args generalizing tf st ps with
  | nil =>
    cases hrun
    exact ⟨[], .nil, rfl, hdf, .refl hok⟩
  | cons a l ihl =>
    rw [List.foldlM_cons, TravFrame.runPure_bind] at hrun
    obtain ⟨⟨⟨x, st₁⟩, ps₁⟩, hx, hrun⟩ := OracleWhnf.ok_of_bind hrun
    rw [TravFrame.runPure_bind] at hx
    obtain ⟨⟨⟨ta, st₂⟩, ps₂⟩, ha, hx⟩ := OracleWhnf.ok_of_bind hx
    cases hx
    obtain ⟨hoa, hma, hna, hra, a', hta, A, hA⟩ := hargs a (.head _)
    have ⟨hera, hdepsa, hgra⟩ := ih a hctx hsc hoa hma hna hra hok hta ⟨A, hA⟩ ha
    obtain ⟨args', hF, rfl, hdeps, hgr⟩ := ihl (tf := .app tf ta) (hctx.mono hgra.next)
      (fun b hb => hargs b (.tail _ hb)) hgra.inv (.app (ErasesDeps.ext hgra.ext hdf) hdepsa) hrun
    exact ⟨ta :: args', .cons hera hF, rfl, hdeps, hgra.trans hgr⟩

/-- Applying an application spine. -/
theorem mkApps_append (l₁ l₂ : List LBTerm) :
    ∀ f : LBTerm, mkApps (mkApps f l₁) l₂ = mkApps f (l₁ ++ l₂) := by
  induction l₁ with
  | nil => intro f; rfl
  | cons a l₁ ih => intro f; exact ih (.app f a)

/-- The dependencies of an application spine are those of its head and arguments. -/
theorem deps_mkApps_of {σ : EvalEnv} {lenv : GlobalDeclarations} {as : List LBTerm} :
    ∀ {f : LBTerm}, ErasesDeps E B σ lenv f →
      (∀ a ∈ as, ErasesDeps E B σ lenv a) → ErasesDeps E B σ lenv (mkApps f as) := by
  induction as with
  | nil => intro f hf _; exact hf
  | cons a l ih =>
    intro f hf has
    exact ih (.app hf (has a (.head _))) fun b hb => has b (.tail _ hb)

/-- `pure` returns its value without changing the states. -/
theorem runPure_pure {α : Type} {a : α} {st : ErasureState} {tc : TravCtx} {pc : PureCtx}
    {ps : PureState} : (Pure.pure a : EraseT PureM α).runPure st tc pc ps = .ok ((a, st), ps) := rfl

/-- The reduced branch of `visitCases` (`LeanToLambdaBox/Erasure.lean:900`): on a saturated spine of
a recognized `casesOn` with more universe parameters than its inductive, which has one
constructor, when the oracle's level `u` of the discriminant's type is not never-zero, a
successful run erases the alternative and applies it to `□` for each field of the constructor and
to the erasures of the extra arguments; this is `Erases.casesReduced`, whose `FieldsErasable` is
`fieldsErasable_reduced` (the recognizer's constructor has no index field, so no index is
substituted). Reference: `eval_iota_sing` (`MR E/EWcbvEval.v:162`) at erasure time; DV-25. -/
theorem casesSat_reduced (hG : CoreEnv E B P decls view cfg) {j : Nat}
    (ih : StepIH E B view cfg decls j) {c : Name} {ci : CasesInfo}
    (hci : casesInfo? decls c = some ci) {cd : DefinitionVal} {iv : InductiveVal}
    (hd : findDecl decls c = some (.defnInfo cd))
    (hiv : findDecl decls ci.indName = some (.inductInfo iv))
    (hlp : cd.levelParams.length ≠ iv.levelParams.length) (h1 : iv.ctors.length = 1) {n : Nat}
    {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n} {S : Name → Prop}
    {us : List Level} {as : List Expr} {t : Metalean.Expr ζ lps.length n} {st : ErasureState}
    {tc : TravCtx} {ps : PureState} {r : LBTerm} {st' : ErasureState} {ps' : PureState}
    {u : Level} (hu : ∀ m, as[casesMajor iv]? = some m →
      Pure.typeLevel ⟨decls⟩ oracleFuel tc.locals m = .ok u) (hz : u.isNeverZero = false)
    (hctx : CtxOK E B lps Γ Δ cfg tc ps) (hsc : ScopeOK decls S)
    (hocc : ∀ d, nameOccurs d (mkAppN (.const c us) as.toArray) = true → S d)
    (hmf : MachineFree cfg (mkAppN (.const c us) as.toArray))
    (hnp : NatPlain cfg (mkAppN (.const c us) as.toArray))
    (hrf : RecShaped cfg decls (mkAppN (.const c us) as.toArray))
    (hok : StateOK E B (evalEnvOf view cfg decls) st)
    (he : TrM E B lps Γ Δ (mkAppN (.const c us) as.toArray) t) (ht : ∃ T, E[Γ] ⊢ t : T)
    (hsat : ci.arity ≤ as.length)
    (hrun : (visitCases (m := PureM) j ci as.toArray).runPure st tc ⟨decls, view⟩ ps =
      .ok ((r, st'), ps')) :
    Erases E B lps (evalEnvOf view cfg decls) Γ Δ (mkAppN (.const c us) as.toArray) r ∧
      ErasesDeps E B (evalEnvOf view cfg decls) st'.gdecls r ∧
      Grows E B (evalEnvOf view cfg decls) S st st' ps ps' := by
  obtain ⟨iv', cd', hiv', hd', hdn, hcs, har, hdp⟩ := casesInfo?_eval (view := view) (cfg := cfg) hci
  rw [hiv] at hiv'; cases hiv'
  rw [hd] at hd'; cases hd'
  obtain ⟨cn, hcn⟩ : ∃ cn, iv.ctors = [cn] := by
    match h : iv.ctors, h1 with
    | [cn], _ => exact ⟨cn, rfl⟩
  obtain ⟨alts, halts, hanp, hrange⟩ := casesInfo?_alts hci hiv
  rw [hcn] at halts
  obtain ⟨cv, hcv, rfl⟩ : ∃ cv, findConst decls cn = some (.ctorInfo cv) ∧
      alts = [.ctor cn cv.numFields] := by
    unfold ctorAlts at halts
    split at halts
    · rename_i cv _ hcv hrest
      simp only [ctorAlts] at hrest
      cases hrest
      cases halts
      exact ⟨cv, hcv, rfl⟩
    · cases halts
  have har2 : ci.arity = casesMajor iv + 1 + 1 := by rw [har, casesArity, hcn]; rfl
  have hmlt : casesMajor iv + 1 < as.length := by omega
  have hdisc : as.toArray[ci.discrPos]? = some (as[casesMajor iv]'(by omega)) := by
    rw [hdp]; simp
  cases j with
  | zero => rw [visitCases] at hrun; cases hrun
  | succ j =>
  rw [visitCases, TravFrame.runPure_bind, getOrFail_run hdisc, Steps.ok_bind'] at hrun
  dsimp only at hrun
  rw [TravFrame.runPure_bind, getConst_run (pc := ⟨decls, view⟩) (show findConst decls _ = _ from hiv),
    Steps.ok_bind'] at hrun
  dsimp only at hrun
  rw [TravFrame.runPure_bind, hdn, getConst_run (pc := ⟨decls, view⟩) (show findConst decls _ = _ from hd),
    Steps.ok_bind'] at hrun
  dsimp only at hrun
  simp only [show (cd.levelParams.length == iv.levelParams.length) = false by simpa using hlp,
    Bool.false_eq_true, ↓reduceIte] at hrun
  rw [TravFrame.runPure_read_bind, TravFrame.runPure_read_bind, TravFrame.runPure_bind,
    TravFrame.runPure_liftM, TravFrame.typeLevel_run, hu _ (List.getElem?_eq_getElem _)] at hrun
  dsimp only [Except.map] at hrun
  rw [Steps.ok_bind', Steps.ok_bind'] at hrun
  dsimp only at hrun
  rw [hz, hanp, hrange, TravFrame.runPure_bind, TravFrame.rco_forIn,
    Nat.toList_rco_eq_singleton (by rw [← har, har2])] at hrun
  have halt : as.toArray[casesMajor iv + 1]? = some (as[casesMajor iv + 1]'hmlt) := by simp
  simp only [List.forIn_cons, List.forIn_nil,
    show Std.Stream.next? (Std.toStream #[CasesAltInfo.ctor cn cv.numFields]) =
      some (CasesAltInfo.ctor cn cv.numFields, (#[CasesAltInfo.ctor cn cv.numFields].toSubarray 1 1))
      from rfl, TravFrame.runPure_bind, getOrFail_run halt, Steps.ok_bind', runPure_pure,
    Bool.not_false, Bool.true_and] at hrun
  have hcv' : findConst decls cn = some (.ctorInfo cv) := hcv
  have hnoidx : (indexFields iv.numParams cv.type).all Option.isNone = true :=
    hG.idx c ci iv hci hiv cn (by rw [hcn]; exact List.mem_singleton_self _) cv hcv
  have hnc : iv.numCtors = 1 := by rw [InductiveVal.numCtors, hcn]; rfl
  simp only [hcn, List.forIn_cons, List.forIn_nil, ↓reduceIte, hnc, beq_self_eq_true,
    List.getElem?_cons_zero, Std.HashMap.getElem?_empty] at hrun
  have hrun' : ((do
        let alt_nt ← visitExpr (m := PureM) j (as[casesMajor iv + 1]'hmlt)
        let branch ← pure (List.foldl LBTerm.app alt_nt (List.replicate cv.numFields LBTerm.box))
        visitAppArgs j branch (Std.Slice.toArray (as.toArray.toSubarray ci.arity))) :
        EraseT PureM LBTerm).runPure st tc ⟨decls, view⟩ ps = .ok ((r, st'), ps') := by
    by_cases hni : iv.numIndices > 0
    · rw [ite_eq_left_of_eq_true _ _ (by simpa using hni), TravFrame.runPure_bind, TravFrame.runPure_bind,
        TravFrame.runPure_bind, getConst_run (pc := ⟨decls, view⟩) hcv', Steps.ok_bind'] at hrun
      dsimp only at hrun
      simp only [hnoidx, ↓reduceIte, runPure_pure, Steps.ok_bind'] at hrun
      rw [TravFrame.runPure_bind, getOrFail_run rfl, Steps.ok_bind'] at hrun
      dsimp only at hrun
      simpa only [Std.HashMap.getElem?_insert_self, Std.HashMap.getElem?_empty] using hrun
    · rw [ite_eq_right_of_eq_false _ _ (by simpa using hni), TravFrame.runPure_bind, getOrFail_run rfl,
        Steps.ok_bind'] at hrun
      dsimp only at hrun
      simpa only [Std.HashMap.getElem?_insert_self] using hrun
  clear hrun
  obtain ⟨T, hT⟩ := ht
  -- the arguments
  have hsp := mkAppN_toArray (.const c us) as
  have hQ : ∀ {Q : Expr → Prop}, (∀ f a, Q (.app f a) → Q f ∧ Q a) →
      Q (mkAppN (.const c us) as.toArray) → ∀ a ∈ as, Q a := fun hQ' h =>
    (foldl_pred hQ' (by rw [← hsp]; exact h)).2
  have hoccA := hQ (Q := fun x => ∀ d, nameOccurs d x = true → S d)
    (fun f a h => ⟨fun d hd => h d (by simp [nameOccurs, hd]),
      fun d hd => h d (by simp [nameOccurs, hd])⟩) hocc
  have hmfA := hQ (Q := MachineFree cfg) (fun _ _ h => h) hmf
  have hnpA := hQ (Q := NatPlain cfg) (fun _ _ h => h) hnp
  have hrfA := hQ (Q := RecShaped cfg decls) (fun _ _ h => h) hrf
  have htyA := (spine_typed (casesOn_notSpecial (σ := evalEnvOf view cfg decls) hG.prog hG.sub hd)
    he ⟨T, hT⟩).2
  have hargs : ∀ a ∈ as, (∀ d, nameOccurs d a = true → S d) ∧ MachineFree cfg a ∧
      NatPlain cfg a ∧ RecShaped cfg decls a ∧ ∃ a', TrM E B lps Γ Δ a a' ∧ ∃ A, E[Γ] ⊢ a' : A :=
    fun a ha => ⟨hoccA a ha, hmfA a ha, hnpA a ha, hrfA a ha, htyA a ha⟩
  -- the alternative
  have haltm : as[casesMajor iv + 1]'hmlt ∈ as := List.getElem_mem _
  rw [TravFrame.runPure_bind] at hrun'
  obtain ⟨⟨⟨alt', st₁⟩, ps₁⟩, halt_run, hrun'⟩ := OracleWhnf.ok_of_bind hrun'
  rw [TravFrame.runPure_bind, runPure_pure, Steps.ok_bind'] at hrun'
  dsimp only at hrun'
  obtain ⟨hoa, hma, hna, hra, a', hta, A, hA⟩ := hargs _ haltm
  have ⟨hera, hdepsa, hgra⟩ := ih.expr j (by omega) _ hctx hsc hoa hma hna hra hok hta ⟨A, hA⟩
    halt_run
  cases j with
  | zero => rw [visitAppArgs] at hrun'; cases hrun'
  | succ j =>
  have hslice : Std.Slice.toArray (as.toArray.toSubarray ci.arity) = (as.drop ci.arity).toArray := by
    rw [← Subarray.toArray_eq_sliceToArray]
    apply Array.ext'
    simp [Subarray.toList_eq]
    rw [List.take_of_length_le (by simp)]
    rcases le_total ci.arity as.length with h | h
    · rw [Nat.min_eq_left h]
    · rw [Nat.min_eq_right h, List.drop_of_length_le h, List.drop_of_length_le (le_refl _)]
  rw [hslice] at hrun'
  obtain ⟨extra', hF, rfl, hdeps, hgr⟩ := visitAppArgs_run (ih.expr j (by omega))
    (hctx.mono hgra.next) hsc (fun a ha => hargs a (List.mem_of_mem_drop ha)) hgra.inv
    (by
      rw [foldl_app_mkApps]
      exact deps_mkApps_of hdepsa fun b hb => by
        rw [(List.mem_replicate.1 hb).2]; exact .box)
    hrun'
  refine ⟨?_, hdeps, hgra.trans hgr⟩
  -- the reduced form
  have hfe : FieldsErasable E B iv.name :=
    fieldsErasable_reduced hG.prog hG.wf hG.sub hG.deps hG.idx hctx.wf hci hcs hd hlp
      (by omega) he hT (fun m m'' hm hmt hmty => Pure.typeLevel_sound hG.prog hG.wf hG.sub hctx.wf
        hctx.locals hctx.nobv hmt hmty (hu m hm)) hz
  obtain ⟨ι, η, s, hBT, hnp₁, -, hlenI⟩ :=
    hG.prog.lookup_ind (SrcDefeq.findDecl_sub (σ := evalEnvOf view cfg decls) hG.sub hiv)
  obtain ⟨cv₂, hcn₂, hcv₂, -, hnp₂, -, -⟩ := SimInd.ind_ctor hG.prog hBT
    (SrcDefeq.findDecl_sub (σ := evalEnvOf view cfg decls) hG.sub hiv) ⟨0, by omega⟩
  rw [hcn] at hcn₂
  simp only [List.getElem?_cons_zero, Option.some.injEq] at hcn₂
  rw [← hcn₂, SrcDefeq.findDecl_sub (σ := evalEnvOf view cfg decls) hG.sub hcv'] at hcv₂
  cases hcv₂
  have hlenF := hF.length_eq
  have has : as = as.take (casesMajor iv) ++ [as[casesMajor iv]'(by omega)] ++
      [as[casesMajor iv + 1]'hmlt] ++ as.drop ci.arity := by
    rw [har2, List.append_assoc, List.append_assoc, List.singleton_append, List.singleton_append,
      ← List.drop_eq_getElem_cons hmlt, ← List.drop_eq_getElem_cons, List.take_append_drop]
  have key := Erases.casesReduced (σ := evalEnvOf view cfg decls) (us := us) (lps := lps) (Γ := Γ)
    (Δ := Δ) (pre := as.take (casesMajor iv)) (maj := as[casesMajor iv]'(by omega))
    (extra := as.drop ci.arity) hcs hfe hcn hcv' (by rw [hnp₂, ← hnp₁]; exact hnoidx)
    (by simp; omega) hera hlenF (fun i a a' h₁ h₂ => EraseProof.forall₂_getElem? hF i a a' h₁ h₂)
  rw [← has] at key
  rw [foldl_app_mkApps, mkApps_append]
  exact key

end

end StepsCases

end EraseProof
