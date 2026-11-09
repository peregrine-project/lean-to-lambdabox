import EraseProof.Simulation.Cases

/-!
# Inductive cases of the relation-level simulation

The cases of `erases_correct` (`MR E/ErasureCorrectness.v:51`) for the rules of `SrcEval` that
involve inductive types: constructor spines (`ctor`, `eta`), Nat literals, projections (`proj`,
`projProp`) and the `casesOn` rules whose alternative is not applied to fields (`casesLitZero`,
`casesProof`). Each case is a theorem whose premises are the rule's premises and the induction
hypotheses of its evaluation premises (`ErasesSim`), as in `EraseProof.Simulation.Cases`. The
λ□ side reads the erased inductive blocks through `ErasesInd` (`SimInd.lookupCtor_of`).
-/

open Lean Erasure
open Metalean (Defeq EnvWF TypeEq WHRed)

namespace EraseProof

namespace SimInd

/-- An evidently zero level is not never-zero. -/
theorem isNeverZero_of_evidentZero : ∀ {l : Level}, EvidentZero l = true → l.isNeverZero = false
  | .zero, _ => rfl
  | .max a b, h => by
    simp only [EvidentZero, Bool.and_eq_true] at h
    simp [Level.isNeverZero, isNeverZero_of_evidentZero h.1, isNeverZero_of_evidentZero h.2]
  | .imax a b, h => by
    simp only [EvidentZero] at h
    simp [Level.isNeverZero, isNeverZero_of_evidentZero h]
  | .succ _, h | .param _, h | .mvar _, h => by simp [EvidentZero] at h

end SimInd

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P : List ConstantInfo}
  {σ : EvalEnv} {lps : List Name} {lenv : GlobalDeclarations}

/-- A `casesOn` that `SrcEval.casesProof` reduces is one the eraser reduces: an evidently zero
level is not never-zero (`Level.isNeverZero`), so in the `casesProof` case of `erases_correct` only
`Erases.casesReduced` and `Erases.box` apply. Reference: none. -/
theorem CasesReduced.of_evidentZero {iv : InductiveVal} {us : List Level} {l : Level} {cn : Name}
    (hl : casesSortLevel iv us = some l) (hz : EvidentZero l = true) (hc : iv.ctors = [cn]) :
    CasesReduced iv us :=
  ⟨by simp [hc], l, hl, SimInd.isNeverZero_of_evidentZero hz⟩

/-- An inductive declared in `Prop` (its declared sort evidently zero) is in `Prop` in Metalean:
its declared type translates (`ConstTyped`) and sort injectivity forces the block's level to `0`
(`SrcProof.ind_level`), so `ErasesInd` makes its λ□ block propositional. Reference:
`isPropositional` (`MR P/PCUICFirstorder.v:109`). -/
theorem PropInductive.of_propInd (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P)
    {S : Name} (h : σ.propInd S = true) : PropInductive E B S := by
  unfold EvalEnv.propInd at h
  split at h
  · rename_i iv hiv
    split at h
    · rename_i k u har
      have hP := SrcDefeq.findDecl_sub hsub hiv
      have hname : iv.name = S := (findDecl_eq_some hP).2
      subst hname
      obtain ⟨ι, η, s, hB, -⟩ := henv.lookup_ind hP
      obtain ⟨a, hk, ha, -, hL⟩ := SrcProof.ind_level henv hE hP hB har
      have ha0 := SrcProof.evidentZero_tr h ha
      refine ⟨ι, η, s, hB, ?_⟩
      have := hL (fun i => Metalean.Level.param i)
      rw [Metalean.Level.inst_id, ha0] at this
      rw [this]
      rfl
    · cases h
  · cases h

namespace SimInd

/-- A recursor at level `0` is a proof. -/
theorem isErasable_recr_zero {ℓ n : Nat} {Γ : Metalean.Ctx ζ ℓ 0 n} {ι : Metalean.IndSig}
    {η : Metalean.Head ζ (.inductive ι)} {s : Fin ι.nsorts} {ls : Fin ι.nlevels → Metalean.Level ℓ}
    {ps : Fin ι.nparams → Metalean.Expr ζ ℓ n} {ms : Fin ι.nsorts → Metalean.Expr ζ ℓ n}
    {mins : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Metalean.Expr ζ ℓ n}
    {is : Fin (ι.nindices s) → Metalean.Expr ζ ℓ n} {maj T : Metalean.Expr ζ ℓ n}
    (ht : E[Γ] ⊢ .recr η s ls .zero ps ms mins is maj : T) :
    IsErasable E Γ (.recr η s ls .zero ps ms mins is maj) := by
  obtain ⟨_, _, _, _, _, -, -, -, -, -, -, hres, hT⟩ := Defeq.recr_inv ht
  exact ⟨_, hT.conv ht, .inr hres.left⟩

/-- A field of a large-eliminating structure in `Prop` is in `Prop`: the structure is not of level
`≥ 1`, so it eliminates as a subsingleton, whose ordinary fields are at level `0` (no indices). -/
theorem field_level_zero {ι : Metalean.IndSig} {I : Metalean.Inductive ζ ι} {s : Fin ι.nsorts}
    {c : Fin (ι.nctors s)} (hst : I.IsStructure s c) (hl : I.level = .zero)
    (f : Fin (ι.ctors s c).nfields) : ((I.ctors s c).ordinary f).level = .zero := by
  rcases hst.largeElim with hsub | h
  · rcases (hsub.eligible s c).ordinary f with h | ⟨i, -⟩
    · exact h
    · exact hst.no_indices.elim i
  · rw [hl] at h
    simpa using h (fun _ => 0)

/-- Every typed translation of a projection out of an inductive in `Prop` is a proof. -/
theorem projOfProp_isErasable {S : Name} {i : Nat} {e₀ : Expr}
    {t T : Metalean.Expr ζ lps.length 0} (hP : PropInductive E B S)
    (he : TrM E B lps .nil [] (.proj S i e₀) t) (ht : E[.nil] ⊢ t : T) : IsErasable E .nil t := by
  obtain ⟨ι', η', s', hB', hl⟩ := hP
  generalize hx : Expr.proj S i e₀ = x at he
  cases he with
  | projStruct hst hi hB =>
    cases hx
    rw [hB] at hB'
    cases hB'
    rw [hst.projTerm_eq_recr] at ht ⊢
    rw [field_level_zero hst hl, Metalean.Level.inst_zero] at ht ⊢
    exact isErasable_recr_zero ht
  | projProof =>
    cases hx
    rw [projProofTerm] at ht ⊢
    exact isErasable_recr_zero ht
  | special => exact absurd hx (CasesWhred.ne_mkAppN_const fun _ _ h => by cases h)
  | _ => cases hx

/-- Every typed translation of a neutral proof projection is erasable. -/
theorem propProj_isErasable (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P)
    {e : Expr} (hp : PropProj σ e) :
    ∀ {t T : Metalean.Expr ζ lps.length 0}, TrM E B lps .nil [] e t → E[.nil] ⊢ t : T →
      IsErasable E .nil t := by
  have hok := SrcDefeq.nil_ok (E := E) (lps := lps)
  have proj : ∀ {S : Name} {i : Nat} {e₀ : Expr} {t T : Metalean.Expr ζ lps.length 0},
      σ.propInd S = true → TrM E B lps .nil [] (.proj S i e₀) t → E[.nil] ⊢ t : T →
      IsErasable E .nil t := fun hS =>
    projOfProp_isErasable (PropInductive.of_propInd henv hE hsub hS)
  induction hp with
  | proj hS => exact fun he ht => proj hS he ht
  | projProj hS => exact fun he ht => proj hS he ht
  | @app f a hf ih =>
    intro t T he ht
    obtain ⟨S, i, e₀, hfn⟩ := RelInst.propProj_head hf
    have hnsp : ¬ SpecialHead B f := fun ⟨c, us, _, hfn', _⟩ => by rw [hfn] at hfn'; cases hfn'
    obtain ⟨f₀, a₀, hf₀, -, rfl, ⟨F, hF⟩, -⟩ := TrM.wf_app hE hok hnsp he ht
    exact IsErasable.app hE hok (ih hf₀ hF) ht

end SimInd

/-- A neutral proof projection is erasable: a projection out of a `Prop` structure is typed only at
a field that is a proof (Metalean's recursor of the projection is at level `0`). Reference: none
(DV-24). -/
theorem ErasableS.propProj (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P)
    {e : Expr} {t T : Metalean.Expr ζ lps.length 0} (hp : PropProj σ e)
    (he : TrM E B lps .nil [] e t) (ht : E[.nil] ⊢ t : T) : ErasableS E B lps .nil [] e :=
  ⟨t, he, SimInd.propProj_isErasable henv hE hsub hp he ht⟩

/-! ## The erased inductive blocks -/

namespace SimInd

/-- The position of a name found by `idxOf?`. -/
theorem getElem?_of_idxOf? {l : List Name} {x : Name} {j : Nat} (h : l.idxOf? x = some j) :
    l[j]? = some x := by
  rw [List.idxOf?_eq_some_iff] at h
  obtain ⟨h1, h2, -⟩ := h
  simp [h1, h2]

/-- The λ□ inductive of a Lean inductive determines it when the block names of `σ` do not
collide. -/
theorem indIdOf_inj (hbinj : BlockNamesInj σ.decls) {T T' : Name} {iid : InductiveId}
    (h₁ : IndIdOf σ T = some iid) (h₂ : IndIdOf σ T' = some iid) : T = T' := by
  unfold IndIdOf at h₁ h₂
  split at h₁
  · rename_i iv hiv
    split at h₂
    · rename_i iv' hiv'
      obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h₁
      obtain ⟨j', hj', he⟩ := Option.map_eq_some_iff.mp h₂
      simp only [InductiveId.mk.injEq] at he
      obtain ⟨hk, rfl⟩ := he
      have hall := (hbinj iv' iv ⟨_, (findDecl_eq_some hiv').1, rfl⟩
        ⟨_, (findDecl_eq_some hiv).1, rfl⟩).1 hk
      have h1 := getElem?_of_idxOf? hj
      have h2 := getElem?_of_idxOf? hj'
      rw [hall, h1] at h2
      exact Option.some.inj h2
    · cases h₂
  · cases h₁

/-- The constructor `C` is the `cv.cidx`-th constructor of its inductive, which has the
constructor's parameter count. -/
theorem ctor_block (henv : ProgEnv P ζ E B) (hsub : SubEnv σ.decls P) {C : Name}
    {cv : ConstructorVal} (hc : findDecl σ.decls C = some (.ctorInfo cv)) {iv : InductiveVal}
    (hiv : findDecl σ.decls cv.induct = some (.inductInfo iv)) :
    iv.ctors[cv.cidx]? = some C ∧ iv.numParams = cv.numParams := by
  have hcP := SrcDefeq.findDecl_sub hsub hc
  have hivP := SrcDefeq.findDecl_sub hsub hiv
  obtain ⟨hm, hn⟩ := findDecl_eq_some hcP
  obtain ⟨ι, ζ₀, E₀, B₀, η₀, lps₀, Is, Cs, Rs, orders, s, k, hblk, rfl, hI⟩ :=
    SrcProof.ctor_mem_block henv hm
  obtain ⟨-, -, -, hpI, -, hcs, -⟩ := hblk.ind s
  obtain ⟨-, -, hind, hcidx, hpC, -⟩ := hblk.ctor s k
  have hfI := CasesWhred.findDecl_of_nodup henv.fresh hI
  rw [CasesWhred.name_inductInfo, ← hind, hivP] at hfI
  cases hfI
  refine ⟨?_, by rw [hpI, hpC]⟩
  rw [hcidx, hcs]
  simp only [List.getElem?_ofFn]
  simp [← hn, CasesWhred.name_ctorInfo]

/-- A constructor of the program is among its inductive's constructors. -/
theorem ctor_listed (henv : ProgEnv P ζ E B) {C : Name} {cv : ConstructorVal}
    (hc : findDecl P C = some (.ctorInfo cv)) :
    ∃ iv, findDecl P cv.induct = some (.inductInfo iv) ∧ C ∈ iv.ctors := by
  obtain ⟨hm, hn⟩ := findDecl_eq_some hc
  obtain ⟨ι, ζ₀, E₀, B₀, η₀, lps₀, Is, Cs, Rs, orders, s, k, hblk, rfl, hI⟩ :=
    SrcProof.ctor_mem_block henv hm
  obtain ⟨-, -, -, -, -, hcs, -⟩ := hblk.ind s
  obtain ⟨-, -, hind, -⟩ := hblk.ctor s k
  have hfI := CasesWhred.findDecl_of_nodup henv.fresh hI
  rw [CasesWhred.name_inductInfo, ← hind] at hfI
  refine ⟨_, hfI, ?_⟩
  rw [hcs, List.mem_ofFn]
  exact ⟨k, by simpa [CasesWhred.name_ctorInfo] using hn⟩

/-- What λ□ needs of an erased constructor: its block's entry has the constructor's parameter
count and field count, and is propositional exactly when the inductive is in `Prop`. -/
theorem lookupCtor_of {lenv : GlobalDeclarations} (henv : ProgEnv P ζ E B)
    (hsub : SubEnv σ.decls P) {C : Name} {cv : ConstructorVal} {iid : InductiveId}
    (hc : findDecl σ.decls C = some (.ctorInfo cv)) (hid : IndIdOf σ cv.induct = some iid)
    (hind : ErasesInd E B σ lenv cv.induct) :
    ∃ mib ob cb, lookupCtor lenv iid cv.cidx = some (mib, ob, cb) ∧ mib.npars = cv.numParams ∧
      cb.nargs = cv.numFields ∧ (ob.propositional = true ↔ PropInductive E B cv.induct) := by
  obtain ⟨iv, hiv, hall⟩ := hind
  have hid' := hid
  unfold IndIdOf at hid'
  rw [hiv] at hid'
  obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp hid'
  obtain ⟨iv', mib, ob, hiv', hl, hnp, -, hctors, hprop⟩ := hall j _ (getElem?_of_idxOf? hj)
  rw [hiv] at hiv'
  cases hiv'
  obtain ⟨hC, hnp'⟩ := ctor_block henv hsub hc hiv
  obtain ⟨cv', cb, hc', hcb, hnargs⟩ := hctors _ _ hC
  rw [hc] at hc'
  cases hc'
  refine ⟨mib, ob, cb, ?_, by rw [hnp, hnp'], hnargs, hprop⟩
  simp [lookupCtor, hl, hcb]

/-- The erased dependencies of a λ□ spine. -/
theorem deps_mkApps {lenv : GlobalDeclarations} :
    ∀ {f : LBTerm} {as : List LBTerm}, ErasesDeps E B σ lenv (mkApps f as) →
      ErasesDeps E B σ lenv f ∧ ∀ a ∈ as, ErasesDeps E B σ lenv a
  | _, [], h => ⟨h, by simp⟩
  | f, a :: as, h => by
    obtain ⟨h1, h2⟩ := deps_mkApps (f := .app f a) (as := as) h
    cases h1 with
    | app hf ha =>
      refine ⟨hf, fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ha
      · exact h2 x hx

/-- The erased block of a constructor that λ□ reaches through its erased dependencies. -/
theorem deps_construct {lenv : GlobalDeclarations} (hbinj : BlockNamesInj σ.decls) {T : Name}
    {iid : InductiveId} {c : Nat} {args : List LBTerm} (hid : IndIdOf σ T = some iid)
    (h : ErasesDeps E B σ lenv (.construct iid c args)) : ErasesInd E B σ lenv T := by
  cases h with
  | construct hid' hind => rw [indIdOf_inj hbinj hid' hid] at hind; exact hind

/-- λ□ evaluates a constructor applied to arguments that evaluate, one by one, up to the
constructor's arity (`eval_construct`). -/
theorem lbeval_construct {lenv : GlobalDeclarations} {iid : InductiveId} {c : Nat}
    {mib : MutualInductiveBody} {ob : OneInductiveBody} {cb : ConstructorBody}
    (hlk : lookupCtor lenv iid c = some (mib, ob, cb)) :
    ∀ (as vs : List LBTerm), as.length = vs.length → as.length ≤ mib.npars + cb.nargs →
      (∀ (i : Nat) a v, as[i]? = some a → vs[i]? = some v → LBEval defaultFlags lenv a v) →
      LBEval defaultFlags lenv (mkApps (.construct iid c []) as) (mkApps (.construct iid c []) vs) := by
  intro as
  induction as using List.reverseRecOn with
  | nil =>
    intro vs hl _ _
    obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero hl.symm
    exact .atom (by simp [mkApps, lbAtom, defaultFlags, hlk])
  | append_singleton as a ih =>
    intro vs hl hle hall
    obtain ⟨vs, v, rfl⟩ : ∃ vs' v, vs = vs' ++ [v] := by
      rcases SimCases.eq_nil_or_snoc vs with rfl | h
      · simp at hl
      · exact h
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hl
    obtain ⟨hall', hav⟩ := SimCases.forall_snoc hl hall
    rw [SimCases.mkApps_snoc, SimCases.mkApps_snoc]
    simp only [List.length_append, List.length_singleton] at hle
    exact .construct rfl hlk (ih vs hl (by omega) hall') (by omega) hav

/-- A choice of one witness per position. -/
theorem choose_list {γ : Type} {n : Nat} {R : Nat → γ → Prop} (h : ∀ i, i < n → ∃ y, R i y) :
    ∃ ys : List γ, ys.length = n ∧ ∀ (i : Nat) y, ys[i]? = some y → R i y := by
  refine ⟨List.ofFn fun i : Fin n => Classical.choose (h i i.2), by simp, fun i y hy => ?_⟩
  rw [List.getElem?_ofFn] at hy
  split at hy
  · rename_i hi
    cases hy
    exact Classical.choose_spec (h i hi)
  · cases hy

/-- A λ□ constructor spine is not `□`. -/
theorem mkApps_construct_ne_box {iid : InductiveId} {c : Nat} {as : List LBTerm} :
    mkApps (.construct iid c []) as ≠ .box := by
  intro h
  have := congrArg headOf h
  rw [headOf_mkApps] at this
  cases this

/-- A spine with fewer arguments than its head's arity erases to `□` or as its η-expansion. -/
theorem eta_inv {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    {c : Name} {us : List Level} {as : List Expr} {e' : Expr} {tb : LBTerm}
    (heta : σ.etaSpine? c us as = some e')
    (h : Erases E B lps σ Γ Δ (mkAppN (.const c us) as.toArray) tb) :
    (tb = .box ∧ ErasableS E B lps Γ Δ (mkAppN (.const c us) as.toArray)) ∨
      Erases E B lps σ Γ Δ e' tb := by
  obtain ⟨ar, har, hlt⟩ := SimCases.etaSpine?_lt heta
  have inj : ∀ {c' : Name} {us' : List Level} {as' : List Expr},
      mkAppN (.const c us) as.toArray = mkAppN (.const c' us') as'.toArray →
        c = c' ∧ us = us' ∧ as = as' := fun hx => by
    rw [mkAppN_eq_foldl, mkAppN_eq_foldl] at hx
    exact foldl_app_const_inj hx
  generalize hx : mkAppN (Expr.const c us) as.toArray = x at h
  cases h with
  | box hb => subst hx; exact .inl ⟨rfl, hb⟩
  | eta heta' h' =>
    obtain ⟨rfl, rfl, rfl⟩ := inj hx
    rw [heta] at heta'
    cases heta'
    exact .inr h'
  | ctor hc' _ _ hle =>
    obtain ⟨rfl, rfl, rfl⟩ := inj hx
    unfold specialArity at har
    rw [hc'] at har
    cases har
    omega
  | cases hco _ _ _ hpre halts =>
    obtain ⟨rfl, rfl, rfl⟩ := inj hx
    rw [SimCases.specialArity_casesOn hco] at har
    cases har
    simp only [List.length_append, List.length_singleton, hpre, halts, casesArity] at hlt
    omega
  | casesReduced hco _ hcs _ _ hpre =>
    obtain ⟨rfl, rfl, rfl⟩ := inj hx
    rw [SimCases.specialArity_casesOn hco] at har
    cases har
    simp only [List.length_append, hpre, casesArity, hcs, List.length_cons,
      List.length_nil] at hlt
    omega
  | quotMk hcq hk _ _ | quotLift hcq hk _ _ _ =>
    obtain ⟨rfl, rfl, rfl⟩ := inj hx
    simp [specialArity, hcq, hk, quotEvalArity] at har
    subst har
    simp at hlt
    omega
  | recLet hcr _ hps hms hmins his | recFix hcr _ hps hms hmins his =>
    obtain ⟨rfl, rfl, rfl⟩ := inj hx
    simp only [specialArity, hcr, Option.some.injEq] at har
    subst har
    simp only [List.length_append, List.length_singleton, hps, hms, hmins, his] at hlt
    omega
  | app hns =>
    obtain ⟨bs, -, rfl⟩ := SrcDefeq.spine_app hx
    refine absurd ⟨c, us, SrcDefeq.getAppFn_mkAppN_const _ _ _, ?_⟩ hns
    rcases SrcDefeq.specialArity_some har with ⟨cv, hcv, -⟩ | ⟨iv, hiv⟩ | ⟨qv, hqv, hq⟩ |
      ⟨rv, hrv, -⟩
    · exact .inl ⟨cv, hcv⟩
    · exact .inr (.inl (by rw [hiv]; rfl))
    · exact .inr (.inr (.inl ⟨qv, hqv, by rw [hq]; rfl⟩))
    · exact .inr (.inr (.inr ⟨rv, hrv⟩))
  | const _ hsa =>
    obtain ⟨-, rfl, -⟩ := SrcDefeq.spine_const hx
    rw [har] at hsa
    cases hsa
  | bvar | fvar | lam | letE | proj | litZero | litSucc | mdata =>
    exact absurd hx.symm (CasesWhred.ne_mkAppN_const fun _ _ h => by cases h)

/-- `lamsOf` with at least one binder is a λ. -/
theorem lamsOf_succ_lam {k : Nat} {ty body e : Expr} (h : lamsOf (k + 1) ty body = some e) :
    ∃ x A b bi, e = .lam x A b bi := by
  cases ty with
  | forallE x d b bi =>
    simp only [lamsOf, Option.map_eq_some_iff] at h
    obtain ⟨e₀, -, rfl⟩ := h
    exact ⟨_, _, _, _, rfl⟩
  | _ => simp [lamsOf] at h

/-- The η-expansion of a spine is a λ. -/
theorem etaSpine?_lam {c : Name} {us : List Level} {as : List Expr} {e' : Expr}
    (h : σ.etaSpine? c us as = some e') : ∃ x A b bi, e' = .lam x A b bi := by
  unfold EvalEnv.etaSpine? at h
  split at h
  · rename_i ci ar hci har
    split at h
    · rename_i hlt
      obtain ⟨ty, -, hl⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨k, hk⟩ : ∃ k, ar - as.length = k + 1 := ⟨ar - as.length - 1, by omega⟩
      rw [hk] at hl
      exact lamsOf_succ_lam hl
    · cases h
  · cases h

/-- An erasure of a λ is a λ□ value. -/
theorem lam_erases_atom {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    {x : Name} {A b : Expr} {bi : BinderInfo} {tb : LBTerm}
    (h : Erases E B lps σ Γ Δ (.lam x A b bi) tb) : lbAtom defaultFlags lenv tb = true := by
  generalize hx : Expr.lam x A b bi = y at h
  cases h with
  | lam | box => rfl
  | ctor | cases | casesReduced | eta | quotMk | quotLift | recLet | recFix =>
    exact absurd hx (CasesWhred.ne_mkAppN_const fun _ _ h => by cases h)
  | bvar | fvar | letE | app | const | proj | litZero | litSucc | mdata => cases hx

/-- The `k`-th constructor of an inductive bound to a Metalean sort: its declaration, counts and
position. -/
theorem ind_ctor (henv : ProgEnv P ζ E B) {T : Name} {iv : InductiveVal} {ι : Metalean.IndSig}
    {η : Metalean.Head ζ (.inductive ι)} {s : Fin ι.nsorts} (hB : B T = some (.ind η s))
    (hiv : findDecl P T = some (.inductInfo iv)) (k : Fin (ι.nctors s)) :
    ∃ cv : ConstructorVal, iv.ctors[k.val]? = some cv.name ∧
      findDecl P cv.name = some (.ctorInfo cv) ∧
      cv.numFields = (ι.ctors s k).nfields + (ι.ctors s k).nrecFields ∧
      cv.numParams = ι.nparams ∧ cv.induct = T ∧ cv.cidx = k.val := by
  obtain ⟨lps₀, Is, Cs, Rs, orders, ⟨⟨_, _, _, _, hblk⟩, -, hfd, -, hind, -⟩⟩ :=
    CasesWhred.ProgEnv.block henv η
  obtain rfl := hind T s hB
  have hI := hfd (.inductInfo (Is s)) (by simp [IndBlock.decls, List.mem_ofFn])
  rw [CasesWhred.name_inductInfo, hiv] at hI
  cases hI
  have hC := hfd (.ctorInfo (Cs s k)) (by
    simp only [IndBlock.decls, List.mem_append, List.mem_flatten, List.mem_ofFn]
    exact .inl (.inr ⟨_, ⟨s, rfl⟩, List.mem_ofFn.mpr ⟨k, rfl⟩⟩))
  obtain ⟨-, -, -, -, -, hcs, -⟩ := hblk.ind s
  obtain ⟨-, -, hind', hcidx, hpC, hf, -⟩ := hblk.ctor s k
  refine ⟨Cs s k, by rw [hcs]; simp, hC, hf, hpC, hind', hcidx⟩

/-- What λ□ needs of the `k`-th constructor of an erased inductive: its block's entry has the
inductive's parameter count and the constructor's field count, and is propositional exactly when
the inductive is in `Prop`. -/
theorem lookupCtor_ind {lenv : GlobalDeclarations} (henv : ProgEnv P ζ E B)
    (hsub : SubEnv σ.decls P) {T : Name} {iid : InductiveId} {ι : Metalean.IndSig}
    {η : Metalean.Head ζ (.inductive ι)} {s : Fin ι.nsorts} (hB : B T = some (.ind η s))
    (hid : IndIdOf σ T = some iid) (hind : ErasesInd E B σ lenv T) (k : Fin (ι.nctors s)) :
    ∃ mib ob cb, lookupCtor lenv iid k.val = some (mib, ob, cb) ∧ mib.npars = ι.nparams ∧
      cb.nargs = (ι.ctors s k).nfields + (ι.ctors s k).nrecFields ∧
      (ob.propositional = true ↔ PropInductive E B T) := by
  obtain ⟨iv, hiv, hall⟩ := hind
  have hid' := hid
  unfold IndIdOf at hid'
  rw [hiv] at hid'
  obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp hid'
  obtain ⟨iv', mib, ob, hiv', hl, hnp, -, hctors, hprop⟩ := hall j _ (getElem?_of_idxOf? hj)
  rw [hiv] at hiv'
  cases hiv'
  have hivP := SrcDefeq.findDecl_sub hsub hiv
  obtain ⟨cv, hcn, hcP, hnf, -, -, -⟩ := ind_ctor henv hB hivP k
  obtain ⟨cv', cb, hc', hcb, hnargs⟩ := hctors _ _ hcn
  rw [SrcDefeq.findDecl_sub hsub hc', Option.some.injEq] at hcP
  cases hcP
  obtain ⟨-, -, -, hpI, -⟩ := henv.lookup_ind hivP
  obtain ⟨ι', η', s', hB', hp', -⟩ := henv.lookup_ind hivP
  rw [hB] at hB'
  cases hB'
  refine ⟨mib, ob, cb, ?_, by rw [hnp, hp'], by rw [hnargs, hnf], hprop⟩
  simp [lookupCtor, hl, hcb]

/-- The λ□ `propositional` flag and parameter count of an erased inductive. -/
theorem indIsPropAndPars_of {lenv : GlobalDeclarations} {T : Name} {iid : InductiveId}
    {iv : InductiveVal} (hid : IndIdOf σ T = some iid) (hind : ErasesInd E B σ lenv T)
    (hiv : findDecl σ.decls T = some (.inductInfo iv)) :
    ∃ b, indIsPropAndPars lenv iid = some (b, iv.numParams) ∧ (b = true ↔ PropInductive E B T) := by
  obtain ⟨iv', hiv', hall⟩ := hind
  rw [hiv] at hiv'
  cases hiv'
  have hid' := hid
  unfold IndIdOf at hid'
  rw [hiv] at hid'
  obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp hid'
  obtain ⟨iv', mib, ob, -, hl, hnp, -, -, hprop⟩ := hall j _ (getElem?_of_idxOf? hj)
  exact ⟨ob.propositional, by simp [indIsPropAndPars, hl, hnp], hprop⟩

/-- Inversion of an erasure of a projection. -/
theorem proj_inv {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    {S : Name} {i : Nat} {e : Expr} {tb : LBTerm} (h : Erases E B lps σ Γ Δ (.proj S i e) tb) :
    (tb = .box ∧ ErasableS E B lps Γ Δ (.proj S i e)) ∨
    ∃ iid iv e', Subsingleton E B S ∧ IndIdOf σ S = some iid ∧
      findDecl σ.decls S = some (.inductInfo iv) ∧
      (PropInductive E B S ∨ ∃ n u, arityShape iv.type = some (n, u) ∧ u.isNeverZero = true) ∧
      Erases E B lps σ Γ Δ e e' ∧ tb = .proj ⟨iid, iv.numParams, i⟩ e' := by
  generalize hx : Expr.proj S i e = x at h
  cases h with
  | proj hss hid hfd hdisj he' => cases hx; exact .inr ⟨_, _, _, hss, hid, hfd, hdisj, he', rfl⟩
  | box hb => subst hx; exact .inl ⟨rfl, hb⟩
  | ctor | cases | casesReduced | eta | quotMk | quotLift | recLet | recFix =>
    exact absurd hx (CasesWhred.ne_mkAppN_const fun _ _ h => by cases h)
  | bvar | fvar | lam | letE | app | const | litZero | litSucc | mdata => cases hx

/-- The major premise of a typed projection has a typed translation. -/
theorem trM_proj_major {S : Name} {i : Nat} {e : Expr} {t T : Metalean.Expr ζ lps.length 0}
    (he : TrM E B lps .nil [] (.proj S i e) t) (ht : E[.nil] ⊢ t : T) :
    ∃ e₀ M, TrM E B lps .nil [] e e₀ ∧ E[.nil] ⊢ e₀ : M := by
  generalize hx : Expr.proj S i e = x at he
  cases he with
  | projStruct hst hi hS he' =>
    cases hx
    exact ⟨_, _, he', recr_major (by rw [← hst.projTerm_eq_recr]; exact ht)⟩
  | projProof hi hS hs hc hr hf hns he' =>
    cases hx
    exact ⟨_, _, he', recr_major (by rw [projProofTerm] at ht; exact ht)⟩
  | special => exact absurd hx (CasesWhred.ne_mkAppN_const fun _ _ h => by cases h)
  | _ => cases hx

/-- A λ□ constructor spine ending in an argument. -/
theorem mkApps_construct_app {ind : InductiveId} {c : Nat} {args : List LBTerm} {f a : LBTerm}
    (h : mkApps (.construct ind c []) args = .app f a) :
    ∃ init, args = init ++ [a] ∧ f = mkApps (.construct ind c []) init := by
  rcases SimCases.eq_nil_or_snoc args with rfl | ⟨init, y, rfl⟩
  · cases h
  · rw [SimCases.mkApps_snoc] at h
    cases h
    exact ⟨init, rfl, rfl⟩

/-- λ□ constructor spines are injective. -/
theorem mkApps_construct_inj {ind ind' : InductiveId} {c c' : Nat} :
    ∀ {args args' : List LBTerm},
      mkApps (.construct ind c []) args = mkApps (.construct ind' c' []) args' → args = args' := by
  intro args
  induction args using List.reverseRecOn with
  | nil =>
    intro args' h
    rcases SimCases.eq_nil_or_snoc args' with rfl | ⟨init, y, rfl⟩
    · rfl
    · rw [SimCases.mkApps_snoc] at h; cases h
  | append_singleton init y ih =>
    intro args' h
    rw [SimCases.mkApps_snoc] at h
    obtain ⟨init', rfl, hf⟩ := mkApps_construct_app h.symm
    rw [ih hf]

/-- The arguments of a λ□ constructor spine that is an evaluation result evaluate to themselves. -/
theorem construct_args {lenv : GlobalDeclarations} {s t : LBTerm}
    (h : LBEval defaultFlags lenv s t) : ∀ (ind : InductiveId) (c : Nat) (args : List LBTerm),
      t = mkApps (.construct ind c []) args → ∀ a ∈ args, LBEval defaultFlags lenv a a := by
  induction h using LBEval.ind with
  | box =>
    intro ind c args h
    exact absurd h.symm mkApps_construct_ne_box
  | beta _ _ _ _ _ ih | zeta _ _ _ ih | iota _ _ _ _ _ _ _ _ ih | iotaBlock _ _ _ _ _ _ _ _ ih
  | iotaSing _ _ _ _ _ _ ih | fix _ _ _ _ _ _ _ ih | fix' _ _ _ _ _ _ _ ih | delta _ _ _ ih
  | proj _ _ _ _ _ _ _ ih | projBlock _ _ _ _ _ _ _ ih => exact ih
  | projProp =>
    intro ind c args h
    exact absurd h.symm mkApps_construct_ne_box
  | fixValue =>
    intro ind c args h
    have := congrArg headOf h
    simp only [headOf, headOf_mkApps] at this
    cases this
  | construct _ _ h₃ _ h₅ ih₃ _ =>
    intro ind c args h
    obtain ⟨init, rfl, hf⟩ := mkApps_construct_app h.symm
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact ih₃ _ _ init (by rw [mkApps_construct_inj hf]) a ha
    · rw [List.mem_singleton.mp ha]; exact LBEval.idem h₅
  | constructBlock h₁ => exact absurd h₁ (by decide)
  | appCong _ h₂ =>
    intro ind c args h
    obtain ⟨init, -, rfl⟩ := mkApps_construct_app h.symm
    simp [isConstructApp, headOf_mkApps, headOf] at h₂
  | prim =>
    intro ind c args h
    have := congrArg headOf h
    simp only [headOf, headOf_mkApps] at this
    cases this
  | atom ha =>
    intro ind c args h
    subst h
    rcases SimCases.eq_nil_or_snoc args with rfl | ⟨init, y, rfl⟩
    · simp
    · rw [SimCases.mkApps_snoc] at ha; simp [lbAtom] at ha

/-- A never-zero level translates to a level that is at least `1` everywhere. -/
theorem isNeverZero_tr {lps : List Name} :
    ∀ {l : Level} {a : Metalean.Level lps.length}, l.isNeverZero = true →
      TrLevel lps l = some a → ∀ ν, 1 ≤ a.eval ν
  | .succ x, a, _, h => by
    simp only [TrLevel, Option.map_eq_some_iff] at h
    obtain ⟨x', -, rfl⟩ := h
    intro ν
    simp
  | .max x y, a, hz, h => by
    simp only [Level.isNeverZero, Bool.or_eq_true] at hz
    simp only [TrLevel, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨x', hx, y', hy, rfl⟩ := h
    intro ν
    simp only [Metalean.Level.eval_max]
    rcases hz with hz | hz
    · exact Nat.le_trans (isNeverZero_tr hz hx ν) (Nat.le_max_left _ _)
    · exact Nat.le_trans (isNeverZero_tr hz hy ν) (Nat.le_max_right _ _)
  | .imax x y, a, hz, h => by
    simp only [Level.isNeverZero] at hz
    simp only [TrLevel, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨x', -, y', hy, rfl⟩ := h
    intro ν
    simp only [Metalean.Level.eval_imax]
    exact Nat.le_trans (isNeverZero_tr hz hy ν) Nat.le_imax_right
  | .zero, _, hz, _ | .param _, _, hz, _ | .mvar _, _, hz, _ => by
    simp [Level.isNeverZero] at hz

/-- The translation of a saturated constructor spine is a node of the constructor's inductive. -/
theorem ctorNode_tr (henv : ProgEnv P ζ E B) (hsub : SubEnv σ.decls P) {C : Name}
    {us : List Level} {args : List Expr} {cv : ConstructorVal}
    {a₀ : Metalean.Expr ζ lps.length 0} (hC : findDecl σ.decls C = some (.ctorInfo cv))
    (hlen : args.length = cv.numParams + cv.numFields)
    (h : TrM E B lps .nil [] (mkAppN (.const C us) args.toArray) a₀) :
    ∃ (ι : Metalean.IndSig) (η : Metalean.Head ζ (.inductive ι)) (s : Fin ι.nsorts)
      (c : Fin (ι.nctors s)) (ls : Fin ι.nlevels → Metalean.Level lps.length)
      (ps : Fin ι.nparams → Metalean.Expr ζ lps.length 0)
      (fds : Fin (ι.ctors s c).nfields → Metalean.Expr ζ lps.length 0)
      (recFds : Fin (ι.ctors s c).nrecFields → Metalean.Expr ζ lps.length 0),
      B cv.induct = some (.ind η s) ∧ a₀ = .ctor η s c ls ps fds recFds := by
  obtain ⟨ι, η, s, k, o, hB, -, hnp, hnf, -, hI⟩ := henv.lookup_ctor (SrcDefeq.findDecl_sub hsub hC)
  obtain ⟨bs', hlen', -, hsat⟩ := TrM.special_inv hB rfl h
  cases hsat with
  | ctorSat ps fs rest fds recFds _ hfs _ _ =>
    simp only [List.length_append, List.length_ofFn] at hlen'
    have hr : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hr
    exact ⟨_, _, _, _, _, _, _, _, hI, rfl⟩
  | ctorEta _ hlt _ => omega

/-- A saturated constructor spine of an inductive whose declared sort is never zero is not
erasable: its node's type is not an arity, and its sort is not `Prop`. -/
theorem ctor_not_erasable (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P)
    {iv : InductiveVal} {n : Nat} {u : Level}
    (hiv : findDecl σ.decls cv.induct = some (.inductInfo iv))
    (har : arityShape iv.type = some (n, u)) (hnz : u.isNeverZero = true) {C : Name}
    {us : List Level} {args : List Expr} (hC : findDecl σ.decls C = some (.ctorInfo cv))
    (hlen : args.length = cv.numParams + cv.numFields) :
    ¬ ErasableS E B lps .nil [] (mkAppN (.const C us) args.toArray) := by
  rintro ⟨t', htr, hEr⟩
  obtain ⟨ι, η, s, c, ls, ps, fds, rf, hB, rfl⟩ := ctorNode_tr henv hsub hC hlen htr
  have hP := SrcDefeq.findDecl_sub hsub hiv
  have hname : iv.name = cv.induct := (findDecl_eq_some hP).2
  rw [← hname] at hB hP
  obtain ⟨a, hk, ha, -, hL⟩ := SrcProof.ind_level henv hE hP hB har
  obtain ⟨T', hT', hk'⟩ := hEr
  refine IsErasable.ctor_not hE SrcDefeq.nil_ok ?_ hT' ⟨T', hT', hk'⟩
  rw [hL ls]
  intro h0
  have h1 := congrArg (Metalean.Level.eval (fun _ => 0)) h0
  rw [Metalean.Level.eval_inst, Metalean.Level.eval_zero] at h1
  have := isNeverZero_tr hnz ha (Metalean.Level.eval (fun _ => 0) ∘
    (fun i : Fin iv.levelParams.length => ls (i.cast hk.symm)))
  omega

/-- The inductive of a recognized `casesOn` is in the evaluation environment. -/
theorem casesOn?_ind {c : Name} {iv : InductiveVal} (h : σ.casesOn? c = some iv) :
    findDecl σ.decls iv.name = some (.inductInfo iv) := by
  unfold EvalEnv.casesOn? at h
  split at h
  · split at h
    · rename_i hfd
      cases h
      have h2 : iv.name = _ := (findDecl_eq_some hfd).2
      rw [h2]
      exact hfd
    · cases h
  · cases h

/-- An argument of a typed `casesOn` spine has a typed translation. -/
theorem casesOn_arg (henv : ProgEnv P ζ E B) (hsub : SubEnv σ.decls P) {c : Name}
    {us : List Level} {iv : InductiveVal} {as : List Expr} {j : Nat} {x : Expr}
    (hcs : σ.casesOn? c = some iv) (hx : as[j]? = some x) {t T : Metalean.Expr ζ lps.length 0}
    (he : TrM E B lps .nil [] (mkAppN (.const c us) as.toArray) t) (ht : E[.nil] ⊢ t : T) :
    ∃ x₀ X, TrM E B lps .nil [] x x₀ ∧ E[.nil] ⊢ x₀ : X := by
  obtain ⟨d, hd⟩ := SrcDefeq.casesOn?_defn hcs
  obtain ⟨η, hB, -⟩ := henv.lookup_def (SrcDefeq.findDecl_sub hsub hd)
  have hns : ¬ SpecialHead B (.const c us) := by
    rintro ⟨c', us', b, hfn, hb, hs⟩
    cases hfn
    rw [hB] at hb; cases hb; cases hs
  obtain ⟨h', as', hh, has, rfl⟩ := CasesWhred.trM_spine_inv hns as he
  obtain ⟨-, htyped⟩ := InstPre.appList_inv ht
  obtain ⟨b, hb, hx'⟩ := CasesWhred.forall₂_getElem? has hx
  obtain ⟨A, hA⟩ := htyped _ (List.mem_of_getElem? hb)
  exact ⟨_, A, hx', hA⟩

/-- The major premise of a split `casesOn` spine. -/
theorem get_major (pre rest : List Expr) (maj : Expr) :
    (pre ++ [maj] ++ rest)[pre.length]? = some maj := by
  simp

/-- An alternative of a split `casesOn` spine. -/
theorem get_alt (pre alts extra : List Expr) (maj : Expr) {j : Nat} (hj : j < alts.length) :
    (pre ++ [maj] ++ alts ++ extra)[pre.length + 1 + j]? = alts[j]? := by
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by simp)]
  simp

/-- An erasable constructor node is a proof: its type is an inductive, not an arity. -/
theorem ctor_isProof {ℓ n : Nat} {Γ : Metalean.Ctx ζ ℓ 0 n} (hE : EnvWF E) (hΓ : E[Γ] ⊢ ok)
    {ι : Metalean.IndSig} {η : Metalean.Head ζ (.inductive ι)} {s : Fin ι.nsorts}
    {c : Fin (ι.nctors s)} {ls : Fin ι.nlevels → Metalean.Level ℓ}
    {ps : Fin ι.nparams → Metalean.Expr ζ ℓ n}
    {fds : Fin (ι.ctors s c).nfields → Metalean.Expr ζ ℓ n}
    {recFds : Fin (ι.ctors s c).nrecFields → Metalean.Expr ζ ℓ n}
    (h : IsErasable E Γ (.ctor η s c ls ps fds recFds)) :
    IsProof E Γ (.ctor η s c ls ps fds recFds) ∧ (E.get η).block.level{ls} = .zero := by
  obtain ⟨T, ht, hT⟩ := h
  have hl : (E.get η).block.level{ls} = .zero := by
    by_contra hl
    exact IsErasable.ctor_not hE hΓ hl ht ⟨T, ht, hT⟩
  obtain ⟨_, _, _, -, -, -, hind, hT'⟩ := Defeq.ctor_inv ht
  refine ⟨⟨_, hT'.conv ht, ?_⟩, hl⟩
  have := hind.left
  rw [hl] at this
  exact this

end SimInd

open SimInd

/-- The `lit` case of `erases_correct`: a Nat literal erases to `□` or to a λ□ constructor chain
(`Erases.litZero`, `Erases.litSucc`), a λ□ value. Reference: the `eval_atom` case of
`erases_correct` (`MR E/ErasureCorrectness.v:1179`) on primitive values. -/
theorem erases_correct_lit (henv : ProgEnv P ζ E B) (hsub : SubEnv σ.decls P)
    (hbinj : BlockNamesInj σ.decls) {k : Nat} :
    ErasesSim E B lps σ lenv (.lit (.natVal k)) (.lit (.natVal k)) := by
  intro t tb he _ her hdeps
  refine ⟨tb, her, ?_⟩
  obtain ⟨ηNat, hB, -⟩ := CasesWhred.trM_lit_inv he
  have lk : ∀ {iid : InductiveId} {c : Nat} {args : List LBTerm} (j : Fin 2),
      IndIdOf σ ``Nat = some iid → ErasesDeps E B σ lenv (.construct iid c args) →
      ∃ mib ob cb, lookupCtor lenv iid j.val = some (mib, ob, cb) ∧ mib.npars = 0 ∧
        cb.nargs = j.val := by
    intro iid c args j hid hd
    obtain ⟨mib, ob, cb, hlk, hnp, hna, -⟩ :=
      lookupCtor_ind henv hsub hB hid (deps_construct hbinj hid hd) j
    refine ⟨mib, ob, cb, hlk, hnp, ?_⟩
    rw [hna]
    match j with
    | 0 => rfl
    | 1 => rfl
  clear he
  induction k generalizing tb with
  | zero =>
    generalize hx : Expr.lit (.natVal 0) = x at her
    cases her with
    | litZero hid =>
      obtain ⟨mib, ob, cb, hlk, -⟩ := lk 0 hid hdeps
      change lookupCtor lenv _ 0 = _ at hlk
      exact .atom (by simp [lbAtom, defaultFlags, hlk])
    | box => exact .atom rfl
    | litSucc => cases hx
    | ctor | cases | casesReduced | eta | quotMk | quotLift | recLet | recFix =>
      exact absurd hx (CasesWhred.ne_mkAppN_const fun _ _ h => by cases h)
    | bvar | fvar | lam | letE | app | const | proj | mdata => cases hx
  | succ k ih =>
    generalize hx : Expr.lit (.natVal (k + 1)) = x at her
    cases her with
    | litSucc hid h' =>
      cases hx
      cases hdeps with
      | app hd0 hd1 =>
      obtain ⟨mib, ob, cb, hlk, hnp, hna⟩ := lk 1 hid hd0
      change lookupCtor lenv _ 1 = _ at hlk
      exact .construct (args := []) rfl hlk (.atom (by simp [lbAtom, defaultFlags, hlk]))
        (by simp [hnp, hna]) (ih h' hd1)
    | box => exact .atom rfl
    | litZero => cases hx
    | ctor | cases | casesReduced | eta | quotMk | quotLift | recLet | recFix =>
      exact absurd hx (CasesWhred.ne_mkAppN_const fun _ _ h => by cases h)
    | bvar | fvar | lam | letE | app | const | proj | mdata => cases hx

/-- The `eta` case of `erases_correct`: a spine with fewer arguments than its head's arity erases
as its η-expansion, a λ, whose erasure is a λ□ value, or to `□`. Reference: none (MetaRocq
η-expands in λ□, `MR E/EEtaExpanded.v`; DV-23). -/
theorem erases_correct_eta (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P)
    {c : Name} {us : List Level} {as : List Expr} {e' : Expr}
    (heta : σ.etaSpine? c us as = some e') :
    ErasesSim E B lps σ lenv (mkAppN (.const c us) as.toArray) e' := by
  intro t tb he ⟨T, ht⟩ her _
  rcases eta_inv heta her with ⟨rfl, hbx⟩ | h
  · exact erases_correct_box henv hE hsub he ht hbx (.eta heta)
  · obtain ⟨x, A, b, bi, rfl⟩ := etaSpine?_lam heta
    exact ⟨tb, h, .atom (lam_erases_atom h)⟩

/-- The `ctor` case of `erases_correct`: a saturated constructor spine erases to `□` or to the λ□
constructor applied to erasures of its arguments, which evaluate one by one (`eval_construct`) to
erasures of the arguments' values. Reference: the `eval_construct` case of `erases_correct`
(`MR E/ErasureCorrectness.v:1068`). -/
theorem erases_correct_ctor (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P)
    (hbinj : BlockNamesInj σ.decls) {c : Name} {us : List Level} {cv : ConstructorVal}
    {as vs : List Expr} (hc : findDecl σ.decls c = some (.ctorInfo cv))
    (hlen : as.length = cv.numParams + cv.numFields) (hlen' : as.length = vs.length)
    (hev : ∀ (i : Nat) a v, as[i]? = some a → vs[i]? = some v → SrcEval σ a v)
    (ih : ∀ (i : Nat) a v, as[i]? = some a → vs[i]? = some v → ErasesSim E B lps σ lenv a v) :
    ErasesSim E B lps σ lenv (mkAppN (.const c us) as.toArray) (mkAppN (.const c us) vs.toArray) := by
  intro t tb he ⟨T, ht⟩ her hdeps
  have hsrc : SrcEval σ (mkAppN (.const c us) as.toArray) (mkAppN (.const c us) vs.toArray) :=
    .ctor hc hlen hlen' hev
  rcases Erases.ctor_inv hc (by omega) her with ⟨rfl, hbx⟩ | ⟨iid, as', hid, rfl, hlen'', hall⟩
  · exact erases_correct_box henv hE hsub he ht hbx hsrc
  have hnp : ¬ PropInductive E B cv.induct := fun hp =>
    mkApps_construct_ne_box (Erases.ctorProp_box hc hp (by omega) her)
  obtain ⟨ι, η, s, k, o, hB, -, -, -, hmo, -⟩ := henv.lookup_ctor (SrcDefeq.findDecl_sub hsub hc)
  obtain ⟨bs', hlb, hargs, hsat⟩ := TrM.special_inv hB rfl he
  have htyped := SrcDefeq.satTr_ctor_typed hmo hsat ht
  obtain ⟨hd0, hdargs⟩ := deps_mkApps hdeps
  have hind := deps_construct hbinj hid hd0
  obtain ⟨mib, ob, cb, hlk, hnpars, hnargs, -⟩ := lookupCtor_of henv hsub hc hid hind
  have hstep : ∀ i, i < as.length → ∃ y, ∀ a v a', as[i]? = some a → vs[i]? = some v →
      as'[i]? = some a' → Erases E B lps σ .nil [] v y ∧ LBEval defaultFlags lenv a' y := by
    intro i hi
    have ha : as[i]? = some as[i] := List.getElem?_eq_getElem hi
    have hv : vs[i]? = some vs[i] := List.getElem?_eq_getElem (by omega)
    have ha' : as'[i]? = some as'[i] := List.getElem?_eq_getElem (by omega)
    have hb' : bs'[i]? = some bs'[i] := List.getElem?_eq_getElem (by omega)
    obtain ⟨A, hA⟩ := htyped _ (List.getElem_mem _)
    obtain ⟨y, hy, hey⟩ := ih i _ _ ha hv (hargs i _ _ ha hb') ⟨A, hA⟩ (hall i _ _ ha ha')
      (hdargs _ (List.getElem_mem _))
    refine ⟨y, fun a v a' h1 h2 h3 => ?_⟩
    rw [ha] at h1; rw [hv] at h2; rw [ha'] at h3
    cases h1; cases h2; cases h3
    exact ⟨hy, hey⟩
  obtain ⟨ys, hys, hysR⟩ := choose_list hstep
  have hget : ∀ (i : Nat) y, ys[i]? = some y → ∃ v a', vs[i]? = some v ∧ as'[i]? = some a' ∧
      Erases E B lps σ .nil [] v y ∧ LBEval defaultFlags lenv a' y := by
    intro i y hy
    have hi : i < as.length := by rw [← hys]; exact (List.getElem?_eq_some_iff.mp hy).1
    exact ⟨vs[i], as'[i], List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega),
      hysR i y hy _ _ _ (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem (by omega))
        (List.getElem?_eq_getElem (by omega))⟩
  refine ⟨mkApps (.construct iid cv.cidx []) ys, .ctor hc hnp hid (by omega) (by omega) ?_,
    lbeval_construct hlk as' ys (by omega) (by omega) ?_⟩
  · intro i v y hv hy
    obtain ⟨v', a', hv', -, hvy, -⟩ := hget i y hy
    rw [hv] at hv'; cases hv'
    exact hvy
  · intro i a' y ha' hy
    obtain ⟨v', a'', -, ha'', -, hey⟩ := hget i y hy
    rw [ha'] at ha''; cases ha''
    exact hey

/-- The `proj` case of `erases_correct`: the major's erasure evaluates to an erasure of the
constructor value, the λ□ constructor applied to erasures of its arguments (then `eval_proj`
selects the field's erasure, itself a λ□ value) or `□` (then the inductive is in `Prop`, as a
never-zero sort has no proofs, `eval_proj_prop` applies, and the field is a proof). Reference: the
`eval_proj` case of `erases_correct` (`MR E/ErasureCorrectness.v:489`). -/
theorem erases_correct_proj (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P)
    (hbinj : BlockNamesInj σ.decls) {S : Name} {i : Nat} {e m a : Expr} {fs : List Expr}
    (hm : SrcEval σ e m) (hcv : CtorValue σ S m 0 fs) (ha : fs[i]? = some a)
    (ih : ErasesSim E B lps σ lenv e m) : ErasesSim E B lps σ lenv (.proj S i e) a := by
  intro t tb he ⟨T, ht⟩ her hdeps
  have hsrc : SrcEval σ (.proj S i e) a := .proj hm hcv ha
  rcases proj_inv her with ⟨rfl, hbx⟩ | ⟨iid, iv, e', -, hid, hiv, hdisj, he', rfl⟩
  · exact erases_correct_box henv hE hsub he ht hbx hsrc
  obtain ⟨e₀, M, he₀, hM⟩ := trM_proj_major he ht
  cases hdeps with
  | proj hidT hindT hde =>
  have hindS : ErasesInd E B σ lenv S := by
    rw [indIdOf_inj hbinj hidT hid] at hindT; exact hindT
  obtain ⟨mb, hmb, hevmb⟩ := ih he₀ ⟨M, hM⟩ he' hde
  obtain ⟨C, us', cv, ps, hC, hind, hcidx, hps, hfs, rfl⟩ := hcv
  have hlen : (ps ++ fs).length = cv.numParams + cv.numFields := by simp [hps, hfs]
  rcases Erases.ctor_inv hC (by omega) hmb with ⟨rfl, hbx⟩ | ⟨iid', as', hid', rfl, hlen', hall⟩
  · -- the major's value is `□`: the inductive is in `Prop`
    have hP : PropInductive E B S := by
      rcases hdisj with hP | ⟨n, u, har, hnz⟩
      · exact hP
      · rw [← hind] at hiv
        exact absurd hbx (ctor_not_erasable henv hE hsub hiv har hnz hC hlen)
    obtain ⟨b, hb, hbP⟩ := indIsPropAndPars_of hid hindS hiv
    obtain rfl : b = true := hbP.mpr hP
    refine ⟨.box, .box ?_, .projProp (p := ⟨iid, iv.numParams, i⟩) rfl hevmb hb⟩
    exact ErasableS.eval henv hE hsub he ht hsrc ⟨t, he, projOfProp_isErasable hP he ht⟩
  · rw [hind] at hid'
    rw [hid] at hid'
    cases hid'
    have hnp : ¬ PropInductive E B cv.induct := fun hp =>
      mkApps_construct_ne_box (Erases.ctorProp_box hC hp (by omega) hmb)
    rw [hind] at hnp
    obtain ⟨mib, ob, cb, hlk, hnpars, hnargs, hprop⟩ :=
      lookupCtor_of henv hsub hC (by rw [hind]; exact hid) (by rw [hind]; exact hindS)
    rw [hind] at hprop
    have hpf : ob.propositional = false := by
      cases h : ob.propositional
      · rfl
      · exact absurd (hprop.mp h) hnp
    rw [← hind] at hiv
    obtain ⟨-, hnpI⟩ := ctor_block henv hsub hC hiv
    have hai : (ps ++ fs)[cv.numParams + i]? = some a := by
      rw [List.getElem?_append_right (by omega), hps, Nat.add_sub_cancel_left]; exact ha
    have hlt : cv.numParams + i < as'.length := by
      have := (List.getElem?_eq_some_iff.mp hai).1; omega
    have ha' := List.getElem?_eq_getElem hlt
    have hera := hall _ _ _ hai ha'
    refine ⟨_, hera, .proj (p := ⟨iid, iv.numParams, i⟩) (cdecl := cb) rfl (hcidx ▸ hevmb) ?_ ?_ ?_
      (construct_args hevmb _ _ _ rfl _ (List.getElem_mem _))⟩
    · show (lookupCtor lenv iid 0).map _ = _
      rw [← hcidx, hlk]
      simp [hpf, hnpars, hnpI]
    · show as'.length = iv.numParams + cb.nargs
      rw [← hlen', hlen, hnpI, hnargs]
    · show as'[iv.numParams + i]? = _
      rw [hnpI]; exact ha'

/-- The `projProp` case of `erases_correct`: the major's value is a neutral proof, whose erasure
evaluates to `□`; the inductive is in `Prop`, so λ□ projects `□` (`eval_proj_prop`), and the
value, a neutral proof projection, is erasable. Reference: none (DV-24); the λ□ side is
`eval_proj_prop` (`MR E/EWcbvEval.v:238`). -/
theorem erases_correct_projProp (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P)
    (hbinj : BlockNamesInj σ.decls) {S : Name} {i : Nat} {e m : Expr}
    (hS : σ.propInd S = true) (hm : SrcEval σ e m) (hv : AtomSpine σ m ∨ PropProj σ m)
    (ih : ErasesSim E B lps σ lenv e m) :
    ErasesSim E B lps σ lenv (.proj S i e) (.proj S i m) := by
  intro t tb he ⟨T, ht⟩ her hdeps
  have hsrc : SrcEval σ (.proj S i e) (.proj S i m) := .projProp hS hm hv
  rcases proj_inv her with ⟨rfl, hbx⟩ | ⟨iid, iv, e', -, hid, hiv, -, he', rfl⟩
  · exact erases_correct_box henv hE hsub he ht hbx hsrc
  obtain ⟨e₀, M, he₀, hM⟩ := trM_proj_major he ht
  cases hdeps with
  | proj hidT hindT hde =>
  have hindS : ErasesInd E B σ lenv S := by
    rw [indIdOf_inj hbinj hidT hid] at hindT; exact hindT
  obtain ⟨mb, hmb, hevmb⟩ := ih he₀ ⟨M, hM⟩ he' hde
  have hmb0 : mb = .box := hv.elim (fun h => Erases.atomSpine_box h hmb hevmb)
    (fun h => Erases.propProj_box h hmb hevmb)
  subst hmb0
  have hP := PropInductive.of_propInd henv hE hsub hS
  obtain ⟨b, hb, hbP⟩ := indIsPropAndPars_of hid hindS hiv
  obtain rfl : b = true := hbP.mpr hP
  refine ⟨.box, .box ?_, .projProp (p := ⟨iid, iv.numParams, i⟩) rfl hevmb hb⟩
  obtain ⟨w, hw, hdw⟩ := SrcEval.defeq henv hE hsub he ht hsrc
  have hpp : PropProj σ (.proj S i m) := hv.elim (.proj hS) (.projProj hS)
  exact ErasableS.propProj henv hE hsub hpp hw hdw.right

/-- The `casesProof` case of `erases_correct`: the `casesOn` is reduced at erasure time
(`CasesReduced.of_evidentZero`), so its erasure is `□` or the erased alternative applied to no
field (`Erases.casesReduced`). Reference: `eval_iota_sing` (`MR E/EWcbvEval.v:162`), applied at
erasure time; DV-24, DV-25. -/
theorem erases_correct_casesProof (henv : ProgEnv P ζ E B) (hE : EnvWF E)
    (hsub : SubEnv σ.decls P) {c : Name} {us vs : List Level} {iv : InductiveVal}
    {as ps : List Expr} {m mv alt v st : Expr} {l : Level} {cn : Name} {cv : ConstructorVal}
    (hcs : σ.casesOn? c = some iv) (hlen : as.length = casesArity iv)
    (hm : as[casesMajor iv]? = some m) (hmv : SrcEval σ m mv) (hat : AtomSpine σ mv)
    (hl : casesSortLevel iv us = some l) (hz : EvidentZero l = true) (hcn : iv.ctors = [cn])
    (hcv : findDecl σ.decls cn = some (.ctorInfo cv)) (hnf : cv.numFields = 0)
    (hst : σ.spineType? mv = some st) (hps : ps.length = cv.numParams)
    (hpi : piInst ps (Pure.instLevels cv.levelParams vs cv.type) = some st)
    (halt : as[casesMajor iv + 1]? = some alt) (hv : SrcEval σ alt v)
    (ihalt : ErasesSim E B lps σ lenv alt v) :
    ErasesSim E B lps σ lenv (mkAppN (.const c us) as.toArray) v := by
  intro t tb he ⟨T, ht⟩ her hdeps
  have hsrc : SrcEval σ (mkAppN (.const c us) as.toArray) v :=
    .casesProof hcs hlen hm hmv hat hl hz hcn hcv hnf hst hps hpi halt hv
  rcases Erases.cases_inv hcs (by omega) her with ⟨rfl, hbx⟩ | ⟨-, -, -, -, -, -, -, -, -, hnr, -⟩ |
    ⟨pre, maj, alt', extra, cn', cv', altb, extra', rfl, -, hcn', hcv', -, hpre, haltb, hlex, -, rfl⟩
  · exact erases_correct_box henv hE hsub he ht hbx hsrc
  · exact absurd (CasesReduced.of_evidentZero hl hz hcn) hnr
  rw [hcn] at hcn'
  cases hcn'
  rw [hcv] at hcv'
  cases hcv'
  have hex : extra = [] := by
    apply List.eq_nil_of_length_eq_zero
    simp only [List.length_append, hpre, casesArity, hcn, List.length_cons,
      List.length_nil] at hlen
    omega
  subst hex
  obtain rfl : extra' = [] := List.eq_nil_of_length_eq_zero hlex.symm
  have halt' : alt' = alt := by
    have := get_alt pre [alt'] [] maj (j := 0) (by simp)
    rw [hpre, Nat.add_zero] at this
    rw [this] at halt
    simpa using halt
  subst halt'
  obtain ⟨a₀, A, ha₀, hA⟩ := casesOn_arg henv hsub hcs halt he ht
  rw [hnf] at hdeps ⊢
  exact ihalt ha₀ ⟨A, hA⟩ haltb hdeps

/-- The `casesLitZero` case of `erases_correct`: `Nat` has two constructors, so its `casesOn` is
not reduced at erasure time; the major's erasure evaluates to the erasure of `0`, λ□'s `Nat`
constructor `0` (`□` is excluded: `Subsingleton` fails on `Nat`), and λ□'s ι selects the erased
first alternative, under no field binder. Reference: the `eval_iota` case of `erases_correct`
(`MR E/ErasureCorrectness.v:182`) on the literal `0`. -/
theorem erases_correct_casesLitZero (henv : ProgEnv P ζ E B) (hE : EnvWF E)
    (hsub : SubEnv σ.decls P) (hbinj : BlockNamesInj σ.decls) {c : Name} {us : List Level}
    {iv : InductiveVal} {as : List Expr} {m alt v : Expr}
    (hcs : σ.casesOn? c = some iv) (hnat : iv.name = ``Nat) (hlen : as.length = casesArity iv)
    (hm : as[casesMajor iv]? = some m) (hmv : SrcEval σ m (.lit (.natVal 0)))
    (halt : as[casesMajor iv + 1]? = some alt) (hv : SrcEval σ alt v)
    (ihm : ErasesSim E B lps σ lenv m (.lit (.natVal 0)))
    (ihalt : ErasesSim E B lps σ lenv alt v) :
    ErasesSim E B lps σ lenv (mkAppN (.const c us) as.toArray) v := by
  intro t tb he ⟨T, ht⟩ her hdeps
  have hok := SrcDefeq.nil_ok (E := E) (lps := lps)
  have hsrc : SrcEval σ (mkAppN (.const c us) as.toArray) v :=
    .casesLitZero hcs hnat hlen hm hmv halt hv
  -- the Metalean `Nat`
  obtain ⟨m₀, M, hm₀, hM⟩ := casesOn_arg henv hsub hcs hm he ht
  obtain ⟨z₀, hz₀, hdz⟩ := SrcEval.defeq henv hE hsub hm₀ hM hmv
  obtain ⟨ηNat, hB, rfl⟩ := CasesWhred.trM_lit_inv hz₀
  have hivN := casesOn?_ind hcs
  rw [hnat] at hivN
  have hivP := SrcDefeq.findDecl_sub hsub hivN
  obtain ⟨ι', η', s', hB', hpI, -, hnc⟩ := henv.lookup_ind hivP
  rw [hB] at hB'
  cases hB'
  have hnc2 : iv.ctors.length = 2 := hnc
  have hnp0 : iv.numParams = 0 := hpI
  -- `Nat` is not a subsingleton in `Prop`
  have hnotProp : ∀ (hss : Subsingleton E B iv.name), PropInductive E B iv.name → False := by
    intro hss hP
    obtain ⟨ι', η', s', hB', hl⟩ := hP
    rw [hnat, hB] at hB'
    cases hB'
    have hz := hdz.right
    have hpr : IsProof E .nil (natLitM ηNat 0 : Metalean.Expr ζ lps.length 0) := by
      obtain ⟨_, _, _, -, -, -, hind, hT'⟩ := Defeq.ctor_inv hz
      have := hind.left
      rw [hl, Metalean.Level.inst_zero] at this
      exact ⟨_, hT'.conv hz, this⟩
    have := (hss natSig ηNat 0 (by rw [hnat]; exact hB) .nil 0 _ _ _ _ hE hok hpr).1
    exact absurd this (by decide)
  rcases Erases.cases_inv hcs (by omega) her with ⟨rfl, hbx⟩ |
    ⟨pre, maj, alts, extra, iid, maj', brs, extra', rfl, -, hss, hid, hpre, halts, hmaj, hbrs, hcf,
      halt', hlex, -, rfl⟩ |
    ⟨-, -, -, -, cn', -, -, -, -, -, hcn', -⟩
  · exact erases_correct_box henv hE hsub he ht hbx hsrc
  rotate_left
  · rw [hcn'] at hnc2; simp at hnc2
  have hex : extra = [] := by
    apply List.eq_nil_of_length_eq_zero
    simp only [List.length_append, List.length_singleton, hpre, casesArity, halts] at hlen
    omega
  subst hex
  obtain rfl : extra' = [] := List.eq_nil_of_length_eq_zero hlex.symm
  have hmaj' : maj = m := by
    rw [← hpre, List.append_assoc, get_major] at hm
    simpa using hm
  subst hmaj'
  cases hdeps with
  | case hidT hindT hdmaj hdbrs =>
  rw [indIdOf_inj hbinj hidT hid] at hindT
  rw [hnat] at hid hindT hss
  -- the major
  obtain ⟨mb, hmb, hevmb⟩ := ihm hm₀ ⟨M, hM⟩ hmaj hdmaj
  obtain ⟨mib, ob, cb, hlk, hnpars, hnargs, hprop⟩ := lookupCtor_ind henv hsub hB hid hindT 0
  have hpf : ob.propositional = false := by
    cases h : ob.propositional
    · rfl
    · exact (hnotProp (by rw [hnat]; exact hss) (by rw [hnat]; exact hprop.mp h)).elim
  have hmbz : mb = .construct iid 0 [] := by
    generalize hx : Expr.lit (.natVal 0) = x at hmb
    cases hmb with
    | litZero hid' => rw [hid] at hid'; cases hid'; rfl
    | box hb =>
      subst hx
      obtain ⟨w, hw, hwE⟩ := hb
      obtain ⟨ηN, hBN, rfl⟩ := CasesWhred.trM_lit_inv hw
      rw [hB] at hBN
      cases hBN
      obtain ⟨hpr, hl⟩ := ctor_isProof hE hok hwE
      have := (hss natSig ηNat 0 hB .nil 0 _ _ _ _ hE hok hpr).1
      exact absurd this (by decide)
    | litSucc => cases hx
    | ctor | cases | casesReduced | eta | quotMk | quotLift | recLet | recFix =>
      exact absurd hx (CasesWhred.ne_mkAppN_const fun _ _ h => by cases h)
    | bvar | fvar | lam | letE | app | const | proj | mdata => cases hx
  subst hmbz
  -- the first alternative, under no field binder
  have halt0 : alts[0]? = some alt := by
    have := get_alt pre alts [] maj (j := 0) (by omega)
    rw [hpre, Nat.add_zero] at this
    rw [← this]
    exact halt
  obtain ⟨cn0, hcn0⟩ : ∃ cn0, iv.ctors[0]? = some cn0 :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨cv0, hcn0', hcP0, hnf0, -⟩ := ind_ctor henv hB hivP (0 : Fin 2)
  change iv.ctors[0]? = _ at hcn0'
  rw [hcn0] at hcn0'
  cases hcn0'
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (hcf 0 _ hcn0)
  have hk0 : k = 0 := by
    unfold ctorFields at hk
    split at hk
    · rename_i cv' hcv'
      rw [SrcDefeq.findDecl_sub hsub hcv', Option.some.injEq] at hcP0
      cases hcP0
      cases hk
      exact hnf0
    · cases hk
  subst hk0
  obtain ⟨br, hbr⟩ : ∃ br, brs[0]? = some br := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨ns, tbr⟩ := br
  obtain ⟨rfl, herb⟩ := ErasesAlt.zero_inv (halt' 0 _ _ _ _ hcn0 halt0 hbr hk)
  obtain ⟨a₀, A, ha₀, hA⟩ := casesOn_arg henv hsub hcs halt he ht
  obtain ⟨vb, hvb, hevb⟩ := ihalt ha₀ ⟨A, hA⟩ herb (hdbrs _ (List.mem_of_getElem? hbr))
  change lookupCtor lenv _ 0 = _ at hlk
  refine ⟨vb, hvb, .iota (args := []) (cdecl := cb) rfl hevmb ?_ hbr ?_ (by simp)
    (by simpa [iotaRed, substl] using hevb)⟩
  · show (lookupCtor lenv iid 0).map _ = _
    rw [hlk]
    simp [hpf, hnpars, hnp0]
  · simp [hnargs, hnp0]

end

end EraseProof
