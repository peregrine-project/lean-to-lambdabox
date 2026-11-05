import EraseProof.Source.ProofSound
import EraseProof.Oracle.Arity
import EraseProof.Erasable.Inv
import EraseProof.Erasable.Levels

/-!
# Atom spines are erasable

`ErasableS.atom`: the typed translation of a spine `c.{us} a₁ … aₖ` whose head is an atom
(`EvalEnv.isAtom`) is erasable. The head's translation is: for an inductive type former, the
inductive node or its η-term, typed by a sort or a Π-telescope over a sort (an arity); for a
constant, the Metalean constant, typed by the translation of its declared type at the levels,
which is an arity (an arity-typed constant), a proposition (a theorem, `ProgEnv.thm`), or an
evident proposition (`ErasableAtom.evidentProp_prop`: under its Π-binders a `DeltaFree` head
applied to exactly the arguments of its declared arity, at an evidently zero sort). An application
of an erasable term is erasable (`IsErasable.app`). Reference: `Is_type_app`
(`MR E/EArities.v:480`) on `tInd`-headed spines, `isPropositional` (`MR P/PCUICFirstorder.v:109`);
DV-11, DV-24.
-/

open Lean Erasure
open Metalean (Defeq TypeEq EnvWF)

namespace EraseProof

namespace ErasableAtom

variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ}

/-! ## Π-telescopes over sorts -/

/-- A Π-telescope over a sort under a substitution. -/
theorem PiSort.subst {ℓ m : Nat} {X : Metalean.Expr ζ ℓ m} {k : Nat} {u : Metalean.Level ℓ}
    (h : SrcProof.PiSort X k u) : ∀ {n : Nat} (σ : Metalean.Subst ζ ℓ m n),
      SrcProof.PiSort (X.subst σ) k u := by
  induction h with
  | sort => intro _ _; exact .sort
  | forallE _ ih => intro _ σ; exact .forallE (ih σ.lift)

/-- A Π-telescope over a sort under a universe instantiation. -/
theorem PiSort.instL {ℓ ℓ' m : Nat} {X : Metalean.Expr ζ ℓ m} {k : Nat} {u : Metalean.Level ℓ}
    (h : SrcProof.PiSort X k u) (ls : Fin ℓ → Metalean.Level ℓ') :
    SrcProof.PiSort X{ls} k u{ls} := by
  induction h with
  | sort => exact .sort
  | forallE _ ih => exact .forallE ih

/-- A closed Π-telescope over a sort, weakened into a context. -/
theorem PiSort.wkClosed {ℓ : Nat} {X : Metalean.Expr ζ ℓ 0} {k : Nat} {u : Metalean.Level ℓ}
    (h : SrcProof.PiSort X k u) : ∀ {n : Nat}, SrcProof.PiSort (X.wkClosed (n := n)) k u
  | 0 => h
  | n + 1 => by
    have := PiSort.subst (PiSort.wkClosed h (n := n)) (fun v => .var (Metalean.Ren.wkFrom n v))
    rwa [Metalean.Expr.subst_vars] at this

/-- A Π-telescope over a sort is an arity shape. -/
theorem PiSort.shape {ℓ n : Nat} {X : Metalean.Expr ζ ℓ n} {k : Nat} {u : Metalean.Level ℓ}
    (h : SrcProof.PiSort X k u) : OracleArity.Shape X := by
  induction h with
  | sort => exact .sort
  | forallE _ ih => exact .forallE ih

/-- A term typed by a Π-telescope of `k` binders over the sort `u`, applied to `k` arguments, has
type `Sort u`. -/
theorem piSort_appList (hE : EnvWF E) {ℓ n : Nat} {Γ : Metalean.Ctx ζ ℓ 0 n} (hΓ : E[Γ] ⊢ ok)
    {u : Metalean.Level ℓ} : ∀ (as : List (Metalean.Expr ζ ℓ n)) {f F X : Metalean.Expr ζ ℓ n}
      {T : Metalean.Expr ζ ℓ n}, E[Γ] ⊢ f : F → E[Γ] ⊢ F ≡ X typ →
      SrcProof.PiSort X as.length u → E[Γ] ⊢ f.appList as : T → E[Γ] ⊢ T ≡ .sort u typ
  | [], f, F, X, T, hf, hFX, hX, hT => by
    cases hX
    exact (Defeq.uniqTy hE hΓ hT hf).trans hFX
  | a :: as, f, F, X, T, hf, hFX, hX, hT => by
    cases hX with
    | @forallE _ _ A C _ hC =>
    obtain ⟨⟨F', hF'⟩, -⟩ := InstPre.appList_inv (as := as) hT
    obtain ⟨A₁, C₁, hf₁, ha, hF'C⟩ := hF'.app_inv
    have hπ : E[Γ] ⊢ .forallE A₁ C₁ ≡ .forallE A C typ :=
      (Defeq.uniqTy hE hΓ hf₁ hf).trans hFX
    obtain ⟨-, hCC⟩ := TypeEq.forallE_inj hE hΓ hπ
    have hC' := PiSort.subst hC (Metalean.Subst.id.extend a)
    exact piSort_appList hE hΓ as hF' (hF'C.trans (TypeEq.instCongr hΓ ha hCC)) hC' hT

/-- An application spine over an erasable head is erasable. -/
theorem IsErasable.appList (hE : EnvWF E) {ℓ n : Nat} {Γ : Metalean.Ctx ζ ℓ 0 n}
    (hΓ : E[Γ] ⊢ ok) : ∀ (as : List (Metalean.Expr ζ ℓ n)) {f T : Metalean.Expr ζ ℓ n},
      IsErasable E Γ f → E[Γ] ⊢ f.appList as : T → IsErasable E Γ (f.appList as)
  | [], _, _, h, _ => h
  | a :: as, f, T, h, ht => by
    obtain ⟨⟨F, hF⟩, -⟩ := InstPre.appList_inv (as := as) ht
    exact IsErasable.appList hE hΓ as (IsErasable.app hE hΓ h hF) ht

/-! ## Theorems -/

section
open Metalean (Sigs Sig Env Entry Head)
variable {B : Binds ζ} {P : List ConstantInfo}

/-- The statement of a theorem translates to a proposition. Reference: `declared_constant` with
`on_global_env` (MC §3.6) for `opaque` entries of Prop type (`ML Checker/Slow/Loader.lean:122`). -/
theorem lookup_thm {c : Name} {v : TheoremVal} (h : ProgEnv P ζ E B)
    (hc : findDecl P c = some (.thmInfo v)) :
    ∃ T, TrM E B v.levelParams .nil [] v.type T ∧ E[.nil] ⊢ T : .prop := by
  induction h with
  | nil => simp [findDecl] at hc
  | @«axiom» _ _ E₀ _ v' _ hP hfr _ _ _ ih | @defn _ _ E₀ _ v' _ _ hP hfr _ _ _ _ _ ih
  | @«opaque» _ _ E₀ _ v' _ hP hfr _ _ _ _ _ ih =>
    rw [findDecl_cons] at hc
    split at hc
    · cases hc
    · obtain ⟨T, hT, hTp⟩ := ih hc
      exact ⟨_, TrM.wkEnv (hP.set_ext hfr _) hT, Metalean.Defeq.map (envS E₀ _) hTp⟩
  | @thm _ _ E₀ _ v' t hP hfr _ _ _ ht htp ih =>
    rw [findDecl_cons] at hc
    split at hc
    · cases hc
      exact ⟨_, TrM.wkEnv (hP.set_ext hfr _) ht, Metalean.Defeq.map (envS E₀ _) htp⟩
    · obtain ⟨T, hT, hTp⟩ := ih hc
      exact ⟨_, TrM.wkEnv (hP.set_ext hfr _) hT, Metalean.Defeq.map (envS E₀ _) hTp⟩
  | @induct _ _ E₀ _ ι _ _ _ Is Cs Rs _ hP _ hfr _ hext _ _ ih =>
    rw [findDecl_append] at hc
    cases hd : findDecl (IndBlock.decls Is Cs Rs) c with
    | some ci =>
      rw [hd] at hc
      cases hc
      obtain ⟨hm, -⟩ := findDecl_eq_some hd
      rcases IndBlock.mem_decls hm with ⟨s, hs⟩ | ⟨s, k, hs⟩ | ⟨s, hs⟩ <;> cases hs
    | none =>
      rw [hd] at hc
      simp only [Option.none_or] at hc
      obtain ⟨T, hT, hTp⟩ := ih hc
      exact ⟨_, TrM.wkEnv (hP.ext_ext hfr hext) hT,
        Metalean.Defeq.map (envS E₀ _) hTp⟩
  | @quot _ _ E₀ _ _ qs _ hP _ _ hfr _ hext _ ih =>
    rw [findDecl_append] at hc
    cases hd : findDecl (qs.reverse.map ConstantInfo.quotInfo) c with
    | some ci =>
      obtain ⟨hm, -⟩ := findDecl_eq_some hd
      rw [hd] at hc
      cases hc
      simp at hm
    | none =>
      rw [hd] at hc
      simp only [Option.none_or] at hc
      obtain ⟨T, hT, hTp⟩ := ih hc
      exact ⟨_, TrM.wkEnv (hP.ext_ext (decls := qs.map .quotInfo)
        (fun ci hci => by obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hci; exact hfr q hq)
        (by rw [List.map_map]; exact hext)) hT, Metalean.Defeq.map (envS E₀ _) hTp⟩

end

/-! ## Evident propositions -/

section
variable {B : Binds ζ} {P : List ConstantInfo} {σ : EvalEnv}

/-- The translation of an evident proposition, typed by a sort in a well-formed context, is a
proposition: under its Π-binders, a `DeltaFree` head applied to exactly the binders of its
declared arity, at an evidently zero sort. Reference: `isPropositional`
(`MR P/PCUICFirstorder.v:109`); `Defeq.forallEDF` (`ML Typing/Defs.lean`) with `imax l 0 = 0`. -/
theorem evidentProp_prop (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P)
    {lps' : List Name} (ty : Expr) (hev : EvidentProp σ.decls ty = true) :
    ∀ {n : Nat} {Γ : Metalean.Ctx ζ lps'.length 0 n} {Δ : MLCtx ζ lps'.length n}
      {Y : Metalean.Expr ζ lps'.length n} {l : Metalean.Level lps'.length},
      TrM E B lps' Γ Δ ty Y → E[Γ] ⊢ ok → E[Γ] ⊢ Y : .sort l → E[Γ] ⊢ Y : .prop := by
  fun_induction EvidentProp σ.decls ty with
  | case1 x A b bi ih =>
    intro n Γ Δ Y l htr hΓ hY
    obtain ⟨A', b', rfl, -, hb⟩ := SrcDefeq.trM_forallE_inv htr
    obtain ⟨l₁, l₂, hA', hb', -⟩ := hY.forallE_ty_inv
    have hbP := ih hev hb (.snoc hΓ ⟨l₁, hA'⟩) hb'
    have := Defeq.forallEDF hA' hbP hbP
    rwa [Metalean.Level.imax_zero] at this
  | case2 d e ih =>
    intro n Γ Δ Y l htr hΓ hY
    generalize hx : Expr.mdata d e = x at htr
    cases htr with
    | mdata h => cases hx; exact ih hev h hΓ hY
    | special => exact absurd hx (CasesWhred.ne_mkAppN_const fun _ _ h => by cases h)
    | _ => cases hx
  | case3 e _ _ h vs hfn ci hci =>
    intro n Γ Δ Y l htr hΓ hY
    obtain ⟨args, rfl⟩ := eq_mkAppN_of_getAppFn hfn
    rw [SrcDefeq.getAppNumArgs_mkAppN_const] at hev
    simp only [Bool.and_eq_true] at hev
    obtain ⟨hdf, hev⟩ := hev
    obtain ⟨k, u, har, hk, hz⟩ : ∃ k u, Erasure.arityShape ci.type = some (k, u) ∧
        k = args.length ∧ EvidentZero (Erasure.Pure.instLevel ci.levelParams vs u) = true := by
      split at hev
      · rename_i k u har
        simp only [Bool.and_eq_true, beq_iff_eq] at hev
        exact ⟨k, u, har, hev.1, hev.2⟩
      · cases hev
    have hcP := SrcDefeq.findDecl_sub hsub hci
    have hname : ci.name = h := (findDecl_eq_some hcP).2
    have hnd := henv.levelParams_nodup (findDecl_eq_some hcP).1
    obtain ⟨b, hb, Th, th, hTh, hth, hthT⟩ := henv.lookup hE hcP
    by_cases hs : b.isSpecial
    · obtain ⟨iv, rfl⟩ : ∃ iv, ci = .inductInfo iv := by
        rcases SrcDefeq.special_kind henv hb hs hcP with h' | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
        · exact h'
        all_goals simp [DeltaFree] at hdf
      have hname' : iv.name = h := hname
      have hcP' : findDecl P iv.name = some (.inductInfo iv) := by rw [hname']; exact hcP
      obtain ⟨ι, η, s, hB, -⟩ := ProgEnv.lookup_ind henv hcP'
      obtain ⟨a, hkl, ha, hdepth, hlev⟩ := SrcProof.ind_level henv hE hcP' hB har
      rw [hname'] at hB
      obtain ⟨as', hlen, -, hsat⟩ := TrM.special_inv hB rfl htr
      cases hsat with
      | @indSat _ _ _ _ ls ps is rest hls =>
        have hr : rest = [] := List.eq_nil_of_length_eq_zero (by simp at hlen; omega)
        subst hr
        obtain ⟨-, -, -, -, hT⟩ := hY.ind_inv
        obtain ⟨ls', hus, hls'⟩ := SrcDefeq.trLevels_cast hls hkl
        have h0 := SrcProof.evidentZero_tr hz (TrLevel_instLevel hus ha)
        rw [hlev] at hT
        have hfun : (fun i : Fin iv.levelParams.length => ls (i.cast hkl.symm)) = ls' :=
          funext fun i => (hls' i).symm
        rw [hfun, h0] at hT
        exact hT.conv hY
      | indEta _ hlt => omega
    · have hns : ¬ SpecialHead B (.const h vs) := by
        rintro ⟨c', us', b', hfn', hb', hs'⟩
        cases hfn'
        rw [hb] at hb'
        cases hb'; exact hs hs'
      obtain ⟨h', as', hh, has, rfl⟩ := CasesWhred.trM_spine_inv hns args htr
      cases b with
      | const η =>
        rw [hname] at hth
        obtain ⟨ls, rfl, hls⟩ := SrcDefeq.trM_const_inv' hb hh
        obtain ⟨ls₀, rfl, hls₀⟩ := SrcDefeq.trM_const_inv' hb hth
        obtain ⟨hk', hls₀'⟩ := SrcDefeq.trLevels_params_nodup hnd hls₀
        obtain ⟨ls', hus, hls'⟩ := SrcDefeq.trLevels_cast hls hk'
        have hlseq : ls₀{ls'} = ls := by
          funext i
          show (ls₀ i){ls'} = ls i
          rw [hls₀' i]
          show ls' (Fin.cast hk' i) = ls i
          rw [hls']
          rfl
        have hc₀ : E[.nil] ⊢ Metalean.Expr.const η ls : Th{ls'} := by
          rw [← hlseq]; exact Metalean.Defeq.instLevel ls' hthT
        have hc : E[Γ] ⊢ Metalean.Expr.const η ls : Th{ls'}.wkClosed := by
          simpa using Metalean.Defeq.wkClosed (Γ := Γ) hc₀
        obtain ⟨a, ha, hPa⟩ := SrcProof.trM_arity har hTh
        have hP : SrcProof.PiSort (Th{ls'}.wkClosed (n := n)) as'.length a{ls'} := by
          rw [← has.length_eq, ← hk]
          exact PiSort.wkClosed (PiSort.instL hPa ls')
        obtain ⟨_, hreg⟩ := hc.regular
        have hT := piSort_appList hE hΓ as' hc (Metalean.IsType.typeEq ⟨_, hreg⟩) hP hY
        rw [SrcProof.evidentZero_tr hz (TrLevel_instLevel hus ha)] at hT
        exact hT.conv hY
      | _ => exact absurd rfl hs
  | case4 => intros; simp_all
  | case5 => intros; simp_all

end

end ErasableAtom

open ErasableAtom

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P : List ConstantInfo}
  {σ : EvalEnv} {lps : List Name}

/-- Atom spines are erasable: the typed translation of a spine whose head is an atom (an inductive
type former, an arity-typed constant, a proof of an evident proposition or a theorem) is a type
former or a proof. Reference: `Is_type_app` (`MR E/EArities.v:480`) on `tInd`-headed spines;
DV-11, DV-24. -/
theorem ErasableS.atom {e : Expr} (henv : ProgEnv P ζ E B) (hE : EnvWF E)
    (hsub : SubEnv σ.decls P) {t T : Metalean.Expr ζ lps.length 0} (hsp : AtomSpine σ e)
    (he : TrM E B lps .nil [] e t) (ht : E[.nil] ⊢ t : T) : ErasableS E B lps .nil [] e := by
  refine ⟨t, he, ?_⟩
  have hok := SrcDefeq.nil_ok (E := E) (lps := lps)
  obtain ⟨c, us, args, rfl, hat⟩ := SrcProof.atomSpine_spine hsp
  obtain ⟨ci, hci⟩ : ∃ ci, findDecl σ.decls c = some ci := by
    unfold EvalEnv.isAtom at hat
    split at hat
    · exact ⟨_, ‹_›⟩
    · cases hat
  simp only [EvalEnv.isAtom, hci, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hat
  obtain ⟨⟨-, hown⟩, hkind⟩ := hat
  have hcP := SrcDefeq.findDecl_sub hsub hci
  have hnd := henv.levelParams_nodup (findDecl_eq_some hcP).1
  have hname : ci.name = c := (findDecl_eq_some hcP).2
  obtain ⟨b, hb, Tc, tc, hTc, htc, htcT⟩ := henv.lookup hE hcP
  rw [hname] at htc
  by_cases hs : b.isSpecial
  · obtain ⟨v, rfl⟩ : ∃ v, ci = .inductInfo v := by
      rcases SrcDefeq.special_kind henv hb hs hcP with h | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact h
      all_goals simp [OwnRules] at hown
    have hname' : v.name = c := hname
    obtain ⟨ι, η, s, hB, -⟩ := ProgEnv.lookup_ind (c := v.name) (iv := v) henv
      (by rw [hname']; exact hcP)
    rw [hname'] at hB
    obtain ⟨as', -, -, hsat⟩ := TrM.special_inv hB rfl he
    cases hsat with
    | indSat ps is rest hls =>
      obtain ⟨⟨F, hF⟩, -⟩ := InstPre.appList_inv ht
      obtain ⟨-, -, -, -, hFs⟩ := hF.ind_inv
      exact IsErasable.appList hE hok rest ⟨F, hF, .inl (OracleArity.Shape.isArity .sort hFs)⟩ ht
    | @indEta _ _ _ _ _ lsm hls hlt =>
      obtain ⟨⟨F, hF⟩, -⟩ := InstPre.appList_inv ht
      have hF' : E[.nil] ⊢ ((E.get η).block.argTele s){lsm}.lam
          (.ind η s lsm (fun p => .var ⟨p.val, by omega⟩)
            fun i => .var ⟨ι.nparams + i.val, by omega⟩) : F := hF
      obtain ⟨U, hok', hbody, hFU⟩ := SrcProof.lam_tele_inv hok _ hF'
      obtain ⟨-, -, -, -, hU⟩ := hbody.ind_inv
      have hp := SrcProof.PiSort.pi (((E.get η).block.argTele s){lsm})
        (SrcProof.PiSort.sort (n := ι.nparams + ι.nindices s) (u := (E.get η).block.level{lsm}))
      exact IsErasable.appList hE hok _ ⟨F, hF, .inl (OracleArity.Shape.isArity (PiSort.shape hp)
        (hFU.trans (SrcProof.pi_congr _ hok' hU)))⟩ ht
  · have hns : ¬ SpecialHead B (.const c us) := by
      rintro ⟨c', us', b', hfn', hb', hs'⟩
      cases hfn'
      rw [hb] at hb'
      cases hb'; exact hs hs'
    obtain ⟨h', as', hh, -, rfl⟩ := CasesWhred.trM_spine_inv hns args he
    cases b with
    | const η =>
      obtain ⟨ls, rfl, hls⟩ := SrcDefeq.trM_const_inv' hb hh
      obtain ⟨ls₀, rfl, hls₀⟩ := SrcDefeq.trM_const_inv' hb htc
      obtain ⟨hk, hls₀'⟩ := SrcDefeq.trLevels_params_nodup hnd hls₀
      obtain ⟨ls', -, hls'⟩ := SrcDefeq.trLevels_cast hls hk
      have hlseq : ls₀{ls'} = ls := by
        funext i
        show (ls₀ i){ls'} = ls i
        rw [hls₀' i]
        show ls' (Fin.cast hk i) = ls i
        rw [hls']
        rfl
      obtain ⟨_, hreg⟩ := htcT.regular
      have hEc : IsErasable E .nil (Metalean.Expr.const η ls₀) := by
        refine ⟨Tc, htcT, ?_⟩
        rcases hkind with (har | hev) | hthm
        · obtain ⟨⟨k, u⟩, har⟩ := Option.isSome_iff_exists.mp har
          obtain ⟨a, -, hPa⟩ := SrcProof.trM_arity har hTc
          exact .inl (OracleArity.Shape.isArity (PiSort.shape hPa) (Metalean.IsType.typeEq ⟨_, hreg⟩))
        · exact .inr (evidentProp_prop henv hE hsub ci.type hev hTc SrcDefeq.nil_ok hreg)
        · obtain ⟨v, rfl⟩ : ∃ v, ci = .thmInfo v := by
            cases ci <;> simp [IsThm] at hthm
            exact ⟨_, rfl⟩
          obtain ⟨T₀, hT₀, hT₀p⟩ := lookup_thm henv hcP
          have hd := DCong.defeq₂ hE (hT₀.dcong hTc (LocCong.refl [])) SrcDefeq.nil_ok
            SrcDefeq.nil_ok (DCong.CtxConv.refl SrcDefeq.nil_ok) ⟨_, hreg⟩ hT₀p
          exact .inr hd.right
      have hEi := IsErasable.instL (ls := ls') hE hEc
      rw [show (Metalean.Expr.const η ls₀){ls'} = Metalean.Expr.const η ls from by
        rw [← hlseq]; rfl] at hEi
      exact IsErasable.appList hE hok as' hEi ht
    | _ => exact absurd rfl hs

end

end EraseProof
