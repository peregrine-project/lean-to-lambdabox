import EraseProof.Oracle.Infer

/-!
# The oracle's type of a structure projection

`OracleInfer.infer_projStruct`: the projection case of `Pure.inferType_sound` for a structure.
The oracle types `proj S i s` as Lean's `inferProjType` does: it instantiates the leading `Π`s of
the constructor's type with the parameters of the major's type (`Pure.instForalls`) and with the
projections `proj S j s` of the earlier fields (`Pure.instProjs`), and returns the domain of the
next `Π`. Each step is the oracle's `app` step on a virtual spine: the constructor applied to the
parameters' images and to the images of the earlier projections. The translator's η-term of the
constructor applied to the parameters and to all projections of the major is definitionally equal
to the constructor node rebuilt from the projections (`SatTyped.ctorEta_defeq`, the structure's
η-rule premise of `IsStructure.rebuildTerm_hasType`), so every prefix of that spine is typed and the
`Π`-instantiation steps go through `OracleInfer.app_step`; the last step types the projection at
the translated domain (`arg_step`).
-/

open Lean Erasure
open Metalean (Defeq TypeEq EnvWF WHRed WHRedS)

namespace EraseProof

/-- The inductive type that lists a constructor is the constructor's inductive type: both are bound
to the same Metalean sort. Reference: `declared_constructor` (MC §3.6). -/
theorem ProgEnv.lookup_ind_ctor {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ}
    {P : List ConstantInfo} {S c : Name} {iv : InductiveVal} (h : ProgEnv P ζ E B)
    (hS : findDecl P S = some (.inductInfo iv)) (hc : c ∈ iv.ctors) :
    ∃ (ι : Metalean.IndSig) (η : Metalean.Head ζ (.inductive ι)) (s : Fin ι.nsorts)
      (k : Fin (ι.nctors s)) (order : List Nat),
      B S = some (.ind η s) ∧ B c = some (.ctor η s k order) := by
  induction h with
  | nil => simp [findDecl] at hS
  | @«axiom» _ _ _ _ v _ hP hfr _ _ _ ih | @defn _ _ _ _ v _ _ hP hfr _ _ _ _ _ ih
  | @thm _ _ _ _ v _ hP hfr _ _ _ _ _ ih | @«opaque» _ _ _ _ v _ hP hfr _ _ _ _ _ ih =>
    rw [findDecl_cons] at hS
    split at hS
    · cases hS
    · obtain ⟨ι, η, s, k, o, hBS, hBc⟩ := ih hS
      have hne : c ≠ v.name := fun he =>
        not_mem_of_findDecl_none hfr (he ▸ hP.bound (by simp [hBc]))
      exact ⟨ι, η.there, s, k, o, by rw [set_wk_ne (Ne.symm ‹_›), hBS]; rfl,
        by rw [set_wk_ne hne, hBc]; rfl⟩
  | @induct _ _ _ _ ι _ _ _ Is Cs Rs _ hP _ hfr _ hext hblk _ ih =>
    rw [findDecl_append] at hS
    cases hd : findDecl (IndBlock.decls Is Cs Rs) S with
    | some ci =>
      rw [hd] at hS
      cases hS
      obtain ⟨hm, hn⟩ := findDecl_eq_some hd
      rcases IndBlock.mem_decls hm with ⟨s, hs⟩ | ⟨s, k, hs⟩ | ⟨s, hs⟩ <;> cases hs
      obtain ⟨hB, -, -, -, -, hcs, -⟩ := hblk.ind s
      rw [hcs, List.mem_ofFn] at hc
      obtain ⟨k, rfl⟩ := hc
      exact ⟨ι, .here, s, k, _, hn ▸ hB, (hblk.ctor s k).1⟩
    | none =>
      rw [hd] at hS
      simp only [Option.none_or] at hS
      obtain ⟨ι', η, s, k, o, hBS, hBc⟩ := ih hS
      have hnot : S ∉ (IndBlock.decls Is Cs Rs).map (·.name) := not_mem_of_findDecl_none hd
      have hnotc : c ∉ (IndBlock.decls Is Cs Rs).map (·.name) := fun hm => by
        obtain ⟨ci, hci, hn⟩ := List.mem_map.mp hm
        exact not_mem_of_findDecl_none (hfr ci hci) (hn ▸ hP.bound (by simp [hBc]))
      exact ⟨ι', η.there, s, k, o, by rw [hext S hnot, Binds.wk, hBS]; rfl,
        by rw [hext c hnotc, Binds.wk, hBc]; rfl⟩
  | @quot _ _ _ _ _ qs _ hP _ _ hfr _ hext _ ih =>
    rw [findDecl_append] at hS
    cases hd : findDecl (qs.reverse.map ConstantInfo.quotInfo) S with
    | some ci =>
      obtain ⟨hm, -⟩ := findDecl_eq_some hd
      rw [hd] at hS
      cases hS
      simp at hm
    | none =>
      rw [hd] at hS
      simp only [Option.none_or] at hS
      obtain ⟨ι', η, s, k, o, hBS, hBc⟩ := ih hS
      have hnot := not_mem_of_findDecl_none hd
      rw [quot_names_reverse, List.mem_reverse] at hnot
      have hnotc : c ∉ qs.map (·.name) := fun hm => by
        obtain ⟨q, hq, hn⟩ := List.mem_map.mp hm
        exact not_mem_of_findDecl_none (hfr q hq) (hn ▸ hP.bound (by simp [hBc]))
      exact ⟨ι', η.there, s, k, o, by rw [hext S hnot, Binds.wk, hBS]; rfl,
        by rw [hext c hnotc, Binds.wk, hBc]; rfl⟩

namespace OracleInfer

/-- `Pure.instProjs` is `Pure.instForalls` on the projections of the earlier fields. Reference: the
loop over the fields in `inferProjType` (`Lean/Meta/InferType.lean`). -/
theorem instProjs_eq (cx : Pure.Ctx) (f : Nat) (ls : List Local) (S : Name) (s : Expr) :
    ∀ (k j : Nat) (r : Expr), Pure.instProjs cx f ls S s k j r =
      Pure.instForalls cx f ls r ((List.range' j k).map fun x => .proj S x s)
  | 0, _, _ => rfl
  | k + 1, j, r => by
    simp only [Pure.instProjs, Pure.instForalls, List.range'_succ, List.map_cons]
    congr 1
    funext w
    split <;> simp [instProjs_eq cx f ls S s k (j + 1)]

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {lps : List Name}
  {P : List ConstantInfo} {cx : Pure.Ctx} {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
  {Δ : MLCtx ζ lps.length n} {ls : List Local}

/-- The last step of the oracle's projection rule: when the type of `tg` reduces to a `Π` and
`tg a'` is typed, `a'` is typed at the image of the `Π`'s domain. Reference: the inversion of
`type_App` (`MR pcuic/theories/PCUICTyping.v:224`). -/
theorem arg_step (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv cx.decls P)
    (hΓ : E[Γ] ⊢ ok) (hloc : LocalsOK E B lps Γ Δ ls) {f : Nat} {Tg Ad Bc : Expr} {x : Name}
    {bi : BinderInfo} {tg a' Tg' U : Metalean.Expr ζ lps.length n}
    (htg : E[Γ] ⊢ tg : Tg') (hTg : TrM E B lps Γ Δ Tg Tg')
    (hw : Pure.whnf cx f ls Tg = .ok (.forallE x Ad Bc bi)) (happ : E[Γ] ⊢ .app tg a' : U) :
    ∃ A', TrM E B lps Γ Δ Ad A' ∧ E[Γ] ⊢ a' : A' := by
  obtain ⟨_, hTgs⟩ := htg.regular
  obtain ⟨W', hW', dW⟩ := Pure.whnf_sound henv hE hsub hΓ hloc hTg hTgs hw
  generalize hx : Expr.forallE x Ad Bc bi = X at hW'
  cases hW' with
  | forallE hA hB =>
    cases hx
    have htg' := (TypeEq.ofDefEq dW).conv htg
    obtain ⟨A0, B0, hf0, ha0, -⟩ := happ.app_inv
    have hTy := Defeq.uniqTy hE hΓ hf0 htg'
    exact ⟨_, hA, (TypeEq.forallE_inj hE hΓ hTy).1.conv ha0⟩
  | special => exact absurd hx (ne_mkAppN_const fun _ _ h => by cases h)
  | _ => cases hx

/-- `Pure.instForalls` along a typed spine: instantiating the `Π`s of a type of `X pre` with the
arguments whose images extend the spine gives a type of the extended spine, when that spine is
typed. Reference: `type_App` (`MR pcuic/theories/PCUICTyping.v:224`), as the oracle's `app` step
(`OracleInfer.app_step`). -/
theorem instForalls_sound (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv cx.decls P)
    (hΓ : E[Γ] ⊢ ok) (hloc : LocalsOK E B lps Γ Δ ls) {f : Nat} {X : Metalean.Expr ζ lps.length n} :
    ∀ {as : List Expr} {as' : List (Metalean.Expr ζ lps.length n)},
      List.Forall₂ (TrM E B lps Γ Δ) as as' →
      ∀ {pre : List (Metalean.Expr ζ lps.length n)} {r r' : Expr}
        {R U : Metalean.Expr ζ lps.length n},
      TrM E B lps Γ Δ r R → E[Γ] ⊢ X.appList pre : R → E[Γ] ⊢ X.appList (pre ++ as') : U →
      Pure.instForalls cx f ls r as = .ok r' →
      ∃ R', TrM E B lps Γ Δ r' R' ∧ E[Γ] ⊢ X.appList (pre ++ as') : R' := by
  intro as as' hF
  induction hF with
  | nil =>
    intro pre r r' R U hr hX _ h
    simp only [Pure.instForalls, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨R, hr, by simpa using hX⟩
  | @cons a a' as as' ha _ ih =>
    intro pre r r' R U hr hX hU h
    simp only [Pure.instForalls] at h
    obtain ⟨W, hw, h⟩ := OracleWhnf.ok_of_bind h
    cases W with
    | forallE x Ad Bc bi =>
      have hpre : pre ++ a' :: as' = (pre ++ [a']) ++ as' := by simp
      rw [hpre] at hU ⊢
      obtain ⟨_, happ⟩ := SatTyped.prefix_typed hU
      rw [TrApps.appList_append] at happ
      obtain ⟨A', hA', happ'⟩ := app_step henv hE hsub hΓ hloc hX hr hw ha happ rfl
      exact ih hA' (by rw [TrApps.appList_append]; exact happ') hU h
    | _ => simp [throw, throwThe, MonadExceptOf.throw] at h

/-- Lists related entry by entry. -/
private theorem forall₂_of_getElem? {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, l₁.length = l₂.length →
      (∀ (j : Nat) a b, l₁[j]? = some a → l₂[j]? = some b → R a b) → List.Forall₂ R l₁ l₂
  | [], [], _, _ => .nil
  | a :: l₁, b :: l₂, hl, h =>
    .cons (h 0 a b rfl rfl) (forall₂_of_getElem? (by simpa using hl)
      fun j a b h1 h2 => h (j + 1) a b h1 h2)
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

/-- The empty-context image of a constructor of positive arity is its η-term. -/
private theorem ctorTerm_zero {ι : Metalean.IndSig} {η : Metalean.Head ζ (.inductive ι)}
    {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} {order : List Nat} {us : List Level}
    {lsM : Fin ι.nlevels → Metalean.Level lps.length} {t₀ : Metalean.Expr ζ lps.length 0}
    (hls : TrLevels lps us ι.nlevels = some lsM)
    (hpos : 0 < ι.nparams + ((ι.ctors s c).nfields + (ι.ctors s c).nrecFields))
    (h : SatTr E lps (.ctor η s c order) us [] t₀) :
    Metalean.Frontend.ctorTerm (E.get η).block η s c lsM order = .ok t₀ := by
  generalize hnil : ([] : List (Metalean.Expr ζ lps.length 0)) = args at h
  cases h with
  | ctorSat ps fs rest fds recFds hls' hfs =>
    have := congrArg List.length hnil
    simp only [List.length_append, List.length_ofFn, List.length_nil] at this
    omega
  | ctorEta hls' _ h₀ =>
    subst hnil
    rw [hls] at hls'; cases hls'
    exact h₀

/-- The oracle's type of a structure projection translates to a type of the projection's image
(the `TrM.projStruct` case of `Pure.inferType_sound`). Reference: `infer` on `tProj`
(`MR S/PCUICSafeRetyping.v:350`), `type_Proj` (`MR pcuic/theories/PCUICTyping.v:262`);
`IsStructure.projTerm_hasType` (`ML Typing/Structure.lean:314`). -/
theorem infer_projStruct (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv cx.decls P)
    {f : Nat} (ih : InferOK E B lps cx ls f) {Γo : List Expr} (hΓ : E[Γ] ⊢ ok)
    (hloc : LocalsOK E B lps Γ Δ ls) (hΓo : OracleCtx (E := E) (B := B) Γ Δ Γo) {S : Name}
    {i : Nat} {e A : Expr} {ι : Metalean.IndSig} {η : Metalean.Head ζ (.inductive ι)}
    {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} {lsM : Fin ι.nlevels → Metalean.Level lps.length}
    {ps : Fin ι.nparams → Metalean.Expr ζ lps.length n}
    {is : Fin (ι.nindices s) → Metalean.Expr ζ lps.length n} {e' U : Metalean.Expr ζ lps.length n}
    (hst : (E.get η).block.IsStructure s c) (hi : i < (ι.ctors s c).nfields)
    (hBS : B S = some (.ind η s)) (he : TrM E B lps Γ Δ e e')
    (hty : TypedExt E Γ e' (.ind η s lsM ps is))
    (ht : E[Γ] ⊢ hst.projTerm η lsM ps ⟨i, hi⟩ e' : U)
    (h : Pure.inferType cx (f + 1) ls Γo (.proj S i e) = .ok A) :
    ∃ A', TrM E B lps Γ Δ A A' ∧ E[Γ] ⊢ hst.projTerm η lsM ps ⟨i, hi⟩ e' : A' := by
  have hB := (hE.entryWF η).block
  have ht' := ht
  rw [hst.projTerm_eq_recr] at ht'
  obtain ⟨ps₁, _, _, is₁, _, -, hps, -, -, -, hmaj, -, -⟩ := ht'.recr_inv
  obtain rfl := hst.indices_eq is₁
  have hps₁ : ∀ p, E[Γ] ⊢ ps₁ p : (E.get η).block.paramType lsM ps₁ p := fun p => (hps p).left
  have he₁ : E[Γ] ⊢ e' : .ind η s lsM ps₁ hst.indices := hmaj.right
  simp only [Pure.inferType] at h
  obtain ⟨Ts, h1, h⟩ := OracleWhnf.ok_of_bind h
  obtain ⟨W, h2, h⟩ := OracleWhnf.ok_of_bind h
  obtain ⟨Ts', hTs, he'Ts⟩ := ih hΓ hloc hΓo he he₁ h1
  obtain ⟨_, hTss⟩ := he'Ts.regular
  obtain ⟨W', hW', dW⟩ := Pure.whnf_sound henv hE hsub hΓ hloc hTs hTss h2
  have he'W := (TypeEq.ofDefEq dW).conv he'Ts
  have hsp := CasesShape.spine_mkAppN W
  generalize spine W = p at h hsp
  obtain ⟨hd, args⟩ := p
  cases hd with
  | const S' us =>
    simp only at h hsp
    split at h
    · rename_i I hSS hfS
      split at h
      · rename_i c' hct hlen
        split at h
        · rename_i ci cv hci
          split at h
          swap
          · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
          rename_i hul
          obtain ⟨r, h3, h⟩ := OracleWhnf.ok_of_bind h
          obtain ⟨Xo, h4, h⟩ := OracleWhnf.ok_of_bind h
          obtain ⟨W2, h5, h⟩ := OracleWhnf.ok_of_bind h
          cases W2 with
          | forallE x d bd bi =>
            simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            obtain rfl : S' = S := beq_iff_eq.mp hSS
            simp only [beq_iff_eq] at hlen hul
            -- the inductive and its constructor in Metalean
            obtain ⟨ι₂, η₂, s₂, hB₂, hnp, hni, -⟩ :=
              henv.lookup_ind (OracleWhnf.findConst_sub hsub hfS)
            rw [hBS] at hB₂; cases hB₂
            obtain ⟨ι₃, η₃, s₃, k, o, hB₃, hBc⟩ := henv.lookup_ind_ctor
              (OracleWhnf.findConst_sub hsub hfS) (by rw [hct]; exact List.mem_singleton_self _)
            rw [hBS] at hB₃; cases hB₃
            obtain ⟨ι₄, η₄, s₄, k₄, o₄, hB₄, -, -, -, hmo, -⟩ :=
              henv.lookup_ctor (OracleWhnf.findConst_sub hsub hci)
            rw [hBc] at hB₄; cases hB₄
            obtain rfl := hst.ctor_unique k
            have hnr : (ι.ctors s k).nrecFields = 0 :=
              Nat.eq_zero_of_not_pos fun h => hst.no_recursive.false ⟨0, h⟩
            -- the major's type
            rw [← hsp] at hW'
            obtain ⟨bs', hbl, hargs, hsat⟩ := TrM.special_inv hBS rfl hW'
            obtain ⟨L, hL⟩ := mapM_of_satTr hsat
            cases hsat with
            | indEta _ hlt => omega
            | indSat ps' is' rest hls =>
              have hrest : rest = [] := by
                apply List.eq_nil_of_length_eq_zero
                have := hbl
                simp only [List.length_append, List.length_ofFn] at this
                omega
              subst hrest
              obtain ⟨rfl, hpsd⟩ := DCong.ind_type_inj hE hΓ he₁ he'W
              have hpsd' : ∀ p, E[Γ] ⊢ ps₁ p ≡ ps' p : (E.get η).block.paramType lsM ps₁ p :=
                fun p => by obtain ⟨_, hd⟩ := hpsd p; exact Defeq.retype hE hΓ hd (hps₁ p)
              -- the constructor's η-term
              obtain ⟨t₀, T₀, hS₀, ht₀⟩ := eta_typed henv hE hsub hBc rfl hci hul hL
              have hpos : 0 < ι.nparams + ((ι.ctors s k).nfields + (ι.ctors s k).nrecFields) := by
                omega
              have h₀ := ctorTerm_zero hls hpos hS₀
              -- the constructor node rebuilt from the projections of the major
              let fs : Fin (ι.ctors s k).nfields → Metalean.Expr ζ lps.length n :=
                fun j => hst.projTerm η lsM ps j e'
              have hN := (DCong.ctor_defeq hE (ps₁ := ps₁) (ps₂ := ps')
                (fds₁ := fun j => hst.projTerm η lsM ps₁ j e') (fds₂ := fs)
                (rf₁ := hst.recursive) (rf₂ := hst.recursive) hpsd' (fun j => by
                  have hf := hst.projTerm_congr hB j hps he₁
                  rw [Metalean.Inductive.IsStructure.projType_eq_projTypeWith] at hf
                  exact hf) (fun j => hst.no_recursive.elim j)).right
              have hrel : ∀ (o' j : Fin ((ι.ctors s k).nfields + (ι.ctors s k).nrecFields)),
                  o[o'.val]? = some j.val →
                    Fin.append fs hst.recursive j = Fin.append fs hst.recursive o' := by
                intro o' j hj
                obtain ⟨ords, recs, rfl, -, hrl, hords, -, hp⟩ := hmo
                have hrecs : recs = [] := List.eq_nil_of_length_eq_zero (hrl.trans hnr)
                subst hrecs
                simp only [List.append_nil] at hp hj
                have hord := hp.eq_of_pairwise
                  (fun a b _ _ h1 h2 => absurd (h1.trans h2) (Nat.lt_irrefl a)) hords
                  List.pairwise_lt_range
                rw [hord, List.getElem?_range o'.isLt] at hj
                obtain rfl : j = o' := Fin.ext (Option.some.inj hj).symm
                rfl
              have hd := SatTyped.ctorEta_defeq hE h₀ ht₀ hN _ hrel
              have hlist : List.ofFn (Fin.append ps' (Fin.append fs hst.recursive)) ++ [] =
                  List.ofFn ps' ++ List.ofFn fs := by
                have hr0 : List.ofFn (hst.recursive : Fin (ι.ctors s k).nrecFields →
                    Metalean.Expr ζ lps.length n) = [] :=
                  List.eq_nil_of_length_eq_zero (by simp [hnr])
                rw [List.append_nil, List.ofFn_fin_append, List.ofFn_fin_append, hr0,
                  List.append_nil]
              have hpre : ∀ as₁ as₂ : List (Metalean.Expr ζ lps.length n),
                  as₁ ++ as₂ = List.ofFn ps' ++ List.ofFn fs →
                    ∃ T₁, E[Γ] ⊢ t₀.wkClosed.appList as₁ : T₁ := fun as₁ as₂ hs =>
                SatTyped.eta_prefix (rest := []) hE hΓ hd hN (hs.trans hlist.symm)
              -- the oracle's type of the constructor
              have hc0 : TrM E B lps Γ Δ (.const c' us) (t₀.wkClosed.appList []) :=
                .special (as := []) hBc rfl rfl (fun _ _ _ h => by simp at h)
                  (.ctorEta hls (by simp only [List.length_nil]; omega) h₀)
              obtain ⟨_, ht0⟩ := hpre [] (List.ofFn ps' ++ List.ofFn fs) rfl
              obtain ⟨R₀, hR₀, htR₀⟩ := const_type henv hE hsub hΓ hci hul hc0 ht0
              -- the parameters
              have hF1 : List.Forall₂ (TrM E B lps Γ Δ) (args.take I.numParams) (List.ofFn ps') :=
                forall₂_of_getElem? (by simp; omega) fun j a a' h1 h2 => by
                  rw [List.getElem?_take] at h1
                  split at h1
                  · exact hargs j a a' h1 (by
                      rw [List.append_nil,
                        List.getElem?_append_left (List.getElem?_eq_some_iff.mp h2).1]
                      exact h2)
                  · cases h1
              obtain ⟨_, hU1⟩ := hpre (List.ofFn ps') (List.ofFn fs) rfl
              obtain ⟨R₁, hR₁, htR₁⟩ := instForalls_sound henv hE hsub hΓ hloc hF1 (pre := [])
                hR₀ htR₀ (by simpa using hU1) h3
              -- the projections of the earlier fields
              rw [instProjs_eq] at h4
              have hF2 : List.Forall₂ (TrM E B lps Γ Δ)
                  ((List.range' 0 i).map fun x => .proj S' x e) ((List.ofFn fs).take i) :=
                forall₂_of_getElem? (by simp; omega) fun j a a' h1 h2 => by
                  rw [List.getElem?_take] at h2
                  split at h2
                  · rename_i hj
                    rw [List.getElem?_map, List.getElem?_range' (by simpa using hj)] at h1
                    have hjn : j < (ι.ctors s k).nfields := by omega
                    rw [List.getElem?_ofFn] at h2
                    simp only [hjn, ↓reduceDIte, Option.map_some, Option.some.injEq, Nat.zero_add,
                      Nat.one_mul] at h1 h2
                    subst h1 h2
                    exact .projStruct hst _ hBS he hty
                  · cases h2
              obtain ⟨_, hU2⟩ := hpre (List.ofFn ps' ++ (List.ofFn fs).take i)
                ((List.ofFn fs).drop i) (by rw [List.append_assoc, List.take_append_drop])
              obtain ⟨R₂, hR₂, htR₂⟩ := instForalls_sound henv hE hsub hΓ hloc hF2
                (pre := [] ++ List.ofFn ps') hR₁ htR₁ (by simpa using hU2) h4
              -- the projected field
              have hfi : (List.ofFn fs)[i]'(by simpa using hi) = fs ⟨i, hi⟩ := List.getElem_ofFn ..
              obtain ⟨_, happ⟩ := hpre (List.ofFn ps' ++ (List.ofFn fs).take i ++ [fs ⟨i, hi⟩])
                ((List.ofFn fs).drop (i + 1)) (by
                  rw [List.append_assoc, List.append_assoc, List.singleton_append, ← hfi,
                    ← List.drop_eq_getElem_cons, List.take_append_drop])
              rw [TrApps.appList_append] at happ
              obtain ⟨D, hD, htD⟩ := arg_step henv hE hsub hΓ hloc htR₂ hR₂ h5
                (by simpa using happ)
              exact ⟨D, hD, htD⟩
          | _ => simp [throw, throwThe, MonadExceptOf.throw] at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
  | _ => simp [throw, throwThe, MonadExceptOf.throw] at h

end

end OracleInfer

end EraseProof
