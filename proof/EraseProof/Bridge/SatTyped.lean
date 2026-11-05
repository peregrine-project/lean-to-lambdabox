import EraseProof.Bridge.Inst

/-!
# Typed prefixes of saturating spines

`SatTr.typed`: when the image of a saturating spine is typed, so is the image of every prefix of
the spine. A prefix that reaches the arity is a prefix of the node's application; a shorter one is
the translator's η-term (`indTerm`, `ctorTerm`, `quotTerm`, `ML Frontend/Translate.lean:103-224`)
applied to the prefix's arguments, which the inversion of the node types at the η-term's binder
types (subject expansion of β). For a recursor the expansion from a partial prefix to a saturated
spine is not covered: a minor premise that `wrapCase` wraps is typed only under the case telescope.
The oracle's type of an exactly saturated recursor spine is obtained without typing the prefix
(`Pure.inferType_recr`).
-/

open Lean Erasure
open Metalean (Defeq TypeEq EnvWF WHRed WHRedS)

namespace EraseProof

namespace SatTyped

section
open Metalean
variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat}

/-- A closed λ-telescope, weakened into a context and applied to arguments that are
definitionally equal to a well-typed substitution for its binders, is definitionally equal to
its body under the substitution. -/
theorem closed_lam_apps {n : Nat} {R : Ctx ζ ℓ 0 n} :
    ∀ {k : Nat} (Θ : Ctx ζ ℓ 0 k) {body T : Expr ζ ℓ k} {xs₁ xs₂ : Fin k → Expr ζ ℓ n},
      E[Θ] ⊢ ok → E[Θ] ⊢ body : T → E[R] ⊢ xs₁ ≡ xs₂ ⊣ Θ →
      E[R] ⊢ (Θ.lam body).wkClosed.apps xs₂ ≡ body.subst xs₁ : T.subst xs₁
  | 0, .nil, body, T, xs₁, xs₂, _, hb, _ => by
    simp only [Expr.apps_zero, Expr.subst_closed]
    exact hb.wkClosed
  | k + 1, .snoc Θ A, body, T, xs₁, xs₂, hΘ, hb, hxs => by
    have hΘ' : E[Θ] ⊢ ok := Tele.Forall.init hΘ
    obtain ⟨u, hA⟩ := Tele.Forall.last hΘ
    have ⟨_, hT⟩ := hb.regular
    have hlam : E[Θ] ⊢ .lam A body : .forallE A T := .lamDF hA hT hT hb hb
    have hsx : ∀ xs : Fin (k + 1) → Expr ζ ℓ n,
        Subst.extend (fun i : Fin k => xs i.castSucc) (xs (Fin.last k)) = xs :=
      fun xs => Fin.snoc_init_self xs
    have hinit : E[R] ⊢ (fun i : Fin k => xs₁ i.castSucc) ≡ (fun i : Fin k => xs₂ i.castSucc) ⊣ Θ :=
      fun v => by
        have h := hxs v.castSucc
        rw [Ctx.get_castSucc, ← hsx xs₁, Expr.wk_subst_extend] at h
        simpa using h
    have ih := closed_lam_apps Θ hΘ' hlam hinit
    have hx : E[R] ⊢ xs₂ (Fin.last k) ≡ xs₁ (Fin.last k) :
        A.subst fun i : Fin k => xs₁ i.castSucc := by
      have h := hxs (Fin.last k)
      rw [Ctx.get_last, ← hsx xs₁, Expr.wk_subst_extend] at h
      simpa using h.symm
    have hinitL : E[R] ⊢ (fun i : Fin k => xs₁ i.castSucc) ⊣ Θ := SubstEq.left hinit
    have hAσ := hA.substitution hinitL
    have hlift := SubstWF.lift ⟨u, hA⟩ hinitL
    have hTσ := hT.substitution hlift
    have hbσ := hb.substitution hlift
    have happ := Defeq.appDF hAσ hTσ ih hx (hTσ.inst_congr hx)
    have hbeta := Defeq.beta hAσ hTσ hbσ hx.right (hTσ.inst_congr hx.right)
      (hbσ.inst_congr hx.right)
    have hty := hTσ.inst_congr hx
    rw [Expr.inst_subst_lift, Expr.inst_subst_lift, hsx] at hbeta
    rw [Expr.inst_subst_lift, Expr.inst_subst_lift, hsx] at hty
    rw [Expr.inst_subst_lift] at happ
    rw [Expr.apps_last]
    exact (TypeEq.ofDefEq hty).conv happ |>.trans hbeta

/-- A term definitionally equal to the head of a typed application spine heads a typed spine with
the same arguments. -/
theorem appList_defeq (hE : EnvWF E) {n : Nat} {R : Ctx ζ ℓ 0 n} (hR : E[R] ⊢ ok) :
    ∀ {X Y U T : Expr ζ ℓ n} (rest : List (Expr ζ ℓ n)),
      E[R] ⊢ X ≡ Y : U → E[R] ⊢ Y.appList rest : T → ∃ T', E[R] ⊢ X.appList rest : T'
  | _, _, U, _, [], h, _ => ⟨U, h.left⟩
  | X, Y, _, _, r :: rest, h, hY => by
    rw [Expr.appList_cons] at hY ⊢
    obtain ⟨⟨_, hYr⟩, -⟩ := InstPre.appList_inv hY
    obtain ⟨A, B, hYf, hr, -⟩ := hYr.app_inv
    have h' := (Defeq.uniqTy hE hR h.right hYf).conv h
    obtain ⟨⟨_, hA⟩, ⟨_, hB⟩⟩ := hYf.regular.choose_spec.forallE_inv
    exact appList_defeq hE hR rest (Defeq.appDF hA hB h' hr (hB.inst_congr hr)) hY

/-- Substitution by the identity leaves a telescope unchanged. -/
theorem substN_id {m k : Nat} (Δ : Ctx ζ ℓ m (m + k)) : Δ.substN Subst.id k = Δ := by
  induction Δ using Tele.addInduction with
  | nil => rfl
  | snoc k Δ t ih => simp only [Ctx.substN, Subst.liftN_id, Expr.subst_id, ih]

/-- The telescope of `indTerm`: the parameters, then the indices over the parameters' variables. -/
theorem argTele_eq {ι : IndSig} (I : Inductive ζ ι) (s : Fin ι.nsorts)
    (ls : Fin ι.nlevels → Level ℓ) :
    (I.argTele s){ls} = I.params{ls} ++ I.indexTele ls s Subst.id := by
  rw [Inductive.argTele, Ctx.instL_append, Inductive.indexTele, substN_id]

/-- `indTerm` applied to the arguments of a typed inductive-type node is definitionally equal to
the node. -/
theorem indEta_defeq (hE : EnvWF E) {n : Nat} {R : Ctx ζ ℓ 0 n} {ι : IndSig}
    {η : Head ζ (.inductive ι)} {s : Fin ι.nsorts} {ls : Fin ι.nlevels → Level ℓ}
    {ps : Fin ι.nparams → Expr ζ ℓ n} {is : Fin (ι.nindices s) → Expr ζ ℓ n} {T : Expr ζ ℓ n}
    (ht : E[R] ⊢ .ind η s ls ps is : T) :
    ∃ U, E[R] ⊢ (Frontend.indTerm (E.get η).block η s ls).wkClosed.apps (Fin.append ps is) ≡
      .ind η s ls ps is : U := by
  have hB := (hE.entryWF η).block
  obtain ⟨hps, his⟩ := Defeq.ind_typed hE ht
  have hσ : E[R] ⊢ Fin.append ps is ⊣ ((E.get η).block.argTele s){ls} :=
    (Inductive.indexSubstEq hB hps his).left
  have hP : E[(E.get η).block.params{ls}] ⊢ ok := hB.paramClosedWF ls
  have hvars (p : Fin ι.nparams) : E[(E.get η).block.params{ls}] ⊢ Expr.var p :
      (E.get η).block.paramType ls Expr.var p := by
    simpa using hP.var p
  have hm := hB.motiveTele (s := s) hP hvars
  have hidx : TeleWF E (fun _ => True) _ _ := Tele.Forall.init hm
  obtain ⟨u, _, hbody⟩ := Tele.Forall.last hm
  have hΘ : E[((E.get η).block.argTele s){ls}] ⊢ ok := by
    rw [argTele_eq]; exact hidx.appendCtxWF hP
  rw [argTele_eq] at hσ hΘ
  have hb' : E[(E.get η).block.params{ls} ++ (E.get η).block.indexTele ls s Subst.id] ⊢
      (.ind η s ls (fun p => .var ⟨p.val, by omega⟩)
        fun i => .var ⟨ι.nparams + i.val, by omega⟩ : Expr ζ ℓ (ι.nparams + ι.nindices s)) :
      .sort u := by
    convert hbody using 2
    all_goals first
      | rfl
      | funext p; simp [Expr.wkN_eq_rename]; rfl
  unfold Frontend.indTerm
  simp only [argTele_eq]
  have hc := closed_lam_apps _ hΘ hb' hσ
  have heq : (Expr.ind η s ls (fun p => .var ⟨p.val, by omega⟩)
      (fun i => .var ⟨ι.nparams + i.val, by omega⟩) :
        Expr ζ ℓ (ι.nparams + ι.nindices s)).subst (Fin.append ps is) = .ind η s ls ps is := by
    simp only [Expr.subst]
    congr 1 <;> funext i
    · exact Fin.append_left ps is i
    · exact Fin.append_right ps is i
  rw [heq] at hc
  exact ⟨_, hc⟩

/-- `quotTerm` of `Quot` applied to the arguments of a typed quotient-type node is definitionally
equal to the node. -/
theorem quotTypeEta_defeq {n : Nat} {R : Ctx ζ ℓ 0 n} {η : Head ζ .quot} {u : Level ℓ}
    {α r T : Expr ζ ℓ n} {t₀ : Expr ζ ℓ 0}
    (h₀ : Frontend.quotTerm η (E.get η).eqHead .type [u] = .ok t₀)
    (ht : E[R] ⊢ .quot η u α r : T) :
    ∃ U, E[R] ⊢ t₀.wkClosed.apps ![α, r] ≡ .quot η u α r : U := by
  cases h₀
  obtain ⟨hα, hr⟩ := ht.quot_formation_inv
  have h1 : E[(#t[] : Ctx ζ ℓ 0 0).snoc (.sort u)] ⊢ ok := .snoc .nil ⟨_, .sortDF⟩
  have hv0 : E[(#t[] : Ctx ζ ℓ 0 0).snoc (.sort u)] ⊢ .var 0 : .sort u := by
    simpa [Ctx.get, Expr.wk] using h1.var 0
  have h2 : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩)]] ⊢ ok :=
    .snoc h1 ⟨_, (Quot.relType_congr hv0).left⟩
  have hb : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩)]] ⊢
      (.quot η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩) : Expr ζ ℓ 2) : .sort u := by
    have v0 := h2.var 0
    have v1 := h2.var 1
    simp [Ctx.get, Expr.wk] at v0 v1
    exact .quotDF v0 v1
  have hσ : E[R] ⊢ ![α, r] ⊣ #t[.sort u, Quot.relType (.var ⟨0, by omega⟩)] := by
    intro v
    match v with
    | 0 => simpa [Ctx.get, Expr.wk] using hα
    | 1 => simpa [Ctx.get, Expr.wk, Subst.lift, Quot.relType] using hr
  have hc := closed_lam_apps _ h2 hb hσ
  exact ⟨_, by simpa using hc⟩

/-- Weakening commutes with substitution under one binder. -/
theorem wk_subst_lift {m n : Nat} (σ : Subst ζ ℓ m n) (e : Expr ζ ℓ m) :
    e.wk.subst σ.lift = (e.subst σ).wk := by
  rw [Expr.wk_subst, ← Expr.subst_wk (e.subst σ), Expr.subst_subst]
  congr 1
  funext v
  simp [Expr.subst_wk]

/-- Weakening a variable. -/
theorem var_wk {n : Nat} (v : Var n) : (Expr.var v : Expr ζ ℓ n).wk = .var v.castSucc := by
  simp [Expr.wk]

/-- Substitution commutes with the type of `Quot.lift`'s compatibility premise. -/
theorem compatType_subst {m n : Nat} (σ : Subst ζ ℓ m n) (ηeq : Head ζ (.inductive Eq.sig))
    (l : Level ℓ) (α r β f : Expr ζ ℓ m) :
    (Quot.compatType ηeq l α r β f).subst σ =
      Quot.compatType ηeq l (α.subst σ) (r.subst σ) (β.subst σ) (f.subst σ) := by
  simp only [Quot.compatType, Quot.eqApp, Expr.subst, Expr.subst_appList, List.map_cons,
    List.map_nil, wk_subst_lift, Subst.lift_castSucc, Subst.lift_last, var_wk]
  simp [funext_iff, Fin.forall_fin_two, Expr.subst]

/-- Weakening commutes with the type of `Quot.lift`'s compatibility premise. -/
theorem compatType_wk {n : Nat} (ηeq : Head ζ (.inductive Eq.sig)) (l : Level ℓ)
    (α r β f : Expr ζ ℓ n) :
    (Quot.compatType ηeq l α r β f).wk = Quot.compatType ηeq l α.wk r.wk β.wk f.wk := by
  rw [← Expr.subst_wk, compatType_subst]
  simp only [Expr.subst_wk]

/-- Substitution commutes with the type of `Quot.ind`'s minor premise. -/
theorem minorType_subst {m n : Nat} (σ : Subst ζ ℓ m n) (η : Head ζ .quot) (l : Level ℓ)
    (α r β : Expr ζ ℓ m) :
    (Quot.minorType η l α r β).subst σ =
      Quot.minorType η l (α.subst σ) (r.subst σ) (β.subst σ) := by
  simp only [Quot.minorType, Quot.minorQuotMk, Expr.subst, wk_subst_lift, Subst.lift_last]

/-- Weakening commutes with the type of `Quot.ind`'s minor premise. -/
theorem minorType_wk {n : Nat} (η : Head ζ .quot) (l : Level ℓ) (α r β : Expr ζ ℓ n) :
    (Quot.minorType η l α r β).wk = Quot.minorType η l α.wk r.wk β.wk := by
  rw [← Expr.subst_wk, minorType_subst]
  simp only [Expr.subst_wk]

/-- Two equalities through a common middle term, at the type of the second. -/
theorem trans_at (hE : EnvWF E) {n : Nat} {R : Ctx ζ ℓ 0 n} (hR : E[R] ⊢ ok)
    {X Y Z U V : Expr ζ ℓ n} (h₁ : E[R] ⊢ X ≡ Y : U) (h₂ : E[R] ⊢ Y ≡ Z : V) :
    E[R] ⊢ X ≡ Z : V :=
  ((Defeq.uniqTy hE hR h₁.right h₂.left).conv h₁).trans h₂

/-- `quotTerm` of `Quot.mk` applied to the arguments of a typed node is definitionally equal to
the node. -/
theorem quotMkEta_defeq (hE : EnvWF E) {n : Nat} {R : Ctx ζ ℓ 0 n} (hR : E[R] ⊢ ok)
    {η : Head ζ .quot} {u : Level ℓ} {α r a T : Expr ζ ℓ n} {t₀ : Expr ζ ℓ 0}
    (h₀ : Frontend.quotTerm η (E.get η).eqHead .ctor [u] = .ok t₀)
    (ht : E[R] ⊢ .quotMk η u α r a : T) :
    ∃ U, E[R] ⊢ t₀.wkClosed.apps ![α, r, a] ≡ .quotMk η u α r a : U := by
  cases h₀
  obtain ⟨α₁, r₁, a₁, hα, hr, ha, -⟩ := ht.quotMk_prem
  have h1 : E[(#t[] : Ctx ζ ℓ 0 0).snoc (.sort u)] ⊢ ok := .snoc .nil ⟨_, .sortDF⟩
  have hv0 : E[(#t[] : Ctx ζ ℓ 0 0).snoc (.sort u)] ⊢ .var 0 : .sort u := by
    simpa [Ctx.get, Expr.wk] using h1.var 0
  have h2 : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩)]] ⊢ ok :=
    .snoc h1 ⟨_, (Quot.relType_congr hv0).left⟩
  have hv0' : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩)]] ⊢ .var 0 : .sort u := by
    simpa [Ctx.get, Expr.wk] using h2.var 0
  have h3 : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩), .var ⟨0, by omega⟩]] ⊢ ok :=
    .snoc h2 ⟨_, hv0'⟩
  have hb : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩), .var ⟨0, by omega⟩]] ⊢
      (.quotMk η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩) (.var ⟨2, by omega⟩) :
        Expr ζ ℓ 3) : .quot η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩) := by
    have v0 := h3.var 0
    have v1 := h3.var 1
    have v2 := h3.var 2
    simp [Ctx.get, Expr.wk] at v0 v1 v2
    exact .quotMkDF v0 v1 v2
  have hσ : E[R] ⊢ ![α₁, r₁, a₁] ≡ ![α, r, a] ⊣
      #t[.sort u, Quot.relType (.var ⟨0, by omega⟩), .var ⟨0, by omega⟩] := by
    intro v
    match v with
    | 0 => simpa [Ctx.get, Expr.wk] using hα
    | 1 => simpa [Ctx.get, Expr.wk, Subst.lift, Quot.relType] using hr
    | 2 => simpa [Ctx.get, Expr.wk] using ha
  have hc := closed_lam_apps _ h3 hb hσ
  simp at hc
  exact ⟨_, trans_at hE hR hc (.quotMkDF hα hr ha)⟩

/-- `quotTerm` of `Quot.lift` applied to the arguments of a typed node is definitionally equal to
the node. -/
theorem quotLiftEta_defeq (hE : EnvWF E) {n : Nat} {R : Ctx ζ ℓ 0 n} (hR : E[R] ⊢ ok)
    {η : Head ζ .quot} {u v : Level ℓ} {α r β f h a T : Expr ζ ℓ n} {t₀ : Expr ζ ℓ 0}
    (h₀ : Frontend.quotTerm η (E.get η).eqHead .lift [u, v] = .ok t₀)
    (ht : E[R] ⊢ .quotLift η u v α r β f h a : T) :
    ∃ U, E[R] ⊢ t₀.wkClosed.apps ![α, r, β, f, h, a] ≡ .quotLift η u v α r β f h a : U := by
  cases h₀
  have hEq := hE.eqBlock η
  obtain ⟨α₁, r₁, β₁, f₁, h₁, a₁, hα, hr, hβ, hf, hh, ha, -⟩ := ht.quotLift_prem
  have c1 : E[#t[(.sort u : Expr ζ ℓ 0)]] ⊢ ok := .snoc .nil ⟨_, .sortDF⟩
  have c1v0 : E[#t[(.sort u : Expr ζ ℓ 0)]] ⊢ .var 0 : .sort u := by
    simpa [Ctx.get, ← Expr.subst_wk, Expr.subst, compatType_subst, Subst.wk, Subst.lift, Subst.comp, Quot.relType] using c1.var 0
  have c2 : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩)]] ⊢ ok :=
    .snoc c1 ⟨_, (Quot.relType_congr c1v0).left⟩
  have c3 : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩), .sort v]] ⊢ ok := .snoc c2 ⟨_, .sortDF⟩
  have c3v0 : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩), .sort v]] ⊢ .var 0 : .sort u := by simpa [Ctx.get, ← Expr.subst_wk, Expr.subst, compatType_subst, Subst.wk, Subst.lift, Subst.comp, Quot.relType] using c3.var 0
  have c3' : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩), .sort v].snoc (.var 0)] ⊢ ok := .snoc c3 ⟨_, c3v0⟩
  have c3v2 : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩), .sort v].snoc (.var 0)] ⊢ .var 2 : .sort v := by simpa [Ctx.get, ← Expr.subst_wk, Expr.subst, compatType_subst, Subst.wk, Subst.lift, Subst.comp, Quot.relType] using c3'.var 2
  have c4 : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩), .sort v,
        .forallE (.var ⟨0, by omega⟩) (.var ⟨2, by omega⟩)]] ⊢ ok := .snoc c3 ⟨_, .forallEDF c3v0 c3v2 c3v2⟩
  have c4v0 : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩), .sort v,
        .forallE (.var ⟨0, by omega⟩) (.var ⟨2, by omega⟩)]] ⊢ .var 0 : .sort u := by simpa [Ctx.get, ← Expr.subst_wk, Expr.subst, compatType_subst, Subst.wk, Subst.lift, Subst.comp, Quot.relType] using c4.var 0
  have c4v1 : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩), .sort v,
        .forallE (.var ⟨0, by omega⟩) (.var ⟨2, by omega⟩)]] ⊢ .var 1 : Quot.relType (.var 0) := by simpa [Ctx.get, ← Expr.subst_wk, Expr.subst, compatType_subst, Subst.wk, Subst.lift, Subst.comp, Quot.relType] using c4.var 1
  have c4v2 : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩), .sort v,
        .forallE (.var ⟨0, by omega⟩) (.var ⟨2, by omega⟩)]] ⊢ .var 2 : .sort v := by simpa [Ctx.get, ← Expr.subst_wk, Expr.subst, compatType_subst, Subst.wk, Subst.lift, Subst.comp, Quot.relType] using c4.var 2
  have c4v3 : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩), .sort v,
        .forallE (.var ⟨0, by omega⟩) (.var ⟨2, by omega⟩)]] ⊢ .var 3 : .forallE (.var 0) (Expr.var 2).wk := by
    simpa [Ctx.get, ← Expr.subst_wk, Expr.subst, compatType_subst, Subst.wk, Subst.lift, Subst.comp, Quot.relType] using c4.var 3
  have c5 : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩), .sort v,
        .forallE (.var ⟨0, by omega⟩) (.var ⟨2, by omega⟩),
        Quot.compatType (E.get η).eqHead v (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩)
          (.var ⟨2, by omega⟩) (.var ⟨3, by omega⟩)]] ⊢ ok := .snoc c4 (Quot.compatType_isType hEq c4v0 c4v1 c4v2 c4v3)
  have c5v0 : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩), .sort v,
        .forallE (.var ⟨0, by omega⟩) (.var ⟨2, by omega⟩),
        Quot.compatType (E.get η).eqHead v (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩)
          (.var ⟨2, by omega⟩) (.var ⟨3, by omega⟩)]] ⊢ .var 0 : .sort u := by simpa [Ctx.get, ← Expr.subst_wk, Expr.subst, compatType_subst, Subst.wk, Subst.lift, Subst.comp, Quot.relType] using c5.var 0
  have c5v1 : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩), .sort v,
        .forallE (.var ⟨0, by omega⟩) (.var ⟨2, by omega⟩),
        Quot.compatType (E.get η).eqHead v (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩)
          (.var ⟨2, by omega⟩) (.var ⟨3, by omega⟩)]] ⊢ .var 1 : Quot.relType (.var 0) := by simpa [Ctx.get, ← Expr.subst_wk, Expr.subst, compatType_subst, Subst.wk, Subst.lift, Subst.comp, Quot.relType] using c5.var 1
  have hg : Ctx.get 4 (#t[.sort u, Quot.relType (.var ⟨0, by omega⟩), .sort v,
        .forallE (.var ⟨0, by omega⟩) (.var ⟨2, by omega⟩),
        Quot.compatType (E.get η).eqHead v (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩)
          (.var ⟨2, by omega⟩) (.var ⟨3, by omega⟩),
        .quot η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩)] : Ctx ζ ℓ 0 6) =
      (Quot.compatType (E.get η).eqHead v (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩)
        (.var ⟨2, by omega⟩) (.var ⟨3, by omega⟩) : Expr ζ ℓ 4).wk.wk := by
    rw [show (4 : Fin 6) = (Fin.last 4).castSucc from rfl, Ctx.get_castSucc, Ctx.get_last]
  have c6 : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩), .sort v,
        .forallE (.var ⟨0, by omega⟩) (.var ⟨2, by omega⟩),
        Quot.compatType (E.get η).eqHead v (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩)
          (.var ⟨2, by omega⟩) (.var ⟨3, by omega⟩),
        .quot η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩)]] ⊢ ok := .snoc c5 ⟨_, .quotDF c5v0 c5v1⟩
  have hb : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩), .sort v,
        .forallE (.var ⟨0, by omega⟩) (.var ⟨2, by omega⟩),
        Quot.compatType (E.get η).eqHead v (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩)
          (.var ⟨2, by omega⟩) (.var ⟨3, by omega⟩),
        .quot η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩)]] ⊢
      (.quotLift η u v (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩) (.var ⟨2, by omega⟩)
        (.var ⟨3, by omega⟩) (.var ⟨4, by omega⟩) (.var ⟨5, by omega⟩) : Expr ζ ℓ 6) :
      .var ⟨2, by omega⟩ := by
    have v0 : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩), .sort v,
        .forallE (.var ⟨0, by omega⟩) (.var ⟨2, by omega⟩),
        Quot.compatType (E.get η).eqHead v (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩)
          (.var ⟨2, by omega⟩) (.var ⟨3, by omega⟩),
        .quot η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩)]] ⊢ .var 0 : .sort u := by simpa [Ctx.get, ← Expr.subst_wk, Expr.subst, compatType_subst, Subst.wk, Subst.lift, Subst.comp, Quot.relType] using c6.var 0
    have v1 : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩), .sort v,
        .forallE (.var ⟨0, by omega⟩) (.var ⟨2, by omega⟩),
        Quot.compatType (E.get η).eqHead v (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩)
          (.var ⟨2, by omega⟩) (.var ⟨3, by omega⟩),
        .quot η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩)]] ⊢ .var 1 : Quot.relType (.var 0) := by simpa [Ctx.get, ← Expr.subst_wk, Expr.subst, compatType_subst, Subst.wk, Subst.lift, Subst.comp, Quot.relType] using c6.var 1
    have v2 : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩), .sort v,
        .forallE (.var ⟨0, by omega⟩) (.var ⟨2, by omega⟩),
        Quot.compatType (E.get η).eqHead v (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩)
          (.var ⟨2, by omega⟩) (.var ⟨3, by omega⟩),
        .quot η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩)]] ⊢ .var 2 : .sort v := by simpa [Ctx.get, ← Expr.subst_wk, Expr.subst, compatType_subst, Subst.wk, Subst.lift, Subst.comp, Quot.relType] using c6.var 2
    have v3 : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩), .sort v,
        .forallE (.var ⟨0, by omega⟩) (.var ⟨2, by omega⟩),
        Quot.compatType (E.get η).eqHead v (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩)
          (.var ⟨2, by omega⟩) (.var ⟨3, by omega⟩),
        .quot η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩)]] ⊢ .var 3 : .forallE (.var 0) (Expr.var 2).wk := by
      simpa [Ctx.get, ← Expr.subst_wk, Expr.subst, compatType_subst, Subst.wk, Subst.lift, Subst.comp, Quot.relType] using c6.var 3
    have v4 : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩), .sort v,
        .forallE (.var ⟨0, by omega⟩) (.var ⟨2, by omega⟩),
        Quot.compatType (E.get η).eqHead v (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩)
          (.var ⟨2, by omega⟩) (.var ⟨3, by omega⟩),
        .quot η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩)]] ⊢ .var 4 :
        Quot.compatType (E.get η).eqHead v (.var 0) (.var 1) (.var 2) (.var 3) := by
      have h4 := c6.var 4
      rw [hg, compatType_wk, compatType_wk] at h4
      simpa [var_wk] using h4
    have v5 : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩), .sort v,
        .forallE (.var ⟨0, by omega⟩) (.var ⟨2, by omega⟩),
        Quot.compatType (E.get η).eqHead v (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩)
          (.var ⟨2, by omega⟩) (.var ⟨3, by omega⟩),
        .quot η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩)]] ⊢ .var 5 : .quot η u (.var 0) (.var 1) := by simpa [Ctx.get, ← Expr.subst_wk, Expr.subst, compatType_subst, Subst.wk, Subst.lift, Subst.comp, Quot.relType] using c6.var 5
    exact .quotLiftDF v0 v1 v2 v3 v4 v5
  have hσ : E[R] ⊢ ![α₁, r₁, β₁, f₁, h₁, a₁] ≡ ![α, r, β, f, h, a] ⊣ #t[.sort u, Quot.relType (.var ⟨0, by omega⟩), .sort v,
        .forallE (.var ⟨0, by omega⟩) (.var ⟨2, by omega⟩),
        Quot.compatType (E.get η).eqHead v (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩)
          (.var ⟨2, by omega⟩) (.var ⟨3, by omega⟩),
        .quot η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩)] := by
    intro w
    match w with
    | 0 => simpa [Ctx.get, ← Expr.subst_wk, Expr.subst, compatType_subst, Subst.wk, Subst.lift, Subst.comp, Quot.relType] using hα
    | 1 => simpa [Ctx.get, ← Expr.subst_wk, Expr.subst, compatType_subst, Subst.wk, Subst.lift, Subst.comp, Quot.relType] using hr
    | 2 => simpa [Ctx.get, ← Expr.subst_wk, Expr.subst, compatType_subst, Subst.wk, Subst.lift, Subst.comp, Quot.relType] using hβ
    | 3 => simpa [Ctx.get, ← Expr.subst_wk, Expr.subst, compatType_subst, Subst.wk, Subst.lift, Subst.comp, Quot.relType] using hf
    | 4 =>
      show E[R] ⊢ h₁ ≡ h : _
      rw [hg, compatType_wk, compatType_wk, compatType_subst]
      simpa [var_wk, Expr.subst] using hh
    | 5 => simpa [Ctx.get, ← Expr.subst_wk, Expr.subst, compatType_subst, Subst.wk, Subst.lift, Subst.comp, Quot.relType] using ha
  have hc := closed_lam_apps _ c6 hb hσ
  simp at hc
  exact ⟨_, trans_at hE hR hc (.quotLiftDF hα hr hβ hf hh ha)⟩

/-- `quotTerm` of `Quot.ind` applied to the arguments of a typed node is definitionally equal to
the node. -/
theorem quotIndEta_defeq (hE : EnvWF E) {n : Nat} {R : Ctx ζ ℓ 0 n} (hR : E[R] ⊢ ok)
    {η : Head ζ .quot} {u : Level ℓ} {α r β f a T : Expr ζ ℓ n} {t₀ : Expr ζ ℓ 0}
    (h₀ : Frontend.quotTerm η (E.get η).eqHead .ind [u] = .ok t₀)
    (ht : E[R] ⊢ .quotInd η u α r β f a : T) :
    ∃ U, E[R] ⊢ t₀.wkClosed.apps ![α, r, β, f, a] ≡ .quotInd η u α r β f a : U := by
  cases h₀
  obtain ⟨α₁, r₁, β₁, f₁, a₁, hα, hr, hβ, hf, ha, hβa, -⟩ := ht.quotInd_prem
  have c1 : E[#t[(.sort u : Expr ζ ℓ 0)]] ⊢ ok := .snoc .nil ⟨_, .sortDF⟩
  have c1v0 : E[#t[(.sort u : Expr ζ ℓ 0)]] ⊢ .var 0 : .sort u := by
    simpa [Ctx.get, ← Expr.subst_wk, Expr.subst, Subst.wk, Subst.lift, Subst.comp, Quot.relType, Quot.motiveType] using c1.var 0
  have c2 : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩)]] ⊢ ok := .snoc c1 ⟨_, (Quot.relType_congr c1v0).left⟩
  have c2v0 : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩)]] ⊢ .var 0 : .sort u := by simpa [Ctx.get, ← Expr.subst_wk, Expr.subst, Subst.wk, Subst.lift, Subst.comp, Quot.relType, Quot.motiveType] using c2.var 0
  have c2v1 : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩)]] ⊢ .var 1 : Quot.relType (.var 0) := by simpa [Ctx.get, ← Expr.subst_wk, Expr.subst, Subst.wk, Subst.lift, Subst.comp, Quot.relType, Quot.motiveType] using c2.var 1
  have c3 : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩),
        Quot.motiveType η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩)]] ⊢ ok := .snoc c2 (Quot.motiveType_isType c2v0 c2v1)
  have c3v0 : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩),
        Quot.motiveType η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩)]] ⊢ .var 0 : .sort u := by simpa [Ctx.get, ← Expr.subst_wk, Expr.subst, Subst.wk, Subst.lift, Subst.comp, Quot.relType, Quot.motiveType] using c3.var 0
  have c3v1 : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩),
        Quot.motiveType η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩)]] ⊢ .var 1 : Quot.relType (.var 0) := by simpa [Ctx.get, ← Expr.subst_wk, Expr.subst, Subst.wk, Subst.lift, Subst.comp, Quot.relType, Quot.motiveType] using c3.var 1
  have c3v2 : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩),
        Quot.motiveType η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩)]] ⊢ .var 2 : Quot.motiveType η u (.var 0) (.var 1) := by
    simpa [Ctx.get, ← Expr.subst_wk, Expr.subst, Subst.wk, Subst.lift, Subst.comp, Quot.relType, Quot.motiveType] using c3.var 2
  have c4 : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩),
        Quot.motiveType η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩),
        Quot.minorType η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩) (.var ⟨2, by omega⟩)]] ⊢ ok := .snoc c3 (Quot.minorType_isType c3v0 c3v1 c3v2)
  have c4v0 : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩),
        Quot.motiveType η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩),
        Quot.minorType η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩) (.var ⟨2, by omega⟩)]] ⊢ .var 0 : .sort u := by simpa [Ctx.get, ← Expr.subst_wk, Expr.subst, Subst.wk, Subst.lift, Subst.comp, Quot.relType, Quot.motiveType] using c4.var 0
  have c4v1 : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩),
        Quot.motiveType η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩),
        Quot.minorType η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩) (.var ⟨2, by omega⟩)]] ⊢ .var 1 : Quot.relType (.var 0) := by simpa [Ctx.get, ← Expr.subst_wk, Expr.subst, Subst.wk, Subst.lift, Subst.comp, Quot.relType, Quot.motiveType] using c4.var 1
  have c5 : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩),
        Quot.motiveType η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩),
        Quot.minorType η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩) (.var ⟨2, by omega⟩),
        .quot η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩)]] ⊢ ok := .snoc c4 ⟨_, .quotDF c4v0 c4v1⟩
  have hg : Ctx.get 3 (#t[.sort u, Quot.relType (.var ⟨0, by omega⟩),
        Quot.motiveType η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩),
        Quot.minorType η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩) (.var ⟨2, by omega⟩),
        .quot η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩)] : Ctx ζ ℓ 0 5) =
      (Quot.minorType η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩) (.var ⟨2, by omega⟩) :
        Expr ζ ℓ 3).wk.wk := by
    rw [show (3 : Fin 5) = (Fin.last 3).castSucc from rfl, Ctx.get_castSucc, Ctx.get_last]
  have hb : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩),
        Quot.motiveType η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩),
        Quot.minorType η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩) (.var ⟨2, by omega⟩),
        .quot η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩)]] ⊢
      (.quotInd η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩) (.var ⟨2, by omega⟩)
        (.var ⟨3, by omega⟩) (.var ⟨4, by omega⟩) : Expr ζ ℓ 5) :
      .app (.var ⟨2, by omega⟩) (.var ⟨4, by omega⟩) := by
    have v0 : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩),
        Quot.motiveType η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩),
        Quot.minorType η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩) (.var ⟨2, by omega⟩),
        .quot η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩)]] ⊢ .var 0 : .sort u := by simpa [Ctx.get, ← Expr.subst_wk, Expr.subst, Subst.wk, Subst.lift, Subst.comp, Quot.relType, Quot.motiveType] using c5.var 0
    have v1 : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩),
        Quot.motiveType η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩),
        Quot.minorType η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩) (.var ⟨2, by omega⟩),
        .quot η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩)]] ⊢ .var 1 : Quot.relType (.var 0) := by simpa [Ctx.get, ← Expr.subst_wk, Expr.subst, Subst.wk, Subst.lift, Subst.comp, Quot.relType, Quot.motiveType] using c5.var 1
    have v2 : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩),
        Quot.motiveType η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩),
        Quot.minorType η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩) (.var ⟨2, by omega⟩),
        .quot η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩)]] ⊢ .var 2 : Quot.motiveType η u (.var 0) (.var 1) := by
      simpa [Ctx.get, ← Expr.subst_wk, Expr.subst, Subst.wk, Subst.lift, Subst.comp, Quot.relType, Quot.motiveType] using c5.var 2
    have v3 : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩),
        Quot.motiveType η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩),
        Quot.minorType η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩) (.var ⟨2, by omega⟩),
        .quot η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩)]] ⊢ .var 3 : Quot.minorType η u (.var 0) (.var 1) (.var 2) := by
      have h3 := c5.var 3
      rw [hg, minorType_wk, minorType_wk] at h3
      simpa [var_wk] using h3
    have v4 : E[#t[.sort u, Quot.relType (.var ⟨0, by omega⟩),
        Quot.motiveType η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩),
        Quot.minorType η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩) (.var ⟨2, by omega⟩),
        .quot η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩)]] ⊢ .var 4 : .quot η u (.var 0) (.var 1) := by simpa [Ctx.get, ← Expr.subst_wk, Expr.subst, Subst.wk, Subst.lift, Subst.comp, Quot.relType, Quot.motiveType] using c5.var 4
    exact .quotIndDF v0 v1 v2 v3 v4
      (Defeq.appDF (Defeq.quotDF v0 v1) .sortDF v2 v4 (by simpa using .sortDF))
  have hσ : E[R] ⊢ ![α₁, r₁, β₁, f₁, a₁] ≡ ![α, r, β, f, a] ⊣ #t[.sort u, Quot.relType (.var ⟨0, by omega⟩),
        Quot.motiveType η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩),
        Quot.minorType η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩) (.var ⟨2, by omega⟩),
        .quot η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩)] := by
    intro w
    match w with
    | 0 => simpa [Ctx.get, ← Expr.subst_wk, Expr.subst, Subst.wk, Subst.lift, Subst.comp, Quot.relType, Quot.motiveType] using hα
    | 1 => simpa [Ctx.get, ← Expr.subst_wk, Expr.subst, Subst.wk, Subst.lift, Subst.comp, Quot.relType, Quot.motiveType] using hr
    | 2 => simpa [Ctx.get, ← Expr.subst_wk, Expr.subst, Subst.wk, Subst.lift, Subst.comp, Quot.relType, Quot.motiveType] using hβ
    | 3 =>
      show E[R] ⊢ f₁ ≡ f : _
      rw [hg, minorType_wk, minorType_wk, minorType_subst]
      simpa [var_wk, Expr.subst] using hf
    | 4 => simpa [Ctx.get, ← Expr.subst_wk, Expr.subst, Subst.wk, Subst.lift, Subst.comp, Quot.relType, Quot.motiveType] using ha
  have hc := closed_lam_apps _ c5 hb hσ
  simp at hc
  exact ⟨_, trans_at hE hR hc (.quotIndDF hα hr hβ hf ha hβa)⟩

end

end SatTyped

end EraseProof

namespace EraseProof

namespace SatTyped

section
open Metalean
variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat}

/-- A prefix of a typed application spine is typed. -/
theorem prefix_typed {n : Nat} {R : Ctx ζ ℓ 0 n} {X T : Expr ζ ℓ n}
    {as₁ as₂ : List (Expr ζ ℓ n)} (h : E[R] ⊢ X.appList (as₁ ++ as₂) : T) :
    ∃ T₁, E[R] ⊢ X.appList as₁ : T₁ := by
  rw [TrApps.appList_append] at h
  exact (InstPre.appList_inv h).1

/-- The η-term's spine of a saturated node: when the η-term applied to the node's arguments is
definitionally equal to the node, every prefix of the η-term's spine is typed. -/
theorem eta_prefix (hE : EnvWF E) {n K : Nat} {R : Ctx ζ ℓ 0 n} (hR : E[R] ⊢ ok)
    {X N T : Expr ζ ℓ n} {xs : Fin K → Expr ζ ℓ n} {rest as₁ as₂ : List (Expr ζ ℓ n)}
    (hd : ∃ U, E[R] ⊢ X.apps xs ≡ N : U) (ht : E[R] ⊢ N.appList rest : T)
    (hs : as₁ ++ as₂ = List.ofFn xs ++ rest) : ∃ T₁, E[R] ⊢ X.appList as₁ : T₁ := by
  obtain ⟨U, hd⟩ := hd
  obtain ⟨T', h⟩ := appList_defeq hE hR rest hd ht
  rw [← appList_ofFn, ← TrApps.appList_append, ← hs] at h
  exact prefix_typed h

end

end SatTyped


section
open Metalean SatTyped
variable {ζ : Sigs} {E : Env ζ} {lps : List Name}

/-- Equal lists that start with tuples of the same length agree on the tuples and the rests. -/
private theorem ofFn_split {α : Type} {K : Nat} {xs ys : Fin K → α} {r r' : List α}
    (h : List.ofFn xs ++ r = List.ofFn ys ++ r') : xs = ys ∧ r = r' := by
  have := List.append_inj h (by simp)
  exact ⟨List.ofFn_injective this.1, this.2⟩

/-- Typed prefixes of saturating spines (subject expansion of the translator's η-terms): when the
image of a spine of an inductive type, a quotient constant or a recursor is typed, the image of every
prefix of the spine is typed, except a partial prefix of a saturated recursor spine (`hr`). A
prefix that reaches the arity is a prefix of the node's application; a shorter one is the η-term applied to the prefix, whose application to the node's arguments is
definitionally equal to the node (`indEta_defeq`, `quotTypeEta_defeq`, `quotMkEta_defeq`,
`quotLiftEta_defeq`, `quotIndEta_defeq`). Reference: `type_of_typing`'s use of the typing of
applications (`MR S/PCUICSafeRetyping.v:806`); the inversion of β (`MR P/PCUICConversion.v`). -/
theorem SatTr.typed (hE : EnvWF E) {n : Nat} {R : Ctx ζ lps.length 0 n} (hR : E[R] ⊢ ok)
    {b : MBinding ζ} {us : List Level}
    (hc : ∀ {ι : IndSig} (η : Head ζ (.inductive ι)) (s : Fin ι.nsorts) (k : Fin (ι.nctors s))
      (o : List Nat), b ≠ .ctor η s k o)
    {as₁ as₂ : List (Expr ζ lps.length n)}
    (hr : ∀ {ι : IndSig} (η : Head ζ (.inductive ι)) (s : Fin ι.nsorts)
      (os : List (List (List Nat))), b = .recr η s os → as₁.length < ι.recrEnd s →
        (as₁ ++ as₂).length < ι.recrEnd s)
    {t₁ t T : Expr ζ lps.length n}
    (h₁ : SatTr E lps b us as₁ t₁) (h : SatTr E lps b us (as₁ ++ as₂) t) (ht : E[R] ⊢ t : T) :
    ∃ T₁, E[R] ⊢ t₁ : T₁ := by
  generalize hA : as₁ ++ as₂ = A at h
  cases h₁ with
  | indSat ps is rest hls =>
    cases h with
    | indSat ps' is' rest' hls' =>
      rw [hls] at hls'; cases hls'
      simp only [List.append_assoc] at hA
      obtain ⟨h1, h2⟩ := ofFn_split hA
      subst h1
      obtain ⟨h3, h4⟩ := ofFn_split h2
      subst h3 h4
      rw [TrApps.appList_append] at ht
      exact (InstPre.appList_inv ht).1
    | indEta _ hlt =>
      have := congrArg List.length hA
      simp only [List.length_append, List.length_ofFn] at this
      omega
  | indEta hls hlt =>
    cases h with
    | indEta hls' _ =>
      rw [hls] at hls'; cases hls'
      rw [← hA] at ht
      exact prefix_typed ht
    | indSat ps is rest hls' =>
      rw [hls] at hls'; cases hls'
      obtain ⟨⟨_, hN⟩, -⟩ := InstPre.appList_inv ht
      refine eta_prefix (as₂ := as₂) hE hR (indEta_defeq hE hN) ht ?_
      rw [hA, List.ofFn_add]
      congr 2 <;> congr 1 <;> funext i
      · exact (Fin.append_left ps is i).symm
      · exact (Fin.append_right ps is i).symm
  | ctorSat | ctorEta => exact absurd rfl (hc _ _ _ _)
  | recrSat mo Af rest mins hRL hls hmo hw =>
    cases h with
    | recrSat mo' Af' rest' mins' hRL' hls' hmo' hw' =>
      obtain ⟨rfl, rfl⟩ := TrDet.RecrLevels.det hRL hRL'
      obtain rfl := TrDet.TrLevels.det hls hls'
      obtain rfl : mo = mo' := funext fun t => funext fun c =>
        Option.some.inj ((hmo t c).symm.trans (hmo' t c))
      simp only [List.append_assoc] at hA
      obtain ⟨rfl, rfl⟩ := ofFn_split hA
      obtain rfl : mins = mins' := funext fun t => funext fun c =>
        Except.ok.inj ((hw t c).symm.trans (hw' t c))
      rw [TrApps.appList_append] at ht
      exact (InstPre.appList_inv ht).1
    | recrEta _ _ _ _ hlt =>
      have := congrArg List.length hA
      simp only [List.length_append, List.length_ofFn] at this
      omega
  | recrEta mo hRL hls hmo hlt h₀ =>
    cases h with
    | recrEta mo' hRL' hls' hmo' _ h₀' =>
      obtain ⟨rfl, rfl⟩ := TrDet.RecrLevels.det hRL hRL'
      obtain rfl := TrDet.TrLevels.det hls hls'
      obtain rfl : mo = mo' := funext fun t => funext fun c =>
        Option.some.inj ((hmo t c).symm.trans (hmo' t c))
      rw [h₀] at h₀'; cases h₀'
      rw [← hA] at ht
      exact prefix_typed ht
    | recrSat _ Af rest _ =>
      have h2 := hr _ _ _ rfl hlt
      have := congrArg List.length hA
      simp only [List.length_append, List.length_ofFn] at this h2
      omega
  | quotType hu =>
    cases h with
    | quotType hu' =>
      rw [hu] at hu'; cases hu'
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at hA
      obtain ⟨rfl, rfl, rfl⟩ := hA
      rw [TrApps.appList_append] at ht
      exact (InstPre.appList_inv ht).1
    | quotEta _ hlt =>
      have := congrArg List.length hA
      simp [quotArity] at this hlt; omega
  | quotMk hu =>
    cases h with
    | quotMk hu' =>
      rw [hu] at hu'; cases hu'
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at hA
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hA
      rw [TrApps.appList_append] at ht
      exact (InstPre.appList_inv ht).1
    | quotEta _ hlt =>
      have := congrArg List.length hA
      simp [quotArity] at this hlt; omega
  | quotLift hu =>
    cases h with
    | quotLift hu' =>
      rw [hu] at hu'; cases hu'
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at hA
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hA
      rw [TrApps.appList_append] at ht
      exact (InstPre.appList_inv ht).1
    | quotEta _ hlt =>
      have := congrArg List.length hA
      simp [quotArity] at this hlt; omega
  | quotInd hu =>
    cases h with
    | quotInd hu' =>
      rw [hu] at hu'; cases hu'
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at hA
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hA
      rw [TrApps.appList_append] at ht
      exact (InstPre.appList_inv ht).1
    | quotEta _ hlt =>
      have := congrArg List.length hA
      simp [quotArity] at this hlt; omega
  | quotEta hu hlt h₀ =>
    cases h with
    | quotEta hu' _ h₀' =>
      rw [hu] at hu'; cases hu'
      rw [h₀] at h₀'; cases h₀'
      rw [← hA] at ht
      exact prefix_typed ht
    | quotType hu' =>
      rw [hu] at hu'; cases hu'
      obtain ⟨⟨_, hN⟩, -⟩ := InstPre.appList_inv ht
      exact eta_prefix (as₂ := as₂) hE hR (quotTypeEta_defeq h₀ hN) ht (by rw [hA]; rfl)
    | quotMk hu' =>
      rw [hu] at hu'; cases hu'
      obtain ⟨⟨_, hN⟩, -⟩ := InstPre.appList_inv ht
      exact eta_prefix (as₂ := as₂) hE hR (quotMkEta_defeq hE hR h₀ hN) ht (by rw [hA]; rfl)
    | quotLift hu' =>
      rw [hu] at hu'; cases hu'
      obtain ⟨⟨_, hN⟩, -⟩ := InstPre.appList_inv ht
      exact eta_prefix (as₂ := as₂) hE hR (quotLiftEta_defeq hE hR h₀ hN) ht (by rw [hA]; rfl)
    | quotInd hu' =>
      rw [hu] at hu'; cases hu'
      obtain ⟨⟨_, hN⟩, -⟩ := InstPre.appList_inv ht
      exact eta_prefix (as₂ := as₂) hE hR (quotIndEta_defeq hE hR h₀ hN) ht (by rw [hA]; rfl)

end

end EraseProof
