import EraseProof.Bridge.Apps
import EraseProof.Bridge.Weak

/-!
# Substitution into the translation

`TrM.inst` and `TrM.inst_let`: instantiating the innermost bound variable of a translated body by
a translated term gives a translation of the instantiated body, definitionally equal to the
substituted image. The proof goes through the translation without its projection premises
(`InstPre.PreTr`): the instantiated body has such a pre-translation, congruent to the substituted
image up to weak-head reduction at the saturated spines (`DCong` with `False`); the image is
typed, so the pre-translation is typed, and a typed pre-translation is a translation
(`PreTr.recover`): every projection's major is typed, by inversion, in the context where the
Metalean term places it, an extension of the context of the translation. Reference: lean4lean
`TrExprS.inst` (`L4 Typing/Inst.lean`); `Defeq.substRen` (`ML Typing/Substitution.lean:176`).
-/

open Lean Erasure

namespace EraseProof

namespace InstPre

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {lps : List Name}

/-- `TrM` without the context and without the typing premises of projections. -/
inductive PreTr (E : Metalean.Env ζ) (B : Binds ζ) (lps : List Name) :
    {n : Nat} → MLCtx ζ lps.length n → Expr → Metalean.Expr ζ lps.length n → Prop
  | bvar : Δ.findB i = some t → PreTr E B lps Δ (.bvar i) t
  | fvar : Δ.findF x = some t → PreTr E B lps Δ (.fvar x) t
  | sort : TrLevel lps u = some l → PreTr E B lps Δ (.sort u) (.sort l)
  | const {kind : Metalean.ConstKind} {nl : Nat} {η : Metalean.Head ζ (.const kind nl)}
      {ls : Fin nl → Metalean.Level lps.length} :
      B c = some (.const η) → TrLevels lps us nl = some ls →
      PreTr E B lps Δ (.const c us) (.const η ls)
  | special {n : Nat} {Δ : MLCtx ζ lps.length n}
      {as : List Lean.Expr} {as' : List (Metalean.Expr ζ lps.length n)}
      {b : MBinding ζ} {t : Metalean.Expr ζ lps.length n} :
      B c = some b → b.isSpecial = true → as.length = as'.length →
      (∀ (i : Nat) a a', as[i]? = some a → as'[i]? = some a' → PreTr E B lps Δ a a') →
      SatTr E lps b us as' t → PreTr E B lps Δ (mkAppN (.const c us) as.toArray) t
  | app : ¬ SpecialHead B f → PreTr E B lps Δ f f' → PreTr E B lps Δ a a' →
      PreTr E B lps Δ (.app f a) (.app f' a')
  | lam : PreTr E B lps Δ A A' → PreTr E B lps (Δ.pushLam none) b b' →
      PreTr E B lps Δ (.lam x A b bi) (.lam A' b')
  | forallE : PreTr E B lps Δ A A' → PreTr E B lps (Δ.pushLam none) b b' →
      PreTr E B lps Δ (.forallE x A b bi) (.forallE A' b')
  | letE : PreTr E B lps Δ T T' → PreTr E B lps Δ v v' →
      PreTr E B lps ((none, .vlet v') :: Δ) b b' →
      PreTr E B lps Δ (.letE x T v b nd) (.letE T' v' b'.wk)
  | mdata : PreTr E B lps Δ e t → PreTr E B lps Δ (.mdata d e) t
  | lit {ηNat : Metalean.Head ζ (.inductive natSig)} {o₀ o₁ : List Nat} :
      B ``Nat = some (.ind ηNat 0) → B ``Nat.zero = some (.ctor ηNat 0 0 o₀) →
      B ``Nat.succ = some (.ctor ηNat 0 1 o₁) → PreTr E B lps Δ (.lit (.natVal k)) (natLitM ηNat k)
  | projStruct {ι : Metalean.IndSig} {η : Metalean.Head ζ (.inductive ι)} {s : Fin ι.nsorts}
      {c : Fin (ι.nctors s)} {ls : Fin ι.nlevels → Metalean.Level lps.length}
      {ps : Fin ι.nparams → Metalean.Expr ζ lps.length n}
      (hst : (E.get η).block.IsStructure s c) (hi : i < (ι.ctors s c).nfields) :
      B S = some (.ind η s) → PreTr E B lps Δ e e' →
      PreTr E B lps Δ (.proj S i e) (hst.projTerm η ls ps ⟨i, hi⟩ e')
  | projProof {ι : Metalean.IndSig} {η : Metalean.Head ζ (.inductive ι)} {s : Fin ι.nsorts}
      {c : Fin (ι.nctors s)} {ls : Fin ι.nlevels → Metalean.Level lps.length}
      {ps : Fin ι.nparams → Metalean.Expr ζ lps.length n} (hi : ι.nindices s = 0) :
      B S = some (.ind η s) → (∀ t : Fin ι.nsorts, t = s) → (∀ d : Fin (ι.nctors s), d = c) →
      (ι.ctors s c).nrecFields = 0 → i < (ι.ctors s c).nfields →
      ¬ (E.get η).block.IsStructure s c →
      PreTr E B lps Δ e e' → PreTr E B lps Δ (.proj S i e) (projProofTerm E η s c ls hi ps i e')

/-- A translation is a pre-translation. -/
theorem PreTr.ofTrM {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    {e : Expr} {t : Metalean.Expr ζ lps.length n} (h : TrM E B lps Γ Δ e t) : PreTr E B lps Δ e t := by
  induction h with
  | bvar h => exact .bvar h
  | fvar h => exact .fvar h
  | sort h => exact .sort h
  | const h₁ h₂ => exact .const h₁ h₂
  | special hb hs hlen _ hsat ih => exact .special hb hs hlen ih hsat
  | app hns _ _ ih₁ ih₂ => exact .app hns ih₁ ih₂
  | lam _ _ ih₁ ih₂ => exact .lam ih₁ ih₂
  | forallE _ _ ih₁ ih₂ => exact .forallE ih₁ ih₂
  | letE _ _ _ ih₁ ih₂ ih₃ => exact .letE ih₁ ih₂ ih₃
  | mdata _ ih => exact .mdata ih
  | lit h h₀ h₁ => exact .lit h h₀ h₁
  | projStruct hst hi hS _ _ ih => exact .projStruct hst hi hS ih
  | projProof hi hS hs hc hr hf hns _ _ ih => exact .projProof hi hS hs hc hr hf hns ih

/-- The locals before (`Δ`) and after (`Δ'`) lifting the Lean bound variables from `dk` on by `d`
and substituting `σ` into the Metalean terms they denote. -/
def MLCtx.Subs {n n' : Nat} (dk d : Nat) (σ : Metalean.Subst ζ ℓ n n') (Δ : MLCtx ζ ℓ n)
    (Δ' : MLCtx ζ ℓ n') : Prop :=
  (∀ i t, Δ.findB i = some t → Δ'.findB (if i < dk then i else i + d) = some (t.subst σ)) ∧
  ∀ x t, Δ.findF x = some t → Δ'.findF x = some (t.subst σ)

theorem MLCtx.Subs.pushLam {ℓ n n' dk d : Nat} {σ : Metalean.Subst ζ ℓ n n'} {Δ : MLCtx ζ ℓ n}
    {Δ' : MLCtx ζ ℓ n'} (h : MLCtx.Subs dk d σ Δ Δ') :
    MLCtx.Subs (dk + 1) d σ.lift (Δ.pushLam none) (Δ'.pushLam none) := by
  constructor
  · intro i t ht
    cases i with
    | zero =>
      simp only [MLCtx.pushLam, MLCtx.findB, MLDecl.denote] at ht ⊢
      cases ht
      simp [MLCtx.findB, MLDecl.denote]
    | succ i =>
      simp only [MLCtx.pushLam, MLCtx.findB, MLCtx.findB_map_wk, Option.map_eq_some_iff] at ht
      obtain ⟨u, hu, rfl⟩ := ht
      have hu' := h.1 i u hu
      have hidx : (if i + 1 < dk + 1 then i + 1 else i + 1 + d) =
          (if i < dk then i else i + d) + 1 := by split_ifs <;> omega
      rw [hidx]
      simp [MLCtx.pushLam, MLCtx.findB, MLCtx.findB_map_wk, hu', Metalean.Expr.wk_subst_lift]
  · intro x t ht
    simp only [MLCtx.pushLam, MLCtx.findF, MLCtx.findF_map_wk, Option.map_eq_some_iff] at ht
    obtain ⟨u, hu, rfl⟩ := ht
    simp [MLCtx.pushLam, MLCtx.findF, MLCtx.findF_map_wk, h.2 x u hu, Metalean.Expr.wk_subst_lift]

theorem MLCtx.Subs.cons {ℓ n n' dk d : Nat} {σ : Metalean.Subst ζ ℓ n n'} {Δ : MLCtx ζ ℓ n}
    {Δ' : MLCtx ζ ℓ n'} (h : MLCtx.Subs dk d σ Δ Δ') (v : Metalean.Expr ζ ℓ n) :
    MLCtx.Subs (dk + 1) d σ ((none, .vlet v) :: Δ) ((none, .vlet (v.subst σ)) :: Δ') := by
  constructor
  · intro i t ht
    cases i with
    | zero =>
      simp only [MLCtx.findB, MLDecl.denote] at ht ⊢
      cases ht
      simp [MLCtx.findB, MLDecl.denote]
    | succ i =>
      simp only [MLCtx.findB] at ht
      have hidx : (if i + 1 < dk + 1 then i + 1 else i + 1 + d) =
          (if i < dk then i else i + d) + 1 := by split_ifs <;> omega
      rw [hidx]
      simpa [MLCtx.findB] using h.1 i t ht
  · intro x t ht
    simpa [MLCtx.findF] using h.2 x t (by simpa [MLCtx.findF] using ht)

/-- Lifting the Lean bound variables and substituting into the image keeps a pre-translation. -/
theorem PreTr.subst {n : Nat} {Δ : MLCtx ζ lps.length n} {e : Expr}
    {t : Metalean.Expr ζ lps.length n} (h : PreTr E B lps Δ e t) :
    ∀ {n' dk d : Nat} {σ : Metalean.Subst ζ lps.length n n'} {Δ' : MLCtx ζ lps.length n'},
      MLCtx.Subs dk d σ Δ Δ' → PreTr E B lps Δ' (e.liftLooseBVars' dk d) (t.subst σ) := by
  induction h with
  | bvar hb =>
    intro _ _ _ _ _ W
    simp only [Expr.liftLooseBVars']
    exact .bvar (W.1 _ _ hb)
  | fvar hf => intro _ _ _ _ _ W; exact .fvar (W.2 _ _ hf)
  | sort hl => intro _ _ _ _ _ _; exact .sort hl
  | const h₁ h₂ => intro _ _ _ _ _ _; exact .const h₁ h₂
  | @special _ _ _ _ as as' _ _ hb hs hlen _ hsat ih =>
    intro _ _ _ σ _ W
    rw [mkAppN_toArray, liftLooseBVars'_foldl, ← mkAppN_toArray]
    refine .special hb hs (by simpa using hlen) (fun i a a' ha ha' => ?_) (hsat.subst σ)
    simp only [List.getElem?_map, Option.map_eq_some_iff] at ha ha'
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    obtain ⟨a₀', ha₀', rfl⟩ := ha'
    exact ih i a₀ a₀' ha₀ ha₀' W
  | app hns _ _ ih₁ ih₂ =>
    intro _ _ _ _ _ W
    refine .app (fun ⟨c, us, b, hc, hB, hs⟩ => hns ⟨c, us, b, ?_, hB, hs⟩) (ih₁ W) (ih₂ W)
    rw [liftLooseBVars'_getAppFn] at hc
    exact liftLooseBVars'_eq_const hc
  | lam _ _ ih₁ ih₂ =>
    intro _ _ _ _ _ W
    simp only [Metalean.Expr.subst]
    exact .lam (ih₁ W) (ih₂ W.pushLam)
  | forallE _ _ ih₁ ih₂ =>
    intro _ _ _ _ _ W
    simp only [Metalean.Expr.subst]
    exact .forallE (ih₁ W) (ih₂ W.pushLam)
  | letE _ _ _ ih₁ ih₂ ih₃ =>
    intro _ _ _ _ _ W
    simp only [Metalean.Expr.subst, Metalean.Expr.wk_subst_lift]
    exact .letE (ih₁ W) (ih₂ W) (ih₃ (W.cons _))
  | mdata _ ih => intro _ _ _ _ _ W; exact .mdata (ih W)
  | lit hB h₀ h₁ =>
    intro _ _ _ _ _ _
    rw [natLitM_subst]
    exact .lit hB h₀ h₁
  | projStruct hst hi hS _ ih =>
    intro _ _ _ _ _ W
    rw [Metalean.Inductive.IsStructure.projTerm_subst]
    exact .projStruct hst hi hS (ih W)
  | projProof hi hS hs hc hr hf hns _ ih =>
    intro _ _ _ _ _ W
    rw [projProofTerm_subst]
    exact .projProof hi hS hs hc hr hf hns (ih W)

/-- Inversion of a pre-translation of a spine of a saturating constant. -/
theorem PreTr.special_inv {n : Nat} {Δ : MLCtx ζ lps.length n} {c : Name} {us : List Level}
    {bs : List Expr} {b : MBinding ζ} {t : Metalean.Expr ζ lps.length n} (hb : B c = some b)
    (hs : b.isSpecial = true) (h : PreTr E B lps Δ (mkAppN (.const c us) bs.toArray) t) :
    ∃ bs' : List (Metalean.Expr ζ lps.length n), bs.length = bs'.length ∧
      (∀ (i : Nat) a a', bs[i]? = some a → bs'[i]? = some a' → PreTr E B lps Δ a a') ∧
      SatTr E lps b us bs' t := by
  generalize hm : mkAppN (Expr.const c us) bs.toArray = m at h
  cases h with
  | const hc =>
    rw [mkAppN_eq_foldl] at hm
    obtain ⟨rfl, rfl, -⟩ := foldl_app_const_inj (as' := []) hm
    rw [hb] at hc; cases hc; cases hs
  | special hb₂ _ hlen hargs hsat =>
    rw [mkAppN_eq_foldl, mkAppN_eq_foldl] at hm
    obtain ⟨rfl, rfl, rfl⟩ := foldl_app_const_inj hm
    rw [hb] at hb₂; cases hb₂
    exact ⟨_, hlen, hargs, hsat⟩
  | app hns => exact absurd (specialHead_of_app hm.symm hb hs) hns
  | _ => exact absurd hm (ne_mkAppN_const fun _ _ h => by cases h).symm

/-- One more argument after a spine of a saturating constant (`TrM.apps`). -/
theorem PreTr.app_special {n : Nat} {Δ : MLCtx ζ lps.length n} {f a : Expr}
    {f' a' : Metalean.Expr ζ lps.length n} (hsp : SpecialHead B f) (hf : PreTr E B lps Δ f f')
    (ha : PreTr E B lps Δ a a') :
    ∃ t, PreTr E B lps Δ (.app f a) t ∧ Metalean.WHRedS E (.app f' a') t := by
  obtain ⟨c, us, b, hfn, hb, hs⟩ := hsp
  obtain ⟨bs, rfl⟩ := eq_mkAppN_of_getAppFn hfn
  obtain ⟨bs', hlen, hargs, hsat⟩ := PreTr.special_inv hb hs hf
  obtain ⟨t, hsat', hred⟩ := hsat.append [a']
  refine ⟨t, ?_, hred⟩
  have happ : Expr.app (mkAppN (Expr.const c us) bs.toArray) a =
      mkAppN (.const c us) (bs ++ [a]).toArray := by
    simp only [mkAppN_eq_foldl, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [happ]
  refine .special hb hs (by simp [hlen]) (fun i x x' hx hx' => ?_) hsat'
  by_cases hi : i < bs.length
  · rw [List.getElem?_append_left hi] at hx
    rw [List.getElem?_append_left (by omega)] at hx'
    exact hargs i x x' hx hx'
  · rw [List.getElem?_append_right (by omega)] at hx
    rw [List.getElem?_append_right (by omega), ← hlen] at hx'
    obtain ⟨h0, rfl⟩ : i - bs.length = 0 ∧ x = a := by
      rcases h : i - bs.length with _ | k
      · rw [h] at hx; simp at hx; exact ⟨rfl, hx.symm⟩
      · rw [h] at hx; simp at hx
    rw [h0] at hx'
    simp at hx'
    subst hx'
    exact ha

end

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {lps : List Name}

/-- A list split after `K` entries. -/
theorem split_ofFn {α : Type} {K : Nat} {xs : Fin K → α} {rest l : List α}
    (h : l.length = (List.ofFn xs ++ rest).length) :
    ∃ (ys : Fin K → α) (rest' : List α), l = List.ofFn ys ++ rest' ∧ rest'.length = rest.length := by
  have hK : K ≤ l.length := by simp at h; omega
  obtain ⟨ys, rest', -, hd, hl⟩ := TrApps.split_at l K hK
  refine ⟨ys, rest', hl, ?_⟩
  rw [← hd]; simp at h ⊢; omega

/-- A saturating binding's images exist for every argument list of the same length. -/
theorem SatTr.replace {n : Nat} {b : MBinding ζ} {us : List Level}
    {as' : List (Metalean.Expr ζ lps.length n)} {t : Metalean.Expr ζ lps.length n}
    (h : SatTr E lps b us as' t) (as'' : List (Metalean.Expr ζ lps.length n))
    (hlen : as''.length = as'.length) : ∃ t'', SatTr E lps b us as'' t'' := by
  cases h with
  | indSat ps is rest hls =>
    obtain ⟨ps'', r₁, rfl, hr₁⟩ := split_ofFn (rest := List.ofFn is ++ rest)
      (by simpa only [List.append_assoc] using hlen)
    obtain ⟨is'', r₂, rfl, -⟩ := split_ofFn hr₁
    exact ⟨_, by simpa only [List.append_assoc] using SatTr.indSat (E := E) ps'' is'' r₂ hls⟩
  | indEta hls hlt => exact ⟨_, .indEta hls (hlen ▸ hlt)⟩
  | @ctorSat _ order ι η s c ls ps fs rest fds recFds hls hfs hord hperm =>
    obtain ⟨ps'', r₁, rfl, hr₁⟩ := split_ofFn (rest := fs ++ rest)
      (by simpa only [List.append_assoc] using hlen)
    let N := (ι.ctors s c).nfields + (ι.ctors s c).nrecFields
    have hN : N ≤ r₁.length := by simp at hr₁; omega
    let G : Fin N → Metalean.Expr ζ lps.length n := fun o =>
      ((r₁.take N)[(order[o.val]?).getD 0]?).getD (.sort .zero)
    have hp : ∀ o : Fin N, ∃ j x, order[o.val]? = some j ∧ (r₁.take N)[j]? = some x ∧
        Fin.append (fun f => G (Fin.castAdd _ f)) (fun r => G (Fin.natAdd _ r)) o = x := by
      intro o
      obtain ⟨j, x, hj, hx, -⟩ := hperm o
      have hjN : j < N := by
        have := (List.getElem?_eq_some_iff.mp hx).1; omega
      refine ⟨j, (r₁.take N)[j]'(by simp; omega), hj, List.getElem?_eq_getElem _, ?_⟩
      rw [Fin.append_castAdd_natAdd (f := G)]
      simp [G, hj, List.getElem?_eq_getElem (show j < (r₁.take N).length by simp; omega)]
    exact ⟨_, by
      simpa only [List.append_assoc, List.take_append_drop] using
        SatTr.ctorSat (E := E) (order := order) ps'' (r₁.take N) (r₁.drop N)
          (fun f => G (Fin.castAdd _ f)) (fun r => G (Fin.natAdd _ r)) hls
          (by simp; omega) hord hp⟩
  | ctorEta hls hlt ht => exact ⟨_, .ctorEta hls (hlen ▸ hlt) ht⟩
  | @recrSat _ _ orders ι η s ls l mo A rest mins hRL hls hmo hw =>
    obtain ⟨A'', r, rfl, -⟩ := split_ofFn hlen
    have hw' t c := TrDet.wrapCase_ok _ _ _ (hw t c)
      (fun p => A'' (Metalean.IndSig.RecrBinder.param (s := s) p).resolve)
      (fun t => A'' (Metalean.IndSig.RecrBinder.motive (s := s) t).resolve)
      (A'' (Metalean.IndSig.RecrBinder.case (s := s) t c).resolve)
    choose mins'' hmins'' using hw'
    exact ⟨_, .recrSat mo A'' r mins'' hRL hls hmo hmins''⟩
  | recrEta mo hRL hls hmo hlt ht => exact ⟨_, .recrEta mo hRL hls hmo (hlen ▸ hlt) ht⟩
  | quotType hu =>
    match as'', hlen with
    | x :: y :: r, _ => exact ⟨_, .quotType (rest := r) (α := x) (r := y) hu⟩
  | quotMk hu =>
    match as'', hlen with
    | x :: y :: z :: r, _ => exact ⟨_, .quotMk (rest := r) (α := x) (r := y) (a := z) hu⟩
  | quotLift hu =>
    match as'', hlen with
    | x₁ :: x₂ :: x₃ :: x₄ :: x₅ :: x₆ :: r, _ =>
      exact ⟨_, .quotLift (rest := r) (α := x₁) (r := x₂) (β := x₃) (f := x₄) (h := x₅) (a := x₆) hu⟩
  | quotInd hu =>
    match as'', hlen with
    | x₁ :: x₂ :: x₃ :: x₄ :: x₅ :: r, _ =>
      exact ⟨_, .quotInd (rest := r) (α := x₁) (r := x₂) (β := x₃) (f := x₄) (a := x₅) hu⟩
  | quotEta hu hlt ht => exact ⟨_, .quotEta hu (hlen ▸ hlt) ht⟩

end

/-- Lifting twice from `s`. -/
theorem liftLooseBVars'_succ (e : Expr) (s d : Nat) :
    (e.liftLooseBVars' s d).liftLooseBVars' s 1 = e.liftLooseBVars' s (d + 1) := by
  induction e generalizing s with
  | bvar i =>
    simp only [Expr.liftLooseBVars']
    congr 1
    split_ifs <;> omega
  | app f a ihf iha => simp [Expr.liftLooseBVars', ihf, iha]
  | lam _ t b _ iht ihb | forallE _ t b _ iht ihb => simp [Expr.liftLooseBVars', iht, ihb]
  | letE _ t v b _ iht ihv ihb => simp [Expr.liftLooseBVars', iht, ihv, ihb]
  | mdata _ e ih | proj _ _ e ih => simp [Expr.liftLooseBVars', ih]
  | _ => rfl

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {lps : List Name}

/-- Congruent, without projection nodes, in every pair of contexts. -/
def Cg (E : Metalean.Env ζ) {ℓ n : Nat} (x y : Metalean.Expr ζ ℓ n) : Prop :=
  ∀ {Γ₁ Γ₂ : Metalean.Ctx ζ ℓ 0 n}, DCong E False Γ₁ Γ₂ x y

theorem Cg.wk {ℓ n : Nat} {x y : Metalean.Expr ζ ℓ n} (h : Cg E x y) : Cg E x.wk y.wk := by
  intro Γ₁ Γ₂
  cases Γ₁ with
  | snoc Γ₁ A₁ =>
    cases Γ₂ with
    | snoc Γ₂ A₂ => exact DCong.wk A₁ A₂ h

/-- Structure projections of congruent majors at the same parameters. -/
theorem projTerm_cg {ι : Metalean.IndSig} {η : Metalean.Head ζ (.inductive ι)}
    {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} (hst : (E.get η).block.IsStructure s c)
    {ℓ : Nat} (ls : Fin ι.nlevels → Metalean.Level ℓ) (f : Fin (ι.ctors s c).nfields) {n : Nat}
    (ps : Fin ι.nparams → Metalean.Expr ζ ℓ n) {maj₁ maj₂ : Metalean.Expr ζ ℓ n}
    (hmaj : Cg E maj₁ maj₂) : Cg E (hst.projTerm η ls ps f maj₁) (hst.projTerm η ls ps f maj₂) := by
  intro Γ₁ Γ₂
  let majG : Metalean.Expr ζ ℓ (n + 1) := .var (Fin.last n)
  let σ (maj : Metalean.Expr ζ ℓ n) : Metalean.Subst ζ ℓ (n + 1) n :=
    Fin.lastCases maj fun v => .var v
  have key (maj) : hst.projTerm η ls ps f maj =
      (hst.projTerm η ls (fun p => (ps p).wk) f majG).subst (σ maj) := by
    rw [Metalean.Inductive.IsStructure.projTerm_subst]
    congr 1
    · funext p
      simp only [σ, Metalean.Expr.wk, Metalean.Expr.wkFrom, Metalean.Expr.rename_subst]
      conv => lhs; rw [← Metalean.Expr.subst_id (ps p)]
      congr 1
      funext v
      simp [Metalean.Subst.precomp, Metalean.Subst.id]
    · simp [majG, σ, Metalean.Expr.subst]
  rw [key maj₁, key maj₂]
  refine DCong.subst _ fun v => ?_
  cases v using Fin.lastCases with
  | last => simpa [σ] using hmaj
  | cast v => simp only [σ, Fin.lastCases_castSucc]; exact .refl

/-- The locals before (`Δ₁`) and after (`Δ₂`) instantiating the Lean bound variable `d` by `a`:
the Metalean terms the others denote are substituted by `σ` up to `Cg`, and `d` denotes a
pre-translation of `a`. -/
def MLCtx.InstA (E : Metalean.Env ζ) (B : Binds ζ) (lps : List Name) {n₁ n₂ : Nat} (a : Expr)
    (d : Nat) (σ : Metalean.Subst ζ lps.length n₁ n₂) (Δ₁ : MLCtx ζ lps.length n₁)
    (Δ₂ : MLCtx ζ lps.length n₂) : Prop :=
  (∀ i t, Δ₁.findB i = some t →
    (i < d → ∃ u, Δ₂.findB i = some u ∧ Cg E (t.subst σ) u) ∧
    (i = d → ∃ u, PreTr E B lps Δ₂ (a.liftLooseBVars' 0 d) u ∧ Cg E (t.subst σ) u) ∧
    (d < i → ∃ u, Δ₂.findB (i - 1) = some u ∧ Cg E (t.subst σ) u)) ∧
  ∀ x t, Δ₁.findF x = some t → ∃ u, Δ₂.findF x = some u ∧ Cg E (t.subst σ) u

/-- Entering a bound variable below every local. -/
theorem MLCtx.Subs.bv {ℓ n : Nat} (Δ : MLCtx ζ ℓ n) :
    MLCtx.Subs 0 1 Metalean.Subst.wk Δ (Δ.pushLam none) := by
  constructor
  · intro i t ht
    simp [MLCtx.pushLam, MLCtx.findB, MLCtx.findB_map_wk, ht, Metalean.Expr.subst_wk]
  · intro x t ht
    simp [MLCtx.pushLam, MLCtx.findF, MLCtx.findF_map_wk, ht, Metalean.Expr.subst_wk]

/-- Entering a `let` below every local. -/
theorem MLCtx.Subs.lt {ℓ n : Nat} (Δ : MLCtx ζ ℓ n) (w : Metalean.Expr ζ ℓ n) :
    MLCtx.Subs 0 1 Metalean.Subst.id Δ ((none, .vlet w) :: Δ) := by
  constructor
  · intro i t ht
    simpa [MLCtx.findB] using ht
  · intro x t ht
    simpa [MLCtx.findF] using ht

theorem MLCtx.InstA.pushLam {n₁ n₂ : Nat} {a : Expr} {d : Nat}
    {σ : Metalean.Subst ζ lps.length n₁ n₂} {Δ₁ : MLCtx ζ lps.length n₁}
    {Δ₂ : MLCtx ζ lps.length n₂} (W : MLCtx.InstA E B lps a d σ Δ₁ Δ₂) :
    MLCtx.InstA E B lps a (d + 1) σ.lift (Δ₁.pushLam none) (Δ₂.pushLam none) := by
  constructor
  · intro i t ht
    cases i with
    | zero =>
      simp only [MLCtx.pushLam, MLCtx.findB, MLDecl.denote, Option.some.injEq] at ht
      subst ht
      refine ⟨fun _ => ⟨_, rfl, ?_⟩, by omega, by omega⟩
      simp only [Metalean.Expr.subst, Metalean.Subst.lift_last]
      exact .refl
    | succ i =>
      simp only [MLCtx.pushLam, MLCtx.findB, MLCtx.findB_map_wk, Option.map_eq_some_iff] at ht
      obtain ⟨u₀, hu₀, rfl⟩ := ht
      obtain ⟨h₁, h₂, h₃⟩ := W.1 i u₀ hu₀
      rw [Metalean.Expr.wk_subst_lift]
      refine ⟨fun hi => ?_, fun hi => ?_, fun hi => ?_⟩
      · obtain ⟨u, hu, hc⟩ := h₁ (by omega)
        exact ⟨u.wk, by simp [MLCtx.pushLam, MLCtx.findB, MLCtx.findB_map_wk, hu], hc.wk⟩
      · obtain ⟨u, hu, hc⟩ := h₂ (by omega)
        refine ⟨u.wk, ?_, hc.wk⟩
        have := hu.subst (MLCtx.Subs.bv Δ₂)
        rwa [liftLooseBVars'_succ, Metalean.Expr.subst_wk] at this
      · obtain ⟨u, hu, hc⟩ := h₃ (by omega)
        refine ⟨u.wk, ?_, hc.wk⟩
        obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        simp only [Nat.add_sub_cancel] at hu
        simp [MLCtx.pushLam, MLCtx.findB, MLCtx.findB_map_wk, hu]
  · intro x t ht
    simp only [MLCtx.pushLam, MLCtx.findF, MLCtx.findF_map_wk, Option.map_eq_some_iff] at ht
    obtain ⟨u₀, hu₀, rfl⟩ := ht
    obtain ⟨u, hu, hc⟩ := W.2 x u₀ hu₀
    rw [Metalean.Expr.wk_subst_lift]
    exact ⟨u.wk, by simp [MLCtx.pushLam, MLCtx.findF, MLCtx.findF_map_wk, hu], hc.wk⟩

theorem MLCtx.InstA.cons {n₁ n₂ : Nat} {a : Expr} {d : Nat}
    {σ : Metalean.Subst ζ lps.length n₁ n₂} {Δ₁ : MLCtx ζ lps.length n₁}
    {Δ₂ : MLCtx ζ lps.length n₂} (W : MLCtx.InstA E B lps a d σ Δ₁ Δ₂)
    {v₁ : Metalean.Expr ζ lps.length n₁} {v₂ : Metalean.Expr ζ lps.length n₂}
    (hv : Cg E (v₁.subst σ) v₂) :
    MLCtx.InstA E B lps a (d + 1) σ ((none, .vlet v₁) :: Δ₁) ((none, .vlet v₂) :: Δ₂) := by
  constructor
  · intro i t ht
    cases i with
    | zero =>
      simp only [MLCtx.findB, MLDecl.denote, Option.some.injEq] at ht
      subst ht
      exact ⟨fun _ => ⟨_, rfl, hv⟩, by omega, by omega⟩
    | succ i =>
      simp only [MLCtx.findB] at ht
      obtain ⟨h₁, h₂, h₃⟩ := W.1 i t ht
      refine ⟨fun hi => ?_, fun hi => ?_, fun hi => ?_⟩
      · obtain ⟨u, hu, hc⟩ := h₁ (by omega)
        exact ⟨u, by simpa [MLCtx.findB] using hu, hc⟩
      · obtain ⟨u, hu, hc⟩ := h₂ (by omega)
        refine ⟨u, ?_, hc⟩
        have := hu.subst (MLCtx.Subs.lt Δ₂ v₂)
        rwa [liftLooseBVars'_succ, Metalean.Expr.subst_id] at this
      · obtain ⟨u, hu, hc⟩ := h₃ (by omega)
        refine ⟨u, ?_, hc⟩
        obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        simpa [MLCtx.findB] using hu
  · intro x t ht
    simpa [MLCtx.findF] using W.2 x t (by simpa [MLCtx.findF] using ht)

end

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {lps : List Name}

/-- Instantiating a bound variable by a term with a pre-translation: the instantiated body has a
pre-translation congruent to the substituted image, up to weak-head reduction at the spines that
saturate. Reference: lean4lean `TrExprS.instN` (`L4 Typing/Inst.lean`). -/
theorem PreTr.instA {n₁ : Nat} {Δ₁ : MLCtx ζ lps.length n₁} {b : Expr}
    {b' : Metalean.Expr ζ lps.length n₁} (h : PreTr E B lps Δ₁ b b') :
    ∀ {n₂ : Nat} {a : Expr} {d : Nat} {σ : Metalean.Subst ζ lps.length n₁ n₂}
      {Δ₂ : MLCtx ζ lps.length n₂}, MLCtx.InstA E B lps a d σ Δ₁ Δ₂ →
      ∃ t, PreTr E B lps Δ₂ (b.instantiate1' a d) t ∧ Cg E (b'.subst σ) t := by
  induction h with
  | bvar hb =>
    intro _ a d σ Δ₂ W
    obtain ⟨h₁, h₂, h₃⟩ := W.1 _ _ hb
    simp only [Expr.instantiate1']
    split_ifs with hlt heq
    · obtain ⟨u, hu, hc⟩ := h₁ hlt; exact ⟨u, .bvar hu, hc⟩
    · obtain ⟨u, hu, hc⟩ := h₂ heq; exact ⟨u, hu, hc⟩
    · obtain ⟨u, hu, hc⟩ := h₃ (by omega); exact ⟨u, .bvar hu, hc⟩
  | fvar hf =>
    intro _ _ _ _ _ W
    obtain ⟨u, hu, hc⟩ := W.2 _ _ hf
    exact ⟨u, .fvar hu, hc⟩
  | sort hl => intro _ _ _ _ _ _; exact ⟨_, .sort hl, fun {_ _} => .refl⟩
  | const h₁ h₂ => intro _ _ _ _ _ _; exact ⟨_, .const h₁ h₂, fun {_ _} => .refl⟩
  | @special c us _ _ as as' _ _ hb hs hlen _ hsat ih =>
    intro _ a d σ Δ₂ W
    rw [mkAppN_toArray, instantiate1'_foldl, ← mkAppN_toArray]
    have hex : ∀ i : Fin as'.length, ∃ t, PreTr E B lps Δ₂
        ((as[i.val]'(by omega)).instantiate1' a d) t ∧ Cg E ((as'[i.val]).subst σ) t :=
      fun i => ih i.val _ _ (List.getElem?_eq_getElem _) (List.getElem?_eq_getElem _) W
    choose f hf using hex
    obtain ⟨t'', hsat''⟩ := InstPre.SatTr.replace (hsat.subst σ) (List.ofFn f) (by simp)
    refine ⟨t'', .special hb hs (by simp [hlen]) (fun i x x' hx hx' => ?_) hsat'', fun {Γ₁ Γ₂} => ?_⟩
    · simp only [List.getElem?_map, Option.map_eq_some_iff] at hx
      obtain ⟨x₀, hx₀, rfl⟩ := hx
      obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hx₀
      rw [List.getElem?_ofFn] at hx'
      have hi' : i < as'.length := hlen ▸ hi
      simp only [hi', dite_true, Option.some.injEq] at hx'
      subst hx'
      exact (hf ⟨i, hi'⟩).1
    · refine SatTr.dcong (hsat.subst σ) hsat'' (by simp) fun i x y hx hy => ?_
      simp only [List.getElem?_map, Option.map_eq_some_iff] at hx
      obtain ⟨x₀, hx₀, rfl⟩ := hx
      obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hx₀
      rw [List.getElem?_ofFn] at hy
      simp only [hi, dite_true, Option.some.injEq] at hy
      subst hy
      exact (hf ⟨i, hi⟩).2
  | @app fn _ _ _ _ _ hns _ _ ihf ihx =>
    intro _ a d σ Δ₂ W
    obtain ⟨tf, hf', cf⟩ := ihf W
    obtain ⟨tx, hx', cx⟩ := ihx W
    simp only [Expr.instantiate1']
    by_cases hsp : SpecialHead B (fn.instantiate1' a d)
    · obtain ⟨t, ht, hred⟩ := PreTr.app_special hsp hf' hx'
      exact ⟨t, ht, fun {_ _} => .red not_false (.app cf cx) hred⟩
    · exact ⟨_, .app hsp hf' hx', fun {_ _} => .app cf cx⟩
  | lam _ _ ihA ihb =>
    intro _ a d σ Δ₂ W
    obtain ⟨tA, hA, cA⟩ := ihA W
    obtain ⟨tb, hb, cb⟩ := ihb W.pushLam
    exact ⟨_, .lam hA hb, fun {_ _} => .lam cA cb⟩
  | forallE _ _ ihA ihb =>
    intro _ a d σ Δ₂ W
    obtain ⟨tA, hA, cA⟩ := ihA W
    obtain ⟨tb, hb, cb⟩ := ihb W.pushLam
    exact ⟨_, .forallE hA hb, fun {_ _} => .forallE cA cb⟩
  | letE _ _ _ ihT ihv ihb =>
    intro _ a d σ Δ₂ W
    obtain ⟨tT, hT, cT⟩ := ihT W
    obtain ⟨tv, hv, cv⟩ := ihv W
    obtain ⟨tb, hb, cb⟩ := ihb (W.cons cv)
    refine ⟨_, .letE hT hv hb, fun {Γ₁ Γ₂} => ?_⟩
    simp only [Metalean.Expr.subst, Metalean.Expr.wk_subst_lift]
    refine .letE cT cv ?_
    rw [Metalean.Expr.inst_wk, Metalean.Expr.inst_wk]
    exact cb
  | mdata _ ih =>
    intro _ a d σ Δ₂ W
    obtain ⟨te, he, ce⟩ := ih W
    exact ⟨te, .mdata he, ce⟩
  | lit hB h₀ h₁ =>
    intro _ _ _ _ _ _
    refine ⟨_, .lit hB h₀ h₁, fun {_ _} => ?_⟩
    rw [natLitM_subst]
    exact .refl
  | projStruct hst hi hS _ ih =>
    intro _ a d σ Δ₂ W
    obtain ⟨te, he, ce⟩ := ih W
    rw [Metalean.Inductive.IsStructure.projTerm_subst]
    exact ⟨_, .projStruct hst hi hS he, projTerm_cg hst _ _ _ ce⟩
  | projProof hi hS hs hc hr hf hns _ ih =>
    intro _ a d σ Δ₂ W
    obtain ⟨te, he, ce⟩ := ih W
    rw [projProofTerm_subst]
    exact ⟨_, .projProof hi hS hs hc hr hf hns he,
      fun {_ _} => TrDet.projProofTerm_dcong _ _ _ _ _ _ (fun _ => .refl) ce⟩

end

section
open Metalean
variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat}

/-- `Γ` embeds in `R` by the injective renaming `ρ`, which preserves the types of variables. -/
def Thin {n m : Nat} (Γ : Ctx ζ ℓ 0 n) (R : Ctx ζ ℓ 0 m) (ρ : Ren n m) : Prop :=
  Function.Injective ρ ∧ ∀ v, R.get (ρ v) = (Γ.get v).rename ρ

theorem Thin.id {n : Nat} (Γ : Ctx ζ ℓ 0 n) : Thin Γ Γ Ren.id :=
  ⟨fun _ _ h => h, fun v => by rw [Expr.rename_id]; rfl⟩

theorem Thin.comp {n m k : Nat} {Γ : Ctx ζ ℓ 0 n} {R : Ctx ζ ℓ 0 m} {R' : Ctx ζ ℓ 0 k}
    {ρ : Ren n m} {ρ' : Ren m k} (h : Thin Γ R ρ) (h' : Thin R R' ρ') :
    Thin Γ R' (ρ'.comp ρ) :=
  ⟨fun _ _ hv => h.1 (h'.1 hv), fun v => by
    rw [Ren.comp, h'.2, h.2, Expr.rename_rename]⟩

theorem wk_rename_lift {n m : Nat} (ρ : Ren n m) (e : Expr ζ ℓ n) :
    e.wk.rename ρ.lift = (e.rename ρ).wk := by
  rw [Expr.wk, Expr.wkFrom, Expr.rename_rename, Expr.wk, Expr.wkFrom, Expr.rename_rename]
  congr 1
  funext v
  simp only [Ren.comp]
  rw [Ren.wkFrom_of_lt v v.isLt, Ren.wkFrom_of_lt _ (ρ v).isLt]
  exact Ren.lift_castSucc ρ v

theorem Thin.lift {n m : Nat} {Γ : Ctx ζ ℓ 0 n} {R : Ctx ζ ℓ 0 m} {ρ : Ren n m}
    (h : Thin Γ R ρ) (A : Expr ζ ℓ n) : Thin (Γ.snoc A) (R.snoc (A.rename ρ)) ρ.lift := by
  refine ⟨fun v w hvw => ?_, fun v => ?_⟩
  · cases v using Fin.lastCases <;> cases w using Fin.lastCases <;>
      simp only [Ren.lift_castSucc, Ren.lift_last] at hvw
    · rfl
    · exact absurd hvw (Fin.castSucc_ne_last _).symm
    · exact absurd hvw (Fin.castSucc_ne_last _)
    · rw [h.1 (Fin.castSucc_injective _ hvw)]
  · cases v using Fin.lastCases with
    | last => rw [Ren.lift_last, Ctx.get_last, Ctx.get_last, wk_rename_lift]
    | cast v => rw [Ren.lift_castSucc, Ctx.get_castSucc, Ctx.get_castSucc, wk_rename_lift, h.2]

/-- An entry of `R ++ Θ` that comes from `R`. -/
theorem get_append_castLE {m : Nat} (R : Ctx ζ ℓ 0 m) :
    ∀ {m' : Nat} (Θ : Ctx ζ ℓ m m') (h : m ≤ m') (v : Var m),
      (R ++ Θ).get (v.castLE h) = (R.get v).rename (Fin.castLE h)
  | _, .nil, h, v => by
    rw [Tele.append_nil]
    have : (Fin.castLE h : Ren m m) = Ren.id := funext fun _ => rfl
    rw [this, Expr.rename_id]; rfl
  | _, .snoc (b := k) Θ A, h, v => by
    have hk : m ≤ k := Tele.le Θ
    rw [Tele.append_snoc, Ctx.get_snoc _ _ _ (by simp; omega)]
    have e : (v.castLE h).castLT (by simp; omega) = v.castLE hk := Fin.ext rfl
    rw [e, get_append_castLE R Θ hk v, Expr.wk, Expr.wkFrom, Expr.rename_rename]
    congr 1
    funext w
    simp only [Ren.comp]
    rw [Ren.wkFrom_of_lt _ (by simp; omega)]
    rfl

theorem Thin.append {m m' : Nat} (R : Ctx ζ ℓ 0 m) (Θ : Ctx ζ ℓ m m') :
    Thin R (R ++ Θ) (Fin.castLE (Tele.le Θ)) :=
  ⟨Fin.castLE_injective _, fun v => get_append_castLE R Θ _ v⟩

/-- The head and the arguments of a typed application spine are typed. -/
theorem appList_inv {n : Nat} {R : Ctx ζ ℓ 0 n} :
    ∀ {f : Expr ζ ℓ n} {as : List (Expr ζ ℓ n)} {T : Expr ζ ℓ n}, E[R] ⊢ f.appList as : T →
      (∃ F, E[R] ⊢ f : F) ∧ ∀ a ∈ as, ∃ A, E[R] ⊢ a : A
  | _, [], _, h => ⟨⟨_, h⟩, by simp⟩
  | _, a :: as, _, h => by
    obtain ⟨⟨F, hf⟩, has⟩ := appList_inv (as := as) h
    obtain ⟨A, B', hf', ha, -⟩ := hf.app_inv
    refine ⟨⟨_, hf'⟩, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨_, ha⟩
    · exact has x hx

/-- The head of a typed `apps` spine is typed. -/
theorem apps_inv {n : Nat} {R : Ctx ζ ℓ 0 n} {f : Expr ζ ℓ n} :
    ∀ {k : Nat} {args : Fin k → Expr ζ ℓ n} {T : Expr ζ ℓ n}, E[R] ⊢ f.apps args : T →
      ∃ F, E[R] ⊢ f : F
  | 0, _, _, h => ⟨_, by simpa using h⟩
  | k + 1, args, _, h => by
    rw [Expr.apps, Fin.foldl_succ_last] at h
    obtain ⟨_, _, hf, -, -⟩ := h.app_inv
    exact apps_inv (k := k) (args := fun i => args i.castSucc) hf

/-- A typed λ-telescope: the extended context is well formed and the body is typed. -/
theorem ctxLam_inv {m : Nat} {R : Ctx ζ ℓ 0 m} (hR : E[R] ⊢ ok) :
    ∀ {m' : Nat} (Θ : Ctx ζ ℓ m m') {body : Expr ζ ℓ m'} {T : Expr ζ ℓ m}, E[R] ⊢ Θ.lam body : T →
      E[R ++ Θ] ⊢ ok ∧ ∃ T', E[R ++ Θ] ⊢ body : T'
  | _, .nil, _, _, h => ⟨hR, _, h⟩
  | _, .snoc Θ A, body, _, h => by
    obtain ⟨hΘ, _, hl⟩ := ctxLam_inv hR Θ (body := .lam A body) h
    obtain ⟨B, hb, hT⟩ := hl.lam_inv hΘ
    obtain ⟨_, hfa⟩ := hT.right
    obtain ⟨_, _, hA, -, -⟩ := hfa.forallE_ty_inv
    exact ⟨.snoc hΘ ⟨_, hA⟩, _, hb⟩

end

section
open Metalean
variable {ζ : Sigs} {E : Env ζ} {lps : List Name}

/-- The shape of a wrapped minor premise: the minor itself, or the λ-telescope of the case
telescope over the weakened minor applied to the field and hypothesis variables. -/
theorem wrapCase_shape {ι : IndSig} {I : Inductive ζ ι} {η : Head ζ (.inductive ι)} {ℓ n : Nat}
    {ls : Fin ι.nlevels → Level ℓ} {ps : Fin ι.nparams → Expr ζ ℓ n}
    {ms : Fin ι.nsorts → Expr ζ ℓ n} {t : Fin ι.nsorts} {c : Fin (ι.nctors t)} {mo : List Nat}
    {minor w : Expr ζ ℓ n} (hw : Frontend.wrapCase I η ls ps ms t c mo minor = .ok w) :
    w = minor ∨ ∃ fv : Fin ((ι.ctors t c).nfields + (ι.ctors t c).nrecFields +
        (ι.ctors t c).nrecFields) → Expr ζ ℓ (n + (ι.ctors t c).nfields +
          (ι.ctors t c).nrecFields + (ι.ctors t c).nrecFields),
      w = Ctx.lam ((((minor.wkN (ι.ctors t c).nfields).wkN (ι.ctors t c).nrecFields).wkN
        (ι.ctors t c).nrecFields).apps fv) (I.caseTele η ls ps ms t c) := by
  unfold Frontend.wrapCase at hw
  dsimp only at hw
  by_cases hid : Frontend.isIdentityOrder mo
      ((ι.ctors t c).nfields + (ι.ctors t c).nrecFields) = true
  · rw [ite_eq_left hid] at hw; cases hw; exact .inl rfl
  · rw [ite_eq_right hid] at hw
    rcases hπ : Frontend.orderMaps? mo
        ((ι.ctors t c).nfields + (ι.ctors t c).nrecFields) with _ | ⟨π, snd⟩
    · rw [hπ] at hw; cases hw
    · rw [hπ] at hw
      dsimp only at hw
      split at hw <;> cases hw
      exact .inr ⟨_, rfl⟩

/-- Every argument of a saturating spine whose image is typed is typed in a thinning of the
context: in the context itself, or, for a minor premise that `wrapCase` wraps, under the case
telescope. A constructor's field order must be a permutation, so that no field is dropped. -/
theorem SatTr.args_typed {n : Nat} {b : MBinding ζ} {us : List Level}
    {as : List (Expr ζ lps.length n)} {t : Expr ζ lps.length n} (h : SatTr E lps b us as t)
    (hord : ∀ {ι : IndSig} (η : Head ζ (.inductive ι)) (s : Fin ι.nsorts) (k : Fin (ι.nctors s))
      (o : List Nat), b = .ctor η s k o →
      MetaOrderOK o (ι.ctors s k).nfields (ι.ctors s k).nrecFields)
    {R : Ctx ζ lps.length 0 n} (hR : E[R] ⊢ ok) (ht : ∃ T, E[R] ⊢ t : T) :
    ∀ a ∈ as, ∃ (m' : Nat) (R' : Ctx ζ lps.length 0 m') (ρ' : Ren n m'), Thin R R' ρ' ∧
      E[R'] ⊢ ok ∧ ∃ T, E[R'] ⊢ a.rename ρ' : T := by
  have here : ∀ a : Expr ζ lps.length n, (∃ T, E[R] ⊢ a : T) →
      ∃ (m' : Nat) (R' : Ctx ζ lps.length 0 m') (ρ' : Ren n m'), Thin R R' ρ' ∧
        E[R'] ⊢ ok ∧ ∃ T, E[R'] ⊢ a.rename ρ' : T :=
    fun a ⟨T, ha⟩ => ⟨n, R, Ren.id, Thin.id R, hR, T, by rw [Expr.rename_id]; exact ha⟩
  obtain ⟨T, ht⟩ := ht
  cases h with
  | indSat ps is rest hls =>
    obtain ⟨⟨_, hi⟩, hrest⟩ := appList_inv ht
    obtain ⟨_, _, hps, his, -⟩ := hi.ind_inv
    intro a ha
    simp only [List.mem_append, List.mem_ofFn] at ha
    rcases ha with (⟨p, rfl⟩ | ⟨i, rfl⟩) | ha
    · exact here _ ⟨_, (hps p).right⟩
    · exact here _ ⟨_, (his i).right⟩
    · exact here _ (hrest a ha)
  | indEta | ctorEta | recrEta | quotEta =>
    intro a ha
    exact here _ ((appList_inv ht).2 a ha)
  | @ctorSat _ order ι η s c ls ps fs rest fds recFds hls hfs hord' hperm =>
    obtain ⟨⟨_, hc⟩, hrest⟩ := appList_inv ht
    obtain ⟨_, _, _, hps, hfds, hrf, -, -⟩ := hc.ctor_inv
    obtain ⟨-, -, -, -, -, -, -, hpm⟩ := hord η s c order rfl
    intro a ha
    simp only [List.mem_append, List.mem_ofFn] at ha
    rcases ha with (⟨p, rfl⟩ | ha) | ha
    · exact here _ ⟨_, (hps p).right⟩
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
      have hjr : j ∈ order := hpm.symm.subset (List.mem_range.mpr (hfs ▸ hj))
      obtain ⟨o, ho, hoj⟩ := List.getElem_of_mem hjr
      obtain ⟨j', x, hj', hx, hfx⟩ := hperm ⟨o, hord' ▸ ho⟩
      rw [List.getElem?_eq_getElem ho, hoj, Option.some.injEq] at hj'
      subst hj'
      rw [List.getElem?_eq_getElem hj, Option.some.injEq] at hx
      subst hx
      rw [← hfx]
      refine Fin.addCases (fun f => ?_) (fun r => ?_) (⟨o, hord' ▸ ho⟩ :
        Fin ((ι.ctors s c).nfields + (ι.ctors s c).nrecFields))
      · rw [Fin.append_left]; exact here _ ⟨_, (hfds f).right⟩
      · rw [Fin.append_right]; exact here _ ⟨_, (hrf r).right⟩
    · exact here _ (hrest a ha)
  | @recrSat _ _ orders ι η s ls l mo A rest mins hRL hls hmo hw =>
    obtain ⟨⟨_, hr⟩, hrest⟩ := appList_inv ht
    obtain ⟨_, _, _, _, _, -, hps, hms, hmins, his, hmaj, -, -⟩ := hr.recr_inv
    intro a ha
    simp only [List.mem_append, List.mem_ofFn] at ha
    rcases ha with ⟨i, rfl⟩ | ha
    · obtain ⟨bd, rfl⟩ := IndSig.RecrBinder.resolve_surjective i
      cases bd with
      | param p => exact here _ ⟨_, (hps p).right⟩
      | motive t => exact here _ ⟨_, (hms t).right⟩
      | index i => exact here _ ⟨_, (his i).right⟩
      | major => exact here _ ⟨_, hmaj.right⟩
      | case t c =>
        have hmin := (hmins t c).right
        have hws := wrapCase_shape (hw t c)
        rcases hws with heq | ⟨fv, heq⟩
        · rw [heq] at hmin; exact here _ ⟨_, hmin⟩
        · rw [heq] at hmin
          obtain ⟨hΘ, _, hbody⟩ := ctxLam_inv hR _ hmin
          obtain ⟨F, hm⟩ := apps_inv hbody
          refine ⟨_, _, _, Thin.append R _, hΘ, F, ?_⟩
          have hre : ∀ (x : Expr ζ lps.length n) (h : n ≤ n + (ι.ctors t c).nfields +
              (ι.ctors t c).nrecFields + (ι.ctors t c).nrecFields),
              x.rename (Fin.castLE h) = ((x.wkN (ι.ctors t c).nfields).wkN
                (ι.ctors t c).nrecFields).wkN (ι.ctors t c).nrecFields := by
            intro x h
            simp only [Expr.wkN_eq_rename, Expr.rename_rename]
            rfl
          rw [hre]
          exact hm
    · exact here _ (hrest a ha)
  | quotType hu =>
    obtain ⟨⟨_, hq⟩, hrest⟩ := appList_inv ht
    obtain ⟨hα, hr⟩ := hq.quot_formation_inv
    intro a ha
    simp only [List.cons_append, List.nil_append, List.mem_cons] at ha
    rcases ha with rfl | rfl | ha
    · exact here _ ⟨_, hα⟩
    · exact here _ ⟨_, hr⟩
    · exact here _ (hrest a ha)
  | quotMk hu =>
    obtain ⟨⟨_, hq⟩, hrest⟩ := appList_inv ht
    obtain ⟨_, _, _, hα, hr, hx, -⟩ := hq.quotMk_prem
    intro a ha
    simp only [List.cons_append, List.nil_append, List.mem_cons] at ha
    rcases ha with rfl | rfl | rfl | ha
    · exact here _ ⟨_, hα.right⟩
    · exact here _ ⟨_, hr.right⟩
    · exact here _ ⟨_, hx.right⟩
    · exact here _ (hrest a ha)
  | quotLift hu =>
    obtain ⟨⟨_, hq⟩, hrest⟩ := appList_inv ht
    obtain ⟨_, _, _, _, _, _, hα, hr, hβ, hf, hh, hx, -⟩ := hq.quotLift_prem
    intro a ha
    simp only [List.cons_append, List.nil_append, List.mem_cons] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | ha
    · exact here _ ⟨_, hα.right⟩
    · exact here _ ⟨_, hr.right⟩
    · exact here _ ⟨_, hβ.right⟩
    · exact here _ ⟨_, hf.right⟩
    · exact here _ ⟨_, hh.right⟩
    · exact here _ ⟨_, hx.right⟩
    · exact here _ (hrest a ha)
  | quotInd hu =>
    obtain ⟨⟨_, hq⟩, hrest⟩ := appList_inv ht
    obtain ⟨_, _, _, _, _, hα, hr, hβ, hf, hx, -, -⟩ := hq.quotInd_prem
    intro a ha
    simp only [List.cons_append, List.nil_append, List.mem_cons] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | ha
    · exact here _ ⟨_, hα.right⟩
    · exact here _ ⟨_, hr.right⟩
    · exact here _ ⟨_, hβ.right⟩
    · exact here _ ⟨_, hf.right⟩
    · exact here _ ⟨_, hx.right⟩
    · exact here _ (hrest a ha)

end

section
open Metalean
variable {ζ : Sigs} {E : Env ζ} {B : Binds ζ} {lps : List Name}

/-- The substitution of a renaming, lifted, is the substitution of the lifted renaming. -/
theorem vars_lift {n m : Nat} (ρ : Ren n m) :
    Subst.lift (fun v => (Expr.var (ρ v) : Expr ζ lps.length m)) = fun v => .var (ρ.lift v) := by
  funext v
  cases v using Fin.lastCases with
  | last => simp
  | cast v => simp [Expr.wk, Expr.wkFrom]

/-- A pre-translation whose image is typed in a thinning of its context is a translation: the
typing premise of each projection holds in the context where the Metalean term places its major,
obtained by inverting the typing of the image. -/
theorem PreTr.recover
    (hord : ∀ c {ι : IndSig} (η : Head ζ (.inductive ι)) (s : Fin ι.nsorts)
      (k : Fin (ι.nctors s)) (o : List Nat), B c = some (.ctor η s k o) →
      MetaOrderOK o (ι.ctors s k).nfields (ι.ctors s k).nrecFields)
    {n : Nat} {Δ : MLCtx ζ lps.length n} {e : Lean.Expr} {t : Expr ζ lps.length n}
    (h : PreTr E B lps Δ e t) :
    ∀ {Γ : Ctx ζ lps.length 0 n} {m : Nat} {R : Ctx ζ lps.length 0 m} {ρ : Ren n m},
      Thin Γ R ρ → E[R] ⊢ ok → (∃ T, E[R] ⊢ t.rename ρ : T) → TrM E B lps Γ Δ e t := by
  induction h with
  | bvar h => intros; exact .bvar h
  | fvar h => intros; exact .fvar h
  | sort h => intros; exact .sort h
  | const h₁ h₂ => intros; exact .const h₁ h₂
  | lit h h₀ h₁ => intros; exact .lit h h₀ h₁
  | @special c us _ _ as as' b _ hb hs hlen _ hsat ih =>
    intro Γ m R ρ hth hR ht
    refine .special hb hs hlen (fun i a a' ha ha' => ?_) hsat
    have hsat' := hsat.subst (fun v => .var (ρ v))
    simp only [Expr.subst_vars] at hsat'
    have hmem : a'.rename ρ ∈ as'.map (·.rename ρ) :=
      List.mem_map.mpr ⟨a', List.mem_of_getElem? ha', rfl⟩
    obtain ⟨m', R', ρ', hth', hR', T', ht'⟩ := SatTr.args_typed hsat'
      (fun η s k o hbo => hord c η s k o (hbo ▸ hb)) hR (by simpa using ht) _ hmem
    rw [Expr.rename_rename] at ht'
    exact ih i a a' ha ha' (hth.comp hth') hR' ⟨_, ht'⟩
  | app hns _ _ ihf iha =>
    intro Γ m R ρ hth hR ⟨T, ht⟩
    rw [← Expr.subst_vars] at ht
    obtain ⟨_, _, hf, ha, -⟩ := ht.app_inv
    simp only [Expr.subst_vars] at hf ha
    exact .app hns (ihf hth hR ⟨_, hf⟩) (iha hth hR ⟨_, ha⟩)
  | lam _ _ ihA ihb =>
    intro Γ m R ρ hth hR ⟨T, ht⟩
    rw [← Expr.subst_vars] at ht
    simp only [Expr.subst, vars_lift, Expr.subst_vars] at ht
    obtain ⟨_, hb, hT⟩ := ht.lam_inv hR
    obtain ⟨_, hfa⟩ := hT.right
    obtain ⟨_, _, hA, -, -⟩ := hfa.forallE_ty_inv
    exact .lam (ihA hth hR ⟨_, hA⟩) (ihb (hth.lift _) (.snoc hR ⟨_, hA⟩) ⟨_, hb⟩)
  | forallE _ _ ihA ihb =>
    intro Γ m R ρ hth hR ⟨T, ht⟩
    rw [← Expr.subst_vars] at ht
    simp only [Expr.subst, vars_lift, Expr.subst_vars] at ht
    obtain ⟨_, _, hA, hB, -⟩ := ht.forallE_ty_inv
    exact .forallE (ihA hth hR ⟨_, hA⟩) (ihb (hth.lift _) (.snoc hR ⟨_, hA⟩) ⟨_, hB⟩)
  | letE _ _ _ ihT ihv ihb =>
    intro Γ m R ρ hth hR ⟨T, ht⟩
    rw [← Expr.subst_vars] at ht
    simp only [Expr.subst, vars_lift, Expr.subst_vars] at ht
    obtain ⟨_, ⟨_, hA⟩, hv, hb, -⟩ := ht.letE_inv hR
    rw [wk_rename_lift, Expr.inst_wk] at hb
    exact .letE (ihT hth hR ⟨_, hA⟩) (ihv hth hR ⟨_, hv⟩) (ihb hth hR ⟨_, hb⟩)
  | mdata _ ih => intro Γ m R ρ hth hR ht; exact .mdata (ih hth hR ht)
  | projStruct hst hi hS _ ih =>
    intro Γ m R ρ hth hR ⟨T, ht⟩
    rw [← Expr.subst_vars, Inductive.IsStructure.projTerm_subst,
      Inductive.IsStructure.projTerm_eq_recr] at ht
    have hmaj := recr_major ht
    simp only [Expr.subst_vars] at hmaj
    refine .projStruct (is := hst.indices) hst hi hS (ih hth hR ⟨_, hmaj⟩)
      ⟨m, R, ρ, hth.1, hth.2, ?_⟩
    rw [← Expr.subst_vars, ← Expr.subst_vars]
    simp only [Expr.subst, Expr.subst_vars]
    rwa [hst.indices_eq (fun i => (hst.indices i : Expr ζ lps.length _).rename ρ)]
  | projProof hi hS hs hc hr hf hns _ ih =>
    intro Γ m R ρ hth hR ⟨T, ht⟩
    rw [← Expr.subst_vars, projProofTerm_subst, projProofTerm] at ht
    have hmaj := recr_major ht
    simp only [Expr.subst_vars] at hmaj
    refine .projProof (is := fun i => absurd i.isLt (by omega)) hi hS hs hc hr hf hns
      (ih hth hR ⟨_, hmaj⟩) ⟨m, R, ρ, hth.1, hth.2, ?_⟩
    rw [← Expr.subst_vars, ← Expr.subst_vars]
    simp only [Expr.subst, Expr.subst_vars]
    convert hmaj using 2
    funext i
    exact absurd i.isLt (by omega)

end

end InstPre

section
open Metalean InstPre
variable {ζ : Sigs} {E : Env ζ} {B : Binds ζ} {lps : List Name}

/-- Substitution of a typed term for the innermost bound variable, up to definitional equality:
the instantiated body has a translation, definitionally equal to the substituted image (a
substituted head that the translator saturates gives the β-reduct of the η-term). Every
constructor's field order in the table is a permutation (`MetaOrderOK`, as `ProgEnv` makes it).
Reference: `Defeq.substitution` (`ML Typing/Substitution.lean:182`), lean4lean `TrExprS.inst`
(`L4 Typing/Inst.lean`). -/
theorem TrM.inst (hE : EnvWF E) {n : Nat} {Γ : Ctx ζ lps.length 0 n}
    {Δ : MLCtx ζ lps.length n} (hΓ : E[Γ] ⊢ ok)
    (hord : ∀ c {ι : IndSig} (η : Head ζ (.inductive ι)) (s : Fin ι.nsorts)
      (k : Fin (ι.nctors s)) (o : List Nat), B c = some (.ctor η s k o) →
      MetaOrderOK o (ι.ctors s k).nfields (ι.ctors s k).nrecFields)
    {A : Expr ζ lps.length n} {T : Expr ζ lps.length (n + 1)} {b a : Lean.Expr}
    {b' : Expr ζ lps.length (n + 1)} {a' : Expr ζ lps.length n}
    (hb : TrM E B lps (Γ.snoc A) (Δ.pushLam none) b b') (ha : TrM E B lps Γ Δ a a')
    (hA : E[Γ] ⊢ a' : A) (hbT : E[Γ.snoc A] ⊢ b' : T) :
    ∃ t, TrM E B lps Γ Δ (b.instantiate1' a) t ∧ E[Γ] ⊢ t ≡ b'.inst a' : T.inst a' := by
  have W : MLCtx.InstA E B lps a 0 (Subst.id.extend a') (Δ.pushLam none) Δ := by
    constructor
    · intro i t ht
      cases i with
      | zero =>
        simp only [MLCtx.pushLam, MLCtx.findB, MLDecl.denote, Option.some.injEq] at ht
        subst ht
        refine ⟨by omega, fun _ => ⟨a', ?_, ?_⟩, by omega⟩
        · rw [liftLooseBVars'_zero]; exact PreTr.ofTrM ha
        · simp only [Expr.subst, Subst.extend_last]; exact fun {_ _} => .refl
      | succ i =>
        simp only [MLCtx.pushLam, MLCtx.findB, MLCtx.findB_map_wk, Option.map_eq_some_iff] at ht
        obtain ⟨u, hu, rfl⟩ := ht
        refine ⟨by omega, by omega, fun _ => ⟨u, by simpa using hu, ?_⟩⟩
        rw [Expr.wk_subst_extend, Expr.subst_id]
        exact fun {_ _} => .refl
    · intro x t ht
      simp only [MLCtx.pushLam, MLCtx.findF, MLCtx.findF_map_wk, Option.map_eq_some_iff] at ht
      obtain ⟨u, hu, rfl⟩ := ht
      refine ⟨u, hu, ?_⟩
      rw [Expr.wk_subst_extend, Expr.subst_id]
      exact fun {_ _} => .refl
  obtain ⟨t, ht, hc⟩ := (PreTr.ofTrM hb).instA W
  have hty : E[Γ] ⊢ b'.inst a' : T.inst a' := (Defeq.inst_congr hbT hA).left
  have hd := DCong.defeq hE not_false (hc (Γ₁ := Γ) (Γ₂ := Γ)) hΓ (DCong.CtxConv.refl hΓ) hty
  exact ⟨t, PreTr.recover hord ht (Thin.id Γ) hΓ ⟨_, by rw [Expr.rename_id]; exact hd.right⟩,
    hd.symm⟩

/-- A `let` body translates as its instantiation by the value (the translator inlines lets), up
to definitional equality. Reference: `WHRed.zeta` (`ML Syntax/Reduction.lean`), lean4lean
`TrExprS.inst` (`L4 Typing/Inst.lean`). -/
theorem TrM.inst_let (hE : EnvWF E) {n : Nat} {Γ : Ctx ζ lps.length 0 n}
    {Δ : MLCtx ζ lps.length n} (hΓ : E[Γ] ⊢ ok)
    (hord : ∀ c {ι : IndSig} (η : Head ζ (.inductive ι)) (s : Fin ι.nsorts)
      (k : Fin (ι.nctors s)) (o : List Nat), B c = some (.ctor η s k o) →
      MetaOrderOK o (ι.ctors s k).nfields (ι.ctors s k).nrecFields)
    {T : Expr ζ lps.length n} {b v : Lean.Expr} {b' v' : Expr ζ lps.length n}
    (hb : TrM E B lps Γ ((none, .vlet v') :: Δ) b b') (hv : TrM E B lps Γ Δ v v')
    (hbT : E[Γ] ⊢ b' : T) :
    ∃ t, TrM E B lps Γ Δ (b.instantiate1' v) t ∧ E[Γ] ⊢ t ≡ b' : T := by
  have W : MLCtx.InstA E B lps v 0 Subst.id ((none, .vlet v') :: Δ) Δ := by
    constructor
    · intro i t ht
      cases i with
      | zero =>
        simp only [MLCtx.findB, MLDecl.denote, Option.some.injEq] at ht
        subst ht
        refine ⟨by omega, fun _ => ⟨v', ?_, ?_⟩, by omega⟩
        · rw [liftLooseBVars'_zero]; exact PreTr.ofTrM hv
        · rw [Expr.subst_id]; exact fun {_ _} => .refl
      | succ i =>
        simp only [MLCtx.findB] at ht
        refine ⟨by omega, by omega, fun _ => ⟨t, by simpa using ht, ?_⟩⟩
        rw [Expr.subst_id]
        exact fun {_ _} => .refl
    · intro x t ht
      refine ⟨t, by simpa [MLCtx.findF] using ht, ?_⟩
      rw [Expr.subst_id]
      exact fun {_ _} => .refl
  obtain ⟨t, ht, hc⟩ := (PreTr.ofTrM hb).instA W
  rw [Expr.subst_id] at hc
  have hd := DCong.defeq hE not_false (hc (Γ₁ := Γ) (Γ₂ := Γ)) hΓ (DCong.CtxConv.refl hΓ) hbT
  exact ⟨t, PreTr.recover hord ht (Thin.id Γ) hΓ ⟨_, by rw [Expr.rename_id]; exact hd.right⟩,
    hd.symm⟩

end

end EraseProof
