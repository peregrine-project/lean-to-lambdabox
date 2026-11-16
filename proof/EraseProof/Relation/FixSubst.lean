import EraseProof.Relation.Abstract
import EraseProof.Bridge.Weak

/-!
# Substituting a fixpoint for its fix variable

The eraser emits a definition erased through its compiled pre-definition as a λ□ fixpoint whose
body abstracts the fix variable `x` (`Erases.constFix`, `ErasesDecl`), and λ□ unfolds the fixpoint
by substituting the fixpoint for the abstracted variable (`eval_fix`, `cunfoldFix`).
`Erases.fixSubst`: replacing `x` (as `toBvar x k`, then `csubst F k`) by a closed λ□ term `F` that
the constants bound to `x`'s Metalean constant erase to keeps the erasure, under the locals without
`x`. The induction follows `AbsFV.Erases.absN`; the translations inside the relation move to the
locals without `x` with `TrM.dropF`. Reference: `erases_subst0` (`MR E/ESubstitution.v:612`), for
the substitution of the unfolded fixpoint (`MR E/EWcbvEval.v`, `eval_fix`); DV-7.
-/

open Lean Erasure

namespace EraseProof

namespace FixSubst

section
variable {p : FVarId → Prop}

/-- Lifting keeps the free variables. -/
theorem FVarsIn_lift : ∀ {e : Expr} {s d : Nat}, FVarsIn p e → FVarsIn p (e.liftLooseBVars' s d)
  | .app f a, _, _, h => ⟨FVarsIn_lift (e := f) h.1, FVarsIn_lift (e := a) h.2⟩
  | .lam _ t b _, _, _, h | .forallE _ t b _, _, _, h =>
    ⟨FVarsIn_lift (e := t) h.1, FVarsIn_lift (e := b) h.2⟩
  | .letE _ t v b _, _, _, h =>
    ⟨FVarsIn_lift (e := t) h.1, FVarsIn_lift (e := v) h.2.1, FVarsIn_lift (e := b) h.2.2⟩
  | .mdata _ e, _, _, h | .proj _ _ e, _, _, h => FVarsIn_lift (e := e) h
  | .fvar _, _, _, h => h
  | .bvar _, _, _, _ | .sort _, _, _, _ | .const .., _, _, _ | .lit _, _, _, _
  | .mvar _, _, _, _ => trivial

/-- Instantiation keeps the free variables of the term and of the value. -/
theorem FVarsIn_instantiate1' {a : Expr} (ha : FVarsIn p a) :
    ∀ {e : Expr} {d : Nat}, FVarsIn p e → FVarsIn p (e.instantiate1' a d)
  | .bvar i, d, _ => by
    simp only [Expr.instantiate1']
    split
    · trivial
    · split
      · exact FVarsIn_lift ha
      · trivial
  | .app f b, _, h => ⟨FVarsIn_instantiate1' ha (e := f) h.1, FVarsIn_instantiate1' ha (e := b) h.2⟩
  | .lam _ t b _, _, h | .forallE _ t b _, _, h =>
    ⟨FVarsIn_instantiate1' ha (e := t) h.1, FVarsIn_instantiate1' ha (e := b) h.2⟩
  | .letE _ t v b _, _, h => ⟨FVarsIn_instantiate1' ha (e := t) h.1,
    FVarsIn_instantiate1' ha (e := v) h.2.1, FVarsIn_instantiate1' ha (e := b) h.2.2⟩
  | .mdata _ e, _, h | .proj _ _ e, _, h => FVarsIn_instantiate1' ha (e := e) h
  | .fvar _, _, h => h
  | .sort _, _, _ | .const .., _, _ | .lit _, _, _ | .mvar _, _, _ => trivial

/-- Instantiating the binders of a type keeps the free variables. -/
theorem FVarsIn_piInst : ∀ {as : List Expr} {T T' : Expr}, (∀ a ∈ as, FVarsIn p a) →
    FVarsIn p T → piInst as T = some T' → FVarsIn p T'
  | [], _, _, _, hT, h => by cases h; exact hT
  | a :: as, .forallE _ _ _ _, _, has, hT, h => by
    simp only [piInst] at h
    exact FVarsIn_piInst (fun y hy => has y (.tail _ hy))
      (FVarsIn_instantiate1' (has a (.head _)) hT.2) h
  | _ :: _, .bvar _, _, _, _, h | _ :: _, .fvar _, _, _, _, h | _ :: _, .mvar _, _, _, _, h
  | _ :: _, .sort _, _, _, _, h | _ :: _, .const .., _, _, _, h | _ :: _, .app .., _, _, _, h
  | _ :: _, .lam .., _, _, _, h | _ :: _, .letE .., _, _, _, h | _ :: _, .lit _, _, _, _, h
  | _ :: _, .mdata .., _, _, _, h | _ :: _, .proj .., _, _, _, h => by cases h

/-- λ-binders over the domains of a type keep the free variables. -/
theorem FVarsIn_lamsOf : ∀ {m : Nat} {T body e : Expr}, lamsOf m T body = some e →
    FVarsIn p T → FVarsIn p body → FVarsIn p e
  | 0, _, _, _, h, _, hb => by cases h; exact hb
  | _ + 1, .forallE _ _ _ _, _, _, h, hT, hb => by
    simp only [lamsOf, Option.map_eq_some_iff] at h
    obtain ⟨e₀, he₀, rfl⟩ := h
    exact ⟨hT.1, FVarsIn_lamsOf he₀ hT.2 hb⟩
  | _ + 1, .bvar _, _, _, h, _, _ | _ + 1, .fvar _, _, _, h, _, _ | _ + 1, .mvar _, _, _, h, _, _
  | _ + 1, .sort _, _, _, h, _, _ | _ + 1, .const .., _, _, h, _, _ | _ + 1, .app .., _, _, h, _, _
  | _ + 1, .lam .., _, _, h, _, _ | _ + 1, .letE .., _, _, h, _, _ | _ + 1, .lit _, _, _, h, _, _
  | _ + 1, .mdata .., _, _, h, _, _ | _ + 1, .proj .., _, _, h, _, _ => by cases h

/-- The η-expansion of a spine has the free variables of its arguments, when the program's types
have none. -/
theorem FVarsIn_etaSpine {σ : EvalEnv} {c : Name} {us : List Level} {as : List Expr} {e' : Expr}
    (hty : ∀ ci, findDecl σ.decls c = some ci → FVarsIn (fun _ => False) ci.type)
    (h : σ.etaSpine? c us as = some e') (has : ∀ a ∈ as, FVarsIn p a) : FVarsIn p e' := by
  unfold EvalEnv.etaSpine? at h
  split at h
  · rename_i ci ar hci _
    split at h
    · simp only [Option.bind_eq_some_iff] at h
      obtain ⟨ty, hty', he⟩ := h
      have hT : FVarsIn p (Pure.instLevels ci.levelParams us ci.type) :=
        AbsFV.FVarsIn_instLevels _ _ (AbsFV.FVarsIn.mono (fun _ h => h.elim) (hty ci hci))
      refine FVarsIn_lamsOf he (FVarsIn_piInst has hT hty') ?_
      rw [mkAppN_toArray, FVarsIn_foldl]
      refine ⟨trivial, fun a ha => ?_⟩
      rcases List.mem_append.1 ha with ha | ha
      · obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.1 ha
        exact FVarsIn_lift (has a₀ ha₀)
      · obtain ⟨i, -, rfl⟩ := List.mem_map.1 ha
        trivial
    · cases h
  · cases h

end

section
variable {c₀ : Name} {us₀ : List Level}

/-- Every occurrence of the constant `c₀` outside binder types, where the erasure reads constants,
is at the levels `us₀`. -/
def ConstAtE (c₀ : Name) (us₀ : List Level) : Expr → Prop
  | .const c us => c = c₀ → us = us₀
  | .app f a => ConstAtE c₀ us₀ f ∧ ConstAtE c₀ us₀ a
  | .lam _ _ b _ => ConstAtE c₀ us₀ b
  | .letE _ _ v b _ => ConstAtE c₀ us₀ v ∧ ConstAtE c₀ us₀ b
  | .mdata _ e | .proj _ _ e => ConstAtE c₀ us₀ e
  | _ => True

/-- `ConstAt` gives `ConstAtE`. -/
theorem ConstAtE.of_constAt : ∀ {e : Expr}, ConstAt c₀ us₀ e → ConstAtE c₀ us₀ e
  | .const _ _, h => h
  | .app f a, h => ⟨ConstAtE.of_constAt (e := f) h.1, ConstAtE.of_constAt (e := a) h.2⟩
  | .lam _ _ b _, h => ConstAtE.of_constAt (e := b) h.2
  | .letE _ _ v b _, h => ⟨ConstAtE.of_constAt (e := v) h.2.1, ConstAtE.of_constAt (e := b) h.2.2⟩
  | .mdata _ e, h | .proj _ _ e, h => ConstAtE.of_constAt (e := e) h
  | .bvar _, _ | .fvar _, _ | .sort _, _ | .forallE .., _ | .lit _, _ | .mvar _, _ => trivial

/-- `ConstAtE` of an application spine. -/
theorem ConstAtE_foldl : ∀ {f : Expr} {as : List Expr},
    ConstAtE c₀ us₀ (as.foldl .app f) ↔ ConstAtE c₀ us₀ f ∧ ∀ a ∈ as, ConstAtE c₀ us₀ a
  | _, [] => by simp
  | f, a :: as => by
    rw [List.foldl_cons, ConstAtE_foldl]
    simp only [ConstAtE, List.mem_cons, forall_eq_or_imp, and_assoc]

/-- Lifting keeps `ConstAtE`. -/
theorem ConstAtE_lift : ∀ {e : Expr} {s d : Nat}, ConstAtE c₀ us₀ e →
    ConstAtE c₀ us₀ (e.liftLooseBVars' s d)
  | .app f a, _, _, h => ⟨ConstAtE_lift (e := f) h.1, ConstAtE_lift (e := a) h.2⟩
  | .lam _ _ b _, _, _, h => ConstAtE_lift (e := b) h
  | .letE _ _ v b _, _, _, h => ⟨ConstAtE_lift (e := v) h.1, ConstAtE_lift (e := b) h.2⟩
  | .mdata _ e, _, _, h | .proj _ _ e, _, _, h => ConstAtE_lift (e := e) h
  | .const _ _, _, _, h => h
  | .bvar _, _, _, _ | .fvar _, _, _, _ | .sort _, _, _, _ | .forallE .., _, _, _
  | .lit _, _, _, _ | .mvar _, _, _, _ => trivial

/-- λ-binders keep `ConstAtE` of the body. -/
theorem ConstAtE_lamsOf : ∀ {m : Nat} {T body e : Expr}, lamsOf m T body = some e →
    ConstAtE c₀ us₀ body → ConstAtE c₀ us₀ e
  | 0, _, _, _, h, hb => by cases h; exact hb
  | _ + 1, .forallE _ _ _ _, _, _, h, hb => by
    simp only [lamsOf, Option.map_eq_some_iff] at h
    obtain ⟨e₀, he₀, rfl⟩ := h
    show ConstAtE c₀ us₀ e₀
    exact ConstAtE_lamsOf he₀ hb
  | _ + 1, .bvar _, _, _, h, _ | _ + 1, .fvar _, _, _, h, _ | _ + 1, .mvar _, _, _, h, _
  | _ + 1, .sort _, _, _, h, _ | _ + 1, .const .., _, _, h, _ | _ + 1, .app .., _, _, h, _
  | _ + 1, .lam .., _, _, h, _ | _ + 1, .letE .., _, _, h, _ | _ + 1, .lit _, _, _, h, _
  | _ + 1, .mdata .., _, _, h, _ | _ + 1, .proj .., _, _, h, _ => by cases h

/-- The η-expansion of a spine keeps `ConstAtE`. -/
theorem ConstAtE_etaSpine {σ : EvalEnv} {c : Name} {us : List Level} {as : List Expr} {e' : Expr}
    (h : σ.etaSpine? c us as = some e') (hs : ConstAtE c₀ us₀ (mkAppN (.const c us) as.toArray)) :
    ConstAtE c₀ us₀ e' := by
  rw [mkAppN_toArray, ConstAtE_foldl] at hs
  unfold EvalEnv.etaSpine? at h
  split at h
  · split at h
    · simp only [Option.bind_eq_some_iff] at h
      obtain ⟨ty, -, he⟩ := h
      refine ConstAtE_lamsOf he ?_
      rw [mkAppN_toArray, ConstAtE_foldl]
      refine ⟨hs.1, fun a ha => ?_⟩
      rcases List.mem_append.1 ha with ha | ha
      · obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.1 ha
        exact ConstAtE_lift (hs.2 a₀ ha₀)
      · obtain ⟨i, -, rfl⟩ := List.mem_map.1 ha
        trivial
    · cases h
  · cases h

end

/-- The replacement of `x` on an application spine. -/
theorem sub_mkApps (F : LBTerm) (x : FVarId) (k : Nat) (f : LBTerm) (as : List LBTerm) :
    csubst F k (_root_.toBvar x k (mkApps f as)) =
      mkApps (csubst F k (_root_.toBvar x k f))
        (as.map fun a => csubst F k (_root_.toBvar x k a)) := by
  rw [RecLam.toBvar_mkApps, RecLam.csubst_mkApps, List.map_map]
  rfl

/-- The replacement of `x` on case branches, under each branch's binders. -/
theorem sub_alts (F : LBTerm) (x : FVarId) (k : Nat) :
    ∀ brs : List (List BinderName × LBTerm), csubstB F k (_root_.toBvarAlts x k brs) =
      brs.map fun br => (br.1, csubst F (k + br.1.length) (_root_.toBvar x (k + br.1.length) br.2))
  | [] => rfl
  | (ns, b) :: brs => by simp [_root_.toBvarAlts, csubstB, sub_alts F x k brs]

/-- The replacement of `x` leaves a closed term without free variables unchanged. -/
theorem sub_closed {F t : LBTerm} {x : FVarId} (k : Nat) (hc : closedn 0 t = true)
    (hx : hasFVar x t = false) : csubst F k (_root_.toBvar x k t) = t := by
  rw [TargetLift.toBvar_noFVar x t k hx, TargetSubst.csubst_closedn F t 0 k hc (Nat.zero_le _)]

end FixSubst

section
open FixSubst
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {lps : List Name}

/-- Substituting a closed λ□ term `F` for the fix variable `x` (abstracted at `k`, the λ□ term
having no loose index from `k` on), which stands for the translation `.const ηx lsx` of the
constant `c₀` only, keeps an erasure of a term that does not mention `x` and mentions `c₀` only at
the levels `us₀` outside binder types (`ConstAtE`), under the locals without `x`, when `c₀` at
`us₀` erases to `F` anywhere.
Reference: `erases_subst0` (`MR E/ESubstitution.v:612`), for the unfolding of `tFix`; DV-7. -/
theorem Erases.fixSubstE {σ : EvalEnv} {F : LBTerm} {x : FVarId} {c₀ : Name}
    {us₀ : List Level} {kind : Metalean.ConstKind} {nl : Nat}
    {ηx : Metalean.Head ζ (.const kind nl)} {lsx : Fin nl → Metalean.Level lps.length}
    (hF : closedn 0 F = true)
    (hty : ∀ c ci, findDecl σ.decls c = some ci → FVarsIn (fun _ => False) ci.type)
    (hinj : ∀ {n : Nat} (Γ : Metalean.Ctx ζ lps.length 0 n) (Δ : MLCtx ζ lps.length n) (c : Name)
      (us : List Level), TrM E B lps Γ Δ (.const c us) (.const ηx lsx) → c = c₀)
    (hc : ∀ {n : Nat} (Γ : Metalean.Ctx ζ lps.length 0 n) (Δ : MLCtx ζ lps.length n),
      Erases E B lps σ Γ Δ (.const c₀ us₀) F)
    {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n} {e : Expr}
    {r : LBTerm} (h : Erases E B lps σ Γ Δ e r) :
    ∀ (k : Nat) (Δ₀ : MLCtx ζ lps.length n), Δ.findFix x = some (.const ηx lsx) →
      MLCtx.Drop x Δ Δ₀ → FVarsIn (· ≠ x) e → ConstAtE c₀ us₀ e → closedn k r = true →
      Erases E B lps σ Γ Δ₀ e (csubst F k (_root_.toBvar x k r)) := by
  have pushX : ∀ {n : Nat} {Δ : MLCtx ζ lps.length n}, Δ.findFix x = some (.const ηx lsx) →
      (Δ.pushLam none).findFix x = some (.const ηx lsx) := by
    intro _ _ h
    simp [MLCtx.pushLam, MLCtx.findFix, MLCtx.findFix_map_wk, h, Metalean.Expr.wk,
      Metalean.Expr.wkFrom, Metalean.Expr.rename]
  have spineF : ∀ {c : Name} {us : List Level} {as : List Expr},
      FVarsIn (· ≠ x) (mkAppN (.const c us) as.toArray) → ∀ a ∈ as, FVarsIn (· ≠ x) a := by
    intro _ _ _ h
    rw [mkAppN_toArray, FVarsIn_foldl] at h
    exact h.2
  have spineQ : ∀ {c : Name} {us : List Level} {as : List Expr},
      ConstAtE c₀ us₀ (mkAppN (.const c us) as.toArray) → ∀ a ∈ as, ConstAtE c₀ us₀ a := by
    intro _ _ _ h
    rw [mkAppN_toArray, ConstAtE_foldl] at h
    exact h.2
  have gmapB : ∀ {k : Nat} {l : List LBTerm} {i : Nat} {y : LBTerm},
      (l.map fun a => csubst F k (_root_.toBvar x k a))[i]? = some y →
        ∃ y₀, l[i]? = some y₀ ∧ csubst F k (_root_.toBvar x k y₀) = y :=
    fun h => by simpa only [List.getElem?_map, Option.map_eq_some_iff] using h
  have mem : ∀ {l : List Expr} {i : Nat} {y : Expr}, l[i]? = some y → y ∈ l :=
    fun h => List.mem_of_getElem? h
  refine Erases.rec
    (motive_1 := fun Γ Δ e r _ => ∀ (k : Nat) Δ₀, Δ.findFix x = some (.const ηx lsx) →
      MLCtx.Drop x Δ Δ₀ → FVarsIn (· ≠ x) e → ConstAtE c₀ us₀ e → closedn k r = true →
      Erases E B lps σ Γ Δ₀ e (csubst F k (_root_.toBvar x k r)))
    (motive_2 := fun Γ Δ m e br _ => ∀ (k : Nat) Δ₀, Δ.findFix x = some (.const ηx lsx) →
      MLCtx.Drop x Δ Δ₀ → FVarsIn (· ≠ x) e → ConstAtE c₀ us₀ e →
      closedn (k + br.1.length) br.2 = true →
      ErasesAlt E B lps σ Γ Δ₀ m e
        (br.1, csubst F (k + br.1.length) (_root_.toBvar x (k + br.1.length) br.2)))
    ?bvar ?fvar ?lam ?letE ?app ?const ?fixVar ?constFix ?ctor ?cases ?casesReduced ?eta ?proj
    ?litZero ?litSucc ?quotMk ?quotLift ?recLet ?recFix ?mdata ?box ?done ?alam ?intro h
  case bvar =>
    intro _ _ _ i k _ _ _ _ _ hcl
    simp only [closedn, decide_eq_true_eq] at hcl
    simp only [_root_.toBvar, csubst, show k ≠ i by omega, show ¬ k < i by omega, ↓reduceIte]
    exact .bvar
  case fvar =>
    intro _ _ _ y k _ _ _ he _ _
    have hy : (y == x) = false := by
      rcases Bool.eq_false_or_eq_true (y == x) with h' | h'
      · exact absurd ((fvarId_beq_iff y x).mp h') he
      · exact h'
    simp only [_root_.toBvar, hy, Bool.false_eq_true, ↓reduceIte, csubst]
    exact .fvar
  case lam =>
    intro _ _ _ _ _ _ _ _ _ hA hAt _ ih k _ hx W he hq hcl
    simp only [_root_.toBvar, csubst]
    exact .lam (TrM.dropF hA W he.1) hAt (ih (k + 1) _ (pushX hx) W.pushLam he.2 hq hcl)
  case letE =>
    intro _ _ _ _ _ _ _ _ _ _ _ hv hvt _ _ ihv ihb k _ hx W he hq hcl
    simp only [closedn, Bool.and_eq_true] at hcl
    simp only [_root_.toBvar, csubst]
    exact .letE (TrM.dropF hv W he.2.1) hvt (ihv k _ hx W he.2.1 hq.1 hcl.1)
      (ihb (k + 1) _ hx (W.cons _) he.2.2 hq.2 hcl.2)
  case app =>
    intro _ _ _ _ _ _ _ hns _ _ ihf iha k _ hx W he hq hcl
    simp only [closedn, Bool.and_eq_true] at hcl
    simp only [_root_.toBvar, csubst]
    exact .app hns (ihf k _ hx W he.1 hq.1 hcl.1) (iha k _ hx W he.2 hq.2 hcl.2)
  case const =>
    intro _ _ _ _ _ hat hsa hnr _ _ _ _ _ _ _
    exact .const hat hsa hnr
  case fixVar =>
    intro _ c _ _ us y _ hat hT hF k _ hx W _ hq _
    have hT' := TrM.dropF hT W trivial
    by_cases hy : y = x
    · subst hy
      rw [hx] at hF
      cases hF
      have hyy : (y == y) = true := (fvarId_beq_iff y y).mpr rfl
      simp only [_root_.toBvar, hyy, ↓reduceIte, csubst]
      obtain rfl := hinj _ _ c us hT'
      rw [hq rfl]
      exact hc _ _
    · have hyx : (y == x) = false := by
        rcases Bool.eq_false_or_eq_true (y == x) with h' | h'
        · exact absurd ((fvarId_beq_iff y x).mp h') hy
        · exact h'
      simp only [_root_.toBvar, hyx, Bool.false_eq_true, ↓reduceIte, csubst]
      exact .fixVar hat hT' (W.2.2 y _ hy hF)
  case constFix =>
    intro _ _ _ _ _ _ _ _ _ _ hci hdef hcas hat hax hpre hca hp ht hb hcl' hfv _ k _ _ _ _ _ _
    rw [sub_closed k (by simpa [closedn, closednD] using hcl')
      (by simp [hasFVar, hasFVarD, hfv x])]
    exact .constFix hci hdef hcas hat hax hpre hca hp ht hb hcl' hfv
  case ctor =>
    intro _ _ _ _ _ _ _ as _ hcv hnp hid hle hlen _ ih k _ hx W he hq hcl
    rw [AbsFV.closedn_mkApps] at hcl
    rw [sub_mkApps]
    refine .ctor hcv hnp hid hle (by simpa using hlen) fun i a a' ha ha' => ?_
    obtain ⟨a₀', ha₀', rfl⟩ := gmapB ha'
    exact ih i a a₀' ha ha₀' k _ hx W (spineF he a (mem ha)) (spineQ hq a (mem ha))
      (hcl.2 _ (List.mem_of_getElem? ha₀'))
  case cases =>
    intro c iv _ _ _ _ _ maj _ pre alts extra _ _ hco hnr hss hid hpre halts _ hbrs hcf _ hlex _
      ihm iha ihe k _ hx W he hq hcl
    have he' := spineF he
    have hq' := spineQ hq
    rw [AbsFV.closedn_mkApps] at hcl
    obtain ⟨hcase, hext⟩ := hcl
    simp only [closedn, Bool.and_eq_true] at hcase
    rw [sub_mkApps]
    simp only [_root_.toBvar, csubst, sub_alts]
    refine .cases hco hnr hss hid hpre halts (ihm k _ hx W (he' maj (by simp))
      (hq' maj (by simp)) hcase.1)
      (by simp [hbrs]) hcf (fun i cn alt br m h1 h2 h3 h4 => ?_) (by simpa using hlex)
      (fun i a a' ha ha' => ?_)
    · rw [List.getElem?_map, Option.map_eq_some_iff] at h3
      obtain ⟨br₀, hbr₀, rfl⟩ := h3
      exact iha i cn alt br₀ m h1 h2 hbr₀ h4 k _ hx W (he' alt (by simp [mem h2]))
        (hq' alt (by simp [mem h2]))
        (AbsFV.closednB_get hcase.2 hbr₀)
    · obtain ⟨a₀', ha₀', rfl⟩ := gmapB ha'
      exact ihe i a a₀' ha ha₀' k _ hx W (he' a (by simp [mem ha])) (hq' a (by simp [mem ha]))
        (hext _ (List.mem_of_getElem? ha₀'))
  case casesReduced =>
    intro c iv _ _ _ _ _ alt _ _ maj pre extra _ hco hfe hcs hcv hidx hpre _ hlex _ iha ihe
      k _ hx W he hq hcl
    have he' := spineF he
    have hq' := spineQ hq
    rw [AbsFV.closedn_mkApps] at hcl
    obtain ⟨halt, hext⟩ := hcl
    rw [sub_mkApps]
    simp only [List.map_append, List.map_replicate]
    have hbox : csubst F k (_root_.toBvar x k .box) = .box := rfl
    rw [hbox]
    refine .casesReduced hco hfe hcs hcv hidx hpre (iha k _ hx W (he' alt (by simp))
      (hq' alt (by simp)) halt)
      (by simpa using hlex) fun i a a' ha ha' => ?_
    obtain ⟨a₀', ha₀', rfl⟩ := gmapB ha'
    exact ihe i a a₀' ha ha₀' k _ hx W (he' a (by simp [mem ha])) (hq' a (by simp [mem ha]))
      (hext _ (by simp [List.mem_of_getElem? ha₀']))
  case eta =>
    intro c _ _ _ _ _ _ _ heta _ ih k _ hx W he hq hcl
    exact .eta heta (ih k _ hx W (FVarsIn_etaSpine (hty c) heta (spineF he))
      (ConstAtE_etaSpine heta hq) hcl)
  case proj =>
    intro _ _ _ _ _ _ _ _ _ hss hid hS hsort _ ih k _ hx W he hq hcl
    simp only [_root_.toBvar, csubst]
    exact .proj hss hid hS hsort (ih k _ hx W he hq hcl)
  case litZero =>
    intro _ _ _ _ hid _ _ _ _ _ _ _
    exact .litZero hid
  case litSucc =>
    intro _ _ _ _ _ _ hid _ ih k _ hx W _ _ hcl
    simp only [closedn, Bool.and_eq_true] at hcl
    simp only [_root_.toBvar, _root_.toBvarList, csubst, csubstL]
    exact .litSucc hid (ih k _ hx W trivial trivial hcl.2)
  case quotMk =>
    intros; rename_i hcq hk _ hlex _ iha ihe k _ hx W he hq hcl
    have he' := spineF he
    have hq' := spineQ hq
    rw [AbsFV.closedn_mkApps] at hcl
    obtain ⟨ha, hext⟩ := hcl
    rw [sub_mkApps]
    refine .quotMk hcq hk (iha k _ hx W (he' _ (by simp)) (hq' _ (by simp)) ha)
      (by simpa using hlex)
      fun i a a' ha ha' => ?_
    obtain ⟨a₀', ha₀', rfl⟩ := gmapB ha'
    exact ihe i a a₀' ha ha₀' k _ hx W (he' a (by simp [mem ha])) (hq' a (by simp [mem ha]))
      (hext _ (List.mem_of_getElem? ha₀'))
  case quotLift =>
    intros; rename_i hcq hk _ _ hlex _ ihf ihq ihe k _ hx W he hq hcl
    have he' := spineF he
    have hq' := spineQ hq
    rw [AbsFV.closedn_mkApps] at hcl
    obtain ⟨hf, hext⟩ := hcl
    rw [sub_mkApps, List.map_cons]
    refine .quotLift hcq hk (ihf k _ hx W (he' _ (by simp)) (hq' _ (by simp)) hf)
      (ihq k _ hx W (he' _ (by simp)) (hq' _ (by simp)) (hext _ List.mem_cons_self))
        (by simpa using hlex)
      fun i a a' ha ha' => ?_
    obtain ⟨a₀', ha₀', rfl⟩ := gmapB ha'
    exact ihe i a a₀' ha ha₀' k _ hx W (he' a (by simp [mem ha])) (hq' a (by simp [mem ha]))
      (hext _ (List.mem_cons_of_mem _ (List.mem_of_getElem? ha₀')))
  case recLet =>
    intro c rv us minors F' _ _ _ maj maj' ps ms mins is extra mins' is' extra' hcr hF' hps hms
      hmins his hlm _ hli _ _ hle _ ihmin ihis ihmaj ihext k _ hx W he hq hcl
    have he' := spineF he
    have hq' := spineQ hq
    obtain ⟨hml, hFc, hFx⟩ := RecLam.RecFixOf.closed hF'
    have hz : (mins'.zip minors).length = rv.numMinors := by
      simp only [List.length_zip]; omega
    obtain ⟨cm, ci, cj, ce⟩ := RecLam.closedn_recLetTerm_inv (by omega) hz hcl
    rw [RecLam.toBvar_recLetTerm x k rv.numMinors hz hFx,
      RecLam.csubst_recLetTerm hF k rv.numMinors (by simpa using hz) hFc]
    simp only [List.map_map]
    refine .recLet hcr hF' hps hms hmins his (by simpa using hlm) (fun i a a' ha ha' => ?_)
      (by simpa using hli) (fun i a a' ha ha' => ?_)
      (ihmaj k _ hx W (he' _ (by simp)) (hq' _ (by simp)) cj) (by simpa using hle)
        (fun i a a' ha ha' => ?_)
    · obtain ⟨a₀', ha₀', rfl⟩ := gmapB ha'
      exact ihmin i a a₀' ha ha₀' k _ hx W (he' a (by simp [mem ha])) (hq' a (by simp [mem ha]))
        (cm _ (List.mem_of_getElem? ha₀'))
    · obtain ⟨a₀', ha₀', rfl⟩ := gmapB ha'
      exact ihis i a a₀' ha ha₀' k _ hx W (he' a (by simp [mem ha])) (hq' a (by simp [mem ha]))
        (ci _ (List.mem_of_getElem? ha₀'))
    · obtain ⟨a₀', ha₀', rfl⟩ := gmapB ha'
      exact ihext i a a₀' ha ha₀' k _ hx W (he' a (by simp [mem ha])) (hq' a (by simp [mem ha]))
        (ce _ (List.mem_of_getElem? ha₀'))
  case recFix =>
    intro c rv us minors F' _ _ _ maj maj' ps ms mins is extra ws is' extra' hcr hF' hps hms
      hmins his hlw _ hws hli _ _ hle _ ihmin ihis ihmaj ihext k _ hx W he hq hcl
    have he' := spineF he
    have hq' := spineQ hq
    obtain ⟨hml, hFc, hFx⟩ := RecLam.RecFixOf.closed hF'
    have hG := RecLam.substl_fix (ws := ws) (by rw [← hlw, hmins]; exact hFc) hFx
      fun w hw => ⟨(hws w hw).1, (hws w hw).2.1⟩
    rw [AbsFV.closedn_mkApps] at hcl
    obtain ⟨-, hargs⟩ := hcl
    rw [sub_mkApps, sub_closed k hG.1 (hG.2 x), List.map_append, List.map_append,
      List.map_singleton]
    refine .recFix hcr hF' hps hms hmins his hlw (fun i a a' ha ha' => ?_) hws
      (by simpa using hli) (fun i a a' ha ha' => ?_)
      (ihmaj k _ hx W (he' _ (by simp)) (hq' _ (by simp)) (hargs _ (by simp))) (by simpa using hle)
      (fun i a a' ha ha' => ?_)
    · have h1 := ihmin i a a' ha ha' k _ hx W (he' a (by simp [mem ha])) (hq' a (by simp [mem ha]))
        (TargetLift.closedn_mono _ 0 k (hws a' (List.mem_of_getElem? ha')).1 (Nat.zero_le _))
      rwa [sub_closed k (hws a' (List.mem_of_getElem? ha')).1
        ((hws a' (List.mem_of_getElem? ha')).2.1 x)] at h1
    · obtain ⟨a₀', ha₀', rfl⟩ := gmapB ha'
      exact ihis i a a₀' ha ha₀' k _ hx W (he' a (by simp [mem ha])) (hq' a (by simp [mem ha]))
        (hargs _ (by simp [List.mem_of_getElem? ha₀']))
    · obtain ⟨a₀', ha₀', rfl⟩ := gmapB ha'
      exact ihext i a a₀' ha ha₀' k _ hx W (he' a (by simp [mem ha])) (hq' a (by simp [mem ha]))
        (hargs _ (by simp [List.mem_of_getElem? ha₀']))
  case mdata =>
    intro _ _ _ _ _ _ _ ih k _ hx W he hq hcl
    exact .mdata (ih k _ hx W he hq hcl)
  case box =>
    intro _ _ _ _ hb k _ _ W he _ _
    obtain ⟨t, ht, hie⟩ := hb
    exact .box ⟨t, TrM.dropF ht W he, hie⟩
  case done =>
    intro _ _ _ _ _ _ ih k _ hx W he hq hcl
    simp only [List.length_nil, Nat.add_zero] at hcl ⊢
    exact .done (ih k _ hx W he hq hcl)
  case alam =>
    intro _ _ _ _ _ _ _ _ _ _ _ hA hAt _ ih k _ hx W he hq hcl
    have e1 : ∀ l : Nat, k + 1 + l = k + (l + 1) := fun l => by omega
    dsimp only at hcl ih ⊢
    simp only [List.length_cons] at hcl ⊢
    have := ih (k + 1) _ (pushX hx) W.pushLam he.2 hq (by rw [e1]; exact hcl)
    rw [e1] at this
    exact .lam (TrM.dropF hA W he.1) hAt this
  case intro =>
    intro _ _ _ _ _ _ _ _ _ _ _ he' hty' _ ih k _ hx W he hq hcl
    have e1 : ∀ l : Nat, k + 1 + l = k + (l + 1) := fun l => by omega
    dsimp only at hcl ih ⊢
    simp only [List.length_cons] at hcl ⊢
    have := ih (k + 1) _ (pushX hx) W.pushLam ⟨FVarsIn_lift he, trivial⟩
      ⟨ConstAtE_lift hq, trivial⟩ (by rw [e1]; exact hcl)
    rw [e1] at this
    exact .intro (TrM.dropF he' W he) hty' this


/-- `Erases.fixSubstE` for a term that mentions `c₀` only at the levels `us₀` (`ConstAt`): the
body of `Erases.constFix` at the constant's levels, whose recursive calls are at those levels.
Reference: `erases_subst0` (`MR E/ESubstitution.v:612`), for the unfolding of `tFix`; DV-7. -/
theorem Erases.fixSubst {σ : EvalEnv} {F : LBTerm} {x : FVarId} {c₀ : Name}
    {us₀ : List Level} {kind : Metalean.ConstKind} {nl : Nat}
    {ηx : Metalean.Head ζ (.const kind nl)} {lsx : Fin nl → Metalean.Level lps.length}
    (hF : closedn 0 F = true)
    (hty : ∀ c ci, findDecl σ.decls c = some ci → FVarsIn (fun _ => False) ci.type)
    (hinj : ∀ {n : Nat} (Γ : Metalean.Ctx ζ lps.length 0 n) (Δ : MLCtx ζ lps.length n) (c : Name)
      (us : List Level), TrM E B lps Γ Δ (.const c us) (.const ηx lsx) → c = c₀)
    (hc : ∀ {n : Nat} (Γ : Metalean.Ctx ζ lps.length 0 n) (Δ : MLCtx ζ lps.length n),
      Erases E B lps σ Γ Δ (.const c₀ us₀) F)
    {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ Δ₀ : MLCtx ζ lps.length n} {e : Expr}
    {r : LBTerm} {k : Nat} (h : Erases E B lps σ Γ Δ e r)
    (hx : Δ.findFix x = some (.const ηx lsx)) (W : MLCtx.Drop x Δ Δ₀) (he : FVarsIn (· ≠ x) e)
    (hq : ConstAt c₀ us₀ e) (hcl : closedn k r = true) :
    Erases E B lps σ Γ Δ₀ e (csubst F k (_root_.toBvar x k r)) :=
  Erases.fixSubstE hF hty hinj hc h k Δ₀ hx W he (ConstAtE.of_constAt hq) hcl
end

end EraseProof
