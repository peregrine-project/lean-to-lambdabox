import EraseProof.Bridge.ProgEnv
import Metalean.Metatheory.SubjectReduction
import Mathlib.Data.List.Sort

/-!
# Projections of constructor values

The translation of a projection of a constructor value is definitionally equal to the translation
of the field (`proj_defeq`): for a structure through Metalean's
`IsStructure.projTerm_ctor_defeq`, for a proof of a non-structure through the ι-reduction of the
proof projection `projProofTerm`. Reference: `eval_proj` (`MR P/PCUICWcbvEval.v:264`).
-/

open Lean

namespace EraseProof

/-- `mkAppN` of a list is a left fold of applications. -/
theorem mkAppN_eq_foldl (f : Expr) (as : List Expr) : mkAppN f as.toArray = as.foldl .app f := by
  simp [mkAppN]; rfl

/-- The head of a left fold of applications. -/
theorem foldl_app_getAppFn (as : List Expr) (f : Expr) :
    (as.foldl .app f).getAppFn = f.getAppFn := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih => exact (ih (.app f a)).trans rfl

/-- Applications of constants are injective in the constant, its levels and the arguments. -/
theorem foldl_app_const_inj {c c' : Name} {us us' : List Level} {as as' : List Expr}
    (h : as.foldl Expr.app (Expr.const c us) = as'.foldl Expr.app (Expr.const c' us')) :
    c = c' ∧ us = us' ∧ as = as' := by
  induction as using List.reverseRecOn generalizing as' with
  | nil =>
    cases as' using List.reverseRecOn with
    | nil => cases h; exact ⟨rfl, rfl, rfl⟩
    | append_singleton as' a' _ => simp at h
  | append_singleton as a ih =>
    cases as' using List.reverseRecOn with
    | nil => simp at h
    | append_singleton as' a' _ =>
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, Expr.app.injEq] at h
      obtain ⟨h1, rfl⟩ := h
      obtain ⟨rfl, rfl, rfl⟩ := ih h1
      exact ⟨rfl, rfl, rfl⟩

/-- β-reduction of a λ-telescope applied to one argument per binder. -/
theorem Ctx.lam_apps_whredS {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {ℓ a k : Nat}
    (Δ : Metalean.Ctx ζ ℓ a (a + k)) (e : Metalean.Expr ζ ℓ (a + k))
    (xs : Fin k → Metalean.Expr ζ ℓ a) :
    Metalean.WHRedS E ((Δ.lam e).apps xs) (e.subst (Fin.append Metalean.Subst.id xs)) := by
  induction Δ using Tele.addInduction with
  | nil => simp; exact Relation.ReflTransGen.refl
  | snoc k Δ₀ t ih =>
    rw [Metalean.Expr.apps_last]
    have h1 := Metalean.WHRedS.frame (.app (xs (Fin.last k))) (ih (.lam t e) fun i => xs i.castSucc)
    refine h1.tail ?_
    have h2 := Metalean.WHRed.beta (E := E) (t := t.subst (Fin.append Metalean.Subst.id fun i => xs i.castSucc))
      (e' := e.subst (Metalean.Subst.lift (Fin.append Metalean.Subst.id fun i => xs i.castSucc)))
      (a := xs (Fin.last k))
    simpa! [Metalean.Expr.inst_subst_lift, Metalean.Subst.extend, ← Fin.append_snoc,
      ← Fin.init_def] using h2

/-- The case of a field `f` of a constructor without recursive fields, applied to the fields, the
(no) recursive fields and the (no) induction hypotheses, reduces to the field. -/
theorem caseOrdinary_apps_whredS {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {ℓ n nsorts : Nat}
    (csig : Metalean.CtorSig nsorts) (h0 : csig.nrecFields = 0)
    (Δ : Metalean.Ctx ζ ℓ n (n + csig.nfields + csig.nrecFields + csig.nrecFields))
    (f : Fin csig.nfields) (fds : Fin csig.nfields → Metalean.Expr ζ ℓ n)
    (recFds ihs : Fin csig.nrecFields → Metalean.Expr ζ ℓ n) :
    Metalean.WHRedS E ((((Δ.lam (csig.caseOrdinary f)).apps fds).apps recFds).apps ihs) (fds f) := by
  obtain ⟨nf, nr, ra, rt⟩ := csig
  dsimp only at h0 Δ f fds recFds ihs ⊢
  subst h0
  simp only [Metalean.Expr.apps_zero]
  have h := Ctx.lam_apps_whredS (E := E) (k := nf) Δ
    (Metalean.CtorSig.caseOrdinary ⟨nf, 0, ra, rt⟩ f : Metalean.Expr ζ ℓ (n + nf + 0 + 0)) fds
  simpa [Metalean.CtorSig.caseOrdinary, Metalean.CtorSig.fieldOrdinary] using h

variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {lps : List Name} {n : Nat}
  {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}

/-- A saturated constructor spine translates to a Metalean constructor whose fields are the
translations of the Lean fields, permuted by the constructor's Metalean field order. -/
theorem TrM.ctor_inv {C : Name} {us : List Level} {as : List Expr}
    {t : Metalean.Expr ζ lps.length n} {ι : Metalean.IndSig}
    {η : Metalean.Head ζ (.inductive ι)} {s : Fin ι.nsorts} {k : Fin (ι.nctors s)}
    {order : List Nat} (hB : B C = some (.ctor η s k order))
    (hlen : as.length = ι.nparams + ((ι.ctors s k).nfields + (ι.ctors s k).nrecFields))
    (h : TrM E B lps Γ Δ (mkAppN (.const C us) as.toArray) t) :
    ∃ (ls : Fin ι.nlevels → Metalean.Level lps.length)
      (ps : Fin ι.nparams → Metalean.Expr ζ lps.length n)
      (fds : Fin (ι.ctors s k).nfields → Metalean.Expr ζ lps.length n)
      (recFds : Fin (ι.ctors s k).nrecFields → Metalean.Expr ζ lps.length n)
      (fs : List (Metalean.Expr ζ lps.length n)),
      t = .ctor η s k ls ps fds recFds ∧
      (∀ (i : Nat) a a', as[i]? = some a → (List.ofFn ps ++ fs)[i]? = some a' →
        TrM E B lps Γ Δ a a') ∧
      (∀ o : Fin ((ι.ctors s k).nfields + (ι.ctors s k).nrecFields),
        ∃ j a, order[o.val]? = some j ∧ fs[j]? = some a ∧ Fin.append fds recFds o = a) := by
  rw [mkAppN_eq_foldl] at h
  generalize hm : as.foldl Expr.app (Expr.const C us) = m at h
  have hfn : m.getAppFn = .const C us := by rw [← hm, foldl_app_getAppFn]; rfl
  cases h with
  | bvar | fvar | sort | lam | forallE | letE | mdata | lit | projStruct | projProof =>
    cases hfn
  | const hc =>
    cases hfn
    rw [hB] at hc
    cases hc
  | app hns =>
    exact absurd ⟨C, us, _, hfn, hB, rfl⟩ hns
  | @special c us' _ _ _ as₂ as' b _ hb _ hl hargs hsat =>
    rw [mkAppN_eq_foldl] at hm
    obtain ⟨rfl, rfl, rfl⟩ := foldl_app_const_inj hm
    rw [hB] at hb
    cases hb
    cases hsat with
    | ctorEta _ hlt => omega
    | ctorSat ps fs rest fds recFds _ hfs _ hperm =>
      have hrest : rest = [] := by
        apply List.eq_nil_of_length_eq_zero
        simp only [List.length_append, List.length_ofFn] at hl
        omega
      subst hrest
      refine ⟨_, ps, fds, recFds, fs, Metalean.Expr.appList_nil _, fun i a a' h1 h2 => hargs i a a' h1 ?_, hperm⟩
      simpa using h2

/-- The proof projection of field `f` of a constructor without recursive fields reduces, by ι and
β, to the field. -/
theorem projProofTerm_ctor_whredS {ι : Metalean.IndSig} {η : Metalean.Head ζ (.inductive ι)}
    {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} {ℓ : Nat} {ls ls₂ : Fin ι.nlevels → Metalean.Level ℓ}
    (hi : ι.nindices s = 0) {ps ps₂ : Fin ι.nparams → Metalean.Expr ζ ℓ n} {f : Nat}
    (hf : f < (ι.ctors s c).nfields) (hnr : (ι.ctors s c).nrecFields = 0)
    {fds : Fin (ι.ctors s c).nfields → Metalean.Expr ζ ℓ n}
    {recFds : Fin (ι.ctors s c).nrecFields → Metalean.Expr ζ ℓ n} :
    Metalean.WHRedS E (projProofTerm E η s c ls hi ps f (.ctor η s c ls₂ ps₂ fds recFds))
      (fds ⟨f, hf⟩) := by
  rw [projProofTerm]
  refine Relation.ReflTransGen.head Metalean.WHRed.iota ?_
  rw [Metalean.Inductive.iotaRhs, dite_eq_left hf]
  exact caseOrdinary_apps_whredS _ hnr _ _ _ _ _

/-- With no recursive field, a field order that satisfies `MetaOrderOK` is the identity, so the
`i`-th Lean field is the `i`-th Metalean field. -/
theorem field_of_order {ι : Metalean.IndSig} {s : Fin ι.nsorts} {k : Fin (ι.nctors s)}
    {order : List Nat} {fs : List (Metalean.Expr ζ lps.length n)}
    {fds : Fin (ι.ctors s k).nfields → Metalean.Expr ζ lps.length n}
    {recFds : Fin (ι.ctors s k).nrecFields → Metalean.Expr ζ lps.length n}
    (hnr : (ι.ctors s k).nrecFields = 0)
    (hmo : MetaOrderOK order (ι.ctors s k).nfields (ι.ctors s k).nrecFields)
    (hperm : ∀ o : Fin ((ι.ctors s k).nfields + (ι.ctors s k).nrecFields),
      ∃ j a, order[o.val]? = some j ∧ fs[j]? = some a ∧ Fin.append fds recFds o = a)
    {i : Nat} (hi : i < (ι.ctors s k).nfields) : fs[i]? = some (fds ⟨i, hi⟩) := by
  obtain ⟨ords, recs, rfl, -, hrl, hords, -, hp⟩ := hmo
  have hrecs : recs = [] := List.eq_nil_of_length_eq_zero (hrl.trans hnr)
  subst hrecs
  simp only [List.append_nil] at hp hperm
  have hord : ords = List.range ((ι.ctors s k).nfields + (ι.ctors s k).nrecFields) :=
    hp.eq_of_pairwise (fun a b _ _ h1 h2 => absurd (h1.trans h2) (Nat.lt_irrefl a)) hords
      List.pairwise_lt_range
  obtain ⟨j, a, hj, ha, heq⟩ := hperm (Fin.castAdd _ ⟨i, hi⟩)
  rw [hord, List.getElem?_range (by simp; omega)] at hj
  cases hj
  rw [Fin.append_left] at heq
  rw [heq]
  exact ha

open Metalean (Defeq EnvWF) in
/-- A projection of a constructor value translates to a term definitionally equal to the
translation of the field. Reference: `eval_proj` (`MR P/PCUICWcbvEval.v:264`);
`IsStructure.projTerm_ctor_defeq` (`ML Metatheory/SubjectReduction.lean:208`). -/
theorem proj_defeq {P : List ConstantInfo} {σ : EvalEnv} {S : Name} {i : Nat} {m a : Expr}
    {fs : List Expr} {t T : Metalean.Expr ζ lps.length n}
    (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hΓ : E[Γ] ⊢ ok)
    (hsub : SubEnv σ.decls P) (hcv : CtorValue σ S m 0 fs) (ha : fs[i]? = some a)
    (he : TrM E B lps Γ Δ (.proj S i m) t) (ht : E[Γ] ⊢ t : T) :
    ∃ a', TrM E B lps Γ Δ a a' ∧ E[Γ] ⊢ t ≡ a' : T := by
  obtain ⟨C, us, cv, ps, hC, hind, hcidx, hps, hfs, rfl⟩ := hcv
  have hCP : findDecl P C = some (.ctorInfo cv) := by
    obtain ⟨hm, hn⟩ := findDecl_eq_some hC
    have h := hsub _ hm
    rwa [hn] at h
  obtain ⟨ι, η, s, k, order, hBC, -, hnp, hnf, hmo, hBS⟩ := henv.lookup_ctor hCP
  rw [hind] at hBS
  have hlen : (ps ++ fs).length = ι.nparams + ((ι.ctors s k).nfields + (ι.ctors s k).nrecFields) := by
    simp [hps, hfs, hnp, hnf]
  have hfield : ∀ {ps₂ : Fin ι.nparams → Metalean.Expr ζ lps.length n}
      {fs' : List (Metalean.Expr ζ lps.length n)} {a' : Metalean.Expr ζ lps.length n},
      (∀ (j : Nat) b b', (ps ++ fs)[j]? = some b → (List.ofFn ps₂ ++ fs')[j]? = some b' →
        TrM E B lps Γ Δ b b') → fs'[i]? = some a' → TrM E B lps Γ Δ a a' := by
    intro ps₂ fs' a' hargs hf
    refine hargs (ps.length + i) a a'
      (by rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]; exact ha) ?_
    rw [hps, hnp, List.getElem?_append_right (by simp)]
    simpa using hf
  generalize hx : Expr.proj S i (mkAppN (Expr.const C us) (ps ++ fs).toArray) = x at he
  cases he with
  | projStruct hst hi hBS' htr _ =>
    cases hx
    rw [hBS] at hBS'
    simp only [Option.some.injEq, MBinding.ind.injEq] at hBS'
    obtain ⟨rfl, h1, h2⟩ := hBS'
    cases h1; cases h2
    obtain ⟨ls₂, ps₂, fds, recFds, fs', rfl, hargs, hperm⟩ := TrM.ctor_inv hBC hlen htr
    obtain rfl := hst.ctor_unique k
    have hnr : (ι.ctors s k).nrecFields = 0 :=
      Nat.eq_zero_of_not_pos fun h => hst.no_recursive.false ⟨0, h⟩
    exact ⟨fds ⟨i, hi⟩, hfield hargs (field_of_order hnr hmo hperm hi),
      hst.projTerm_ctor_defeq ⟨i, hi⟩ hE hΓ ht⟩
  | projProof hi0 hBS' _ hc hnr hi _ htr _ =>
    cases hx
    rw [hBS] at hBS'
    simp only [Option.some.injEq, MBinding.ind.injEq] at hBS'
    obtain ⟨rfl, h1, h2⟩ := hBS'
    cases h1; cases h2
    obtain ⟨ls₂, ps₂, fds, recFds, fs', rfl, hargs, hperm⟩ := TrM.ctor_inv hBC hlen htr
    obtain rfl := hc k
    exact ⟨fds ⟨i, hi⟩, hfield hargs (field_of_order hnr hmo hperm hi),
      Metalean.WHRedS.defeq hE hΓ (projProofTerm_ctor_whredS hi0 hi hnr) ht⟩
  | @special c us' _ _ _ as₂ =>
    have h := congrArg Expr.getAppFn hx.symm
    rw [mkAppN_eq_foldl (.const c us') as₂, foldl_app_getAppFn] at h
    cases h
  | _ => cases hx

end EraseProof
