import EraseProof.Spec
import Metalean.Syntax.Substitution
import Metalean.Syntax.Reduction

/-!
# The field permutation of constructors

Metalean stores the ordinary fields of a constructor first and the recursive ones last
(`ML Syntax/Expr.lean:73`); Lean's fields are in declaration order. The translator reconciles the
two orders by wrapping each recursor minor with `wrapCase` (`ML Frontend/Translate.lean:84`), a
λ over the minor's Metalean case telescope that applies the minor to the fields in Lean order.
`ctorSat_iota` states that this wrapper, applied to Metalean fields and induction hypotheses,
reduces by β to the minor applied to the fields in Lean order; no other lemma of the development
mentions the permutation.
-/

open Lean Erasure
open Metalean (WHRed WHRedS)

namespace EraseProof

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {ℓ n : Nat}

/-- A λ over a telescope of `k` binders, applied to `k` arguments, reduces by β to its body with
the arguments substituted for the telescope's variables. The untyped counterpart of
`Ctx.lam_applyFamily` (`ML Typing/Telescope.lean:353`). -/
theorem Ctx.lam_apps_whred {m k : Nat} (Δ : Metalean.Ctx ζ ℓ n m) (hk : m = n + k)
    (e : Metalean.Expr ζ ℓ m) (xs : Fin k → Metalean.Expr ζ ℓ n) (σ : Metalean.Subst ζ ℓ m n)
    (hσ : ∀ v : Fin m, σ v = if h : v.val < n then .var ⟨v.val, h⟩ else xs ⟨v.val - n, by omega⟩) :
    E ⊢ (Δ.lam e).apps xs ⤳* e.subst σ := by
  subst hk
  induction Δ using Tele.addInduction with
  | nil =>
    have : σ = Metalean.Subst.id := funext fun v => by
      rw [hσ]; simp [Metalean.Subst.id]
    subst this
    simp [Metalean.Expr.subst_id]
    exact .refl
  | snoc k Δ₀ t₁ ih =>
    let σ₀ : Metalean.Subst ζ ℓ (n + k) n := fun v => σ v.castSucc
    have h₀ := ih (fun i => xs i.castSucc) (.lam t₁ e) σ₀ fun v => by
      simp only [σ₀, hσ, Fin.val_castSucc]
      split_ifs <;> first | omega | rfl
    have hσ' : σ = σ₀.extend (xs (Fin.last k)) := by
      funext v
      cases v using Fin.lastCases with
      | last =>
        rw [hσ]
        split
        · rename_i h; exact absurd h (by simp [Nat.add_eq])
        exact (congrArg xs (Fin.ext (by simp))).trans (Metalean.Subst.extend_last σ₀ _).symm
      | cast v => simp [σ₀]
    rw [Metalean.Expr.apps_last]
    refine (WHRedS.frame (.app (xs (Fin.last k))) h₀).tail ?_
    simp only [Metalean.Frame.plug, Metalean.Expr.subst]
    have := WHRed.beta (E := E) (t := t₁.subst σ₀) (e' := e.subst σ₀.lift) (a := xs (Fin.last k))
    rwa [Metalean.Expr.inst_subst_lift, ← hσ'] at this

end

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {n : Nat}

/-- A successful `Fin.mapM` in `Option` (`ML Control.lean:46`) has every component. -/
theorem mapM_option_eq_some {α : Type} : ∀ {k : Nat} {f : Fin k → Option α} {g : Fin k → α},
    Fin.mapM (m := Option) (α := fun _ => α) f = some g → ∀ i, f i = some (g i)
  | 0, _, _, _, i => i.elim0
  | k + 1, f, g, h, i => by
    simp only [Fin.mapM] at h
    cases h0 : f 0 with
    | none => simp [h0, Seq.seq] at h
    | some a =>
      cases ht : Fin.mapM (m := Option) (α := fun _ => α) (fun i : Fin k => f i.succ) with
      | none => simp [h0, ht, Seq.seq] at h
      | some r =>
        simp [h0, ht] at h
        subst h
        obtain ⟨_ | j, hj⟩ := i
        · exact h0
        · exact mapM_option_eq_some ht ⟨j, by omega⟩


/-- Applying to a list of arguments built by `List.ofFn` is applying to the tuple. -/
theorem appList_ofFn {ℓ k : Nat} (e : Metalean.Expr ζ ℓ n) (g : Fin k → Metalean.Expr ζ ℓ n) :
    e.appList (List.ofFn g) = e.apps g := by
  induction k generalizing e with
  | zero => simp
  | succ k ih => rw [List.ofFn_succ, Metalean.Expr.appList_cons, ih, Metalean.Expr.apps_succ]

/-- Applying to a list of arguments is applying to a tuple with the same components. -/
theorem appList_eq_apps {ℓ k : Nat} (e : Metalean.Expr ζ ℓ n) {fs : List (Metalean.Expr ζ ℓ n)}
    (g : Fin k → Metalean.Expr ζ ℓ n) (hl : fs.length = k) (h : ∀ j : Fin k, fs[j.val]? = some (g j)) :
    e.appList fs = e.apps g := by
  have : fs = List.ofFn g := List.ext_getElem? fun i => by
    by_cases hi : i < k
    · simpa [List.getElem?_ofFn, hi] using h ⟨i, hi⟩
    · simp [List.getElem?_eq_none_iff.mpr (show fs.length ≤ i by omega), hi]
  rw [this, appList_ofFn]

/-- The substitution of a case telescope's variables (`CtorSig.caseSubst`, `ML Syntax/Expr.lean:464`)
is the identity below `n` and the fields and hypotheses, in this order, above. -/
theorem caseSubst_eq {ℓ k : Nat} (csig : Metalean.CtorSig k)
    (fds : Fin csig.nfields → Metalean.Expr ζ ℓ n) (recFds ihs : Fin csig.nrecFields → Metalean.Expr ζ ℓ n)
    (v : Fin (n + csig.nfields + csig.nrecFields + csig.nrecFields)) :
    csig.caseSubst fds recFds ihs v = if h : v.val < n then .var ⟨v.val, h⟩ else
      Fin.append (Fin.append fds recFds) ihs ⟨v.val - n, by omega⟩ := by
  cases v using Fin.addCases with
  | right r =>
    have : (⟨(Fin.natAdd (n + csig.nfields + csig.nrecFields) r).val - n, by simp; omega⟩ :
        Fin (csig.nfields + csig.nrecFields + csig.nrecFields)) =
        Fin.natAdd (csig.nfields + csig.nrecFields) r := Fin.ext (by simp; omega)
    split
    · rename_i h; simp at h; omega
    rw [this, Fin.append_right]
    simp [Metalean.CtorSig.caseSubst]
  | left v =>
    cases v using Fin.addCases with
    | right q =>
      have : (⟨(Fin.castAdd csig.nrecFields (Fin.natAdd (n + csig.nfields) q)).val - n,
          by simp; omega⟩ : Fin (csig.nfields + csig.nrecFields + csig.nrecFields)) =
          Fin.castAdd csig.nrecFields (Fin.natAdd csig.nfields q) := Fin.ext (by simp; omega)
      split
      · rename_i h; simp at h; omega
      rw [this, Fin.append_left, Fin.append_right]
      simp [Metalean.CtorSig.caseSubst]
    | left v =>
      cases v using Fin.addCases with
      | right f =>
        have : (⟨(Fin.castAdd csig.nrecFields (Fin.castAdd csig.nrecFields (Fin.natAdd n f))).val - n,
            by simp; omega⟩ : Fin (csig.nfields + csig.nrecFields + csig.nrecFields)) =
            Fin.castAdd csig.nrecFields (Fin.castAdd csig.nrecFields f) := Fin.ext (by simp)
        split
        · rename_i h; simp at h; omega
        rw [this, Fin.append_left, Fin.append_left]
        simp [Metalean.CtorSig.caseSubst]
      | left v =>
        split
        swap; · rename_i h; simp at h
        simp [Metalean.CtorSig.caseSubst, Metalean.Subst.id]

/-- The permutation lemma: a minor wrapped by `wrapCase` (`ML Frontend/Translate.lean:84`), applied
to the Metalean fields (ordinary `fds`, then recursive `recFds`) and the induction hypotheses `ihs`,
reduces by β to the minor applied to the fields in Lean order (`fs`, related to `fds` and
`recFds` by the constructor's Metalean order as in `SatTr.ctorSat`) and the hypotheses. Every
consumer of the field permutation uses this lemma only. Reference: none (Lean's field order vs
Metalean's, `ML Syntax/Expr.lean:73`). -/
theorem ctorSat_iota {ι : Metalean.IndSig} {ℓ : Nat} {I : Metalean.Inductive ζ ι}
    {η : Metalean.Head ζ (.inductive ι)} {ls : Fin ι.nlevels → Metalean.Level ℓ}
    {ps : Fin ι.nparams → Metalean.Expr ζ ℓ n} {ms : Fin ι.nsorts → Metalean.Expr ζ ℓ n}
    {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} {order : List Nat} {minor w : Metalean.Expr ζ ℓ n}
    (hw : Metalean.Frontend.wrapCase I η ls ps ms s c order minor = .ok w)
    (_ho : MetaOrderOK order (ι.ctors s c).nfields (ι.ctors s c).nrecFields)
    (fs : List (Metalean.Expr ζ ℓ n)) (hfs : fs.length = (ι.ctors s c).nfields + (ι.ctors s c).nrecFields)
    (fds : Fin (ι.ctors s c).nfields → Metalean.Expr ζ ℓ n)
    (recFds : Fin (ι.ctors s c).nrecFields → Metalean.Expr ζ ℓ n)
    (hperm : ∀ o : Fin ((ι.ctors s c).nfields + (ι.ctors s c).nrecFields),
      ∃ j a, order[o.val]? = some j ∧ fs[j]? = some a ∧ Fin.append fds recFds o = a)
    (ihs : Fin (ι.ctors s c).nrecFields → Metalean.Expr ζ ℓ n) :
    E ⊢ ((w.apps fds).apps recFds).apps ihs ⤳* (minor.appList fs).apps ihs := by
  unfold Metalean.Frontend.wrapCase at hw
  dsimp only at hw
  by_cases hid : Metalean.Frontend.isIdentityOrder order
      ((ι.ctors s c).nfields + (ι.ctors s c).nrecFields) = true
  · rw [ite_eq_left hid] at hw
    cases hw
    have hord : order = List.range ((ι.ctors s c).nfields + (ι.ctors s c).nrecFields) :=
      beq_iff_eq.mp hid
    rw [appList_eq_apps minor (Fin.append fds recFds) hfs fun o => ?_, Metalean.Expr.apps_append]
    · exact .refl
    obtain ⟨j, a, hj, ha, rfl⟩ := hperm o
    rw [hord, List.getElem?_range o.isLt] at hj
    cases hj
    exact ha
  · rw [ite_eq_right hid] at hw
    rcases hπ : Metalean.Frontend.orderMaps? order
        ((ι.ctors s c).nfields + (ι.ctors s c).nrecFields) with _ | ⟨π, snd⟩
    · rw [hπ] at hw; cases hw
    · rw [hπ] at hw
      dsimp only at hw
      obtain ⟨x, hx⟩ : ∃ x, Fin.mapM (m := Option) (fun j => (π j).map fun o =>
          (Metalean.Expr.var ⟨n + o.val, by omega⟩ : Metalean.Expr ζ ℓ
            (n + (ι.ctors s c).nfields + (ι.ctors s c).nrecFields + (ι.ctors s c).nrecFields))) = x :=
        ⟨_, rfl⟩
      rw [hx] at hw
      rcases x with _ | fieldVars
      · cases hw
      · dsimp only at hw
        cases hw
        have hfv' := mapM_option_eq_some hx
        unfold Metalean.Frontend.orderMaps? at hπ
        split_ifs at hπ with hlen
        simp only [Option.some.injEq, Prod.mk.injEq] at hπ
        obtain ⟨rfl, -⟩ := hπ
        -- each Lean field `j` sits at Metalean position `o j`
        have hpos : ∀ j : Fin ((ι.ctors s c).nfields + (ι.ctors s c).nrecFields),
            ∃ o : Fin ((ι.ctors s c).nfields + (ι.ctors s c).nrecFields),
              fieldVars j = .var ⟨n + o.val, by omega⟩ ∧ order[o.val]? = some j.val := by
          intro j
          have h := hfv' j
          simp only [Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
          obtain ⟨o, ⟨o', hidx, ho'⟩, hvar⟩ := h
          split_ifs at ho' with hlt
          cases ho'
          refine ⟨⟨o', hlt⟩, hvar.symm, ?_⟩
          obtain ⟨hlt', hget, -⟩ := List.idxOf?_eq_some_iff.mp hidx
          simp [List.getElem?_eq_getElem hlt', hget]
        choose o hvar hord using hpos
        have hsub := caseSubst_eq (ι.ctors s c) fds recFds ihs
        rw [← Metalean.Expr.apps_append (args₁ := fds),
          ← Metalean.Expr.apps_append (args₁ := Fin.append fds recFds)]
        have key : ∀ {X Y Z : Metalean.Expr ζ ℓ n}, E ⊢ X ⤳* Y → Y = Z → E ⊢ X ⤳* Z :=
          fun h e => e ▸ h
        refine key (Ctx.lam_apps_whred _ (by omega) _ _ _ hsub) ?_
        rw [Metalean.Expr.subst_apps, Metalean.Expr.wkN_subst_case,
          appList_eq_apps minor (fun j => Fin.append fds recFds (o j)) hfs fun j => ?_,
          ← Metalean.Expr.apps_append]
        · congr 1
          funext i
          cases i using Fin.addCases with
          | left j =>
            rw [Fin.append_left, Fin.append_left, hvar j, Metalean.Expr.subst, hsub]
            split
            · rename_i h; exact absurd h (by simp)
            · exact (congrArg _ (Fin.ext (by simp))).trans (Fin.append_left _ _ (o j))
          | right r =>
            rw [Fin.append_right, Fin.append_right, Metalean.Expr.subst, hsub]
            split
            · rename_i h; simp at h; omega
            · exact (congrArg _ (Fin.ext (by simp; omega))).trans (Fin.append_right _ _ r)
        · obtain ⟨j', a, hj', ha, rfl⟩ := hperm (o j)
          rw [hord j] at hj'
          cases hj'
          exact ha

end

end EraseProof
