import EraseProof.Spec
import EraseProof.TargetFacts

/-!
# Erased dependencies

`ErasesDeps` (the λ□ environment holds erasures of a term's dependencies) survives substitution
(`ErasesDeps.csubst`) and λ□ evaluation (`ErasesDeps.eval`), for every certificate predicate.
Copy of `ML-V Relation/Deps.lean:97-260` (#16, commit `f3b934f`), with the relation's parameters
`cert σ` in place of `E B σ`.
-/

open Lean

namespace EraseProof

section
variable {cert : BoxCert} {σ : EvalEnv} {lenv : GlobalDeclarations}

/-- An element of `csubstL t k as` is the substitution of an element of `as`. -/
private theorem mem_csubstL {t : LBTerm} {k : Nat} : ∀ {as : List LBTerm} {a : LBTerm},
    a ∈ csubstL t k as → ∃ a' ∈ as, a = csubst t k a'
  | [], _, h => nomatch h
  | _ :: _, _, h => by
    simp only [csubstL, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨_, List.mem_cons_self, rfl⟩
    · obtain ⟨a', ha', he⟩ := mem_csubstL h
      exact ⟨a', List.mem_cons_of_mem _ ha', he⟩

/-- A branch body of `csubstB t k bs` is the substitution of a branch body of `bs`. -/
private theorem mem_csubstB {t : LBTerm} {k : Nat} :
    ∀ {bs : List (List BinderName × LBTerm)} {b : List BinderName × LBTerm},
    b ∈ csubstB t k bs → ∃ b' ∈ bs, ∃ k', b.2 = csubst t k' b'.2
  | [], _, h => nomatch h
  | (_, _) :: _, _, h => by
    simp only [csubstB, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨_, List.mem_cons_self, _, rfl⟩
    · obtain ⟨b', hb', k', he⟩ := mem_csubstB h
      exact ⟨b', List.mem_cons_of_mem _ hb', k', he⟩

/-- A body of `csubstD t k ds` is the substitution of a body of `ds`. -/
private theorem mem_csubstD {t : LBTerm} {k : Nat} :
    ∀ {ds : List (@FixDef LBTerm)} {d : @FixDef LBTerm},
    d ∈ csubstD t k ds → ∃ d' ∈ ds, d.body = csubst t k d'.body
  | [], _, h => nomatch h
  | ⟨_, _, _⟩ :: _, _, h => by
    simp only [csubstD, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨_, List.mem_cons_self, rfl⟩
    · obtain ⟨d', hd', he⟩ := mem_csubstD h
      exact ⟨d', List.mem_cons_of_mem _ hd', he⟩

/-- Dependencies are preserved by substitution. Reference: `erases_deps_subst`
(`MR E/EDeps.v:94`). -/
theorem ErasesDeps.csubst (ha : ErasesDeps cert σ lenv a) (hb : ErasesDeps cert σ lenv b) :
    ErasesDeps cert σ lenv (csubst a k b) := by
  induction hb generalizing k with
  | box => exact .box
  | bvar =>
    simp only [EraseProof.csubst]
    split
    · exact ha
    · split <;> exact .bvar
  | fvar => exact .fvar
  | lambda _ ih => exact .lambda ih
  | letIn _ _ ihv ihb => exact .letIn ihv ihb
  | app _ _ ihf iha => exact .app ihf iha
  | const hc hl hd hbody => exact .const hc hl hd hbody
  | construct hi hind _ ih =>
    refine .construct hi hind fun a' ha' => ?_
    obtain ⟨a'', ha'', rfl⟩ := mem_csubstL ha'
    exact ih a'' ha''
  | case hi hind _ _ ihd ihb =>
    refine .case hi hind ihd fun br hbr => ?_
    obtain ⟨br', hbr', k', he⟩ := mem_csubstB hbr
    rw [he]
    exact ihb br' hbr'
  | proj hi hind _ ihd => exact .proj hi hind ihd
  | fix _ ih =>
    refine .fix fun d hd => ?_
    obtain ⟨d', hd', he⟩ := mem_csubstD hd
    rw [he]
    exact ih d' hd'

/-- Substituting terms with erased dependencies. Reference: `erases_deps_substl`
(`MR E/EDeps.v:208`). -/
theorem ErasesDeps.substl : ∀ {ts : List LBTerm} {b : LBTerm},
    (∀ t ∈ ts, ErasesDeps cert σ lenv t) → ErasesDeps cert σ lenv b →
      ErasesDeps cert σ lenv (EraseProof.substl ts b)
  | [], _, _, hb => hb
  | t :: _, _, hts, hb => by
    simp only [EraseProof.substl, List.foldl_cons]
    exact ErasesDeps.substl (fun u hu => hts u (List.mem_cons_of_mem _ hu))
      (ErasesDeps.csubst (hts t List.mem_cons_self) hb)

/-- An application spine has erased dependencies iff its head and arguments have. Reference:
`erases_deps_mkApps` (`MR E/EDeps.v:17`) and `erases_deps_mkApps_inv` (`:31`). -/
theorem ErasesDeps.mkApps_iff : ∀ {f : LBTerm} {args : List LBTerm},
    ErasesDeps cert σ lenv (mkApps f args) ↔
      ErasesDeps cert σ lenv f ∧ ∀ a ∈ args, ErasesDeps cert σ lenv a
  | _, [] => by simp [mkApps]
  | _, a :: as => by
    rw [mkApps, ErasesDeps.mkApps_iff]
    constructor
    · rintro ⟨hfa, has⟩
      cases hfa with
      | app hf ha =>
        exact ⟨hf, fun b hb => (List.mem_cons.1 hb).elim (fun h => h ▸ ha) (has b)⟩
    · rintro ⟨hf, has⟩
      exact ⟨.app hf (has a List.mem_cons_self), fun b hb => has b (List.mem_cons_of_mem _ hb)⟩

/-! ## Evaluation -/

/-- Dependencies are preserved by λ□ evaluation. Reference: `erases_deps_eval`
(`MR E/EDeps.v:275`). -/
theorem ErasesDeps.eval (h : ErasesDeps cert σ lenv tb) (hev : LBEval defaultFlags lenv tb vb) :
    ErasesDeps cert σ lenv vb := by
  induction hev using LBEval.ind with
  | box => exact .box
  | beta _ _ _ ih1 ih2 ih3 =>
    cases h with
    | app hf ha =>
      cases ih1 hf with
      | lambda hbody => exact ih3 (ErasesDeps.csubst (ih2 ha) hbody)
  | zeta _ _ ih1 ih2 =>
    cases h with
    | letIn hv hbody => exact ih2 (ErasesDeps.csubst (ih1 hv) hbody)
  | iota _ _ _ hbr _ _ _ ihd ihr =>
    cases h with
    | case _ _ hd hbrs =>
      obtain ⟨-, hargs⟩ := ErasesDeps.mkApps_iff.1 (ihd hd)
      refine ihr (ErasesDeps.substl (fun t ht => ?_) (hbrs _ (List.mem_of_getElem? hbr)))
      exact hargs t (List.mem_of_mem_drop (List.mem_reverse.1 ht))
  | iotaBlock hb => exact absurd hb (by decide)
  | iotaSing _ _ _ hbrs _ _ ihr =>
    cases h with
    | case _ _ _ hb =>
      subst hbrs
      refine ihr (ErasesDeps.substl (fun t ht => ?_) (hb _ List.mem_cons_self))
      rw [List.eq_of_mem_replicate ht]
      exact .box
  | fix _ _ _ hunf _ ih1 ih2 ih3 =>
    cases h with
    | app hf ha =>
      obtain ⟨hfix, hargs⟩ := ErasesDeps.mkApps_iff.1 (ih1 hf)
      refine ih3 (.app (ErasesDeps.mkApps_iff.2 ⟨?_, hargs⟩) (ih2 ha))
      cases hfix with
      | fix hbodies =>
        unfold cunfoldFix at hunf
        obtain ⟨d, hd, he⟩ := Option.map_eq_some_iff.1 hunf
        have hfn := (Prod.mk.inj he).2
        subst hfn
        refine ErasesDeps.substl (fun t ht => ?_) (hbodies d (List.mem_of_getElem? hd))
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 ht
        exact .fix hbodies
  | fixValue _ _ _ _ _ ih1 ih2 =>
    cases h with
    | app hf ha => exact .app (ih1 hf) (ih2 ha)
  | fix' hb => exact absurd hb (by decide)
  | delta hc hbody _ ih =>
    cases h with
    | const _ hl _ hdeps =>
      rw [hl] at hc
      cases hc
      exact ih (hdeps _ hbody)
  | proj _ _ _ _ hget _ ihd ihr =>
    cases h with
    | proj _ _ hd =>
      obtain ⟨-, hargs⟩ := ErasesDeps.mkApps_iff.1 (ihd hd)
      exact ihr (hargs _ (List.mem_of_getElem? hget))
  | projBlock hb => exact absurd hb (by decide)
  | projProp => exact .box
  | construct _ _ _ _ _ ih1 ih2 =>
    cases h with
    | app hf ha => exact .app (ih1 hf) (ih2 ha)
  | constructBlock hb => exact absurd hb (by decide)
  | appCong _ _ _ ih1 ih2 =>
    cases h with
    | app hf ha => exact .app (ih1 hf) (ih2 ha)
  | prim => exact h
  | atom => exact h

end

end EraseProof
