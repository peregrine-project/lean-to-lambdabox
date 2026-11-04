import EraseProof.Spec
import EraseProof.TargetFacts

/-!
# Erased dependencies

`ErasesDeps` (the λ□ environment holds erasures of a term's dependencies) survives fresh growth
of the λ□ environment (`ErasesDeps.ext`), substitution (`ErasesDeps.csubst`) and λ□ evaluation
(`ErasesDeps.eval`).
-/

open Lean

namespace EraseProof

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {σ : EvalEnv}
  {lenv lenv' : GlobalDeclarations}

/-- The derived `==` on module paths implies equality. Reference: `modpath_eq_dec`
(`MR common/theories/Kernames.v:232`). -/
private theorem modPath_eq_of_beq : ∀ {a b : ModPath}, (a == b) = true → a = b
  | .MPfile d₁, .MPfile d₂, h => by
    have h' : (d₁ == d₂) = true := h
    rw [beq_iff_eq.1 h']
  | .MPdot m₁ i₁, .MPdot m₂ i₂, h => by
    have h' : (m₁ == m₂ && i₁ == i₂) = true := h
    rw [Bool.and_eq_true] at h'
    rw [modPath_eq_of_beq h'.1, beq_iff_eq.1 h'.2]
  | .MPfile _, .MPdot .., h | .MPdot .., .MPfile _, h => nomatch h

/-- The derived `==` on kernames implies equality. Reference: `reflect_kername`
(`MR common/theories/Kernames.v:325`). -/
private theorem kername_eq_of_beq {a b : Kername} (h : (a == b) = true) : a = b := by
  obtain ⟨m₁, i₁⟩ := a
  obtain ⟨m₂, i₂⟩ := b
  have h' : (m₁ == m₂ && i₁ == i₂) = true := h
  rw [Bool.and_eq_true] at h'
  rw [modPath_eq_of_beq h'.1, beq_iff_eq.1 h'.2]

/-- A kername found in `lenv` is found, with the same declaration, after fresh growth. -/
private theorem find?_ext {kn : Kername} {d : Kername × GlobalDecl}
    (hx : ∃ new, lenv' = new ++ lenv ∧ ∀ kn ∈ new.map (·.1), lenv.find? (·.1 == kn) = none)
    (h : lenv.find? (·.1 == kn) = some d) : lenv'.find? (·.1 == kn) = some d := by
  obtain ⟨new, rfl, hfresh⟩ := hx
  have hnew : new.find? (·.1 == kn) = none := by
    rw [List.find?_eq_none]
    intro y hy hyk
    have hnone := hfresh y.1 (List.mem_map.2 ⟨y, hy, rfl⟩)
    rw [kername_eq_of_beq hyk, h] at hnone
    cases hnone
  rw [List.find?_append, hnew, Option.none_or]
  exact h

/-- `ErasesInd` survives fresh growth of the λ□ environment. -/
private theorem ErasesInd.ext
    (hx : ∃ new, lenv' = new ++ lenv ∧ ∀ kn ∈ new.map (·.1), lenv.find? (·.1 == kn) = none)
    (h : ErasesInd E B σ lenv T) : ErasesInd E B σ lenv' T := by
  obtain ⟨iv, hiv, hall⟩ := h
  refine ⟨iv, hiv, fun j n hj => ?_⟩
  obtain ⟨iv', mib, ob, h1, hl, h3⟩ := hall j n hj
  refine ⟨iv', mib, ob, h1, ?_, h3⟩
  unfold lookupInd at hl ⊢
  split at hl
  · rename_i d heq
    rw [find?_ext hx heq]
    exact hl
  · cases hl

/-- `ErasesDeps` is stable under fresh growth of the λ□ environment. Reference: `erases_deps_cons`
(`MR E/EDeps.v:492`). -/
theorem ErasesDeps.ext (hx : ∃ new, lenv' = new ++ lenv ∧
      ∀ kn ∈ new.map (·.1), lenv.find? (·.1 == kn) = none)
    (h : ErasesDeps E B σ lenv tb) : ErasesDeps E B σ lenv' tb := by
  induction h with
  | box => exact .box
  | bvar => exact .bvar
  | fvar => exact .fvar
  | lambda _ ih => exact .lambda ih
  | letIn _ _ ihv ihb => exact .letIn ihv ihb
  | app _ _ ihf iha => exact .app ihf iha
  | const hc hl hd _ ih =>
    refine .const hc ?_ hd ih
    unfold lookupConst at hl ⊢
    split at hl
    · rename_i d heq
      rw [find?_ext hx heq]
      exact hl
    · cases hl
  | construct hi hind _ ih => exact .construct hi (ErasesInd.ext hx hind) ih
  | case hi hind _ _ ihd ihb => exact .case hi (ErasesInd.ext hx hind) ihd ihb
  | proj hi hind _ ihd => exact .proj hi (ErasesInd.ext hx hind) ihd

/-! ## Substitution -/

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

/-- Dependencies are preserved by substitution. Reference: `erases_deps_subst`
(`MR E/EDeps.v:94`). -/
theorem ErasesDeps.csubst (ha : ErasesDeps E B σ lenv a) (hb : ErasesDeps E B σ lenv b) :
    ErasesDeps E B σ lenv (csubst a k b) := by
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

/-- Substituting terms with erased dependencies. Reference: `erases_deps_substl`
(`MR E/EDeps.v:208`). -/
private theorem ErasesDeps.substl : ∀ {ts : List LBTerm} {b : LBTerm},
    (∀ t ∈ ts, ErasesDeps E B σ lenv t) → ErasesDeps E B σ lenv b →
      ErasesDeps E B σ lenv (EraseProof.substl ts b)
  | [], _, _, hb => hb
  | t :: _, _, hts, hb => by
    simp only [EraseProof.substl, List.foldl_cons]
    exact ErasesDeps.substl (fun u hu => hts u (List.mem_cons_of_mem _ hu))
      (ErasesDeps.csubst (hts t List.mem_cons_self) hb)

/-- An application spine has erased dependencies iff its head and arguments have. Reference:
`erases_deps_mkApps` (`MR E/EDeps.v:17`) and `erases_deps_mkApps_inv` (`:31`). -/
private theorem ErasesDeps.mkApps_iff : ∀ {f : LBTerm} {args : List LBTerm},
    ErasesDeps E B σ lenv (mkApps f args) ↔
      ErasesDeps E B σ lenv f ∧ ∀ a ∈ args, ErasesDeps E B σ lenv a
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
theorem ErasesDeps.eval (h : ErasesDeps E B σ lenv tb) (hev : LBEval defaultFlags lenv tb vb) :
    ErasesDeps E B σ lenv vb := by
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
  | fix _ _ _ _ _ ih1 =>
    cases h with
    | app hf _ =>
      obtain ⟨hfix, -⟩ := ErasesDeps.mkApps_iff.1 (ih1 hf)
      cases hfix
  | fixValue _ _ _ _ _ ih1 =>
    cases h with
    | app hf _ =>
      obtain ⟨hfix, -⟩ := ErasesDeps.mkApps_iff.1 (ih1 hf)
      cases hfix
  | fix' _ _ _ _ _ ih1 =>
    cases h with
    | app hf _ => cases ih1 hf
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
