import EraseProof.Spec

/-!
# Closedness, lifting and closed substitution of λ□ terms

The lemmas on `closedn`, `lbLift`, `csubst` and `substl`, and on the let-bindings of a
recursor's erasure (`recLets`), that the closedness and substitution lemmas of the erasure
relation (`EraseProof/Relation/`) use: a verbatim selection of `proof/EraseProof/TargetFacts.lean`,
`TargetLift.lean` and `Relation/Rec.lean` of the Metalean development of this repository (#16,
commit `f3b934f`). Reference: `MR E/ELiftSubst.v` (`closedn_lift`, `lift_closed`, `subst_lift`)
and `MR E/ECSubst.v` (`closed_csubst`).
-/

open Lean Erasure

namespace EraseProof

/-! ## Closed substitutions (`ML-V TargetFacts.lean:202`) -/

namespace TargetSubst

mutual
/-- `csubst` below the closedness bound is the identity. -/
theorem csubst_closedn (f : LBTerm) : ∀ (t : LBTerm) (k j : Nat), closedn k t = true → k ≤ j →
    csubst f j t = t
  | .box, _, _, _, _ => rfl
  | .bvar m, k, j, h, hkj => by
    simp only [closedn, decide_eq_true_eq] at h
    simp only [csubst]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  | .fvar _, _, _, _, _ => rfl
  | .lambda na b, k, j, h, hkj => by
    simp only [closedn] at h
    simp only [csubst, csubst_closedn f b (k + 1) (j + 1) h (by omega)]
  | .letIn na b b', k, j, h, hkj => by
    simp only [closedn, Bool.and_eq_true] at h
    simp only [csubst, csubst_closedn f b k j h.1 hkj, csubst_closedn f b' (k + 1) (j + 1) h.2 (by omega)]
  | .app u v, k, j, h, hkj => by
    simp only [closedn, Bool.and_eq_true] at h
    simp only [csubst, csubst_closedn f u k j h.1 hkj, csubst_closedn f v k j h.2 hkj]
  | .const _, _, _, _, _ => rfl
  | .construct i c args, k, j, h, hkj => by
    simp only [closedn] at h
    simp only [csubst, csubstL_closedn f args k j h hkj]
  | .case ip c brs, k, j, h, hkj => by
    simp only [closedn, Bool.and_eq_true] at h
    simp only [csubst, csubst_closedn f c k j h.1 hkj, csubstB_closedn f brs k j h.2 hkj]
  | .proj p c, k, j, h, hkj => by
    simp only [closedn] at h
    simp only [csubst, csubst_closedn f c k j h hkj]
  | .fix defs i, k, j, h, hkj => by
    simp only [closedn] at h
    simp only [csubst, csubstD_closedn f defs (k + defs.length) (j + defs.length) h (by omega)]
  | .prim _, _, _, _, _ => rfl
theorem csubstL_closedn (f : LBTerm) : ∀ (as : List LBTerm) (k j : Nat), closednL k as = true →
    k ≤ j → csubstL f j as = as
  | [], _, _, _, _ => rfl
  | a :: as, k, j, h, hkj => by
    simp only [closednL, Bool.and_eq_true] at h
    simp only [csubstL, csubst_closedn f a k j h.1 hkj, csubstL_closedn f as k j h.2 hkj]
theorem csubstB_closedn (f : LBTerm) : ∀ (bs : List (List BinderName × LBTerm)) (k j : Nat),
    closednB k bs = true → k ≤ j → csubstB f j bs = bs
  | [], _, _, _, _ => rfl
  | (ns, b) :: bs, k, j, h, hkj => by
    simp only [closednB, Bool.and_eq_true] at h
    simp only [csubstB, csubst_closedn f b (k + ns.length) (j + ns.length) h.1 (by omega),
      csubstB_closedn f bs k j h.2 hkj]
theorem csubstD_closedn (f : LBTerm) : ∀ (ds : List (@FixDef LBTerm)) (k j : Nat),
    closednD k ds = true → k ≤ j → csubstD f j ds = ds
  | [], _, _, _, _ => rfl
  | ⟨nm, b, r⟩ :: ds, k, j, h, hkj => by
    simp only [closednD, Bool.and_eq_true] at h
    simp only [csubstD, csubst_closedn f b k j h.1 hkj, csubstD_closedn f ds k j h.2 hkj]
end

theorem length_csubstD (f : LBTerm) (k : Nat) : ∀ ds : List (@FixDef LBTerm),
    (csubstD f k ds).length = ds.length
  | [] => rfl
  | ⟨_, _, _⟩ :: ds => by simp [csubstD, length_csubstD f k ds]

end TargetSubst

/-! ## Lifting (`ML-V TargetLift.lean:18`) -/

namespace TargetLift

theorem length_lbLiftD (n k : Nat) : ∀ ds : List (@FixDef LBTerm), (lbLiftD n k ds).length = ds.length
  | [] => rfl
  | ⟨_, _, _⟩ :: ds => by simp [lbLiftD, length_lbLiftD n k ds]

mutual
/-- `closedn` is monotone in its bound. Reference: `closed_upwards` (`MR E/ELiftSubst.v`). -/
theorem closedn_mono : ∀ (t : LBTerm) (k k' : Nat), closedn k t = true → k ≤ k' →
    closedn k' t = true
  | .box, _, _, _, _ => rfl
  | .bvar m, k, k', h, hk => by simp only [closedn, decide_eq_true_eq] at h ⊢; omega
  | .fvar _, _, _, _, _ => rfl
  | .lambda _ b, k, k', h, hk => closedn_mono b (k + 1) (k' + 1) h (by omega)
  | .letIn _ b b', k, k', h, hk => by
    simp only [closedn, Bool.and_eq_true] at h ⊢
    exact ⟨closedn_mono b k k' h.1 hk, closedn_mono b' (k + 1) (k' + 1) h.2 (by omega)⟩
  | .app u v, k, k', h, hk => by
    simp only [closedn, Bool.and_eq_true] at h ⊢
    exact ⟨closedn_mono u k k' h.1 hk, closedn_mono v k k' h.2 hk⟩
  | .const _, _, _, _, _ => rfl
  | .construct _ _ args, k, k', h, hk => closednL_mono args k k' h hk
  | .case _ c brs, k, k', h, hk => by
    simp only [closedn, Bool.and_eq_true] at h ⊢
    exact ⟨closedn_mono c k k' h.1 hk, closednB_mono brs k k' h.2 hk⟩
  | .proj _ c, k, k', h, hk => closedn_mono c k k' h hk
  | .fix defs _, k, k', h, hk => closednD_mono defs _ _ h (by omega)
  | .prim _, _, _, _, _ => rfl
theorem closednL_mono : ∀ (as : List LBTerm) (k k' : Nat), closednL k as = true → k ≤ k' →
    closednL k' as = true
  | [], _, _, _, _ => rfl
  | a :: as, k, k', h, hk => by
    simp only [closednL, Bool.and_eq_true] at h ⊢
    exact ⟨closedn_mono a k k' h.1 hk, closednL_mono as k k' h.2 hk⟩
theorem closednB_mono : ∀ (bs : List (List BinderName × LBTerm)) (k k' : Nat),
    closednB k bs = true → k ≤ k' → closednB k' bs = true
  | [], _, _, _, _ => rfl
  | (ns, b) :: bs, k, k', h, hk => by
    simp only [closednB, Bool.and_eq_true] at h ⊢
    exact ⟨closedn_mono b _ _ h.1 (by omega), closednB_mono bs k k' h.2 hk⟩
theorem closednD_mono : ∀ (ds : List (@FixDef LBTerm)) (k k' : Nat), closednD k ds = true →
    k ≤ k' → closednD k' ds = true
  | [], _, _, _, _ => rfl
  | ⟨nm, b, r⟩ :: ds, k, k', h, hk => by
    simp only [closednD, Bool.and_eq_true] at h ⊢
    exact ⟨closedn_mono b k k' h.1 hk, closednD_mono ds k k' h.2 hk⟩
end

mutual
/-- Lifting from below the bound raises the bound. Reference: `closedn_lift`
(`MR E/ELiftSubst.v`). -/
theorem closedn_lbLift (n : Nat) : ∀ (t : LBTerm) (k j : Nat), closedn k t = true → j ≤ k →
    closedn (k + n) (lbLift n j t) = true
  | .box, _, _, _, _ => rfl
  | .bvar m, k, j, h, hj => by
    simp only [closedn, decide_eq_true_eq] at h
    simp only [lbLift]
    split <;> simp only [closedn, decide_eq_true_eq] <;> omega
  | .fvar _, _, _, _, _ => rfl
  | .lambda _ b, k, j, h, hj => by
    have := closedn_lbLift n b (k + 1) (j + 1) h (by omega)
    simp only [lbLift, closedn]
    rwa [show k + n + 1 = k + 1 + n by omega]
  | .letIn _ b b', k, j, h, hj => by
    simp only [closedn, Bool.and_eq_true] at h
    have h2 := closedn_lbLift n b' (k + 1) (j + 1) h.2 (by omega)
    simp only [lbLift, closedn, Bool.and_eq_true]
    exact ⟨closedn_lbLift n b k j h.1 hj, by rwa [show k + n + 1 = k + 1 + n by omega]⟩
  | .app u v, k, j, h, hj => by
    simp only [closedn, Bool.and_eq_true] at h
    simp only [lbLift, closedn, Bool.and_eq_true]
    exact ⟨closedn_lbLift n u k j h.1 hj, closedn_lbLift n v k j h.2 hj⟩
  | .const _, _, _, _, _ => rfl
  | .construct _ _ args, k, j, h, hj => closednL_lbLift n args k j h hj
  | .case _ c brs, k, j, h, hj => by
    simp only [closedn, Bool.and_eq_true] at h
    simp only [lbLift, closedn, Bool.and_eq_true]
    exact ⟨closedn_lbLift n c k j h.1 hj, closednB_lbLift n brs k j h.2 hj⟩
  | .proj _ c, k, j, h, hj => closedn_lbLift n c k j h hj
  | .fix defs _, k, j, h, hj => by
    simp only [closedn] at h
    have := closednD_lbLift n defs (k + defs.length) (j + defs.length) h (by omega)
    simp only [lbLift, closedn, length_lbLiftD]
    rwa [show k + n + defs.length = k + defs.length + n by omega]
  | .prim _, _, _, _, _ => rfl
theorem closednL_lbLift (n : Nat) : ∀ (as : List LBTerm) (k j : Nat), closednL k as = true →
    j ≤ k → closednL (k + n) (lbLiftL n j as) = true
  | [], _, _, _, _ => rfl
  | a :: as, k, j, h, hj => by
    simp only [closednL, Bool.and_eq_true] at h
    simp only [lbLiftL, closednL, Bool.and_eq_true]
    exact ⟨closedn_lbLift n a k j h.1 hj, closednL_lbLift n as k j h.2 hj⟩
theorem closednB_lbLift (n : Nat) : ∀ (bs : List (List BinderName × LBTerm)) (k j : Nat),
    closednB k bs = true → j ≤ k → closednB (k + n) (lbLiftB n j bs) = true
  | [], _, _, _, _ => rfl
  | (ns, b) :: bs, k, j, h, hj => by
    simp only [closednB, Bool.and_eq_true] at h
    have h1 := closedn_lbLift n b (k + ns.length) (j + ns.length) h.1 (by omega)
    simp only [lbLiftB, closednB, Bool.and_eq_true]
    exact ⟨by rwa [show k + n + ns.length = k + ns.length + n by omega],
      closednB_lbLift n bs k j h.2 hj⟩
theorem closednD_lbLift (n : Nat) : ∀ (ds : List (@FixDef LBTerm)) (k j : Nat),
    closednD k ds = true → j ≤ k → closednD (k + n) (lbLiftD n j ds) = true
  | [], _, _, _, _ => rfl
  | ⟨nm, b, r⟩ :: ds, k, j, h, hj => by
    simp only [closednD, Bool.and_eq_true] at h
    simp only [lbLiftD, closednD, Bool.and_eq_true]
    exact ⟨closedn_lbLift n b k j h.1 hj, closednD_lbLift n ds k j h.2 hj⟩
end

mutual
/-- Lifting above the closedness bound is the identity. Reference: `lift_closed`
(`MR E/ELiftSubst.v`). -/
theorem lbLift_closedn (n : Nat) : ∀ (t : LBTerm) (j : Nat), closedn j t = true →
    lbLift n j t = t
  | .box, _, _ => rfl
  | .bvar m, j, h => by
    simp only [closedn, decide_eq_true_eq] at h
    simp only [lbLift]
    rw [ite_eq_right (by omega)]
  | .fvar _, _, _ => rfl
  | .lambda na b, j, h => by
    simp only [closedn] at h
    simp only [lbLift, lbLift_closedn n b (j + 1) h]
  | .letIn na b b', j, h => by
    simp only [closedn, Bool.and_eq_true] at h
    simp only [lbLift, lbLift_closedn n b j h.1, lbLift_closedn n b' (j + 1) h.2]
  | .app u v, j, h => by
    simp only [closedn, Bool.and_eq_true] at h
    simp only [lbLift, lbLift_closedn n u j h.1, lbLift_closedn n v j h.2]
  | .const _, _, _ => rfl
  | .construct i c args, j, h => by
    simp only [closedn] at h
    simp only [lbLift, lbLiftL_closedn n args j h]
  | .case ip c brs, j, h => by
    simp only [closedn, Bool.and_eq_true] at h
    simp only [lbLift, lbLift_closedn n c j h.1, lbLiftB_closedn n brs j h.2]
  | .proj p c, j, h => by
    simp only [closedn] at h
    simp only [lbLift, lbLift_closedn n c j h]
  | .fix defs i, j, h => by
    simp only [closedn] at h
    simp only [lbLift, lbLiftD_closedn n defs (j + defs.length) h]
  | .prim _, _, _ => rfl
theorem lbLiftL_closedn (n : Nat) : ∀ (as : List LBTerm) (j : Nat), closednL j as = true →
    lbLiftL n j as = as
  | [], _, _ => rfl
  | a :: as, j, h => by
    simp only [closednL, Bool.and_eq_true] at h
    simp only [lbLiftL, lbLift_closedn n a j h.1, lbLiftL_closedn n as j h.2]
theorem lbLiftB_closedn (n : Nat) : ∀ (bs : List (List BinderName × LBTerm)) (j : Nat),
    closednB j bs = true → lbLiftB n j bs = bs
  | [], _, _ => rfl
  | (ns, b) :: bs, j, h => by
    simp only [closednB, Bool.and_eq_true] at h
    simp only [lbLiftB, lbLift_closedn n b (j + ns.length) h.1, lbLiftB_closedn n bs j h.2]
theorem lbLiftD_closedn (n : Nat) : ∀ (ds : List (@FixDef LBTerm)) (j : Nat),
    closednD j ds = true → lbLiftD n j ds = ds
  | [], _, _ => rfl
  | ⟨nm, b, r⟩ :: ds, j, h => by
    simp only [closednD, Bool.and_eq_true] at h
    simp only [lbLiftD, lbLift_closedn n b j h.1, lbLiftD_closedn n ds j h.2]
end

open TargetSubst in
mutual
/-- Substituting a closed term lowers the bound. Reference: `closed_csubst` (`MR E/ECSubst.v`). -/
theorem closedn_csubst {u : LBTerm} (hu : closedn 0 u = true) : ∀ (b : LBTerm) (k j : Nat),
    closedn (k + 1) b = true → j ≤ k → closedn k (csubst u j b) = true
  | .box, _, _, _, _ => rfl
  | .bvar m, k, j, h, hj => by
    simp only [closedn, decide_eq_true_eq] at h
    simp only [csubst]
    split
    · exact closedn_mono u 0 k hu (Nat.zero_le _)
    · split <;> simp only [closedn, decide_eq_true_eq] <;> omega
  | .fvar _, _, _, _, _ => rfl
  | .lambda _ b, k, j, h, hj => closedn_csubst hu b (k + 1) (j + 1) h (by omega)
  | .letIn _ b b', k, j, h, hj => by
    simp only [closedn, Bool.and_eq_true] at h
    simp only [csubst, closedn, Bool.and_eq_true]
    exact ⟨closedn_csubst hu b k j h.1 hj, closedn_csubst hu b' (k + 1) (j + 1) h.2 (by omega)⟩
  | .app f a, k, j, h, hj => by
    simp only [closedn, Bool.and_eq_true] at h
    simp only [csubst, closedn, Bool.and_eq_true]
    exact ⟨closedn_csubst hu f k j h.1 hj, closedn_csubst hu a k j h.2 hj⟩
  | .const _, _, _, _, _ => rfl
  | .construct _ _ args, k, j, h, hj => closednL_csubst hu args k j h hj
  | .case _ c brs, k, j, h, hj => by
    simp only [closedn, Bool.and_eq_true] at h
    simp only [csubst, closedn, Bool.and_eq_true]
    exact ⟨closedn_csubst hu c k j h.1 hj, closednB_csubst hu brs k j h.2 hj⟩
  | .proj _ c, k, j, h, hj => closedn_csubst hu c k j h hj
  | .fix defs _, k, j, h, hj => by
    simp only [closedn] at h
    simp only [csubst, closedn, length_csubstD]
    exact closednD_csubst hu defs (k + defs.length) (j + defs.length)
      (by rwa [show k + defs.length + 1 = k + 1 + defs.length by omega]) (by omega)
  | .prim _, _, _, _, _ => rfl
theorem closednL_csubst {u : LBTerm} (hu : closedn 0 u = true) : ∀ (as : List LBTerm) (k j : Nat),
    closednL (k + 1) as = true → j ≤ k → closednL k (csubstL u j as) = true
  | [], _, _, _, _ => rfl
  | a :: as, k, j, h, hj => by
    simp only [closednL, Bool.and_eq_true] at h
    simp only [csubstL, closednL, Bool.and_eq_true]
    exact ⟨closedn_csubst hu a k j h.1 hj, closednL_csubst hu as k j h.2 hj⟩
theorem closednB_csubst {u : LBTerm} (hu : closedn 0 u = true) :
    ∀ (bs : List (List BinderName × LBTerm)) (k j : Nat), closednB (k + 1) bs = true → j ≤ k →
      closednB k (csubstB u j bs) = true
  | [], _, _, _, _ => rfl
  | (ns, b) :: bs, k, j, h, hj => by
    simp only [closednB, Bool.and_eq_true] at h
    simp only [csubstB, closednB, Bool.and_eq_true]
    exact ⟨closedn_csubst hu b (k + ns.length) (j + ns.length)
      (by rw [show k + ns.length + 1 = k + 1 + ns.length by omega]; exact h.1) (by omega),
      closednB_csubst hu bs k j h.2 hj⟩
theorem closednD_csubst {u : LBTerm} (hu : closedn 0 u = true) :
    ∀ (ds : List (@FixDef LBTerm)) (k j : Nat), closednD (k + 1) ds = true → j ≤ k →
      closednD k (csubstD u j ds) = true
  | [], _, _, _, _ => rfl
  | ⟨nm, b, r⟩ :: ds, k, j, h, hj => by
    simp only [closednD, Bool.and_eq_true] at h
    simp only [csubstD, closednD, Bool.and_eq_true]
    exact ⟨closedn_csubst hu b k j h.1 hj, closednD_csubst hu ds k j h.2 hj⟩
end

/-- `substl` of closed terms closes the bound they fill. -/
theorem closedn_substl : ∀ (ts : List LBTerm) (b : LBTerm) (k : Nat),
    (∀ t ∈ ts, closedn 0 t = true) → closedn (k + ts.length) b = true →
      closedn k (substl ts b) = true
  | [], _, _, _, h => h
  | t :: ts, b, k, hts, h => by
    show closedn k (substl ts (csubst t 0 b)) = true
    refine closedn_substl ts _ k (fun x hx => hts x (.tail _ hx)) ?_
    refine closedn_csubst (hts t (.head _)) b _ 0 ?_ (Nat.zero_le _)
    simpa [Nat.add_assoc, Nat.add_comm 1] using h

open TargetSubst in
mutual
/-- Substituting a closed term above a lift commutes with it. Reference: `subst_lift`-style
commutations (`MR E/ELiftSubst.v`), for closed substitutions. -/
theorem csubst_lbLift {u : LBTerm} (hu : closedn 0 u = true) (n : Nat) :
    ∀ (t : LBTerm) (d j : Nat), j ≤ d →
      csubst u (d + n) (lbLift n j t) = lbLift n j (csubst u d t)
  | .box, _, _, _ => rfl
  | .bvar m, d, j, hj => by
    simp only [lbLift, csubst]
    by_cases hm : j ≤ m
    · rw [ite_eq_left hm]
      simp only [csubst]
      rcases Nat.lt_trichotomy d m with h | rfl | h
      · rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
        simp only [lbLift]
        rw [ite_eq_left (by omega), show m + n - 1 = m - 1 + n by omega]
      · rw [ite_eq_left rfl, ite_eq_left rfl, lbLift_closedn n u j (TargetLift.closedn_mono u 0 j hu
          (Nat.zero_le _))]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
        simp only [lbLift]
        rw [ite_eq_left hm]
    · rw [ite_eq_right hm]
      simp only [csubst]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      simp only [lbLift]
      rw [ite_eq_right hm]
  | .fvar _, _, _, _ => rfl
  | .lambda na b, d, j, hj => by
    have := csubst_lbLift hu n b (d + 1) (j + 1) (by omega)
    simp only [lbLift, csubst]
    rw [show d + n + 1 = d + 1 + n by omega, this]
  | .letIn na b b', d, j, hj => by
    have := csubst_lbLift hu n b' (d + 1) (j + 1) (by omega)
    simp only [lbLift, csubst]
    rw [show d + n + 1 = d + 1 + n by omega, this, csubst_lbLift hu n b d j hj]
  | .app f a, d, j, hj => by
    simp only [lbLift, csubst, csubst_lbLift hu n f d j hj, csubst_lbLift hu n a d j hj]
  | .const _, _, _, _ => rfl
  | .construct i c args, d, j, hj => by
    simp only [lbLift, csubst, csubstL_lbLift hu n args d j hj]
  | .case ip c brs, d, j, hj => by
    simp only [lbLift, csubst, csubst_lbLift hu n c d j hj, csubstB_lbLift hu n brs d j hj]
  | .proj p c, d, j, hj => by simp only [lbLift, csubst, csubst_lbLift hu n c d j hj]
  | .fix defs i, d, j, hj => by
    have := csubstD_lbLift hu n defs (d + defs.length) (j + defs.length) (by omega)
    simp only [lbLift, csubst, length_lbLiftD, length_csubstD]
    rw [show d + n + defs.length = d + defs.length + n by omega, this]
  | .prim _, _, _, _ => rfl
theorem csubstL_lbLift {u : LBTerm} (hu : closedn 0 u = true) (n : Nat) :
    ∀ (as : List LBTerm) (d j : Nat), j ≤ d →
      csubstL u (d + n) (lbLiftL n j as) = lbLiftL n j (csubstL u d as)
  | [], _, _, _ => rfl
  | a :: as, d, j, hj => by
    simp only [lbLiftL, csubstL, csubst_lbLift hu n a d j hj, csubstL_lbLift hu n as d j hj]
theorem csubstB_lbLift {u : LBTerm} (hu : closedn 0 u = true) (n : Nat) :
    ∀ (bs : List (List BinderName × LBTerm)) (d j : Nat), j ≤ d →
      csubstB u (d + n) (lbLiftB n j bs) = lbLiftB n j (csubstB u d bs)
  | [], _, _, _ => rfl
  | (ns, b) :: bs, d, j, hj => by
    have := csubst_lbLift hu n b (d + ns.length) (j + ns.length) (by omega)
    simp only [lbLiftB, csubstB]
    rw [show d + n + ns.length = d + ns.length + n by omega, this, csubstB_lbLift hu n bs d j hj]
theorem csubstD_lbLift {u : LBTerm} (hu : closedn 0 u = true) (n : Nat) :
    ∀ (ds : List (@FixDef LBTerm)) (d j : Nat), j ≤ d →
      csubstD u (d + n) (lbLiftD n j ds) = lbLiftD n j (csubstD u d ds)
  | [], _, _, _ => rfl
  | ⟨nm, b, r⟩ :: ds, d, j, hj => by
    simp only [lbLiftD, csubstD, csubst_lbLift hu n b d j hj, csubstD_lbLift hu n ds d j hj]
end

end TargetLift

/-! ## The let-bindings of a recursor's erasure (`ML-V Relation/Rec.lean:17`) -/

namespace RecLam

open TargetLift TargetSubst

theorem recLets_cons (d : Nat) (m : LBTerm) (mi : RecMinor) (ms : List (LBTerm × RecMinor))
    (b : LBTerm) :
    recLets d ((m, mi) :: ms) b = .letIn (binderNameOf mi.name) (lbLift d 0 m) (recLets (d + 1) ms b) :=
  rfl

/-- The bindings are closed under `k` when the minors are and the body is under the bindings. -/
theorem closedn_recLets : ∀ (ms : List (LBTerm × RecMinor)) (d k : Nat) (b : LBTerm),
    (∀ p ∈ ms, closedn k p.1 = true) → closedn (k + d + ms.length) b = true →
      closedn (k + d) (recLets d ms b) = true
  | [], d, k, b, _, hb => hb
  | (m, mi) :: ms, d, k, b, hm, hb => by
    rw [recLets_cons]
    simp only [closedn, Bool.and_eq_true]
    refine ⟨closedn_lbLift d m k 0 (hm _ (.head _)) (Nat.zero_le _), ?_⟩
    have := closedn_recLets ms (d + 1) k b (fun p hp => hm p (.tail _ hp))
      (by simpa [Nat.add_assoc, Nat.add_comm 1] using hb)
    rwa [show k + (d + 1) = k + d + 1 by omega] at this

/-- A closed substitution in the bindings substitutes in the minors and, under the bindings, in
the body. -/
theorem csubst_recLets {u : LBTerm} (hu : closedn 0 u = true) :
    ∀ (ms : List (LBTerm × RecMinor)) (d k : Nat) (b : LBTerm),
      csubst u (k + d) (recLets d ms b) =
        recLets d (ms.map (Prod.map (csubst u k) id)) (csubst u (k + d + ms.length) b)
  | [], d, k, b => rfl
  | (m, mi) :: ms, d, k, b => by
    rw [List.map_cons, Prod.map, recLets_cons, recLets_cons]
    simp only [csubst, id]
    rw [csubst_lbLift hu d m k 0 (Nat.zero_le _),
      show k + d + 1 = k + (d + 1) by omega, csubst_recLets hu ms (d + 1) k b]
    simp only [List.length_cons, show k + (d + 1) + ms.length = k + d + (ms.length + 1) by omega]

/-- `closedn` of an application spine. -/
theorem closedn_mkApps {k : Nat} : ∀ {f : LBTerm} {as : List LBTerm},
    closedn k (mkApps f as) = true ↔ closedn k f = true ∧ ∀ a ∈ as, closedn k a = true
  | _, [] => by simp [mkApps]
  | _, a :: as => by
    rw [mkApps, closedn_mkApps]
    simp only [closedn, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp, and_assoc]

theorem csubst_mkApps (t : LBTerm) (k : Nat) :
    ∀ (f : LBTerm) (as : List LBTerm), csubst t k (mkApps f as) = mkApps (csubst t k f) (as.map (csubst t k))
  | _, [] => rfl
  | f, a :: as => by
    rw [mkApps, csubst_mkApps t k (.app f a) as]
    simp [csubst, mkApps]

/-- The let-bound form of `Erases.recLet`. -/
abbrev recLetTerm (N : Nat) (mins' : List LBTerm) (minors : List RecMinor) (F : LBTerm)
    (is' : List LBTerm) (maj' : LBTerm) (extra' : List LBTerm) : LBTerm :=
  mkApps (recLets 0 (mins'.zip minors) (mkApps F ((is' ++ [maj']).map (lbLift N 0)))) extra'

/-- A closed substitution in the let-bound form substitutes in the parts. -/
theorem csubst_recLetTerm {u : LBTerm} (hu : closedn 0 u = true) (d N : Nat) {mins' : List LBTerm}
    {minors : List RecMinor} {F : LBTerm} {is' : List LBTerm} {maj' : LBTerm}
    {extra' : List LBTerm} (hz : (mins'.zip minors).length = N) (hF : closedn N F = true) :
    csubst u d (recLetTerm N mins' minors F is' maj' extra') =
      recLetTerm N (mins'.map (csubst u d)) minors F (is'.map (csubst u d)) (csubst u d maj')
        (extra'.map (csubst u d)) := by
  unfold recLetTerm
  rw [csubst_mkApps]
  congr 1
  have := csubst_recLets hu (mins'.zip minors) 0 d (mkApps F ((is' ++ [maj']).map (lbLift N 0)))
  rw [Nat.add_zero] at this
  rw [this, ← List.zip_map_left, hz, csubst_mkApps,
    csubst_closedn u F N (d + N) hF (by omega)]
  congr 2
  simp only [List.map_append, List.map_map, List.map_cons, List.map_nil]
  congr 1
  · refine List.map_congr_left fun a _ => ?_
    exact csubst_lbLift hu N a d 0 (Nat.zero_le _)
  · rw [csubst_lbLift hu N maj' d 0 (Nat.zero_le _)]

end RecLam

end EraseProof
