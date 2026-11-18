import EraseProof.Spec

/-!
# Closedness, lifting, free variables and closed substitution of λ□ terms

The lemmas on `closedn`, `lbLift`, `hasFVar`, `csubst`, `substl` and the traversal's abstraction
of a free variable (`toBvar`), and on the let-bindings of a recursor's erasure (`recLets`), that
the closedness, substitution and abstraction lemmas of the erasure relation
(`EraseProof/Relation/`) use: a verbatim selection of `proof/EraseProof/TargetFacts.lean`,
`TargetLift.lean`, `Relation/Rec.lean` and `Bridge/Basic.lean` (`fvarId_beq_iff`) of the Metalean
development of this repository (#16, commit `f3b934f`). Reference: `MR E/ELiftSubst.v` (`closedn_lift`, `lift_closed`, `subst_lift`)
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

/-- The derived `BEq` of free variables is equality. Copy of `ML-V Bridge/Basic.lean:35`. -/
theorem fvarId_beq_iff (x y : FVarId) : (x == y) = true ↔ x = y := by
  cases x; cases y
  show instBEqFVarId.beq _ _ = true ↔ _
  simp [instBEqFVarId.beq]

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

/-! ## Free variables and the abstraction of a free variable (`ML-V TargetLift.lean:128`) -/

mutual
/-- A lifted term closed under the raised bound is closed under the bound. -/
theorem closedn_of_lbLift (n : Nat) : ∀ (t : LBTerm) (k j : Nat),
    closedn (k + n) (lbLift n j t) = true → j ≤ k → closedn k t = true
  | .box, _, _, _, _ => rfl
  | .bvar m, k, j, h, hj => by
    simp only [lbLift] at h
    split at h <;> simp only [closedn, decide_eq_true_eq] at h ⊢ <;> omega
  | .fvar _, _, _, _, _ => rfl
  | .lambda _ b, k, j, h, hj => by
    simp only [lbLift, closedn] at h
    exact closedn_of_lbLift n b (k + 1) (j + 1) (by rwa [show k + 1 + n = k + n + 1 by omega])
      (by omega)
  | .letIn _ b b', k, j, h, hj => by
    simp only [lbLift, closedn, Bool.and_eq_true] at h
    simp only [closedn, Bool.and_eq_true]
    exact ⟨closedn_of_lbLift n b k j h.1 hj, closedn_of_lbLift n b' (k + 1) (j + 1)
      (by rw [show k + 1 + n = k + n + 1 by omega]; exact h.2) (by omega)⟩
  | .app u v, k, j, h, hj => by
    simp only [lbLift, closedn, Bool.and_eq_true] at h
    simp only [closedn, Bool.and_eq_true]
    exact ⟨closedn_of_lbLift n u k j h.1 hj, closedn_of_lbLift n v k j h.2 hj⟩
  | .const _, _, _, _, _ => rfl
  | .construct _ _ args, k, j, h, hj => closednL_of_lbLift n args k j h hj
  | .case _ c brs, k, j, h, hj => by
    simp only [lbLift, closedn, Bool.and_eq_true] at h
    simp only [closedn, Bool.and_eq_true]
    exact ⟨closedn_of_lbLift n c k j h.1 hj, closednB_of_lbLift n brs k j h.2 hj⟩
  | .proj _ c, k, j, h, hj => closedn_of_lbLift n c k j h hj
  | .fix defs _, k, j, h, hj => by
    simp only [lbLift, closedn, length_lbLiftD] at h
    simp only [closedn]
    exact closednD_of_lbLift n defs (k + defs.length) (j + defs.length)
      (by rwa [show k + defs.length + n = k + n + defs.length by omega]) (by omega)
  | .prim _, _, _, _, _ => rfl
theorem closednL_of_lbLift (n : Nat) : ∀ (as : List LBTerm) (k j : Nat),
    closednL (k + n) (lbLiftL n j as) = true → j ≤ k → closednL k as = true
  | [], _, _, _, _ => rfl
  | a :: as, k, j, h, hj => by
    simp only [lbLiftL, closednL, Bool.and_eq_true] at h
    simp only [closednL, Bool.and_eq_true]
    exact ⟨closedn_of_lbLift n a k j h.1 hj, closednL_of_lbLift n as k j h.2 hj⟩
theorem closednB_of_lbLift (n : Nat) : ∀ (bs : List (List BinderName × LBTerm)) (k j : Nat),
    closednB (k + n) (lbLiftB n j bs) = true → j ≤ k → closednB k bs = true
  | [], _, _, _, _ => rfl
  | (ns, b) :: bs, k, j, h, hj => by
    simp only [lbLiftB, closednB, Bool.and_eq_true] at h
    simp only [closednB, Bool.and_eq_true]
    exact ⟨closedn_of_lbLift n b (k + ns.length) (j + ns.length)
      (by rw [show k + ns.length + n = k + n + ns.length by omega]; exact h.1) (by omega),
      closednB_of_lbLift n bs k j h.2 hj⟩
theorem closednD_of_lbLift (n : Nat) : ∀ (ds : List (@FixDef LBTerm)) (k j : Nat),
    closednD (k + n) (lbLiftD n j ds) = true → j ≤ k → closednD k ds = true
  | [], _, _, _, _ => rfl
  | ⟨nm, b, r⟩ :: ds, k, j, h, hj => by
    simp only [lbLiftD, closednD, Bool.and_eq_true] at h
    simp only [closednD, Bool.and_eq_true]
    exact ⟨closedn_of_lbLift n b k j h.1 hj, closednD_of_lbLift n ds k j h.2 hj⟩
end

mutual
/-- Lifting keeps the free variables. -/
theorem hasFVar_lbLift (x : FVarId) (n : Nat) : ∀ (t : LBTerm) (k : Nat),
    hasFVar x (lbLift n k t) = hasFVar x t
  | .box, _ => rfl
  | .bvar m, k => by simp only [lbLift]; split <;> rfl
  | .fvar _, _ => rfl
  | .lambda _ b, k => hasFVar_lbLift x n b (k + 1)
  | .letIn _ b b', k => by
    simp only [lbLift, hasFVar, hasFVar_lbLift x n b k, hasFVar_lbLift x n b' (k + 1)]
  | .app u v, k => by simp only [lbLift, hasFVar, hasFVar_lbLift x n u k, hasFVar_lbLift x n v k]
  | .const _, _ => rfl
  | .construct _ _ args, k => hasFVarL_lbLift x n args k
  | .case _ c brs, k => by
    simp only [lbLift, hasFVar, hasFVar_lbLift x n c k, hasFVarB_lbLift x n brs k]
  | .proj _ c, k => hasFVar_lbLift x n c k
  | .fix defs _, k => hasFVarD_lbLift x n defs _
  | .prim _, _ => rfl
theorem hasFVarL_lbLift (x : FVarId) (n : Nat) : ∀ (as : List LBTerm) (k : Nat),
    hasFVarL x (lbLiftL n k as) = hasFVarL x as
  | [], _ => rfl
  | a :: as, k => by simp only [lbLiftL, hasFVarL, hasFVar_lbLift x n a k, hasFVarL_lbLift x n as k]
theorem hasFVarB_lbLift (x : FVarId) (n : Nat) : ∀ (bs : List (List BinderName × LBTerm)) (k : Nat),
    hasFVarB x (lbLiftB n k bs) = hasFVarB x bs
  | [], _ => rfl
  | (ns, b) :: bs, k => by
    simp only [lbLiftB, hasFVarB, hasFVar_lbLift x n b _, hasFVarB_lbLift x n bs k]
theorem hasFVarD_lbLift (x : FVarId) (n : Nat) : ∀ (ds : List (@FixDef LBTerm)) (k : Nat),
    hasFVarD x (lbLiftD n k ds) = hasFVarD x ds
  | [], _ => rfl
  | ⟨nm, b, r⟩ :: ds, k => by
    simp only [lbLiftD, hasFVarD, hasFVar_lbLift x n b k, hasFVarD_lbLift x n ds k]
end

mutual
/-- Substituting a term without the free variable `x` adds no `x`. -/
theorem hasFVar_csubst (x : FVarId) {u : LBTerm} (hu : hasFVar x u = false) :
    ∀ (b : LBTerm) (k : Nat), hasFVar x b = false → hasFVar x (csubst u k b) = false
  | .box, _, _ => rfl
  | .bvar m, k, _ => by
    simp only [csubst]
    split
    · exact hu
    · split <;> rfl
  | .fvar _, _, h => h
  | .lambda _ b, k, h => hasFVar_csubst x hu b (k + 1) h
  | .letIn _ b b', k, h => by
    simp only [hasFVar, Bool.or_eq_false_iff] at h
    simp only [csubst, hasFVar, Bool.or_eq_false_iff]
    exact ⟨hasFVar_csubst x hu b k h.1, hasFVar_csubst x hu b' (k + 1) h.2⟩
  | .app f a, k, h => by
    simp only [hasFVar, Bool.or_eq_false_iff] at h
    simp only [csubst, hasFVar, Bool.or_eq_false_iff]
    exact ⟨hasFVar_csubst x hu f k h.1, hasFVar_csubst x hu a k h.2⟩
  | .const _, _, _ => rfl
  | .construct _ _ args, k, h => hasFVarL_csubst x hu args k h
  | .case _ c brs, k, h => by
    simp only [hasFVar, Bool.or_eq_false_iff] at h
    simp only [csubst, hasFVar, Bool.or_eq_false_iff]
    exact ⟨hasFVar_csubst x hu c k h.1, hasFVarB_csubst x hu brs k h.2⟩
  | .proj _ c, k, h => hasFVar_csubst x hu c k h
  | .fix defs _, k, h => hasFVarD_csubst x hu defs _ h
  | .prim _, _, _ => rfl
theorem hasFVarL_csubst (x : FVarId) {u : LBTerm} (hu : hasFVar x u = false) :
    ∀ (as : List LBTerm) (k : Nat), hasFVarL x as = false → hasFVarL x (csubstL u k as) = false
  | [], _, _ => rfl
  | a :: as, k, h => by
    simp only [hasFVarL, Bool.or_eq_false_iff] at h
    simp only [csubstL, hasFVarL, Bool.or_eq_false_iff]
    exact ⟨hasFVar_csubst x hu a k h.1, hasFVarL_csubst x hu as k h.2⟩
theorem hasFVarB_csubst (x : FVarId) {u : LBTerm} (hu : hasFVar x u = false) :
    ∀ (bs : List (List BinderName × LBTerm)) (k : Nat), hasFVarB x bs = false →
      hasFVarB x (csubstB u k bs) = false
  | [], _, _ => rfl
  | (ns, b) :: bs, k, h => by
    simp only [hasFVarB, Bool.or_eq_false_iff] at h
    simp only [csubstB, hasFVarB, Bool.or_eq_false_iff]
    exact ⟨hasFVar_csubst x hu b _ h.1, hasFVarB_csubst x hu bs k h.2⟩
theorem hasFVarD_csubst (x : FVarId) {u : LBTerm} (hu : hasFVar x u = false) :
    ∀ (ds : List (@FixDef LBTerm)) (k : Nat), hasFVarD x ds = false →
      hasFVarD x (csubstD u k ds) = false
  | [], _, _ => rfl
  | ⟨nm, b, r⟩ :: ds, k, h => by
    simp only [hasFVarD, Bool.or_eq_false_iff] at h
    simp only [csubstD, hasFVarD, Bool.or_eq_false_iff]
    exact ⟨hasFVar_csubst x hu b k h.1, hasFVarD_csubst x hu ds k h.2⟩
end

/-- `substl` of terms without the free variable `x` adds no `x`. -/
theorem hasFVar_substl (x : FVarId) : ∀ (ts : List LBTerm) (b : LBTerm),
    (∀ t ∈ ts, hasFVar x t = false) → hasFVar x b = false → hasFVar x (substl ts b) = false
  | [], _, _, h => h
  | t :: ts, b, hts, h =>
    hasFVar_substl x ts _ (fun y hy => hts y (.tail _ hy))
      (hasFVar_csubst x (hts t (.head _)) b 0 h)

theorem length_toBvarDefs (x : FVarId) (k : Nat) :
    ∀ ds : List (@FixDef LBTerm), (toBvarDefs x k ds).length = ds.length
  | [] => rfl
  | _ :: ds => by simp only [toBvarDefs, List.length_cons, length_toBvarDefs x k ds]

mutual
/-- Abstracting a free variable commutes with lifting below the abstraction level. -/
theorem toBvar_lbLift (x : FVarId) (n : Nat) : ∀ (t : LBTerm) (d j : Nat), j ≤ d →
    toBvar x (d + n) (lbLift n j t) = lbLift n j (toBvar x d t)
  | .box, _, _, _ => rfl
  | .bvar m, d, j, _ => by by_cases hm : j ≤ m <;> simp [lbLift, toBvar, hm]
  | .fvar y, d, j, hj => by
    simp only [lbLift, toBvar]
    split
    · simp only [lbLift, ite_eq_left hj]
    · rfl
  | .lambda na b, d, j, hj => by
    have := toBvar_lbLift x n b (d + 1) (j + 1) (by omega)
    simp only [lbLift, toBvar]
    rw [show d + n + 1 = d + 1 + n by omega, this]
  | .letIn na b b', d, j, hj => by
    have := toBvar_lbLift x n b' (d + 1) (j + 1) (by omega)
    simp only [lbLift, toBvar]
    rw [show d + n + 1 = d + 1 + n by omega, this, toBvar_lbLift x n b d j hj]
  | .app u v, d, j, hj => by
    simp only [lbLift, toBvar, toBvar_lbLift x n u d j hj, toBvar_lbLift x n v d j hj]
  | .const _, _, _, _ => rfl
  | .construct i c args, d, j, hj => by
    simp only [lbLift, toBvar, toBvarL_lbLift x n args d j hj]
  | .case (_, _) c brs, d, j, hj => by
    simp only [lbLift, toBvar, toBvar_lbLift x n c d j hj, toBvarB_lbLift x n brs d j hj]
  | .proj p c, d, j, hj => by simp only [lbLift, toBvar, toBvar_lbLift x n c d j hj]
  | .fix defs i, d, j, hj => by
    have := toBvarD_lbLift x n defs (d + defs.length) (j + defs.length) (by omega)
    simp only [lbLift, toBvar, length_lbLiftD, length_toBvarDefs]
    rw [show d + n + defs.length = d + defs.length + n by omega, this]
  | .prim _, _, _, _ => rfl
theorem toBvarL_lbLift (x : FVarId) (n : Nat) : ∀ (as : List LBTerm) (d j : Nat), j ≤ d →
    toBvarList x (d + n) (lbLiftL n j as) = lbLiftL n j (toBvarList x d as)
  | [], _, _, _ => rfl
  | a :: as, d, j, hj => by
    simp only [lbLiftL, toBvarList, toBvar_lbLift x n a d j hj, toBvarL_lbLift x n as d j hj]
theorem toBvarB_lbLift (x : FVarId) (n : Nat) : ∀ (bs : List (List BinderName × LBTerm)) (d j : Nat),
    j ≤ d → toBvarAlts x (d + n) (lbLiftB n j bs) = lbLiftB n j (toBvarAlts x d bs)
  | [], _, _, _ => rfl
  | (ns, b) :: bs, d, j, hj => by
    have := toBvar_lbLift x n b (d + ns.length) (j + ns.length) (by omega)
    simp only [lbLiftB, toBvarAlts]
    rw [show d + n + ns.length = d + ns.length + n by omega, this, toBvarB_lbLift x n bs d j hj]
theorem toBvarD_lbLift (x : FVarId) (n : Nat) : ∀ (ds : List (@FixDef LBTerm)) (d j : Nat),
    j ≤ d → toBvarDefs x (d + n) (lbLiftD n j ds) = lbLiftD n j (toBvarDefs x d ds)
  | [], _, _, _ => rfl
  | ⟨nm, b, r⟩ :: ds, d, j, hj => by
    simp only [lbLiftD, toBvarDefs, toBvar_lbLift x n b d j hj, toBvarD_lbLift x n ds d j hj]
end

mutual
/-- Abstracting a free variable that does not occur is the identity. -/
theorem toBvar_noFVar (x : FVarId) : ∀ (t : LBTerm) (d : Nat), hasFVar x t = false →
    toBvar x d t = t
  | .box, _, _ => rfl
  | .bvar _, _, _ => rfl
  | .fvar y, d, h => by
    simp only [hasFVar] at h
    simp only [toBvar]
    rw [ite_eq_right]
    intro hy
    have := (fvarId_beq_iff y x).mp hy
    subst this
    rw [(fvarId_beq_iff y y).mpr rfl] at h
    cases h
  | .lambda na b, d, h => by simp only [toBvar, toBvar_noFVar x b (d + 1) h]
  | .letIn na b b', d, h => by
    simp only [hasFVar, Bool.or_eq_false_iff] at h
    simp only [toBvar, toBvar_noFVar x b d h.1, toBvar_noFVar x b' (d + 1) h.2]
  | .app u v, d, h => by
    simp only [hasFVar, Bool.or_eq_false_iff] at h
    simp only [toBvar, toBvar_noFVar x u d h.1, toBvar_noFVar x v d h.2]
  | .const _, _, _ => rfl
  | .construct i c args, d, h => by simp only [toBvar, toBvarL_noFVar x args d h]
  | .case (_, _) c brs, d, h => by
    simp only [hasFVar, Bool.or_eq_false_iff] at h
    simp only [toBvar, toBvar_noFVar x c d h.1, toBvarB_noFVar x brs d h.2]
  | .proj p c, d, h => by simp only [toBvar, toBvar_noFVar x c d h]
  | .fix defs i, d, h => by simp only [toBvar, toBvarD_noFVar x defs _ h]
  | .prim _, _, _ => rfl
theorem toBvarL_noFVar (x : FVarId) : ∀ (as : List LBTerm) (d : Nat), hasFVarL x as = false →
    toBvarList x d as = as
  | [], _, _ => rfl
  | a :: as, d, h => by
    simp only [hasFVarL, Bool.or_eq_false_iff] at h
    simp only [toBvarList, toBvar_noFVar x a d h.1, toBvarL_noFVar x as d h.2]
theorem toBvarB_noFVar (x : FVarId) : ∀ (bs : List (List BinderName × LBTerm)) (d : Nat),
    hasFVarB x bs = false → toBvarAlts x d bs = bs
  | [], _, _ => rfl
  | (ns, b) :: bs, d, h => by
    simp only [hasFVarB, Bool.or_eq_false_iff] at h
    simp only [toBvarAlts, toBvar_noFVar x b _ h.1, toBvarB_noFVar x bs d h.2]
theorem toBvarD_noFVar (x : FVarId) : ∀ (ds : List (@FixDef LBTerm)) (d : Nat),
    hasFVarD x ds = false → toBvarDefs x d ds = ds
  | [], _, _ => rfl
  | ⟨nm, b, r⟩ :: ds, d, h => by
    simp only [hasFVarD, Bool.or_eq_false_iff] at h
    simp only [toBvarDefs, toBvar_noFVar x b d h.1, toBvarD_noFVar x ds d h.2]
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

/-- The converse of `closedn_recLets`. -/
theorem closedn_recLets_inv : ∀ (ms : List (LBTerm × RecMinor)) (d k : Nat) (b : LBTerm),
    closedn (k + d) (recLets d ms b) = true →
      (∀ p ∈ ms, closedn k p.1 = true) ∧ closedn (k + d + ms.length) b = true
  | [], d, k, b, h => ⟨fun _ hp => (nomatch hp), h⟩
  | (m, mi) :: ms, d, k, b, h => by
    rw [recLets_cons] at h
    simp only [closedn, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := closedn_recLets_inv ms (d + 1) k b
      (by rw [show k + (d + 1) = k + d + 1 by omega]; exact h.2)
    refine ⟨fun p hp => ?_, by simpa [Nat.add_assoc, Nat.add_comm 1] using h2⟩
    rcases List.mem_cons.1 hp with rfl | hp
    · exact closedn_of_lbLift d m k 0 h.1 (Nat.zero_le _)
    · exact h1 p hp


/-- A free variable of the bindings is one of a minor or of the body. -/
theorem hasFVar_recLets (x : FVarId) : ∀ (ms : List (LBTerm × RecMinor)) (d : Nat) (b : LBTerm),
    hasFVar x (recLets d ms b) = true → (∃ p ∈ ms, hasFVar x p.1 = true) ∨ hasFVar x b = true
  | [], _, _, h => .inr h
  | (m, mi) :: ms, d, b, h => by
    rw [recLets_cons] at h
    simp only [hasFVar, Bool.or_eq_true, hasFVar_lbLift] at h
    rcases h with h | h
    · exact .inl ⟨_, .head _, h⟩
    · rcases hasFVar_recLets x ms (d + 1) b h with ⟨p, hp, h⟩ | h
      · exact .inl ⟨p, .tail _ hp, h⟩
      · exact .inr h

/-- Abstracting a free variable in the bindings abstracts it in the minors and, under the
bindings, in the body. -/
theorem toBvar_recLets (x : FVarId) : ∀ (ms : List (LBTerm × RecMinor)) (d k : Nat) (b : LBTerm),
    _root_.toBvar x (k + d) (recLets d ms b) =
      recLets d (ms.map (Prod.map (_root_.toBvar x k) id))
        (_root_.toBvar x (k + d + ms.length) b)
  | [], d, k, b => rfl
  | (m, mi) :: ms, d, k, b => by
    rw [List.map_cons, Prod.map, recLets_cons, recLets_cons]
    simp only [_root_.toBvar, id]
    rw [toBvar_lbLift x d m k 0 (Nat.zero_le _),
      show k + d + 1 = k + (d + 1) by omega, toBvar_recLets x ms (d + 1) k b]
    simp only [List.length_cons, show k + (d + 1) + ms.length = k + d + (ms.length + 1) by omega]


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


/-- The bindings of closed minors: the lifts are the identity. -/
theorem recLets_closed : ∀ (ms : List (LBTerm × RecMinor)) (d : Nat) (b : LBTerm),
    (∀ p ∈ ms, closedn 0 p.1 = true) →
      recLets d ms b = ms.foldr (fun p b => .letIn (binderNameOf p.2.name) p.1 b) b
  | [], _, _, _ => rfl
  | (m, mi) :: ms, d, b, h => by
    rw [recLets_cons, lbLift_closedn d m 0 (h _ (.head _)),
      recLets_closed ms (d + 1) b (fun p hp => h p (.tail _ hp))]
    rfl


/-- A free variable of an application spine is one of its head or of an argument. -/
theorem hasFVar_mkApps {x : FVarId} : ∀ {f : LBTerm} {as : List LBTerm},
    hasFVar x (mkApps f as) = true → hasFVar x f = true ∨ ∃ a ∈ as, hasFVar x a = true
  | _, [], h => .inl h
  | f, a :: as, h => by
    rcases hasFVar_mkApps (f := .app f a) (as := as) h with h | ⟨b, hb, h⟩
    · simp only [hasFVar, Bool.or_eq_true] at h
      rcases h with h | h
      · exact .inl h
      · exact .inr ⟨a, .head _, h⟩
    · exact .inr ⟨b, .tail _ hb, h⟩

theorem toBvar_mkApps (x : FVarId) (d : Nat) :
    ∀ (f : LBTerm) (as : List LBTerm),
      _root_.toBvar x d (mkApps f as) = mkApps (_root_.toBvar x d f) (as.map (_root_.toBvar x d))
  | _, [] => rfl
  | f, a :: as => by
    rw [mkApps, toBvar_mkApps x d (.app f a) as]
    simp [_root_.toBvar, mkApps]


/-- The fixpoint of `RecFixOf` with closed minors substituted is closed and has no free variable. -/
theorem substl_fix {F : LBTerm} {ws : List LBTerm} (hF : closedn ws.length F = true)
    (hFx : ∀ x, hasFVar x F = false)
    (hws : ∀ w ∈ ws, closedn 0 w = true ∧ ∀ x, hasFVar x w = false) :
    closedn 0 (substl ws.reverse F) = true ∧ ∀ x, hasFVar x (substl ws.reverse F) = false :=
  ⟨closedn_substl _ F 0 (fun w hw => (hws w (List.mem_reverse.1 hw)).1)
      (by simpa using hF),
    fun x => hasFVar_substl x _ F (fun w hw => (hws w (List.mem_reverse.1 hw)).2 x) (hFx x)⟩


/-- Abstracting a free variable in the let-bound form abstracts it in the parts. -/
theorem toBvar_recLetTerm (x : FVarId) (d N : Nat) {mins' : List LBTerm} {minors : List RecMinor}
    {F : LBTerm} {is' : List LBTerm} {maj' : LBTerm} {extra' : List LBTerm}
    (hz : (mins'.zip minors).length = N) (hF : ∀ y, hasFVar y F = false) :
    _root_.toBvar x d (recLetTerm N mins' minors F is' maj' extra') =
      recLetTerm N (mins'.map (_root_.toBvar x d)) minors F (is'.map (_root_.toBvar x d))
        (_root_.toBvar x d maj') (extra'.map (_root_.toBvar x d)) := by
  unfold recLetTerm
  rw [toBvar_mkApps]
  congr 1
  have := toBvar_recLets x (mins'.zip minors) 0 d
    (mkApps F ((is' ++ [maj']).map (lbLift N 0)))
  rw [Nat.add_zero] at this
  rw [this, ← List.zip_map_left, hz, toBvar_mkApps, toBvar_noFVar x F _ (hF x)]
  congr 2
  simp only [List.map_append, List.map_map, List.map_cons, List.map_nil]
  congr 1
  · refine List.map_congr_left fun a _ => ?_
    exact toBvar_lbLift x N a d 0 (Nat.zero_le _)
  · rw [toBvar_lbLift x N maj' d 0 (Nat.zero_le _)]


/-- An element of the first list of a zip with a list at least as long. -/
theorem mem_zip_left {α β : Type} : ∀ {l₁ : List α} {l₂ : List β} {a : α},
    l₁.length ≤ l₂.length → a ∈ l₁ → ∃ b, (a, b) ∈ l₁.zip l₂
  | _ :: _, [], _, h, _ => by simp at h
  | x :: l₁, y :: l₂, a, h, ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨y, by simp⟩
    · obtain ⟨b, hb⟩ := mem_zip_left (l₂ := l₂) (by simp at h; omega) ha
      exact ⟨b, by simp [hb]⟩

/-- The parts of a closed let-bound form are closed. -/
theorem closedn_recLetTerm_inv {d N : Nat} {mins' : List LBTerm} {minors : List RecMinor}
    {F : LBTerm} {is' : List LBTerm} {maj' : LBTerm} {extra' : List LBTerm}
    (hlen : mins'.length ≤ minors.length) (hz : (mins'.zip minors).length = N)
    (h : closedn d (recLetTerm N mins' minors F is' maj' extra') = true) :
    (∀ a ∈ mins', closedn d a = true) ∧ (∀ a ∈ is', closedn d a = true) ∧ closedn d maj' = true ∧
      ∀ a ∈ extra', closedn d a = true := by
  unfold recLetTerm at h
  obtain ⟨h1, h2⟩ := closedn_mkApps.1 h
  have h1' := closedn_recLets_inv (mins'.zip minors) 0 d _ (by simpa using h1)
  rw [Nat.add_zero, hz] at h1'
  obtain ⟨hm, hb⟩ := h1'
  obtain ⟨-, hargs⟩ := closedn_mkApps.1 hb
  have harg : ∀ a ∈ is' ++ [maj'], closedn d a = true := fun a ha =>
    closedn_of_lbLift N a d 0 (hargs _ (by
      have := List.mem_map_of_mem (f := lbLift N 0) ha
      simpa using this)) (Nat.zero_le _)
  refine ⟨fun a ha => ?_, fun a ha => harg a (by simp [ha]), harg maj' (by simp), h2⟩
  obtain ⟨b, hb⟩ := mem_zip_left hlen ha
  exact hm _ hb

/-- A free variable of the let-bound form is one of its parts. -/
theorem hasFVar_recLetTerm {x : FVarId} {N : Nat} {mins' : List LBTerm} {minors : List RecMinor}
    {F : LBTerm} {is' : List LBTerm} {maj' : LBTerm} {extra' : List LBTerm}
    (hF : ∀ y, hasFVar y F = false)
    (h : hasFVar x (recLetTerm N mins' minors F is' maj' extra') = true) :
    (∃ a ∈ mins', hasFVar x a = true) ∨ (∃ a ∈ is', hasFVar x a = true) ∨ hasFVar x maj' = true ∨
      ∃ a ∈ extra', hasFVar x a = true := by
  unfold recLetTerm at h
  rcases hasFVar_mkApps h with h | h
  · rcases hasFVar_recLets x _ 0 _ h with ⟨p, hp, h⟩ | h
    · exact .inl ⟨p.1, (List.of_mem_zip hp).1, h⟩
    · rcases hasFVar_mkApps h with h | ⟨a, ha, h⟩
      · rw [hF x] at h; cases h
      · obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.1 ha
        rw [hasFVar_lbLift] at h
        rcases List.mem_append.1 ha₀ with ha₀ | ha₀
        · exact .inr (.inl ⟨a₀, ha₀, h⟩)
        · rw [List.mem_singleton.1 ha₀] at h; exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr h))


end RecLam

end EraseProof
