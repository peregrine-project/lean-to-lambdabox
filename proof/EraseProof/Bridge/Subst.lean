import EraseProof.Bridge.Perm

/-!
# Substitution into the images of the translation

Metalean substitutions (`Expr.subst`, `ML Syntax/Expr.lean:469`) commute with the term builders
that the saturating rules of `TrM` use: the unary literals (`natLitM`), the proof projections
(`projProofTerm`), the minor wrapper (`wrapCase_subst`), and so with every rule of `SatTr`
(`SatTr.subst`). Renamings, weakenings and instantiations are substitutions, so these lemmas serve
the weakening and substitution lemmas of the translation.
-/

open Lean Erasure

namespace EraseProof

section
variable {ζ : Metalean.Sigs} {ℓ n m : Nat}

/-- Substitution leaves a unary literal unchanged (it is closed). -/
theorem natLitM_subst (ηNat : Metalean.Head ζ (.inductive natSig)) (k : Nat)
    (σ : Metalean.Subst ζ ℓ n m) : (natLitM ηNat k : Metalean.Expr ζ ℓ n).subst σ = natLitM ηNat k := by
  induction k with
  | zero =>
    simp only [natLitM, Metalean.Expr.subst]
    congr <;> funext i <;> exact i.elim0
  | succ k ih =>
    simp only [natLitM, Metalean.Expr.subst]
    congr
    all_goals funext i
    all_goals first | exact i.elim0 | (refine Fin.cases ?_ (fun j => j.elim0) i; simpa using ih)

/-- A successful `Fin.mapM` in `Option` from its components. -/
theorem mapM_option_of_eq_some : ∀ {k : Nat} {α : Fin k → Type} {f : ∀ i, Option (α i)}
    {g : ∀ i, α i}, (∀ i, f i = some (g i)) → Fin.mapM (m := Option) (α := α) f = some g
  | 0, _, _, g, _ => by
    simp only [Fin.mapM]
    congr; funext i; exact i.elim0
  | k + 1, α, f, g, h => by
    simp only [Fin.mapM, h 0, mapM_option_of_eq_some (α := fun i => α i.succ)
      (f := fun i : Fin k => f i.succ) (g := fun i => g i.succ) (fun i => h i.succ)]
    exact congrArg some (funext fun i => by obtain ⟨_ | j, hj⟩ := i <;> rfl)

/-- A lifted substitution on a variable of the new block. -/
theorem Subst.liftN_ge (σ : Metalean.Subst ζ ℓ n m) (k : Nat) (v : Fin (n + k)) (h : n ≤ v.val) :
    σ.liftN k v = .var ⟨m + (v.val - n), by omega⟩ := by
  induction k with
  | zero => omega
  | succ k ih =>
    simp only [Metalean.Subst.liftN, Metalean.Subst.lift]
    split
    · rename_i hv
      rw [ih ⟨v.val, hv⟩ h]
      simp [Metalean.Expr.wk, Metalean.Expr.wkFrom, Metalean.Ren.wkFrom]
      omega
    · congr 1; ext; simp; omega

/-- The case substitution lifting (`CtorSig.liftCaseSubst`) on a variable of the case telescope. -/
theorem Subst.liftN₃_ge (σ : Metalean.Subst ζ ℓ n m) (a b c : Nat) (v : Fin (n + a + b + c))
    (h : n ≤ v.val) :
    ((σ.liftN a).liftN b).liftN c v = .var ⟨m + (v.val - n), by omega⟩ := by
  obtain ⟨v, hv⟩ := v
  simp only at h ⊢
  by_cases hc : v < n + a + b
  · show ((σ.liftN a).liftN b).liftN c (Fin.castAdd c ⟨v, hc⟩) = _
    rw [Metalean.Subst.liftN_castAdd]
    by_cases hb : v < n + a
    · show (((σ.liftN a).liftN b) (Fin.castAdd b ⟨v, hb⟩)).wkN c = _
      rw [Metalean.Subst.liftN_castAdd, Subst.liftN_ge σ a _ h]
      simp
    · rw [Subst.liftN_ge (σ.liftN a) b _ (by simp; omega)]
      simp; omega
  · rw [Subst.liftN_ge ((σ.liftN a).liftN b) c _ (by simp; omega)]
    congr 2; simp; omega

/-- `wrapCase` (`ML Frontend/Translate.lean:84`) commutes with substitution. -/
theorem wrapCase_subst {ι : Metalean.IndSig} (I : Metalean.Inductive ζ ι)
    (η : Metalean.Head ζ (.inductive ι)) (ls : Fin ι.nlevels → Metalean.Level ℓ)
    (ps : Fin ι.nparams → Metalean.Expr ζ ℓ n) (ms : Fin ι.nsorts → Metalean.Expr ζ ℓ n)
    (t : Fin ι.nsorts) (c : Fin (ι.nctors t)) (mo : List Nat) {minor w : Metalean.Expr ζ ℓ n}
    (σ : Metalean.Subst ζ ℓ n m) (hw : Metalean.Frontend.wrapCase I η ls ps ms t c mo minor = .ok w) :
    Metalean.Frontend.wrapCase I η ls (fun p => (ps p).subst σ) (fun t => (ms t).subst σ) t c mo
      (minor.subst σ) = .ok (w.subst σ) := by
  unfold Metalean.Frontend.wrapCase at hw ⊢
  dsimp only at hw ⊢
  by_cases hid : Metalean.Frontend.isIdentityOrder mo
      ((ι.ctors t c).nfields + (ι.ctors t c).nrecFields) = true
  · rw [ite_eq_left hid] at hw ⊢
    cases hw
    rfl
  · rw [ite_eq_right hid] at hw ⊢
    rcases hπ : Metalean.Frontend.orderMaps? mo
        ((ι.ctors t c).nfields + (ι.ctors t c).nrecFields) with _ | ⟨π, snd⟩
    · rw [hπ] at hw; cases hw
    · rw [hπ] at hw
      dsimp only at hw ⊢
      obtain ⟨x, hx⟩ : ∃ x, Fin.mapM (m := Option) (fun j => (π j).map fun o =>
          (Metalean.Expr.var ⟨n + o.val, by omega⟩ : Metalean.Expr ζ ℓ
            (n + (ι.ctors t c).nfields + (ι.ctors t c).nrecFields + (ι.ctors t c).nrecFields))) = x :=
        ⟨_, rfl⟩
      rw [hx] at hw
      rcases x with _ | fieldVars
      · cases hw
      · dsimp only at hw
        cases hw
        have hfv := mapM_option_eq_some hx
        rw [mapM_option_of_eq_some (g := fun j => (fieldVars j).subst
          ((((σ.liftN (ι.ctors t c).nfields).liftN (ι.ctors t c).nrecFields).liftN
            (ι.ctors t c).nrecFields))) fun j => ?_]
        · dsimp only
          rw [Metalean.Ctx.lam_subst₃, Metalean.Inductive.caseTele_subst, Metalean.Expr.subst_apps]
          simp only [Metalean.Expr.wkN_subst]
          congr 3
          funext i
          cases i using Fin.addCases with
          | left j => simp
          | right r =>
            simp only [Fin.append_right, Metalean.Expr.subst]
            rw [Subst.liftN₃_ge σ _ _ _ _ (by simp; omega)]
            congr 2; simp; omega
        · have h := hfv j
          simp only [Option.map_eq_some_iff] at h ⊢
          obtain ⟨o, ho, hvar⟩ := h
          refine ⟨o, ho, ?_⟩
          rw [← hvar]
          simp only [Metalean.Expr.subst]
          rw [Subst.liftN₃_ge σ _ _ _ _ (by simp)]
          congr 2; simp

/-- The proof projection `projProofTerm` commutes with substitution. -/
theorem projProofTerm_subst (E : Metalean.Env ζ) {ι : Metalean.IndSig}
    (η : Metalean.Head ζ (.inductive ι)) (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (ls : Fin ι.nlevels → Metalean.Level ℓ) (hi : ι.nindices s = 0) (f : Nat) :
    ∀ {n m : Nat} (ps : Fin ι.nparams → Metalean.Expr ζ ℓ n) (maj : Metalean.Expr ζ ℓ n)
      (σ : Metalean.Subst ζ ℓ n m),
      (projProofTerm E η s c ls hi ps f maj).subst σ =
        projProofTerm E η s c ls hi (fun p => (ps p).subst σ) f (maj.subst σ) := by
  induction f using Nat.strong_induction_on with
  | _ f ih =>
  intro n m ps maj σ
  rw [projProofTerm, projProofTerm]
  simp only [Metalean.Expr.subst]
  congr 1
  · funext t
    refine (Metalean.Ctx.lam_subst (k := ι.nindices s + 1) _ _ _).trans ?_
    rw [Metalean.Inductive.motiveTele_subst]
    congr 1
    split
    · rw [Metalean.Ctor.ordinaryFieldExpr_subst]
      congr 1
      · funext p; exact Metalean.Expr.wkN_subst σ (ps p) _
      · funext j
        split
        · rw [ih j (by omega)]
          congr 1
          · funext p; exact Metalean.Expr.wkN_subst σ (ps p) _
          · exact Metalean.Subst.liftN_last σ _
        · rfl
    · rfl
  · funext t d
    split
    · rename_i hf
      have hco := Metalean.CtorSig.caseOrdinary_subst (ζ := ζ) (ℓ := ℓ) (ι.ctors t d) σ ⟨f, hf⟩
      rw [Metalean.Ctx.lam_subst₃, Metalean.Inductive.caseTele_subst]
      refine congrArg₂ Metalean.Ctx.lam hco ?_
      congr 1
      funext t'
      refine (Metalean.Ctx.lam_subst (k := ι.nindices s + 1) _ _ _).trans ?_
      rw [Metalean.Inductive.motiveTele_subst]
      congr 1
      split
      · rw [Metalean.Ctor.ordinaryFieldExpr_subst]
        congr 1
        · funext p; exact Metalean.Expr.wkN_subst σ (ps p) _
        · funext j
          split
          · rw [ih j (by omega)]
            congr 1
            · funext p; exact Metalean.Expr.wkN_subst σ (ps p) _
            · exact Metalean.Subst.liftN_last σ _
          · rfl
      · rfl
    · rfl
  · funext i; exact absurd i.isLt (by omega)

end

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {lps : List Name}

/-- Every rule of `SatTr` commutes with substitution: the substituted arguments of a saturating
binding give the substituted image. -/
theorem SatTr.subst {n m : Nat} {b : MBinding ζ} {us : List Level}
    {args : List (Metalean.Expr ζ lps.length n)} {t : Metalean.Expr ζ lps.length n}
    (h : SatTr E lps b us args t) (σ : Metalean.Subst ζ lps.length n m) :
    SatTr E lps b us (args.map (·.subst σ)) (t.subst σ) := by
  cases h with
  | indSat ps is rest hls =>
    simpa [List.map_ofFn, Function.comp_def] using
      SatTr.indSat (E := E) (fun p => (ps p).subst σ) (fun i => (is i).subst σ) (rest.map (·.subst σ)) hls
  | indEta hls hlen =>
    simpa [Metalean.Expr.wkClosed_subst] using
      SatTr.indEta (E := E) (args := args.map (·.subst σ)) hls (by simpa using hlen)
  | ctorSat ps fs rest fds recFds hls hfs hord hperm =>
    simpa [List.map_ofFn, Function.comp_def] using
      SatTr.ctorSat (E := E) (fun p => (ps p).subst σ) (fs.map (·.subst σ)) (rest.map (·.subst σ))
        (fun i => (fds i).subst σ) (fun i => (recFds i).subst σ) hls (by simpa using hfs) hord
        fun o => by
          obtain ⟨j, a, h₁, h₂, h₃⟩ := hperm o
          refine ⟨j, a.subst σ, h₁, by simp [h₂], ?_⟩
          rw [← h₃]
          exact (congrFun (Metalean.Subst.append_comp fds recFds σ) o).symm
  | ctorEta hls hlen ht =>
    simpa [Metalean.Expr.wkClosed_subst] using
      SatTr.ctorEta (E := E) (args := args.map (·.subst σ)) hls (by simpa using hlen) ht
  | recrSat mo A rest mins hRL hls hmo hwrap =>
    simpa [List.map_ofFn, Function.comp_def] using
      SatTr.recrSat (E := E) mo (fun i => (A i).subst σ) (rest.map (·.subst σ))
        (fun t c => (mins t c).subst σ) hRL hls hmo
        fun t c => wrapCase_subst _ _ _ _ _ _ _ _ σ (hwrap t c)
  | recrEta mo hRL hls hmo hlen ht =>
    simpa [Metalean.Expr.wkClosed_subst] using
      SatTr.recrEta (E := E) (args := args.map (·.subst σ)) mo hRL hls hmo (by simpa using hlen) ht
  | quotType hu | quotMk hu | quotLift hu | quotInd hu =>
    simp only [List.map_cons, ML.Expr.subst_appList,
      Metalean.Expr.subst, List.cons_append, List.nil_append]
    first | exact .quotType hu | exact .quotMk hu | exact .quotLift hu | exact .quotInd hu
  | quotEta hu hlen ht =>
    simpa [Metalean.Expr.wkClosed_subst] using
      SatTr.quotEta (E := E) (args := args.map (·.subst σ)) hu (by simpa using hlen) ht

end

end EraseProof
