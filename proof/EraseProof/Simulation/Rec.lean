import EraseProof.Simulation.Ind
import EraseProof.Simulation.RecFix

/-!
# The recursor ι case of the relation-level simulation

A saturated recursor of a single inductive without indices (`SrcEval.recIota`) is erased to the λ□
fixpoint of `recFix` under `let`s of its erased minors (`Erases.recLet`), or with erased minors
substituted (`Erases.recFix`). The λ□ evaluation binds the minors' values, unfolds the fixpoint on
the major's value (a Nat literal's being λ□'s constructor chain), selects the constructor's
alternative (a λ□ `case`, or, in the `direct` form, the alternative of a constructor without
fields) and applies the minor's value to the fields and to the recursive calls on the recursive
fields, which are erasures of the source induction hypotheses at the minors' values (in the form of
the input). The let-bound minors need not be closed: each binding is lifted over the ones before it,
and a substitution below the bindings removes one lift (`SimRec.csubst_recLets_succ`). Adapted from
`ML-V Simulation/Rec.lean`: no `□` alternative, no typed translation; the shapes ML-V reads from
Metalean's inductive blocks are `recShape`'s (`SimRec.recShape_spec`) and the environment conditions
`RecsShaped` (a motive binding the major premise only, the inductive's parameter count) and
`NatCtors`. Reference: none (MetaRocq has no recursors; DV-30); the λ□ steps are `eval_zeta`,
`eval_fix`, `eval_beta` and `eval_iota` (`MR E/EWcbvEval.v`).
-/

open Lean Erasure

namespace EraseProof

namespace SimRec

open TargetSubst TargetLift RecEval RecFix

variable {cert : BoxCert} {σ : EvalEnv} {lenv : GlobalDeclarations}

/-! ## λ□: lifts and the let-bindings of the minors -/

mutual
/-- A lift by zero is the identity. Reference: `lift0_id` (`MR E/ELiftSubst.v`). -/
theorem lbLift_zero : ∀ (t : LBTerm) (j : Nat), lbLift 0 j t = t
  | .box, _ | .fvar _, _ | .const _, _ | .prim _, _ => rfl
  | .bvar m, j => by simp only [lbLift]; split <;> rfl
  | .lambda na b, j => by simp only [lbLift, lbLift_zero b (j + 1)]
  | .letIn na b b', j => by simp only [lbLift, lbLift_zero b j, lbLift_zero b' (j + 1)]
  | .app f a, j => by simp only [lbLift, lbLift_zero f j, lbLift_zero a j]
  | .construct i c args, j => by simp only [lbLift, lbLiftL_zero args j]
  | .case ip c brs, j => by simp only [lbLift, lbLift_zero c j, lbLiftB_zero brs j]
  | .proj p c, j => by simp only [lbLift, lbLift_zero c j]
  | .fix defs i, j => by simp only [lbLift, lbLiftD_zero defs (j + defs.length)]
theorem lbLiftL_zero : ∀ (as : List LBTerm) (j : Nat), lbLiftL 0 j as = as
  | [], _ => rfl
  | a :: as, j => by simp only [lbLiftL, lbLift_zero a j, lbLiftL_zero as j]
theorem lbLiftB_zero : ∀ (bs : List (List BinderName × LBTerm)) (j : Nat), lbLiftB 0 j bs = bs
  | [], _ => rfl
  | (ns, b) :: bs, j => by simp only [lbLiftB, lbLift_zero b (j + ns.length), lbLiftB_zero bs j]
theorem lbLiftD_zero : ∀ (ds : List (@FixDef LBTerm)) (j : Nat), lbLiftD 0 j ds = ds
  | [], _ => rfl
  | ⟨nm, b, r⟩ :: ds, j => by simp only [lbLiftD, lbLift_zero b j, lbLiftD_zero ds j]
end

mutual
/-- A substitution at an index the lift skipped removes one lift. Reference: `simpl_subst_rec`
(`MR E/ELiftSubst.v`), for `csubst`. -/
theorem csubst_lbLift_succ (u : LBTerm) (n : Nat) :
    ∀ (t : LBTerm) (j k : Nat), j ≤ k → k ≤ j + n → csubst u k (lbLift (n + 1) j t) = lbLift n j t
  | .box, _, _, _, _ | .fvar _, _, _, _, _ | .const _, _, _, _, _ | .prim _, _, _, _, _ => rfl
  | .bvar m, j, k, h1, h2 => by
    simp only [lbLift]
    by_cases hm : j ≤ m
    · simp only [hm, ↓reduceIte, csubst]
      rw [ite_eq_right (by omega), ite_eq_left (by omega)]
      congr 1
    · simp only [hm, ↓reduceIte, csubst]
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  | .lambda na b, j, k, h1, h2 => by
    simp only [lbLift, csubst, csubst_lbLift_succ u n b (j + 1) (k + 1) (by omega) (by omega)]
  | .letIn na b b', j, k, h1, h2 => by
    simp only [lbLift, csubst, csubst_lbLift_succ u n b j k h1 h2,
      csubst_lbLift_succ u n b' (j + 1) (k + 1) (by omega) (by omega)]
  | .app f a, j, k, h1, h2 => by
    simp only [lbLift, csubst, csubst_lbLift_succ u n f j k h1 h2,
      csubst_lbLift_succ u n a j k h1 h2]
  | .construct i c args, j, k, h1, h2 => by
    simp only [lbLift, csubst, csubstL_lbLift_succ u n args j k h1 h2]
  | .case ip c brs, j, k, h1, h2 => by
    simp only [lbLift, csubst, csubst_lbLift_succ u n c j k h1 h2,
      csubstB_lbLift_succ u n brs j k h1 h2]
  | .proj p c, j, k, h1, h2 => by simp only [lbLift, csubst, csubst_lbLift_succ u n c j k h1 h2]
  | .fix defs i, j, k, h1, h2 => by
    simp only [lbLift, csubst, length_lbLiftD,
      csubstD_lbLift_succ u n defs (j + defs.length) (k + defs.length) (by omega) (by omega)]
theorem csubstL_lbLift_succ (u : LBTerm) (n : Nat) :
    ∀ (as : List LBTerm) (j k : Nat), j ≤ k → k ≤ j + n →
      csubstL u k (lbLiftL (n + 1) j as) = lbLiftL n j as
  | [], _, _, _, _ => rfl
  | a :: as, j, k, h1, h2 => by
    simp only [lbLiftL, csubstL, csubst_lbLift_succ u n a j k h1 h2,
      csubstL_lbLift_succ u n as j k h1 h2]
theorem csubstB_lbLift_succ (u : LBTerm) (n : Nat) :
    ∀ (bs : List (List BinderName × LBTerm)) (j k : Nat), j ≤ k → k ≤ j + n →
      csubstB u k (lbLiftB (n + 1) j bs) = lbLiftB n j bs
  | [], _, _, _, _ => rfl
  | (ns, b) :: bs, j, k, h1, h2 => by
    simp only [lbLiftB, csubstB, csubst_lbLift_succ u n b (j + ns.length) (k + ns.length)
      (by omega) (by omega), csubstB_lbLift_succ u n bs j k h1 h2]
theorem csubstD_lbLift_succ (u : LBTerm) (n : Nat) :
    ∀ (ds : List (@FixDef LBTerm)) (j k : Nat), j ≤ k → k ≤ j + n →
      csubstD u k (lbLiftD (n + 1) j ds) = lbLiftD n j ds
  | [], _, _, _, _ => rfl
  | ⟨nm, b, r⟩ :: ds, j, k, h1, h2 => by
    simp only [lbLiftD, csubstD, csubst_lbLift_succ u n b j k h1 h2,
      csubstD_lbLift_succ u n ds j k h1 h2]
end

/-- A substitution below the bindings of `recLets` removes one lift from each binding and
substitutes in the body under the bindings. -/
theorem csubst_recLets_succ (u : LBTerm) : ∀ (ms : List (LBTerm × RecMinor)) (k : Nat) (b : LBTerm),
    csubst u k (recLets (k + 1) ms b) = recLets k ms (csubst u (k + ms.length) b)
  | [], k, b => by simp [recLets]
  | (m, mi) :: ms, k, b => by
    rw [RecLam.recLets_cons, RecLam.recLets_cons]
    simp only [csubst]
    rw [csubst_lbLift_succ u k m 0 k (Nat.zero_le _) (by omega), csubst_recLets_succ u ms (k + 1) b]
    simp only [List.length_cons, show k + 1 + ms.length = k + (ms.length + 1) by omega]

/-- The body of the bindings has the bindings' dependencies. -/
theorem deps_recLets_body : ∀ {ms : List (LBTerm × RecMinor)} {d : Nat} {b : LBTerm},
    ErasesDeps cert σ lenv (recLets d ms b) → ErasesDeps cert σ lenv b
  | [], _, _, h => h
  | (_, _) :: _, _, _, h => by
    rw [RecLam.recLets_cons] at h
    cases h with | letIn _ hb => exact deps_recLets_body hb

/-- The let-bound minors of `Erases.recLet` evaluate, one by one, to closed erasures of the minors'
values, which have erased dependencies; λ□ evaluates the bindings as the body with the values
substituted, whose dependencies are erased. The minors' erasures need not be closed: a
substitution below the bindings removes one lift from each (`csubst_recLets_succ`). -/
theorem recLets_sim : ∀ (mins mvs : List Expr) (ms : List (LBTerm × RecMinor)) (b : LBTerm),
    mins.length = mvs.length → mins.length = ms.length →
    (∀ (i : Nat) m p, mins[i]? = some m → ms[i]? = some p → Erases noCert σ [] m p.1) →
    (∀ (i : Nat) m mv, mins[i]? = some m → mvs[i]? = some mv → ErasesSim σ lenv m mv) →
    (∀ (i : Nat) mv, mvs[i]? = some mv → AbsFV.LBV 0 mv) →
    ErasesDeps noCert σ lenv (recLets 0 ms b) →
    ∃ ws : List LBTerm, ws.length = mvs.length ∧
      (∀ (i : Nat) mv w, mvs[i]? = some mv → ws[i]? = some w → Erases noCert σ [] mv w) ∧
      (∀ w ∈ ws, closedn 0 w = true ∧ LBFixed w ∧ ErasesDeps noCert σ lenv w) ∧
      ErasesDeps noCert σ lenv (substl ws.reverse b) ∧
      ∀ r, LBEval defaultFlags lenv (substl ws.reverse b) r →
        LBEval defaultFlags lenv (recLets 0 ms b) r
  | [], [], [], b, _, _, _, _, _, hd => ⟨[], rfl, fun _ _ _ h => by simp at h,
      fun _ h => by simp at h, hd, fun _ h => h⟩
  | [], _ :: _, _, _, hl, _, _, _, _, _ | _ :: _, [], _, _, hl, _, _, _, _, _ => by simp at hl
  | [], [], _ :: _, _, _, hl, _, _, _, _ | _ :: _, _ :: _, [], _, _, hl, _, _, _, _ => by simp at hl
  | m :: mins, mv :: mvs, (p, mi) :: ms, b, hl1, hl2, her, ih, hlbv, hd => by
    rw [RecLam.recLets_cons, lbLift_zero] at hd ⊢
    cases hd with
    | letIn hdp hdr =>
    obtain ⟨w, hw, hev⟩ := ih 0 m mv rfl rfl (her 0 m _ rfl rfl) hdp
    have hwc : closedn 0 w = true := Erases.closed (hlbv 0 mv rfl) hw
    have hdw := ErasesDeps.eval hdp hev
    have hdr' := ErasesDeps.csubst (k := 0) hdw hdr
    rw [csubst_recLets_succ] at hdr'
    obtain ⟨ws, hwl, hwe, hwsc, hdb, hevb⟩ := recLets_sim mins mvs ms _ (by simpa using hl1)
      (by simpa using hl2) (fun i m p h1 h2 => her (i + 1) m p h1 h2)
      (fun i m mv h1 h2 => ih (i + 1) m mv h1 h2) (fun i mv h => hlbv (i + 1) mv h) hdr'
    have hsub : substl (w :: ws).reverse b = substl ws.reverse (csubst w (0 + ms.length) b) := by
      have hl : ms.length = ws.reverse.length := by simp at hl1 hl2; simp; omega
      rw [Nat.zero_add, hl, ← csubst_substl hwc ws.reverse b fun g hg =>
        (hwsc g (List.mem_reverse.1 hg)).1, List.reverse_cons, substl, List.foldl_append]
      rfl
    refine ⟨w :: ws, by simp [hwl], fun i mv' w' h1 h2 => ?_, fun w' hw' => ?_, hsub ▸ hdb,
      fun r h => .zeta hev (by rw [csubst_recLets_succ]; exact hevb r (hsub ▸ h))⟩
    · cases i with
      | zero => cases h1; cases h2; exact hw
      | succ i => exact hwe i mv' w' h1 h2
    · rcases List.mem_cons.1 hw' with rfl | hw'
      · exact ⟨hwc, RecEval.LBEval.fixed hev, hdw⟩
      · exact hwsc w' hw'

/-- `substl` of `n` terms cancels a lift by `n`. -/
theorem substl_lbLift : ∀ (ws : List LBTerm) (t : LBTerm), substl ws (lbLift ws.length 0 t) = t
  | [], t => lbLift_zero t 0
  | w :: ws, t => by
    show substl ws (csubst w 0 (lbLift (ws.length + 1) 0 t)) = t
    rw [csubst_lbLift_succ w ws.length t 0 0 (Nat.le_refl _) (Nat.zero_le _)]
    exact substl_lbLift ws t

/-- `substl` of an application. -/
theorem substl_app : ∀ (ws : List LBTerm) (a b : LBTerm),
    substl ws (.app a b) = .app (substl ws a) (substl ws b)
  | [], _, _ => rfl
  | w :: ws, a, b => substl_app ws (csubst w 0 a) (csubst w 0 b)

/-- A chain of `let`s has the dependencies of its values and body. -/
theorem deps_letChain {b : LBTerm} (hb : ErasesDeps cert σ lenv b) :
    ∀ (ms : List (LBTerm × RecMinor)), (∀ p ∈ ms, ErasesDeps cert σ lenv p.1) →
      ErasesDeps cert σ lenv (ms.foldr (fun p b => .letIn (binderNameOf p.2.name) p.1 b) b)
  | [], _ => hb
  | p :: ms, h => .letIn (h p (.head _)) (deps_letChain hb ms fun q hq => h q (.tail _ hq))

/-- The converse of `recLets_sim`'s evaluation on bindings that are closed λ□ values. -/
theorem eval_recLets_inv : ∀ (ms : List (LBTerm × RecMinor)) (b r : LBTerm),
    (∀ p ∈ ms, closedn 0 p.1 = true ∧ LBFixed p.1) →
    LBEval defaultFlags lenv (recLets 0 ms b) r →
      LBEval defaultFlags lenv (substl (ms.map (·.1)).reverse b) r
  | [], _, _, _, h => h
  | (m, mi) :: ms, b, r, hm, h => by
    rw [RecLam.recLets_cons, lbLift_zero] at h
    cases h with
    | zeta h1 h2 =>
      obtain rfl := (hm _ (.head _)).2 _ _ h1
      rw [csubst_recLets_succ] at h2
      have hms : ∀ p ∈ ms, closedn 0 p.1 = true ∧ LBFixed p.1 := fun p hp => hm p (.tail _ hp)
      have := eval_recLets_inv ms _ r hms h2
      rw [Nat.zero_add, ← List.length_map (f := (·.1)), ← List.length_reverse,
        ← csubst_substl (hm _ (.head _)).1 _ b fun g hg => by
          obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hg)
          exact (hms p hp).1] at this
      rw [List.map_cons, List.reverse_cons, substl, List.foldl_append]
      exact this
    | atom ha => simp [lbAtom] at ha

/-- Appending to a λ□ spine. Copy of `ML-V Simulation/RecEval.lean:31`. -/
theorem mkApps_append : ∀ (t : LBTerm) (l l' : List LBTerm), mkApps t (l ++ l') = mkApps (mkApps t l) l'
  | _, [], _ => rfl
  | t, a :: l, l' => mkApps_append (.app t a) l l'

/-- An argument may be replaced by a term that evaluates to it, if it is a value. Copy of
`ML-V Simulation/RecEval.lean:324`. -/
theorem eval_app_arg {G a av r : LBTerm} (h : LBEval defaultFlags lenv (.app G av) r)
    (ha : LBEval defaultFlags lenv a av) (hf : LBFixed av) :
    LBEval defaultFlags lenv (.app G a) r := by
  cases h with
  | box h₁ h₂ => obtain rfl := hf _ _ h₂; exact .box h₁ ha
  | beta h₁ h₂ h₃ => obtain rfl := hf _ _ h₂; exact .beta h₁ ha h₃
  | fix h₀ h₁ h₂ h₃ h₄ => obtain rfl := hf _ _ h₂; exact .fix h₀ h₁ ha h₃ h₄
  | fixValue h₀ h₁ h₂ h₃ h₄ => obtain rfl := hf _ _ h₂; exact .fixValue h₀ h₁ ha h₃ h₄
  | fix' h₀ => cases h₀
  | construct h₀ h₁ h₂ h₃ h₄ => obtain rfl := hf _ _ h₄; exact .construct h₀ h₁ h₂ h₃ ha
  | appCong h₁ h₂ h₃ => obtain rfl := hf _ _ h₃; exact .appCong h₁ h₂ ha
  | atom h => simp [lbAtom] at h

/-- Arguments of a spine may be replaced by terms that evaluate to them, if they are values.
Adapted from `ML-V Simulation/RecEval.lean:338`, with the pointwise relation by index. -/
theorem eval_args_replace {H : LBTerm} :
    ∀ {bs cs : List LBTerm}, bs.length = cs.length →
      (∀ (i : Nat) b c, bs[i]? = some b → cs[i]? = some c →
        LBEval defaultFlags lenv b c ∧ LBFixed c) →
      ∀ (pre : List LBTerm) (r : LBTerm), LBEval defaultFlags lenv (mkApps H (pre ++ cs)) r →
        LBEval defaultFlags lenv (mkApps H (pre ++ bs)) r
  | [], [], _, _, _, _, h => h
  | [], _ :: _, hl, _, _, _, _ | _ :: _, [], hl, _, _, _, _ => by simp at hl
  | b :: bs, c :: cs, hl, hbc, pre, r, hr => by
    have h1 := eval_args_replace (bs := bs) (cs := cs) (by simpa using hl)
      (fun i b' c' h1 h2 => hbc (i + 1) b' c' h1 h2) (pre ++ [c]) r (by simpa using hr)
    have hb := hbc 0 b c rfl rfl
    rw [mkApps_append, mkApps_snoc] at h1
    rw [show pre ++ b :: bs = (pre ++ [b]) ++ bs by simp, mkApps_append, mkApps_snoc]
    exact SimCases.lbeval_mkApps_congr bs (fun f' hf' => eval_app_arg hf' hb.1 hb.2) h1

/-! ## λ□: the fixpoint with the minors substituted (`ML-V Simulation/Rec.lean:150`) -/

/-- The alternatives of the fixpoint of a recursor of a single inductive, one per constructor.
Copy of `ML-V Simulation/Rec.lean:33`. -/
def recCs (minors : List RecMinor) : List (Nat × RecMinor × ConstructorArgMask) :=
  (List.range minors.length).map fun ci =>
    (ci, minors.getD ci default, Array.replicate (minors.getD ci default).fields.length .keep)

/-- The body of the fixpoint under the major's λ, with the minors' erasures `ws` substituted and
the recursive call `fixv`. Copy of `ML-V Simulation/Rec.lean:152`. -/
def recBody (direct : Bool) (indid : InductiveId) (npars : Nat) (minors : List RecMinor)
    (ws : List LBTerm) (fixv : Nat → LBTerm) : LBTerm :=
  innerS direct indid npars (recCs minors) (altG (fun gi _ => ws.getD gi .box) fixv)

/-- The fixpoint with the minors' erasures substituted. Copy of `ML-V Simulation/Rec.lean:157`. -/
def recFIX (nm x : BinderName) (direct : Bool) (indid : InductiveId) (npars : Nat)
    (minors : List RecMinor) (ws : List LBTerm) : LBTerm :=
  .fix [⟨nm, .lambda x (recBody direct indid npars minors ws fun B => .bvar (B + 1)), 0⟩] 0

/-- An alternative of `recCs` is at a minor's position. Copy of `ML-V Simulation/Rec.lean:161`. -/
theorem recCs_fst {minors : List RecMinor} {c : Nat × RecMinor × ConstructorArgMask}
    (hc : c ∈ recCs minors) : c.1 < minors.length := by
  unfold recCs at hc
  obtain ⟨ci, hci, rfl⟩ := List.mem_map.1 hc
  exact List.mem_range.1 hci

/-- In the simple shape, induction hypotheses recurse on fields. Copy of
`ML-V Simulation/Rec.lean:167`. -/
theorem simple_fields {minors : List RecMinor} (hs : ∀ c ∈ recCs minors, SimpleAlt c) :
    ∀ c ∈ recCs minors, ∀ h ∈ c.2.1.ihs, h.field < c.2.1.fields.length :=
  fun c hc h hh => ((hs c hc).2 h hh).2.2

/-- The fixpoint of `recFix_shape` with closed minors substituted. Copy of
`ML-V Simulation/Rec.lean:171`. -/
theorem substl_recFix {N : Nat} {nm x : BinderName} {direct : Bool} {indid : InductiveId}
    {npars : Nat} {minors : List RecMinor} {ws : List LBTerm}
    (hs : ∀ c ∈ recCs minors, SimpleAlt c) (hN : minors.length = N) (hwl : ws.length = N)
    (hws : ∀ w ∈ ws, closedn 0 w = true) :
    substl ws.reverse (.fix [{ name := nm, principalArgIdx := 0, body := .lambda x (innerS direct
      indid npars (recCs minors)
      (altG (fun gi B => .bvar (B + 2 + (N - 1 - gi))) (fun B => .bvar (B + 1)))) }] 0) =
      recFIX nm x direct indid npars minors ws := by
  have hws' : ∀ u ∈ ws.reverse, closedn 0 u = true := fun u hu => hws u (List.mem_reverse.1 hu)
  unfold recFIX recBody
  rw [substl_fix1 nm x 0 ws.reverse, foldl_csubst_innerS _ _ _ _ 2 (by omega) (simple_fields hs)]
  congr 4
  refine innerS_congr fun c hc => ?_
  obtain ⟨gi, mi, mask⟩ := c
  have hgi := recCs_fst hc
  simp only [altG]
  congr 2
  · rw [show mi.fields.length + 2 + (N - 1 - gi) = (2 + mi.fields.length) + (N - 1 - gi) by omega,
      foldl_csubst_bvar _ _ _ hws']
    have hlt : N - 1 - gi < ws.reverse.length := by simp; omega
    rw [dite_eq_left hlt, List.getElem_reverse, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega), Option.getD_some]
    congr 1
    try simp only [List.length_reverse]
    omega
  · exact foldl_csubst_bvar_lt (by omega) _

/-- An entry of closed terms, `□` by default, is closed. Copy of `ML-V Simulation/Rec.lean:198`. -/
theorem closedn_getD {ws : List LBTerm} (hws : ∀ w ∈ ws, closedn 0 w = true) (i : Nat) :
    closedn 0 (ws.getD i .box) = true := by
  rw [List.getD_eq_getElem?_getD]
  cases h : ws[i]? with
  | none => rfl
  | some w => exact hws w (List.mem_of_getElem? h)

/-- λ□'s `eval_fix` and `eval_beta` on the fixpoint: the major's value is substituted into the
body, the recursive calls are the fixpoint. Copy of `ML-V Simulation/Rec.lean:207`. -/
theorem eval_recFIX {nm x : BinderName} {direct : Bool} {indid : InductiveId} {npars : Nat}
    {minors : List RecMinor} {ws : List LBTerm} {maj' mb r : LBTerm}
    (hs : ∀ c ∈ recCs minors, SimpleAlt c) (hws : ∀ w ∈ ws, closedn 0 w = true)
    (hcl : closedn 0 (recFIX nm x direct indid npars minors ws) = true)
    (hmaj : LBEval defaultFlags lenv maj' mb)
    (h : LBEval defaultFlags lenv (innerSD direct indid npars (recCs minors)
      (altG (fun gi _ => ws.getD gi .box) fun _ => recFIX nm x direct indid npars minors ws) mb) r) :
    LBEval defaultFlags lenv (.app (recFIX nm x direct indid npars minors ws) maj') r := by
  refine .fix (mfix := [⟨nm, .lambda x (recBody direct indid npars minors ws fun B => .bvar (B + 1)),
    0⟩]) (idx := 0) (argsv := []) rfl (.atom rfl) hmaj rfl ?_
  show LBEval defaultFlags lenv (.app (.lambda x (csubst (recFIX nm x direct indid npars minors ws) 1
    (recBody direct indid npars minors ws fun B => .bvar (B + 1)))) mb) r
  refine .beta (.atom rfl) (LBEval.idem hmaj) ?_
  unfold recBody
  rw [csubst_innerS _ _ _ _ _ _ 1 (by omega) (simple_fields hs)]
  rw [show innerS direct indid npars (recCs minors)
      (altG (fun c B => csubst (recFIX nm x direct indid npars minors ws) (1 + B) (ws.getD c .box))
        fun B => csubst (recFIX nm x direct indid npars minors ws) (1 + B) (.bvar (B + 1))) =
      innerS direct indid npars (recCs minors)
      (altG (fun gi _ => ws.getD gi .box) fun _ => recFIX nm x direct indid npars minors ws) by
    congr 1
    funext c
    obtain ⟨gi, mi, mask⟩ := c
    simp only [altG]
    congr 2
    · exact csubst_closedn _ _ 0 _ (closedn_getD hws gi) (Nat.zero_le _)
    · simp only [csubst]; rw [ite_eq_left (by omega)]]
  rwa [csubst0_innerS _ _ _ _ _ _ (fun c _ => closedn_getD hws c) (fun _ => hcl)
    (simple_fields hs)]

/-- The dependencies of the fixpoint's body give those of the minors' erasures. Copy of
`ML-V Simulation/Rec.lean:238`, with `cert`. -/
theorem deps_recBody {direct : Bool} {indid : InductiveId} {npars : Nat} {minors : List RecMinor}
    {ws : List LBTerm} {fixv : Nat → LBTerm}
    (h : ErasesDeps cert σ lenv (recBody direct indid npars minors ws fixv)) :
    ∀ c ∈ recCs minors, ErasesDeps cert σ lenv (ws.getD c.1 .box) := by
  have hhead : ∀ (gi n : Nat) (fv : LBTerm) (ihs : List RecIH),
      ErasesDeps cert σ lenv (recAltS (ws.getD gi .box) n fv ihs) →
        ErasesDeps cert σ lenv (ws.getD gi .box) := fun gi B fv ihs h =>
    (ErasesDeps.mkApps_iff.1 h).1
  unfold recBody innerS at h
  split at h
  · rename_i c' hcs
    intro c hc
    rw [hcs] at hc
    obtain rfl := List.mem_singleton.1 hc
    obtain ⟨gi, mi, mask⟩ := c
    rw [foldl_app_eq_mkApps] at h
    have h1 := (ErasesDeps.mkApps_iff.1 h).1
    simp only [altG] at h1
    have : ∀ (xs : List BinderName) (b : LBTerm), ErasesDeps cert σ lenv (xs.foldr .lambda b) →
        ErasesDeps cert σ lenv b := by
      intro xs
      induction xs with
      | nil => exact fun _ h => h
      | cons x xs ih => intro b h; cases h with | lambda h => exact ih b h
    exact hhead _ _ _ _ (this _ _ h1)
  · cases h with
    | case _ _ _ hbrs =>
    intro c hc
    obtain ⟨gi, mi, mask⟩ := c
    exact hhead _ _ _ _ (hbrs _ (List.mem_map.2 ⟨_, hc, rfl⟩))

/-! ## The shape of the fixpoint -/

/-- A successful `mapM` gives, entry by entry, the images. Copy of
`ML-V Bridge/RecWhred.lean:330`. -/
theorem mapM_get {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM f = some r →
      r.length = l.length ∧ ∀ (i : Nat) x, l[i]? = some x → ∃ y, r[i]? = some y ∧ f x = some y
  | [], r, h => by simp at h; subst h; exact ⟨rfl, fun _ _ h => nomatch h⟩
  | x :: l, r, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, hy, ys, hys, rfl⟩ := h
    obtain ⟨hl, hall⟩ := mapM_get hys
    refine ⟨by simp [hl], fun i z hz => ?_⟩
    cases i with
    | zero => simp at hz; subst hz; exact ⟨y, rfl, hy⟩
    | succ i => obtain ⟨w, hw, hf⟩ := hall i z (by simpa using hz); exact ⟨w, by simpa using hw, hf⟩

/-- A successful `guard` holds. -/
theorem guard_some {c : Prop} [Decidable c] {u : Unit} (h : (guard c : Option Unit) = some u) : c := by
  unfold guard at h
  split at h
  · assumption
  · cases h

/-- What `recShape` computes: as many motives as asked, a minor per field count, whose fields are
that many, and whose induction hypotheses recurse on a field, into a motive. -/
theorem recShape_spec {P M : Nat} {type : Expr} {ns : List Nat} {motives : List (List Name)}
    {minors : List RecMinor} (h : recShape P M type ns = some (motives, minors)) :
    motives.length = M ∧ minors.length = ns.length ∧ ∀ (i : Nat) n mi, ns[i]? = some n →
      minors[i]? = some mi → mi.fields.length = n ∧ ∀ ih ∈ mi.ihs, ih.field < n ∧ ih.member < M := by
  unfold recShape at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨u, hg, mins, hmins, rfl, rfl⟩ := h
  have hg := guard_some hg
  simp only [Bool.and_eq_true, beq_iff_eq] at hg
  obtain ⟨hlm, hln⟩ := hg
  obtain ⟨hlen, hget⟩ := mapM_get hmins
  refine ⟨by simpa using hlm, by simp [hlen, hln], fun i n mi hn hmi => ?_⟩
  have hi : i < ns.length := (List.getElem?_eq_some_iff.1 hn).1
  obtain ⟨y, hy, hgy⟩ := hget i _ (List.getElem?_eq_getElem (by simp [hln]; omega))
  rw [hmi] at hy
  cases hy
  simp only [List.getElem_zipIdx, List.getElem_zip] at hgy
  have hn' : ns[i] = n := by simpa [List.getElem?_eq_getElem hi] using hn
  subst hn'
  simp only [Option.bind_eq_some_iff, Option.some.injEq] at hgy
  obtain ⟨u', hg', ihs, hihs, rfl⟩ := hgy
  have hg' := guard_some hg'
  refine ⟨by simp only [List.length_map, List.length_take]; omega, fun ih hih => ?_⟩
  obtain ⟨z, -, hz⟩ := Decls.mem_mapM hihs ih hih
  split at hz
  · simp only [Option.bind_eq_some_iff] at hz
    obtain ⟨last, -, hz⟩ := hz
    split at hz
    · simp only [Option.bind_eq_some_iff, Option.some.injEq] at hz
      obtain ⟨u'', hg'', rfl⟩ := hz
      have hg'' := guard_some hg''
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hg''
      exact ⟨by dsimp only; omega, by dsimp only; omega⟩
    · cases hz
  · cases hz

/-- The block of a recursor of one inductive: the inductive and its constructors, in order.
Adapted from `ML-V Bridge/RecWhred.lean:162`. -/
theorem recBlock?_single {rv : RecursorVal} {T : Name} {iv : InductiveVal}
    {cvs : List ConstructorVal} (hall : rv.all = [T]) (h : σ.recBlock? rv = some ([iv], cvs)) :
    findDecl σ.decls T = some (.inductInfo iv) ∧ cvs.length = iv.ctors.length ∧
      ∀ (i : Nat) C, iv.ctors[i]? = some C →
        ∃ cv, cvs[i]? = some cv ∧ findDecl σ.decls C = some (.ctorInfo cv) := by
  unfold EvalEnv.recBlock? recBlockOf? at h
  rw [hall] at h
  simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨_, ⟨a1, ha1, _, rfl, rfl⟩, cvs', hcvs, h⟩ := h
  simp only [Prod.mk.injEq, List.cons.injEq, and_true] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hcvs
  obtain ⟨hl, hget⟩ := mapM_get hcvs
  refine ⟨?_, hl, fun i C hC => ?_⟩
  · split at ha1
    · cases ha1; assumption
    · cases ha1
  · obtain ⟨y, hy, hfy⟩ := hget i C hC
    split at hfy
    · cases hfy; exact ⟨_, hy, by assumption⟩
    · cases hfy

/-- The fixpoint `recFix` of a recursor of a single inductive without indices whose induction
hypotheses take no arguments: one λ for the major premise around the `case` (or the `direct`
form), the alternative of the constructor `ci` applying the bound minor `ci` to the fields and to
the fixpoint on the recursive fields. Adapted from `ML-V Simulation/Rec.lean:41`, with
`recShape_spec` and `RecsShaped` for the shapes ML-V reads from Metalean's block. -/
theorem recFix_shape (hrs : RecsShaped σ.decls) {c : Name} {rv : RecursorVal} {T : Name}
    {iv : InductiveVal} {cvs : List ConstructorVal} {motives : List (List Name)}
    {minors minors' : List RecMinor} {F : LBTerm}
    (hcr : findDecl σ.decls c = some (.recInfo rv)) (hall : rv.all = [T])
    (hblk : σ.recBlock? rv = some ([iv], cvs)) (hni : rv.numIndices = 0)
    (hshape : recShape rv.numParams rv.numMotives rv.type (cvs.map (·.numFields)) =
      some (motives, minors))
    (hihs : ∀ mi ∈ minors, mi.ihs.map (fun h => (h.field, h.binders)) =
      (List.range' (mi.fields.length - mi.ihs.length) mi.ihs.length).map fun f => (f, []))
    (hRF : RecFixOf σ rv minors' F) :
    minors' = minors ∧ minors.length = rv.numMinors ∧ minors.length = iv.ctors.length ∧
    rv.numParams = iv.numParams ∧
    (∀ (i : Nat) cv, cvs[i]? = some cv → ∃ mi, minors[i]? = some mi ∧
        mi.fields.length = cv.numFields) ∧
    (∀ c ∈ recCs minors, SimpleAlt c) ∧
    ∃ indid direct nm x, IndIdOf σ iv.name = some indid ∧
      F = .fix [{ name := nm, principalArgIdx := 0, body := .lambda x (innerS direct indid
        rv.numParams (recCs minors)
        (altG (fun gi B => .bvar (B + 2 + (rv.numMinors - 1 - gi))) (fun B => .bvar (B + 1)))) }] 0 ∧
      (direct = true → iv.ctors.length = 1 →
        σ.propInd iv.name = true ∨ ∀ cn ∈ iv.ctors, ctorFields σ cn = some 0) := by
  obtain ⟨ivs, cvs', motives', members, T', ivT, j, direct, hblk', hshape', hml, hmem, -, hivT,
    hj, hd, rfl, -, -⟩ := hRF
  rw [hblk] at hblk'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hblk')
  rw [hshape] at hshape'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hshape')
  obtain ⟨hTiv, hcl, hcget⟩ := recBlock?_single hall hblk
  obtain ⟨hnp, hmot⟩ := hrs c rv T iv hcr hall hTiv hni
  obtain ⟨x, rfl⟩ := hmot _ _ _ hshape
  obtain ⟨hM, hmlc, hmin⟩ := recShape_spec hshape
  simp only [List.length_singleton, List.length_map] at hM hmlc
  rw [hall, List.idxOf?_eq_some_iff] at hj
  obtain ⟨hj1, hj2, -⟩ := hj
  simp only [List.length_singleton, Nat.lt_one_iff] at hj1
  subst hj1
  have hT : T' = T := by simpa using hj2.symm
  subst hT
  rw [hTiv] at hivT
  cases hivT
  have hlen : minors.length = iv.ctors.length := by omega
  simp [recMembers, Option.bind_eq_some_iff] at hmem
  obtain ⟨indid, hid, masks, hmasks, rfl⟩ := hmem
  have hfl : ∀ (i : Nat) cv, cvs[i]? = some cv → ∃ mi, minors[i]? = some mi ∧
      mi.fields.length = cv.numFields := by
    intro i cv h
    have hi := (List.getElem?_eq_some_iff.1 h).1
    obtain ⟨mi, hmi⟩ : ∃ mi, minors[i]? = some mi := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    exact ⟨mi, hmi, (hmin i cv.numFields mi (by simp [h]) hmi).1⟩
  have hsimple : ∀ c ∈ recCs minors, SimpleAlt c := by
    intro c hc
    unfold recCs at hc
    obtain ⟨ci, hci, rfl⟩ := List.mem_map.1 hc
    have hci' := List.mem_range.1 hci
    obtain ⟨cv, hcv⟩ : ∃ cv, cvs[ci]? = some cv := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hmi : minors[ci]? = some (minors.getD ci default) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hci']; rfl
    obtain ⟨hfl', hih⟩ := hmin ci cv.numFields _ (by simp [hcv]) hmi
    refine ⟨rfl, fun h hh => ⟨?_, by have := (hih h hh).2; omega, by rw [hfl']; exact (hih h hh).1⟩⟩
    have := hihs _ (List.mem_of_getElem? hmi)
    have hm : (h.field, h.binders) ∈ (minors.getD ci default).ihs.map (fun h => (h.field, h.binders)) :=
      List.mem_map.2 ⟨h, hh, rfl⟩
    rw [this] at hm
    obtain ⟨f, -, hf⟩ := List.mem_map.1 hm
    exact (Prod.mk.inj hf).2.symm
  have hcs : (List.range (min iv.ctors.length minors.length)).map (fun c =>
      (c, (List.take iv.ctors.length minors)[c]?.getD default, masks[c]?.getD #[])) =
      recCs minors := by
    unfold recCs
    rw [← hlen, Nat.min_self, List.take_length]
    refine List.map_congr_left fun ci hci => ?_
    have hci' := List.mem_range.1 hci
    simp only [List.getD_eq_getElem?_getD, Prod.mk.injEq, true_and]
    obtain ⟨C, hC⟩ : ∃ C, iv.ctors[ci]? = some C := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨mk, hmk, hfk⟩ := (mapM_get hmasks).2 ci C hC
    obtain ⟨cv, hcv, hCcv⟩ := hcget ci C hC
    obtain ⟨mi, hmi, hmf⟩ := hfl ci cv hcv
    rw [hmk, hmi]
    simp only [Option.getD_some]
    obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.1 hfk
    simp only [ctorFields, hCcv, Option.some.injEq] at hk
    rw [← hk, hmf]
  refine ⟨rfl, hml, hlen, hnp, hfl, hsimple, indid, direct, fixDefName (mkRecName iv.name),
    binderNameOf x, hid, ?_, fun h h1 => hd h iv (.head _) h1⟩
  rw [recFix_eq]
  simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil, List.foldr_cons,
    List.foldr_nil, Nat.sub_self, Nat.zero_add]
  rw [hcs]
  congr 4
  refine innerS_congr fun c hc => ?_
  exact altF_simple _ ⟨iv.name, [x], indid, recCs minors⟩ rfl (hsimple c hc)

/-! ## The major premise's value -/

/-- `erases_natLitCtor` on a literal: `0` erases to λ□'s constructor `0` of ``Nat``, the erasure of
``Nat.zero``; `k + 1` to the constructor `1` applied to the erasure of `k`, the erasure of
``Nat.succ`` applied to `k`. -/
theorem erases_natLit (hnat : NatShaped σ) (hnc : NatCtors σ) {k : Nat} {T : Name} {i : Nat}
    {fs : List Expr} (hcv : CtorValue σ T (natLitCtor (.lit (.natVal k))) i fs) {mb : LBTerm}
    (hmb : Erases noCert σ [] (.lit (.natVal k)) mb) :
    Erases noCert σ [] (natLitCtor (.lit (.natVal k))) mb := by
  obtain ⟨C, us, cv, ps, hC, hind, hcidx, hps, hfs, hpf⟩ := hcv

  have hNat : ∀ {iid}, IndIdOf σ ``Nat = some iid → σ.propInd ``Nat = false := by
    intro iid hid
    unfold IndIdOf at hid
    split at hid
    · rename_i iv hiv; exact (hnat iv hiv).2.1
    · cases hid
  cases k with
  | zero =>
    have hpf' : mkAppN (.const ``Nat.zero []) ([] : List Expr).toArray =
        mkAppN (.const C us) (ps ++ fs).toArray := hpf
    obtain ⟨rfl, rfl, hl⟩ := mkAppN_const_inj hpf'
    obtain ⟨hTN, h0⟩ := hnc.1 cv hC
    have hl' := congrArg List.length hl
    simp only [List.length_nil, List.length_append] at hl'
    generalize hx : Expr.lit (.natVal 0) = x at hmb
    cases hmb with
    | litZero hid =>
      have h1 := Erases.ctor (cert := noCert) (Γ := []) (us := []) (as := []) (as' := []) hC
        (by rw [hTN]; exact hNat hid) (by rw [hTN]; exact hid) (by omega) rfl
        (fun _ _ _ h => nomatch h)
      rw [h0] at h1
      exact h1
    | litSucc => cases hx
    | ctor | cases | casesReduced | quotMk | quotLift | recLet | recFix => cases SimCases.spine_fn hx
    | bvar | fvar | lam | etaLam | letE | app | const | proj | box => cases hx
  | succ k =>
    have hpf' : mkAppN (.const ``Nat.succ []) [Expr.lit (.natVal k)].toArray =
        mkAppN (.const C us) (ps ++ fs).toArray := hpf
    obtain ⟨rfl, rfl, hl⟩ := mkAppN_const_inj hpf'
    obtain ⟨hTN, h1⟩ := hnc.2 cv hC
    have hl' := congrArg List.length hl
    simp only [List.length_cons, List.length_nil, List.length_append] at hl'
    obtain ⟨iid, t, hid, rfl, h'⟩ : ∃ iid t, IndIdOf σ ``Nat = some iid ∧
        mb = .app (.construct iid 1 []) t ∧ Erases noCert σ [] (.lit (.natVal k)) t := by
      generalize hx : Expr.lit (.natVal (k + 1)) = x at hmb
      cases hmb with
      | litSucc hid h' => cases hx; exact ⟨_, _, hid, rfl, h'⟩
      | litZero => cases hx
      | ctor | cases | casesReduced | quotMk | quotLift | recLet | recFix => cases SimCases.spine_fn hx
      | bvar | fvar | lam | etaLam | letE | app | const | proj | box => cases hx
    have h2 := Erases.ctor (cert := noCert) (Γ := []) (us := []) (as := [.lit (.natVal k)])
      (as' := [t]) hC (by rw [hTN]; exact hNat hid) (by rw [hTN]; exact hid) (by simp; omega) rfl
      fun j a a' ha ha' => by
        match j, ha, ha' with
        | 0, ha, ha' => cases ha; cases ha'; exact h'
    rw [h1] at h2
    exact h2

/-- An erasure of a value is one of its constructor form (`natLitCtor`): λ□'s numerals
(`Erases.litZero`, `Erases.litSucc`) are the erasures of ``Nat.zero`` and of ``Nat.succ`` at the
literal below (`Erases.ctor`), the constructors `0` and `1` of ``Nat`` (`NatCtors`), which is not
declared in `Prop` (`NatShaped`). Adapted from `ML-V Simulation/Rec.lean:792`, without the `□`
alternative. -/
theorem erases_natLitCtor (hnat : NatShaped σ) (hnc : NatCtors σ) {mj : Expr} {T : Name} {i : Nat}
    {fs : List Expr} (hcv : CtorValue σ T (natLitCtor mj) i fs) {mb : LBTerm}
    (hmb : Erases noCert σ [] mj mb) : Erases noCert σ [] (natLitCtor mj) mb := by
  rcases Decls.natLitCtor_cases mj with ⟨k, rfl⟩ | h
  · exact erases_natLit hnat hnc hcv hmb
  · rw [h]; exact hmb

/-- The constructor form of a value without loose bound variables has none. -/
theorem lbv_natLitCtor {mj : Expr} (h : AbsFV.LBV 0 mj) : AbsFV.LBV 0 (natLitCtor mj) := by
  rcases Decls.natLitCtor_cases mj with ⟨k, rfl⟩ | hm
  · cases k with
    | zero => trivial
    | succ k => exact ⟨trivial, trivial⟩
  · rw [hm]; exact h

/-! ## The ι step -/

/-- The recursor ι with closed λ□ values `ws` of the minors substituted into the fixpoint: λ□
unfolds the fixpoint on the major's value, a λ□ constructor value, selects the constructor's
alternative (a `case`, or the `direct` form of a constructor without fields) and applies the
minor's value to the fields and to the recursive calls, whose evaluations are those of erasures of
the source induction hypotheses (`hIH`), whose values the continuation is applied to. Adapted from
`ML-V Simulation/Rec.lean:355`, without the typed translation. -/
theorem rec_core (hbinj : BlockNamesInj σ.decls) (hcl : CtorsListed σ.decls)
    (hrs : RecsShaped σ.decls) {c : Name} {rv : RecursorVal} {T : Name} {iv : InductiveVal}
    {cvs : List ConstructorVal} {motives : List (List Name)} {minors : List RecMinor} {mj : Expr}
    {k : Nat} {mi : RecMinor} {mk : Expr} {us : List Level} {v : Expr}
    {ps ms mvs fs rfs ihvs : List Expr}
    (hcr : findDecl σ.decls c = some (.recInfo rv)) (hall : rv.all = [T])
    (hblk : σ.recBlock? rv = some ([iv], cvs)) (hni : rv.numIndices = 0)
    (hshape : recShape rv.numParams rv.numMotives rv.type (cvs.map (·.numFields)) =
      some (motives, minors))
    (hihs : ∀ mi ∈ minors, mi.ihs.map (fun h => (h.field, h.binders)) =
      (List.range' (mi.fields.length - mi.ihs.length) mi.ihs.length).map fun f => (f, []))
    (hcv : CtorValue σ T mj k fs) (hmj : AbsFV.LBV 0 mj) (hmi : minors[k]? = some mi)
    (hmk : mvs[k]? = some mk) (hrfs : (mi.ihs.mapM fun h => fs[h.field]?) = some rfs)
    (hrl : rfs.length = ihvs.length)
    (ihih : ∀ (i : Nat) f w, rfs[i]? = some f → ihvs[i]? = some w →
      ErasesSim σ lenv (mkAppN (.const c us) (ps ++ ms ++ mvs ++ [f]).toArray) w)
    (ihv : ErasesSim σ lenv (mkAppN mk (fs ++ ihvs).toArray) v)
    {minors' : List RecMinor} {F : LBTerm} (hRF : RecFixOf σ rv minors' F)
    {ws : List LBTerm} (hwN : ws.length = rv.numMinors)
    (hwe : ∀ (i : Nat) x x', mvs[i]? = some x → ws[i]? = some x' → Erases noCert σ [] x x')
    (hwc : ∀ w ∈ ws, closedn 0 w = true ∧ ErasesDeps noCert σ lenv w)
    (hIH : ∀ f f', Erases noCert σ [] f f' → ErasesDeps noCert σ lenv f' → closedn 0 f' = true →
      ∃ t, Erases noCert σ [] (mkAppN (.const c us) (ps ++ ms ++ mvs ++ [f]).toArray) t ∧
        ErasesDeps noCert σ lenv t ∧ ∀ r, LBEval defaultFlags lenv t r →
          LBEval defaultFlags lenv (.app (substl ws.reverse F) f') r)
    {maj' mb : LBTerm} (hmb : Erases noCert σ [] mj mb) (hevmb : LBEval defaultFlags lenv maj' mb)
    (hdmb : ErasesDeps noCert σ lenv mb) :
    ∃ vb, Erases noCert σ [] v vb ∧ LBEval defaultFlags lenv (.app (substl ws.reverse F) maj') vb := by
  have hFc : closedn rv.numMinors F = true := by
    obtain ⟨_, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, -, hFc, -⟩ := hRF; exact hFc
  obtain ⟨hmm, hmlN, hmlC, hnp, hfl, hsimple, indid, direct, nm, x, hid, rfl, hdir⟩ :=
    recFix_shape hrs hcr hall hblk hni hshape hihs hRF
  subst minors'
  have hwscl : ∀ w ∈ ws, closedn 0 w = true := fun w hw => (hwc w hw).1
  have hFIX := substl_recFix (N := rv.numMinors) (nm := nm) (x := x) (direct := direct)
    (indid := indid) (npars := rv.numParams) hsimple hmlN hwN hwscl
  have hFcl : closedn 0 (recFIX nm x direct indid rv.numParams minors ws) = true := by
    rw [← hFIX]
    exact TargetLift.closedn_substl _ _ 0 (fun u hu => hwscl u (List.mem_reverse.1 hu))
      (by rw [List.length_reverse, Nat.zero_add, hwN]; exact hFc)
  rw [hFIX] at hIH ⊢
  -- the constructor of the major's value and its λ□ block entry
  obtain ⟨C, usC, cv, psC, hC, hind, hcidx, hpsC, hfsC, rfl⟩ := hcv
  obtain ⟨iid, as', hid', rfl, hlen', hallE, hpI, -⟩ := Erases.ctor_inv hC hmb
  obtain ⟨hTiv, -, hcget⟩ := recBlock?_single hall hblk
  have hivT : iv.name = T := (Decls.findDecl_eq_some hTiv).2
  have hiid : iid = indid := by
    rw [hind, ← hivT, hid] at hid'; exact (Option.some.inj hid').symm
  subst hiid
  obtain ⟨iv₀, hiv₀, hk, hnpC⟩ := hcl C cv hC
  rw [hind, hTiv] at hiv₀
  cases hiv₀
  obtain ⟨hd0, hdargs⟩ := ErasesDeps.mkApps_iff.1 hdmb
  have hidT : IndIdOf σ T = some iid := hivT ▸ hid
  have hindT := ErasesDeps.construct_ind hbinj hidT hd0
  obtain ⟨mib, ob, cb, cv', hlk, hC', hnpars, hnargs, hprop⟩ := ErasesInd.lookupCtor hidT hindT hTiv hk
  rw [hC] at hC'
  cases hC'
  have hpT : σ.propInd T = false := hind ▸ hpI
  have hpf : ob.propositional = false :=
    Bool.eq_false_iff.2 fun h => by rw [hprop.1 h] at hpT; cases hpT
  -- the minor of the constructor binds its fields
  obtain ⟨cv₁, hcv₁, hC₁⟩ := hcget _ _ (hcidx ▸ hk)
  rw [hC] at hC₁
  cases hC₁
  obtain ⟨mi', hmi', hmif⟩ := hfl k cv hcv₁
  rw [hmi] at hmi'
  cases hmi'
  have hkm : k < minors.length := (List.getElem?_eq_some_iff.mp hmi).1
  have hkc : (k, mi, Array.replicate mi.fields.length ConstructorArgRelevance.keep) ∈
      recCs minors := by
    unfold recCs
    refine List.mem_map.2 ⟨k, List.mem_range.2 hkm, ?_⟩
    rw [List.getD_eq_getElem?_getD, hmi, Option.getD_some]
  have hsk := hsimple _ hkc
  have hwk : ws.getD k .box = ws[k]'(by omega) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hmkw : Erases noCert σ [] mk (ws.getD k .box) := by
    rw [hwk]; exact hwe k mk _ hmk (List.getElem?_eq_getElem _)
  have hdwk : ErasesDeps noCert σ lenv (ws.getD k .box) := by
    rw [hwk]; exact (hwc _ (List.getElem_mem _)).2
  -- the fields' erasures
  generalize hus : as'.drop cv.numParams = fs' at *
  have hfs' : fs'.length = fs.length := by
    rw [← hus, List.length_drop, ← hlen', List.length_append, hpsC]; omega
  have hres : ∀ a ∈ as', LBEval defaultFlags lenv a a := SimCases.construct_args hevmb _ _ _ rfl
  have hfe : ∀ (j : Nat) f f', fs[j]? = some f → fs'[j]? = some f' →
      Erases noCert σ [] f f' ∧ closedn 0 f' = true ∧ LBFixed f' ∧ ErasesDeps noCert σ lenv f' := by
    intro j f f' hf hf'
    have hf'' : as'[cv.numParams + j]? = some f' := by rw [← hus, List.getElem?_drop] at hf'; exact hf'
    have herf := hallE _ _ _ (by
      rw [List.getElem?_append_right (by omega), hpsC, Nat.add_sub_cancel_left]; exact hf) hf''
    have hmem := List.mem_of_getElem? hf''
    exact ⟨herf, Erases.closed ((AbsFV.LBV_mkAppN.1 hmj) f
      (List.mem_append_right _ (List.mem_of_getElem? hf))) herf,
      RecEval.LBEval.fixed (hres f' hmem), hdargs f' hmem⟩
  -- the induction hypotheses' erasures and their values
  obtain ⟨hrlen, hrget⟩ := mapM_get hrfs
  have hIHv : ∀ i < ihvs.length, ∃ d : LBTerm, ∃ h w, mi.ihs[i]? = some h ∧ ihvs[i]? = some w ∧
      Erases noCert σ [] w d ∧ ErasesDeps noCert σ lenv d ∧
      LBEval defaultFlags lenv (.app (recFIX nm x direct iid rv.numParams minors ws)
        (fs'.getD h.field .box)) d := by
    intro i hi
    obtain ⟨h, hh⟩ : ∃ h, mi.ihs[i]? = some h := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨w, hw⟩ : ∃ w, ihvs[i]? = some w := ⟨_, List.getElem?_eq_getElem hi⟩
    obtain ⟨rf, hrf, hfrf⟩ := hrget i h hh
    have hfld : h.field < fs.length := hfs' ▸ (List.getElem?_eq_some_iff.1 hfrf).1
    obtain ⟨f', hf'⟩ : ∃ f', fs'[h.field]? = some f' :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨herf, hclf, -, hdf⟩ := hfe _ _ _ hfrf hf'
    obtain ⟨t, hert, hdt, hevt⟩ := hIH rf f' herf hdf hclf
    obtain ⟨vb, hvb, hev⟩ := ihih i rf w hrf hw hert hdt
    refine ⟨vb, h, w, hh, hw, hvb, ErasesDeps.eval hdt hev, ?_⟩
    rw [List.getD_eq_getElem?_getD, hf', Option.getD_some]
    exact hevt vb hev
  obtain ⟨ds, hdsl, hds⟩ := SimCases.choose_list hIHv
  -- the continuation
  have herv : Erases noCert σ [] (mkAppN mk (fs ++ ihvs).toArray)
      (mkApps (ws.getD k .box) (fs' ++ ds)) := by
    refine SimCases.Erases.spine (by simp [hfs', hdsl]) (fun j a a' ha ha' => ?_) hmkw
    by_cases hj : j < fs.length
    · rw [List.getElem?_append_left hj] at ha
      rw [List.getElem?_append_left (by omega)] at ha'
      exact (hfe j a a' ha ha').1
    · rw [List.getElem?_append_right (by omega)] at ha
      rw [List.getElem?_append_right (by omega), hfs'] at ha'
      obtain ⟨h, w, -, hw, hvb, -⟩ := hds _ _ ha'
      rw [ha] at hw
      cases hw
      exact hvb
  have hdv : ErasesDeps noCert σ lenv (mkApps (ws.getD k .box) (fs' ++ ds)) := by
    refine ErasesDeps.mkApps_iff.2 ⟨hdwk, fun a ha => ?_⟩
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
      exact (hfe j _ _ (List.getElem?_eq_getElem (by omega)) (List.getElem?_eq_getElem hj)).2.2.2
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
      exact (hds j _ (List.getElem?_eq_getElem hj)).choose_spec.choose_spec.2.2.2.1
  obtain ⟨vb, hvb, hevb⟩ := ihv herv hdv
  have hev' := eval_args_replace
    (bs := mi.ihs.map fun h => .app (recFIX nm x direct iid rv.numParams minors ws)
      (fs'.getD h.field .box)) (cs := ds) (by simp only [List.length_map]; omega)
    (fun i b d hb hd => by
      obtain ⟨h, w, hh, -, -, -, hev⟩ := hds i d hd
      rw [List.getElem?_map, hh] at hb
      cases hb
      exact ⟨hev, RecEval.LBEval.fixed hev⟩) fs' vb hevb
  refine ⟨vb, hvb, eval_recFIX hsimple hwscl hFcl hevmb ?_⟩
  have hcsl : (recCs minors).length = minors.length := by simp [recCs]
  have hfsl : fs.length = mi.fields.length := by rw [hfsC, hmif]
  by_cases hd1 : direct = true ∧ iv.ctors.length = 1
  · -- the direct form: a constructor without fields
    obtain ⟨rfl, h1⟩ := hd1
    have hcn : ctorFields σ C = some 0 := by
      rcases hdir rfl h1 with hp | hz
      · rw [hivT, hpT] at hp; cases hp
      · exact hz C (List.mem_of_getElem? hk)
    simp only [ctorFields, hC, Option.some.injEq] at hcn
    have hf0 : mi.fields.length = 0 := by omega
    have hih0 : mi.ihs = [] := List.eq_nil_iff_forall_not_mem.2 fun h hh => by
      have := (hsk.2 h hh).2.2; simp at this; omega
    have hk0 : k = 0 := by omega
    subst hk0
    obtain ⟨c0, hc0⟩ : ∃ c0, recCs minors = [c0] :=
      List.length_eq_one_iff.1 (by rw [hcsl]; omega)
    have hc0' : c0 = (0, mi, Array.replicate mi.fields.length ConstructorArgRelevance.keep) := by
      rw [hc0] at hkc; exact (List.mem_singleton.1 hkc).symm
    subst hc0'
    have hfs0 : fs' = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [hfs0, hih0] at hev'
    rw [hc0]
    simp only [innerSD, altG, altNames, recAltS, hf0, hih0, List.range_zero, List.map_nil,
      List.append_nil, List.length_nil, List.replicate_zero, List.foldr_nil, List.foldl_nil]
    exact hev'
  · -- a λ□ `case` on the major's value
    have hcase : innerSD direct iid rv.numParams (recCs minors)
        (altG (fun gi _ => ws.getD gi .box) fun _ =>
          recFIX nm x direct iid rv.numParams minors ws)
        (mkApps (.construct iid cv.cidx []) as') =
        .case (iid, rv.numParams) (mkApps (.construct iid cv.cidx []) as')
          ((recCs minors).map (altG (fun gi _ => ws.getD gi .box) fun _ =>
            recFIX nm x direct iid rv.numParams minors ws)) := by
      unfold innerSD
      split
      · rename_i c₁ hcs₁
        exact absurd ⟨rfl, by rw [← hmlC, ← hcsl, hcs₁]; rfl⟩ hd1
      · rfl
    rw [hcase]
    have hbr : ((recCs minors).map (altG (fun gi _ => ws.getD gi .box) fun _ =>
        recFIX nm x direct iid rv.numParams minors ws))[cv.cidx]? =
        some (altNames mi, recAltS (ws.getD k .box) mi.fields.length
          (recFIX nm x direct iid rv.numParams minors ws) mi.ihs) := by
      rw [List.getElem?_map, hcidx]
      unfold recCs
      rw [List.getElem?_map, List.getElem?_range hkm, Option.map_some, Option.map_some,
        List.getD_eq_getElem?_getD, hmi, Option.getD_some]
      rfl
    have hnpR : rv.numParams = cv.numParams := by rw [hnp, hnpC]
    refine .iota (args := as') (cdecl := cb) rfl (LBEval.idem hevmb) ?_ hbr ?_ ?_ ?_
    · show (lookupCtor lenv iid cv.cidx).map _ = _
      rw [hlk]
      simp [hpf, hnpars, hnp]
    · rw [← hlen', List.length_append, hpsC, hfsC, hnpR, hnargs]
    · rw [hnpR, hus, hfs', length_altNames, hfsl]
    · show LBEval defaultFlags lenv (substl (as'.drop rv.numParams).reverse
        (recAltS (ws.getD k .box) mi.fields.length
          (recFIX nm x direct iid rv.numParams minors ws) mi.ihs)) vb
      rw [show as'.drop rv.numParams = fs' by rw [hnpR]; exact hus]
      have hcl' : ∀ u ∈ fs', closedn 0 u = true := fun u hu => by
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hu
        exact (hfe j _ _ (List.getElem?_eq_getElem (by omega)) (List.getElem?_eq_getElem hj)).2.1
      have := substl_recAltS (closedn_getD hwscl k) hFcl hcl' mi.ihs (by
        intro h hh; rw [hfs', hfsl]; exact (hsk.2 h hh).2.2)
      rw [← hfsl, ← hfs', this]
      exact hev'

/-! ## The `recIota` case -/

/-- A recursor spine split as `Erases.recLet` and `Erases.recFix` read it, without indices. Copy
of `ML-V Simulation/Rec.lean:879`. -/
theorem spine_split {ps ms mins ps' ms' mins' is extra : List Lean.Expr} {maj maj' : Lean.Expr}
    (h : ps ++ ms ++ mins ++ [maj] = ps' ++ ms' ++ mins' ++ is ++ [maj'] ++ extra)
    (h1 : ps.length = ps'.length) (h2 : ms.length = ms'.length) (h3 : mins.length = mins'.length)
    (h4 : is.length = 0) :
    ps = ps' ∧ ms = ms' ∧ mins = mins' ∧ is = [] ∧ maj = maj' ∧ extra = [] := by
  obtain rfl := List.eq_nil_of_length_eq_zero h4
  have hl := congrArg List.length h
  simp only [List.length_append, List.length_singleton, List.length_nil] at hl
  obtain rfl : extra = [] := List.eq_nil_of_length_eq_zero (by omega)
  simp only [List.append_nil] at h
  obtain ⟨h5, h6⟩ := List.append_inj h (by simp; omega)
  obtain ⟨h7, h8⟩ := List.append_inj h5 (by simp; omega)
  obtain ⟨h9, h10⟩ := List.append_inj h7 h1
  simp only [List.cons.injEq, and_true] at h6
  exact ⟨h9, h10, h8, rfl, h6, rfl⟩

end SimRec

namespace SimCases

open TargetSubst TargetLift RecEval RecFix SimRec

variable {σ : EvalEnv} {lenv : GlobalDeclarations}

/-- The `recIota` case of `erases_correct`. The erasure is the fixpoint under `let`s of the erased
minors (`Erases.recLet`), which λ□ evaluates to the minors' values (`SimRec.recLets_sim`, the
minors' erasures need not be closed), or the fixpoint with erasures of the minors substituted
(`Erases.recFix`), λ□ values, hence erasures of the minors' values; then `SimRec.rec_core` at the
major's constructor form (`natLitCtor`; `SimRec.erases_natLitCtor`), with the induction
hypotheses erased in the input's form. Closedness of the minors' and of the major's values comes
from the rule's certificate. Adapted from `ML-V Simulation/Rec.lean:958`, without the `□`
alternative and the typed translation. Reference: none (MetaRocq has no recursors; DV-30). -/
theorem erases_correct_recIota (hbinj : BlockNamesInj σ.decls) (hcl : CtorsListed σ.decls)
    (hnat : NatShaped σ) (hnc : NatCtors σ) (hrs : RecsShaped σ.decls) {env : ConLeche.Env}
    {c : Name} {rv : RecursorVal} {T : Name} {iv : InductiveVal} {cvs : List ConstructorVal}
    {motives : List (List Name)} {minors : List RecMinor} {maj mj : Expr} {k : Nat}
    {mi : RecMinor} {mk : Expr} {us : List Level} {v : Expr}
    {ps ms mins mvs fs rfs ihvs : List Expr}
    (hcr : findDecl σ.decls c = some (.recInfo rv)) (hall : rv.all = [T])
    (hblk : σ.recBlock? rv = some ([iv], cvs)) (hni : rv.numIndices = 0)
    (hshape : recShape rv.numParams rv.numMotives rv.type (cvs.map (·.numFields)) =
      some (motives, minors))
    (hihs : ∀ mi ∈ minors, mi.ihs.map (fun h => (h.field, h.binders)) =
      (List.range' (mi.fields.length - mi.ihs.length) mi.ihs.length).map fun f => (f, []))
    (hps : ps.length = rv.numParams) (hms : ms.length = rv.numMotives)
    (hmins : mins.length = rv.numMinors) (hlm : mins.length = mvs.length)
    (hcv : CtorValue σ T (natLitCtor mj) k fs) (hmi : minors[k]? = some mi)
    (hmk : mvs[k]? = some mk)
    (hok : CLOk env (mkAppN (.const c us) (ps ++ ms ++ mvs ++ [mj]).toArray))
    (hrfs : (mi.ihs.mapM fun h => fs[h.field]?) = some rfs) (hrl : rfs.length = ihvs.length)
    (ihm : ∀ (i : Nat) m mv, mins[i]? = some m → mvs[i]? = some mv → ErasesSim σ lenv m mv)
    (ihmaj : ErasesSim σ lenv maj mj)
    (ihih : ∀ (i : Nat) f w, rfs[i]? = some f → ihvs[i]? = some w →
      ErasesSim σ lenv (mkAppN (.const c us) (ps ++ ms ++ mvs ++ [f]).toArray) w)
    (ihv : ErasesSim σ lenv (mkAppN mk (fs ++ ihvs).toArray) v) :
    ErasesSim σ lenv (mkAppN (.const c us) (ps ++ ms ++ mins ++ [maj]).toArray) v := by
  intro tb her hdeps
  have hlbv := AbsFV.LBV_mkAppN.1 hok.lbv
  have hlmv : ∀ (i : Nat) mv, mvs[i]? = some mv → AbsFV.LBV 0 mv := fun i mv h =>
    hlbv mv (by simp [List.mem_of_getElem? h])
  have hmj : AbsFV.LBV 0 (natLitCtor mj) := lbv_natLitCtor (hlbv mj (by simp))
  -- the major's value in constructor form
  have hmajv : ∀ {majE : LBTerm}, Erases noCert σ [] maj majE → ErasesDeps noCert σ lenv majE →
      ∃ mb, Erases noCert σ [] (natLitCtor mj) mb ∧ LBEval defaultFlags lenv majE mb ∧
        ErasesDeps noCert σ lenv mb := fun hm hd => by
    obtain ⟨mb, hmb, hevmb⟩ := ihmaj hm hd
    exact ⟨mb, erases_natLitCtor hnat hnc hcv hmb, hevmb, ErasesDeps.eval hd hevmb⟩
  rcases Erases.rec_inv hcr her with
    ⟨minors', F, ps', ms', mins', is, maj', extra, minsE, is', majE, extra', hRF, has, hps',
      hms', hmins', his, hlmE, hminE, hli, -, hmajE, hle, -, rfl⟩ |
    ⟨minors', F, ps', ms', mins', is, maj', extra, ws, is', majE, extra', hRF, has, hps', hms',
      hmins', his, hlw, hwE, hws, hli, -, hmajE, hle, -, rfl⟩
  · -- the fixpoint under `let`s of the erased minors
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ :=
      spine_split has (by omega) (by omega) (by omega) (by omega)
    obtain rfl : is' = [] := List.eq_nil_of_length_eq_zero (by simpa using hli.symm)
    obtain rfl : extra' = [] := List.eq_nil_of_length_eq_zero (by simpa using hle.symm)
    have hmN : minors'.length = rv.numMinors := by
      obtain ⟨_, _, _, _, _, _, _, _, -, -, hml, -⟩ := hRF; exact hml
    simp only [List.nil_append, List.map_cons, List.map_nil, mkApps] at hdeps ⊢
    -- the minors' erasures evaluate, one by one, to erasures of the minors' values
    obtain ⟨ws, hwl, hwe, hwc, hdb, hevb⟩ := recLets_sim mins mvs (minsE.zip minors') _ hlm
      (by simp; omega) (fun i m q hm hq => by
        obtain ⟨q1, q2⟩ := q
        rw [List.getElem?_zip_eq_some] at hq
        exact hminE i m q1 hm hq.1) ihm hlmv hdeps
    have hbody : substl ws.reverse (.app F (lbLift rv.numMinors 0 majE)) =
        .app (substl ws.reverse F) majE := by
      rw [substl_app, show rv.numMinors = ws.reverse.length by simp; omega, substl_lbLift]
    rw [hbody] at hdb hevb
    cases hdb with
    | app hdFs hdmaj =>
    have hdF : ErasesDeps noCert σ lenv F := by
      cases deps_recLets_body hdeps with | app hdF _ => exact hdF
    obtain ⟨mb, hmb, hevmb, hdmb⟩ := hmajv hmajE hdmaj
    have hwz : (ws.zip minors').map (·.1) = ws := List.map_fst_zip (by omega)
    obtain ⟨vb, hvb, hev⟩ := rec_core hbinj hcl hrs hcr hall hblk hni hshape hihs hcv hmj hmi hmk
      hrfs hrl ihih ihv hRF (by omega) hwe (fun w hw => ⟨(hwc w hw).1, (hwc w hw).2.2⟩)
      (fun f f' hf hdf hclf => by
        have h1 := Erases.recLet (ps := ps) (ms := ms) (mins := mvs) (is := []) (extra := [])
          (mins' := ws) (is' := []) (extra' := []) (maj := f) (maj' := f') (us := us) (Γ := [])
          hcr hRF hps hms (hlm ▸ hmins) hni.symm (by omega) hwe rfl
          (fun _ _ _ h => by simp at h) hf rfl (fun _ _ _ h => by simp at h)
        simp only [List.append_nil, List.nil_append, List.map_cons, List.map_nil, mkApps] at h1
        have hcz : ∀ q ∈ ws.zip minors', closedn 0 q.1 = true ∧ LBFixed q.1 := fun q hq => by
          have := hwc q.1 (List.of_mem_zip hq).1; exact ⟨this.1, this.2.1⟩
        refine ⟨_, h1, ?_, fun r h => ?_⟩
        · rw [RecLam.recLets_closed _ 0 _ fun q hq => (hcz q hq).1]
          refine deps_letChain (.app hdF ?_) _ fun q hq => (hwc q.1 (List.of_mem_zip hq).1).2.2
          rw [lbLift_closedn _ _ 0 hclf]; exact hdf
        · have := eval_recLets_inv _ _ r hcz h
          rwa [hwz, substl_app, show rv.numMinors = ws.reverse.length by simp; omega,
            substl_lbLift] at this) hmb hevmb hdmb
    exact ⟨vb, hvb, hevb vb hev⟩
  · -- the fixpoint with erasures of the minors substituted
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ :=
      spine_split has (by omega) (by omega) (by omega) (by omega)
    obtain rfl : is' = [] := List.eq_nil_of_length_eq_zero (by simpa using hli.symm)
    obtain rfl : extra' = [] := List.eq_nil_of_length_eq_zero (by simpa using hle.symm)
    simp only [List.nil_append, List.append_nil] at hdeps ⊢
    change ErasesDeps noCert σ lenv (.app (substl ws.reverse F) majE) at hdeps
    cases hdeps with
    | app hdF hdmaj =>
    -- the dependencies of the minors' erasures
    have hdws : ∀ (i : Nat) w, ws[i]? = some w → ErasesDeps noCert σ lenv w := by
      obtain ⟨hmm, hmlN, -, -, -, hsimple, indid, direct, nm, x, -, rfl, -⟩ :=
        recFix_shape hrs hcr hall hblk hni hshape hihs hRF
      subst minors'
      have hwscl : ∀ w ∈ ws, closedn 0 w = true := fun w hw => (hws w hw).1
      have hFIX := substl_recFix (N := rv.numMinors) (nm := nm) (x := x) (direct := direct)
        (indid := indid) (npars := rv.numParams) hsimple hmlN (by omega) hwscl
      rw [hFIX] at hdF
      have hdbody : ErasesDeps noCert σ lenv (recBody direct indid rv.numParams minors ws
          fun B => .bvar (B + 1)) := by
        cases hdF with
        | fix hd =>
          have := hd _ (.head _)
          cases this with
          | lambda hb => exact hb
      have h1 := deps_recBody hdbody
      intro i w hw
      have hi := (List.getElem?_eq_some_iff.mp hw).1
      have hmem : (i, minors.getD i default,
          Array.replicate (minors.getD i default).fields.length ConstructorArgRelevance.keep) ∈
          recCs minors := List.mem_map.2 ⟨i, List.mem_range.2 (by omega), rfl⟩
      have := h1 _ hmem
      rwa [List.getD_eq_getElem?_getD, hw, Option.getD_some] at this
    -- the erasures of the minors are erasures of their values
    have hwe : ∀ (i : Nat) x x', mvs[i]? = some x → ws[i]? = some x' →
        Erases noCert σ [] x x' := by
      intro i mv w h1 h2
      obtain ⟨m, hm⟩ : ∃ m, mins[i]? = some m :=
        ⟨_, List.getElem?_eq_getElem (by have := (List.getElem?_eq_some_iff.mp h1).1; omega)⟩
      obtain ⟨w', hw', hev⟩ := ihm i m mv hm h1 (hwE i m w hm h2) (hdws i w h2)
      obtain rfl := (hws w (List.mem_of_getElem? h2)).2.2 _ _ hev
      exact hw'
    obtain ⟨mb, hmb, hevmb, hdmb⟩ := hmajv hmajE hdmaj
    exact rec_core hbinj hcl hrs hcr hall hblk hni hshape hihs hcv hmj hmi hmk hrfs hrl ihih ihv
      hRF (by omega) hwe (fun w hw => ⟨(hws w hw).1, by
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
        exact hdws i _ (List.getElem?_eq_getElem hi)⟩)
      (fun f f' hf hdf _ => ⟨_, by
        have h1 := Erases.recFix (ps := ps) (ms := ms) (mins := mvs) (is := []) (extra := [])
          (is' := []) (extra' := []) (maj := f) (maj' := f') (us := us) (Γ := []) hcr hRF hps hms
          (hlm ▸ hmins) hni.symm (by omega) hwe hws rfl (fun _ _ _ h => by simp at h) hf rfl
          (fun _ _ _ h => by simp at h)
        simp only [List.append_nil, List.nil_append] at h1
        exact h1, .app hdF hdf, fun _ h => h⟩) hmb hevmb hdmb

end SimCases


end EraseProof
