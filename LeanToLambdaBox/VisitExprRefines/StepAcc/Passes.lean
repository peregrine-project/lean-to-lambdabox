import LeanToLambdaBox.VisitExprRefines.MotivesAcc
import LeanToLambdaBox.VisitExprRefines.Step.Passes

/-!
# The pass-facing steps of the accumulator induction

`doc/rework/12-REPAIRS-W9.md` §2.5 at the eight members `Step/Passes.lean` discharges. Five of
them are pass-throughs; three — `Erasure.visitConstructor`, `Erasure.visitProj` and
`Erasure.visitCases` — call `Erasure.register_inductive`, and that is where the accumulator
*grows*: `accGrows_register_inductive` is `regInv_registerInd_run` (W9-B) at the cold branch
and `SpecGrow.refl` at the branch the registry already answers.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean Erasure Witness Lean.Order

set_option synthInstance.maxSize 4000

/-! ## The accumulator across one block registration -/

/-- **The accumulator across `Erasure.register_inductive`.** At a registry hit the call leaves
the state alone; at a miss it is `regInv_registerInd_run`, whose prefix is the extension. The
three state invariants the accumulator carries beside the triple are re-established by their
own preservation lemmas — `regKeyed_register_inductive`,
`indBlocksCover_register_inductive`, and `RunConcl.canon` for the constant registry. -/
theorem accGrows_register_inductive {lenv : Environment} {env : VEnv} {Us : List Name}
    {gw : Void IO.RealWorld → NameGenerator} {tbl : SourceTable} {indinfo : InductiveVal}
    {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
    {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
    {r : InductiveId × InductiveArgMasks} {s₁ : ErasureState} {w₁ : Void IO.RealWorld}
    (P : ErasureSpec lenv env Us gw) (A : AccAsks lenv env tbl gw)
    (hcfg : ConfigPinned ctx.config)
    (hfind : lenv.find? indinfo.name = some (.inductInfo indinfo))
    (hrun : Erasure.register_inductive indinfo s ctx cctx ref w = .ok (r, s₁) w₁) :
    AccGrows lenv env tbl s s₁ := by
  intro Γ₀ hA
  cases hi : s.inductives.get? indinfo.name with
  | some rc =>
    refine ⟨Γ₀, SpecGrow.refl _, ?_⟩
    rw [(run_register_inductive_hit_ok hi hrun).2.1]
    exact hA
  | none =>
    obtain ⟨pre, -, hg, hacc, hrkm, henr⟩ :=
      regInv_registerInd_run P A.upstream hA.acc hA.keyed hA.canon hA.cover hA.rkm hA.enr
        (A.fresh indinfo) A.indSafe hcfg hfind hi hrun
    exact ⟨pre ++ Γ₀, hg, hacc, hrkm, henr,
      regKeyed_register_inductive P hfind hcfg hrun hA.keyed,
      (run_register_inductive_runConcl hrun).canon hA.canon,
      indBlocksCover_register_inductive P hfind hrun hA.cover⟩

section Steps

variable {lenv : Environment} {env : VEnv} {tbl : SourceTable} {cfg : ErasureConfig}
  {gw : Void IO.RealWorld → NameGenerator}

/-! ## Step 2 — `Erasure.visitLiteral` -/

/-- **Step 2.** The peano arm is one `Erasure.visitConstructor` call; the machine arms are
dead at a pinned configuration. -/
theorem stepAcc_visitLiteral : StepAcc2 lenv env tbl cfg gw := by
  intro P₀ _A htbl hcfg _hcb _M vCtor h3
  refine ⟨?_, bodyLe2 h3.2⟩
  intro l s ctx cctx ref w t s' w' hrun Us Δ n hinv hl hpeano hpeanoB hsup hex
  have P := P₀ Us
  subst hl
  replace h3 := h3.1
  have hpe : ctx.config.nat = .peano := by rw [hinv.cfg]; exact hcfg.2.2.1
  obtain ⟨I, hI, ⟨cz, hzm, hzn, hzi⟩, ⟨cs, hsm, hsn, hsi⟩⟩ := pass_peano_ctors hpeanoB
  have hcz : CtorOf env ``Nat.zero ``Nat 0 := by
    have h := pass_ctorOf_of_tabled P htbl hI hzm; rwa [hzn, hzi] at h
  have hcs : CtorOf env ``Nat.succ ``Nat 1 := by
    have h := pass_ctorOf_of_tabled P htbl hI hsm; rwa [hsn, hsi] at h
  obtain ⟨ve, hve⟩ := hex
  simp only [visitLiteralBody] at hrun
  rw [run_read_bind] at hrun
  cases hve with
  | lit hcl htrC =>
    cases n with
    | zero =>
      simp only [hpe] at hrun
      exact h3 _ _ _ _ _ _ _ _ _ _ hrun _ Δ hinv ⟨_, _, hcz⟩ (fun i hi => absurd hi (by simp))
    | succ m =>
      simp only [hpe] at hrun
      have hinner : ∃ ve', TrExprS env Us Δ (.lit (.natVal m)) ve' := by
        cases htrC with | app _ _ _ htra => exact ⟨_, htra⟩
      have hargs : ArgsOk env Us tbl Δ #[Expr.lit (.natVal m)] := by
        intro i hi
        have hi0 : i = 0 := by simpa using hi
        subst hi0
        exact ⟨pass_supported_lit hpeano hpeanoB hsup.kernames, hinner⟩
      exact h3 _ _ _ _ _ _ _ _ _ _ hrun _ Δ hinv ⟨_, _, hcs⟩ hargs

/-! ## Step 10 — `Erasure.visitProj` -/

/-- **Step 10.** The declaration fetch leaves the state alone, the registration grows the
accumulator, and the discriminant is one sub-run. -/
theorem stepAcc_visitProj : StepAcc10 lenv env tbl cfg gw := by
  intro P₀ A htbl hcfg _hcb M vExpr h1
  refine ⟨?_, bodyLe10 h1.2⟩
  have h1le := h1.2
  intro tn i e s ctx cctx ref w t s' w' hrun Us Δ I np nf hinv hind hinf harity hi hsup hex
  have P := P₀ Us
  have hregm := hinv.indcanon
  replace h1 := h1.1
  obtain ⟨iv, hfind, hname, hnp, -⟩ := P.block_adequate.bwd tn np [nf] harity
  have hcfgc : ConfigPinned ctx.config := by rw [hinv.cfg]; exact hcfg
  simp only [visitProjBody] at hrun
  rw [run_bind_ok] at hrun
  obtain ⟨ci, s₁, w₁, hci, hk⟩ := hrun
  have hs₁ : s₁ = s := run_getConstInfo_state _ _ _ _ _ hci
  subst hs₁
  obtain ⟨hle₁, hfind'⟩ :=
    P.lookup_adequate.constInfo tn cctx ref w ci w₁ (pass_getConstInfo_core hci)
  have hcieq : ci = .inductInfo iv := by rw [hfind] at hfind'; exact (Option.some.inj hfind').symm
  subst hcieq
  simp only [] at hk
  rw [run_bind_ok] at hk
  obtain ⟨r, s₂, w₂, hregrun, hk⟩ := hk
  have hrc := run_register_inductive_runConcl hregrun
  have hregm₂ := run_register_inductive_models P hfind hcfgc hregm hregrun
  have hle₂ := run_register_inductive_gen P hcfgc hregrun
  have haccR :=
    accGrows_register_inductive P A hcfgc (by rw [hname]; exact hfind) hregrun
  rw [run_bind_ok] at hk
  obtain ⟨t₀, s₃, w₃, hve, hp⟩ := hk
  rw [run_pure] at hp
  cases hp
  exact haccR.trans (h1 e s₂ ctx cctx ref w₂ t₀ _ _ hve _ Δ
    ((hinv.mono_state hrc hregm₂).mono (NameGenerator.LE.trans hle₁ hle₂)) hsup hex)

/-! ## Step 3 — `Erasure.visitConstructor` -/

/-- **Step 3.** Two declaration fetches and an environment query leave the state alone, the
registration grows the accumulator, and the spine is `Erasure.visitAppArgs`. The `@[extern]`
arm and both machine-`Nat` arms are dead at a pinned configuration, so neither
`Erasure.visitLiteral` nor `Erasure.visitConst` is reached. -/
theorem stepAcc_visitConstructor : StepAcc3 lenv env tbl cfg gw := by
  intro P₀ A _htbl hcfg _hcb M vLit vConst vArgs _h2 _h4 h7
  refine ⟨?_, bodyLe3 _h2.2 _h4.2 h7.2⟩
  intro cn args s ctx cctx ref w t s' w' hrun Us Δ hinv hctor hargs
  have P := P₀ Us
  have hregm := hinv.indcanon
  have hcfgc : ConfigPinned ctx.config := by rw [hinv.cfg]; exact hcfg
  replace h7 := h7.1
  obtain ⟨I, k, hck⟩ := hctor
  obtain ⟨cv, hcvf, hcvI, hcvk⟩ := P.block_adequate.ctorBwd cn I k hck
  simp only [visitConstructorBody] at hrun
  rw [run_bind_ok] at hrun
  obtain ⟨ci, s₁, w₁, hci, hk⟩ := hrun
  have hs₁ : s₁ = s := run_getConstInfo_state _ _ _ _ _ hci
  subst hs₁
  obtain ⟨hle₁, hfind'⟩ :=
    P.lookup_adequate.constInfo cn cctx ref w ci w₁ (pass_getConstInfo_core hci)
  have hcieq : ci = .ctorInfo cv := by rw [hcvf] at hfind'; exact (Option.some.inj hfind').symm
  subst hcieq
  simp only [] at hk
  rw [run_bind_ok] at hk
  obtain ⟨ci2, s₂, w₂, hci2, hk⟩ := hk
  have hs₂ : s₂ = s₁ := run_getConstInfo_state _ _ _ _ _ hci2
  subst hs₂
  obtain ⟨hle₂, hfind2⟩ :=
    P.lookup_adequate.constInfo cv.induct cctx ref w₁ ci2 w₂ (pass_getConstInfo_core hci2)
  have hck' : CtorOf env cn cv.induct cv.cidx := P.block_adequate.ctor cn cv hcvf
  obtain ⟨iid0, np, nfs, hII⟩ := hck'.indInfo
  have harity : IndArity env cv.induct np nfs := hII.arity
  obtain ⟨iv, hivf, hivn, hivp, hkf⟩ := P.block_adequate.bwd cv.induct np nfs harity
  have hnf : nfs[cv.cidx]? = some cv.numFields :=
    pass_kernelFields_at P A.upstream hcvf hivn harity hkf
  have hself : iv.name ∈ iv.all := P.block_adequate.selfMem cv.induct iv hivf
  have hci2eq : ci2 = .inductInfo iv := by rw [hivf] at hfind2; exact (Option.some.inj hfind2).symm
  subst hci2eq
  simp only [] at hk
  rw [run_bind_ok] at hk
  obtain ⟨r, s₃, w₃, hregrun, hk⟩ := hk
  have hrc := run_register_inductive_runConcl hregrun
  have hregm₃ := run_register_inductive_models P hivf hcfgc hregm hregrun
  have hle₃ := run_register_inductive_gen P hcfgc hregrun
  have hget := pass_register_inductive_entry P (by rw [hivn]; exact hivf) hself hcfgc hregrun
  have hmod := hregm₃ iv.name r np nfs hget (by rw [hivn]; exact harity)
  have haccR := accGrows_register_inductive P A hcfgc (by rw [hivn]; exact hivf) hregrun
  have hmask : r.2[cv.cidx]! = Array.replicate cv.numFields ConstructorArgRelevance.keep := by
    have h0 := hmod.2 cv.cidx cv.numFields hnf
    have hlt : cv.cidx < r.2.length := by
      rcases List.getElem?_eq_some_iff.mp h0 with ⟨hlt, -⟩; exact hlt
    rw [getElem!_pos r.2 cv.cidx hlt]
    exact Option.some.inj ((List.getElem?_eq_getElem hlt).symm.trans h0)
  rw [run_bind_ok] at hk
  obtain ⟨le, s₄, w₄, hgenv, hk⟩ := hk
  have hs₄ : s₄ = s₃ := run_getEnv_state _ _ _ _ _ hgenv
  subst hs₄
  have hle₄ := P.prim_monotone.getEnv _ ctx cctx ref w₃ le _ w₄ hgenv
  rw [run_bind_ok] at hk
  obtain ⟨ctx', s₅, w₅, hrd, hk⟩ := hk
  rw [run_read] at hrd
  cases hrd
  have hext : ctx.config.extern = Config.Extern.preferLogical := hcfgc.2.1
  have hpe : ctx.config.nat = Config.Nat.peano := hcfgc.2.2.1
  have hcond : (isExtern le cn && (ctx.config.extern == Config.Extern.preferAxiom)) = false := by
    rw [hext]; simp only [Bool.and_eq_false_iff]; exact Or.inr (by decide)
  rw [hcond] at hk
  simp only [Bool.false_eq_true, if_false] at hk
  rw [run_bind_ok] at hk
  obtain ⟨ctx'', s₆, w₆, hrd2, hk⟩ := hk
  rw [run_read] at hrd2
  cases hrd2
  simp only [hpe] at hk
  have hfil : (Std.Slice.toArray (args.toSubarray 0 cv.numParams) ++
      filter r.2[cv.cidx]!
        (Subarray.copy (args.toSubarray cv.numParams (cv.numParams + cv.numFields))) ++
      Std.Slice.toArray (args.toSubarray (cv.numParams + cv.numFields) args.size)) = args := by
    rw [Subarray.copy_eq_toArray, Subarray.toArray_eq_sliceToArray, hmask,
      pass_slice_toArray, pass_slice_toArray, pass_slice_toArray,
      pass_filter_replicate_keep _ _ (by simp; omega)]
    simp
    exact Or.inr (Nat.le_max_right _ _)
  rw [hfil] at hk
  have hle : gw w ≤ gw w₄ :=
    NameGenerator.LE.trans hle₁ (NameGenerator.LE.trans hle₂
      (NameGenerator.LE.trans hle₃ hle₄))
  have hhead : HeadRefines env Us tbl ctx Δ s₄ (.const cn ([] : List Level))
      (.construct r.1 cv.cidx []) :=
    fun _ _ => ErasesLBMode.ctor_head hck' (hivn ▸ hmod.1)
  exact haccR.trans (h7 _ _ _ _ _ _ _ _ _ _ hk _ Δ (Expr.const cn ([] : List Level))
    ((hinv.mono_state hrc hregm₃).mono hle) hhead hargs)

/-! ## Step 13 — `Erasure.visitCtorEta` -/

/-- **Step 13.** `Meta.inferType` leaves the state alone; the spine goes to the loop. -/
theorem stepAcc_visitCtorEta : StepAcc13 lenv env tbl cfg gw := by
  intro P₀ _A _htbl _hcfg _hcb _M vGo h14
  refine ⟨?_, bodyLe13 h14.2⟩
  intro cn ar e s ctx cctx ref w t s' w' hrun Us Δ us hinv hfn hctor har hargs
  have P := P₀ Us
  replace h14 := h14.1
  simp only [visitCtorEtaBody] at hrun
  rw [run_bind_ok] at hrun
  obtain ⟨ty, s₁, w₁, hinfer, hk⟩ := hrun
  have hs₁ : s₁ = s := run_liftMetaM_state _ _ _ _ _ hinfer
  subst hs₁
  have hle₁ := (P.prim_monotone.inferType _ _ _ _ _ _ _ _ _ hinfer).1
  rw [expr_withApp_eq] at hk
  exact h14 _ _ _ _ _ _ _ _ _ _ _ _ _ hk _ Δ (hinv.mono hle₁) hctor har hargs

/-! ## Steps 15 and 16 — the `casesOn` η loop -/

/-- **Step 15.** As step 13, at the `casesOn` spine. -/
theorem stepAcc_visitCasesEta : StepAcc15 lenv env tbl cfg gw := by
  intro P₀ _A _htbl _hcfg _hcb _M vGo h16
  refine ⟨?_, bodyLe15 h16.2⟩
  intro ci e s ctx cctx ref w t s' w' hrun Us Δ con us I hinv hfn hhead har hsup hargs hex
  have P := P₀ Us
  replace h16 := h16.1
  simp only [visitCasesEtaBody] at hrun
  rw [run_bind_ok] at hrun
  obtain ⟨ty, s₁, w₁, hinfer, hk⟩ := hrun
  have hs₁ : s₁ = s := run_liftMetaM_state _ _ _ _ _ hinfer
  subst hs₁
  have hle₁ := (P.prim_monotone.inferType _ _ _ _ _ _ _ _ _ hinfer).1
  rw [expr_withApp_eq] at hk
  have hsp := pass_srcSpine_self (e := e) hfn
  exact h16 _ _ _ _ _ _ _ _ _ _ _ _ hk _ Δ con us I (hinv.mono hle₁) hhead har
    (by rw [hsp]; exact hsup) hargs (by rw [hsp]; exact hex)

/-- **Step 16.** At a saturated spine the η-expansion branch is dead and the run is
`Erasure.visitCases` on the nose. -/
theorem stepAcc_visitCasesEtaGo : StepAcc16 lenv env tbl cfg gw := by
  intro _P _A _htbl _hcfg _hcb _M vExpr vGo vCases h1 _h16 h17
  refine ⟨?_, bodyLe16 h1.2 _h16.2 h17.2⟩
  intro ci ty fe args s ctx cctx ref w t s' w' hrun Us Δ con us I hinv hhead har hsup hargs hex
  replace h17 := h17.1
  simp only [visitCasesEtaGoBody] at hrun
  rw [if_pos har] at hrun
  exact h17 _ _ _ _ _ _ _ _ _ _ hrun _ Δ con us I hinv hhead har hsup hargs hex

/-! ## Step 14 — the constructor η loop -/

/-- **Step 14.** At a saturated spine the run is `Erasure.visitConstructor` on the nose. -/
theorem stepAcc_visitCtorEtaGo : StepAcc14 lenv env tbl cfg gw := by
  intro _P _A _htbl _hcfg _hcb _M vExpr vCtor vGo h1 h3 _h14
  refine ⟨?_, bodyLe14 h1.2 h3.2 _h14.2⟩
  intro cn ar ty fe args s ctx cctx ref w t s' w' hrun Us Δ hinv hctor har hargs
  replace h3 := h3.1
  simp only [visitCtorEtaGoBody] at hrun
  rw [if_pos har] at hrun
  exact h3 _ _ _ _ _ _ _ _ _ _ hrun _ Δ hinv hctor hargs

end Steps

end LeanToLambdaBox
