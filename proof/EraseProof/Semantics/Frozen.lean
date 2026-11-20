import EraseProof.Semantics.Iota
import EraseProof.Semantics.Rec
import ConLeche.Model.Rules.IotaSound
import ConLeche.Verify.Rules.Certs
import ConLeche.Verify.Rules.Bridge
import ConLeche.Verify.Inductives.ClassMatchRun
import ConLeche.Verify.PropWhen
import ConLeche.SetTheory.Derive.Univ

/-!
# The meaning of source evaluation: a `casesOn` on a frozen proof

The case `casesFrozen` of `srcEval_sound`, in the form of `EraseProof.Semantics.Iota`: on the
`unmark` readings, the recognized `casesOn` reduces by δ and β to its recursor applied to the
discriminant, a proof that is not a constructor application. con-leche's semantic ι
(`CL ConLeche/Model/Rules/IotaSound.lean:646 Red.iota_sound`) takes the major's reduction as a
claim conditional on the point (`CL ConLeche/Model/Rules/Motive.lean:102 RedSem`), so a constructor
application built for the step stands for the discriminant: the claim is vacuous because con-leche
types the discriminant as a proof, which denotes the point (`proof_pt`). A constructor without
fields fires at case 2 of the ι case split (by the stored facts, `iotaNoCert`: a K rule); one with
fields at case 3, by the full-grade certificate of its telescope at the projections of the
discriminant. β over the alternative's wrapper ends at the alternative applied to the projections.
-/

open Lean Erasure
open ConLeche.Semantics ConLeche.SetModel ConLeche.SetTheory ConLeche.Verify ConLeche.Model
  ConLeche.Model.Rules

namespace EraseProof

universe w

namespace SemCases

variable {env : ConLeche.Env}

/-- The stored records the ι step of the recognized `casesOn` constant `cC` on a frozen
discriminant reads, at its one constructor `cj` with `nP` parameters and `nF` fields, the
discriminant at position `k` of the `D` arguments and the constructor's alternative at `k + 1`:
the records of `CasesIotaAt` at the recursor `R` and the alternative `0`; for a constructor without
fields, the ι case split's case 2 by the stored facts (`CL ConLeche/Kernel/CoreDefs.lean:1040
iotaNoCert`); for one with fields, no indices (`mI = rP`), distinct level parameters of the
`casesOn` constant, the parameters passed on as its first `nP` variables (before the discriminant)
and a rule that fires at a member major (`CL ConLeche/Kernel/Env.lean:118 RecRuleFire`, `.plain`).
Reference: `casesInfo?` (`LeanToLambdaBox/Erasure/Pure.lean:107`) on the stored records, the rule
shape of `CL ConLeche/Kernel/Inductives/GenRec.lean:189 classGenRule`. -/
def CasesFrozenAt (env : ConLeche.Env) (cC R cj : ConLeche.Name) (D k nP nF : Nat) : Prop :=
  ∃ (cvD : ConLeche.ConstantVal) (val : ConLeche.Expr) (hint : ConLeche.ReducibilityHint)
    (rargs : List ConLeche.Expr) (cvR : ConLeche.ConstantVal) (mI rP : Nat)
    (isK : Bool) (rules : List ConLeche.RecRule) (cvj : ConLeche.ConstantVal) (induct : ConLeche.Name)
    (rl : ConLeche.RecRule) (pos : Nat) (w : ConLeche.Expr) (ihs : List ConLeche.Expr),
    env.find? cC = some (.defnInfo cvD val hint) ∧ val.looseBVarsBounded 0 = true ∧
    clLams val = (D, ConLeche.Expr.mkAppN (.const R (cvD.levelParams.map .param)) rargs) ∧
    env.find? R = some (.recInfo cvR mI rP isK rules) ∧
    cvR.levelParams.length = cvD.levelParams.length ∧ clPis cvR.type = mI + 1 ∧ rP ≤ mI ∧
    rargs.length = mI + 1 ∧ rargs[mI]? = some (.bvar (D - 1 - k)) ∧
    pos < rP ∧ rargs[pos]? = some w ∧
    clLams w = (nF + ihs.length, ConLeche.Expr.mkAppN
      (.bvar (nF + ihs.length + (D - 1 - (k + 1)))) (fbv nF (nF + ihs.length))) ∧
    env.find? cj = some (.ctorInfo cvj nP nF induct) ∧
    rules.find? (fun r => r.ctor == cj) = some rl ∧ rl.nfields = nF ∧
    (∃ ihs' : List ConLeche.Expr, ihs'.length = ihs.length ∧
      clLams rl.rhs = (rP + nF, ConLeche.Expr.mkAppN (.bvar (nF + (rP - 1 - pos))) (fbv nF nF ++ ihs'))) ∧
    (nF = 0 →
      ConLeche.iotaNoCert env.find? isK induct (ConLeche.recFireLevelCount rl cvj.levelParams) = true) ∧
    (0 < nF → mI = rP ∧ cvD.levelParams.Nodup ∧ nP ≤ k ∧
      (∀ i < nP, rargs[i]? = some (.bvar (D - 1 - i))) ∧ rl.fire = .plain)

/-! ## A proof denotes the point -/

/-- A level that `isAlwaysZero` (`CL ConLeche/Kernel/Level.lean:201`) evaluates to zero
(`CL ConLeche/Verify/PropWhen.lean:34 zeronessOf_sound`). Reference: none. -/
theorem eval_of_isAlwaysZero {u : ConLeche.Level} (h : u.isAlwaysZero = true)
    (φ : ConLeche.Name → Nat) : u.eval φ = 0 := by
  have hs := ConLeche.PropWhen.zeronessOf_sound φ u
  unfold ConLeche.Level.isAlwaysZero at h
  split at h
  · rename_i heq
    rw [heq] at hs
    simpa [ConLeche.PropWhen.holds] using hs.symm
  · cases h

/-- A closed reading con-leche types as a proof (`CLProof`) denotes the proof point at every
valuation: its type is a member of the sort its own type reduces to (`infer_sound` twice,
`red_sound` on `CL ConLeche/Verify/Rules/Bridge.lean:59 whnf_bridge`), a sort zero at every
valuation, `univ 0` (`CL ConLeche/SetTheory/Derive/Univ.lean:37 univ_zero`), whose members hold
only the point (`CL ConLeche/SetTheory/Derive/Pt.lean:125 eq_pt_of_mem_univZero`). The closed
case of `clCert_proof_pt_statement`. Reference: none (DV-32). -/
theorem proof_pt {V : Type w} [ConLeche.SetTheory V] (m : EnvModelM V env) (φ : ConLeche.Name → Nat)
    {F : Nat} {c T : ConLeche.Expr} (h : ConLeche.inferTypeCore .verified false env F 0 c = .ok T)
    (hpr : CLProof env F 0 T) (hfv : c.hasFvar = false) (hb : c.looseBVarsBounded 0 = true)
    {ea : ConLeche.Term.Term} (hea : denote m.base2.acval env φ 0 c = some ea) (ρ : Nat → V) :
    interp V ρ ea = pt := by
  obtain ⟨S, u, hS, hw, hz⟩ := hpr
  have hin := Rules.RulesInputs.ofSem m φ
  have hnil := ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hfv
  have hnc : ∀ l, l ∉ c.fvarLeaves := fun l hl => by rw [hnil] at hl; cases hl
  have hfc : Frame 0 c :=
    ⟨ConLeche.Expr.WScoped.of_not_hasFvar hfv, hb, fun l hl => absurd hl (hnc l)⟩
  obtain ⟨hfT, hsT, ta, hta, hcs⟩ :=
    infer_sound hin (ConLeche.Rules.inferTypeCore_bridge h) hfc (ctx0 m φ hnc).1 hea
  have hnT : ∀ l, l ∉ T.fvarLeaves := fun l hl => hnc l (hsT l hl)
  obtain ⟨hfS, hsS, sa, hsa, hTs⟩ :=
    infer_sound hin (ConLeche.Rules.inferTypeCore_bridge hS) hfT (ctx0 m φ hnT).1 hta
  have hnS : ∀ l, l ∉ S.fvarLeaves := fun l hl => hnT l (hsS l hl)
  obtain ⟨-, -, ua, hua, hsu⟩ :=
    red_sound hin (ConLeche.Rules.whnf_bridge hw) hfS (ctx0 m φ hnS).1 hsa
  simp only [denote, Option.some.injEq] at hua
  subst hua
  obtain ⟨-, -, hmem⟩ := hcs ρ (Sat_nil V ρ) ((ctx0 m φ hnc).2 ρ)
  obtain ⟨-, hwsa, hTmem⟩ := hTs ρ (Sat_nil V ρ) ((ctx0 m φ hnT).2 ρ)
  obtain ⟨-, hseq⟩ := hsu ρ (Sat_nil V ρ) ((ctx0 m φ hnS).2 ρ) hwsa.1 hwsa.2.ne_pt
  rw [hseq, interp_sort, eval_of_isAlwaysZero hz, univ_zero] at hTmem
  exact eq_pt_of_mem_univZero hTmem hmem

/-! ## The constructor application built for the step -/

/-- A spine has no free variables when its head and arguments have none. -/
theorem hasFvar_mkAppN : ∀ (as : List ConLeche.Expr) {f : ConLeche.Expr}, f.hasFvar = false →
    (∀ a ∈ as, a.hasFvar = false) → (ConLeche.Expr.mkAppN f as).hasFvar = false
  | [], _, hf, _ => hf
  | a :: as, f, hf, ha => hasFvar_mkAppN as (f := .app f a)
      (by simp [ConLeche.Expr.hasFvar, hf, ha a (List.mem_cons_self ..)])
      fun x hx => ha x (List.mem_cons_of_mem _ hx)

/-- A list whose members read reads as a spine. -/
theorem denoteSpine_of {V : Type w} [ConLeche.SetTheory V] (m : EnvModelM V env)
    (φ : ConLeche.Name → Nat) : ∀ (as : List ConLeche.Expr),
    (∀ a ∈ as, ∃ aa, denote m.base2.acval env φ 0 a = some aa) →
    ∃ vs, DenoteSpine m.base2.acval env φ 0 as vs
  | [], _ => ⟨[], .nil⟩
  | a :: as, h => by
    obtain ⟨aa, ha⟩ := h a (List.mem_cons_self ..)
    obtain ⟨vs, hvs⟩ := denoteSpine_of m φ as fun x hx => h x (List.mem_cons_of_mem _ hx)
    exact ⟨aa :: vs, .cons ha hvs⟩

/-- A list is pointwise definitionally equal to itself (`CL ConLeche/Rules/Rel.lean:766
DefEqList`). -/
theorem defEqList_refl {d : Nat} : ∀ (as : List ConLeche.Expr), ConLeche.Rules.DefEqList env d as as
  | [] => .nil
  | _ :: as => .cons .refl (defEqList_refl as)

/-- Every argument a full-grade telescope certificate accepts has a full-grade type
(`CL ConLeche/Verify/InferLemmas.lean:1428 iotaCertsFull_step_inv`). -/
theorem certs_infer {F d : Nat} {args : List ConLeche.Expr} {ty : ConLeche.Expr}
    (h : ConLeche.iotaCertsFull (ConLeche.pureFns .verified false env F) env d ty args = .ok true) :
    ∀ x ∈ args, ∃ t, ConLeche.inferTypeCore .verified false env F d x = .ok t := by
  induction args generalizing ty with
  | nil => intro x hx; simp at hx
  | cons a rest ih =>
    cases ty
    case forallE t₀ body =>
      obtain ⟨ta, hta, -, hrest⟩ := ConLeche.iotaCertsFull_step_inv h
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨ta, hta⟩
      · exact ih hrest x hx
    all_goals simp [ConLeche.iotaCertsFull, pure, Except.pure] at h

/-- The closed arguments a full-grade telescope certificate accepts read
(`CL ConLeche/Model/Tiers.lean:346 acceptedReads_of`). -/
theorem reads_of_certs {V : Type w} [ConLeche.SetTheory V] (m : EnvModelM V env)
    (φ : ConLeche.Name → Nat) {F : Nat} {ty : ConLeche.Expr} {xs : List ConLeche.Expr}
    (h : ConLeche.iotaCertsFull (ConLeche.pureFns .verified false env F) env 0 ty xs = .ok true)
    (hfv : ∀ x ∈ xs, x.hasFvar = false) (hb : ∀ x ∈ xs, x.looseBVarsBounded 0 = true) :
    ∀ x ∈ xs, ∃ xa, denote m.base2.acval env φ 0 x = some xa := fun x hx => by
  obtain ⟨t, ht⟩ := certs_infer h x hx
  have hnil := ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar (hfv x hx)
  exact acceptedReads_of m.base2 φ ht (ConLeche.Expr.WScoped.of_not_hasFvar (hfv x hx)) (hb x hx)
    fun l hl => by rw [hnil] at hl; cases hl

/-- The major's reduction to a closed term built for the step, claimed where the major is not the
point (`RedSem`): vacuous on a major that denotes the point. Reference: none (DV-25). -/
theorem major_pt {V : Type w} [ConLeche.SetTheory V] (m : EnvModelM V env) (φ : ConLeche.Name → Nat)
    {cd fab : ConLeche.Expr}
    (hpt : ∀ ea, denote m.base2.acval env φ 0 cd = some ea → ∀ ρ : Nat → V, interp V ρ ea = pt)
    (hfv : fab.hasFvar = false) (hb : fab.looseBVarsBounded 0 = true)
    (hden : ∀ ea, denote m.base2.acval env φ 0 cd = some ea →
      ∃ fa, denote m.base2.acval env φ 0 fab = some fa) :
    RedSem m.base2 φ 0 cd fab := by
  intro _ Δa ea _ hea
  have hnil := ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hfv
  obtain ⟨fa, hfa⟩ := hden ea hea
  exact ⟨⟨ConLeche.Expr.WScoped.of_not_hasFvar hfv, hb, fun l hl => by rw [hnil] at hl; cases hl⟩,
    fun l hl => (by rw [hnil] at hl; cases hl), fa, hfa,
    fun ρ _ _ _ hne => absurd (hpt ea hea ρ) hne⟩

/-! ## The ι chain on a frozen discriminant -/

/-- The ι chain of a recognized `casesOn` on a frozen discriminant, on the readings: δ of the
`casesOn` constant and β over its `D` λs (`red_sound`), ι at the recursor's rule for the one
constructor `cj` (`CL ConLeche/Model/Rules/IotaSound.lean:646 Red.iota_sound`) with the major's
reduction to a constructor application built for the step (`major_pt`, the discriminant `cd`
denoting the point): without fields, at case 2 of the ι case split (`CL ConLeche/Model/Rules/Sound.lean:260
iotaCaseS_sound`), the constructor applied to `nP` copies of the discriminant; with fields, at
case 3, the constructor at the rule's comparands
(`CL ConLeche/Kernel/CoreDefs.lean:995 recFireComparands`) applied to them and to the
projections of the discriminant, the comparisons by reflexivity
(`CL ConLeche/Verify/Inductives/ClassMatchRun.lean:283 isEquivList_self`, `defEqList_sound`) and
the telescope by the certificate `hcert` (`CL ConLeche/Verify/Rules/Certs.lean:35
iotaCertsFull_bridge`, `CL ConLeche/Model/Rules/Sound.lean:288 certsF_sound`); then β over the
alternative's wrapper (`red_sound`), composed by `CL ConLeche/Model/Rules/RedSound.lean:55
Red.trans_sound`. The spine `cC us args` reduces to the alternative `args[k+1]` applied to the
projections of the discriminant. Reference: `eval_iota_sing` (`MR E/EWcbvEval.v:162`). -/
theorem casesFrozen_redSem {V : Type w} [ConLeche.SetTheory V] (m : EnvModelM V env)
    (φ : ConLeche.Name → Nat) {cC R cj S : ConLeche.Name} {D k nP nF : Nat}
    (hat : CasesFrozenAt env cC R cj D k nP nF) {us : List ConLeche.Level}
    {args : List ConLeche.Expr} {cd calt : ConLeche.Expr}
    (hlen : args.length = D) (hcl : ∀ a ∈ args, a.looseBVarsBounded 0 = true)
    (hfv : ∀ a ∈ args, a.hasFvar = false)
    (hus : ∀ cvD val hint, env.find? cC = some (.defnInfo cvD val hint) →
      us.length = cvD.levelParams.length)
    (hk : args[k]? = some cd) (halt : args[k + 1]? = some calt)
    (hpt : ∀ ea, denote m.base2.acval env φ 0 cd = some ea → ∀ ρ : Nat → V, interp V ρ ea = pt)
    (hcert : 0 < nF → ∃ (cvR : ConLeche.ConstantVal) (mI rP : Nat) (isK : Bool)
      (rules : List ConLeche.RecRule) (rl : ConLeche.RecRule) (cvC : ConLeche.ConstantVal)
      (nP' nF' : Nat) (ind : ConLeche.Name) (F : Nat),
      env.find? R = some (.recInfo cvR mI rP isK rules) ∧
      rules.find? (fun r => r.ctor == cj) = some rl ∧
      env.find? cj = some (.ctorInfo cvC nP' nF' ind) ∧
      ConLeche.iotaCertsFull (ConLeche.pureFns .verified false env F) env 0
        (cvC.type.instantiateLevelParams cvC.levelParams
          (ConLeche.recFireComparands rl nP' cvR.levelParams us cvC.levelParams (args.take nP) rP).1)
        ((ConLeche.recFireComparands rl nP' cvR.levelParams us cvC.levelParams (args.take nP) rP).2 ++
          (List.range nF').map fun j => .proj S j cd) = .ok true) :
    RedSem m.base2 φ 0 (ConLeche.Expr.mkAppN (.const cC us) args)
      (ConLeche.Expr.mkAppN calt ((List.range nF).map fun j => .proj S j cd)) := by
  obtain ⟨cvD, val, hint, rargs, cvR, mI, rP, isK, rules, cvj, induct, rl, pos, w, ihs,
    hfD, hvcl, hval, hfR, hlpR, hpis, hrP, hrlen, hrmaj, hpos, hw, hwsh, hfj, hrl, hnf,
    ⟨ihs', hihs', hrhs⟩, hK, hF⟩ := hat
  have hin := Rules.RulesInputs.ofSem m φ
  have husl := hus cvD val hint hfD
  have hkD : k < D := by have := (List.getElem?_eq_some_iff.mp hk).1; omega
  have hjD : k + 1 < D := by have := (List.getElem?_eq_some_iff.mp halt).1; omega
  have hargcl : ∀ v ∈ args.reverse, v.looseBVarsBounded 0 = true := fun v hv => hcl v (by simpa using hv)
  -- δ
  have hδ : ConLeche.Rules.Red env 0 (ConLeche.Expr.mkAppN (.const cC us) args)
      (ConLeche.Expr.mkAppN (val.instantiateLevelParams cvD.levelParams us) args) := by
    refine .delta ?_
    simp [ConLeche.unfoldDefinition, ConLeche.Expr.getAppFn_mkAppN, ConLeche.Expr.getAppArgs_mkAppN,
      ConLeche.Expr.getAppFn, ConLeche.Expr.getAppArgs, hfD, husl]
  -- β over the `casesOn` value
  have hβ := red_betas (env := env) (d := 0) D (val.instantiateLevelParams cvD.levelParams us)
    ((ConLeche.Expr.mkAppN (.const R (cvD.levelParams.map .param)) rargs).instantiateLevelParams
      cvD.levelParams us) (by rw [clLams_instLP, hval]) args [] hlen
  rw [ConLeche.Expr.instantiateList_nil, List.append_nil, ConLeche.instantiateLevelParams_mkAppN,
    instantiateList_mkAppN, List.map_map] at hβ
  let inst : ConLeche.Expr → ConLeche.Expr := fun x =>
    (x.instantiateLevelParams cvD.levelParams us).instantiateList args.reverse 0
  let usR := (cvD.levelParams.map ConLeche.Level.param).map (ConLeche.Level.subst cvD.levelParams us)
  let e := ConLeche.Expr.mkAppN (.const R usR) (rargs.map inst)
  have he : ((ConLeche.Expr.const R (cvD.levelParams.map .param)).instantiateLevelParams
      cvD.levelParams us).instantiateList args.reverse 0 = .const R usR := by
    rw [ConLeche.Expr.instantiateLevelParams, ConLeche.Expr.instantiateList]
  rw [he] at hβ
  change ConLeche.Rules.Red env 0 _ e at hβ
  -- closedness of the recursor's arguments
  have hbody := clLams_bounded D hval hvcl
  rw [Nat.zero_add, mkAppN_bounded_iff] at hbody
  have hinstcl : ∀ x ∈ rargs, (inst x).looseBVarsBounded 0 = true := fun x hx =>
    bounded_instantiateList _ _ 0 hargcl (by
      rw [ConLeche.Expr.looseBVarsBounded_instantiateLevelParams, List.length_reverse, hlen,
        Nat.zero_add]; exact hbody.2 x hx)
  have hargsE : e.getAppArgs = rargs.map inst := by
    simp [e, ConLeche.Expr.getAppArgs_mkAppN, ConLeche.Expr.getAppArgs]
  have hvar : ∀ {i : Nat} {x : ConLeche.Expr}, i < D → args[i]? = some x →
      inst (.bvar (D - 1 - i)) = x := fun {i x} hi hx => by
    show (ConLeche.Expr.bvar (D - 1 - i)).instantiateList args.reverse 0 = x
    exact instantiateList_rev_bvar (by omega)
      (by rw [hlen, show D - 1 - (D - 1 - i) = i by omega]; exact hx) (hcl x (List.mem_of_getElem? hx))
  have hmajE : e.getAppArgs.getD mI (.bvar 0) = cd := by
    rw [hargsE, List.getD_eq_getElem?_getD, List.getElem?_map, hrmaj]
    exact hvar hkD hk
  -- the projections of the discriminant, and the reduct
  let cprojs := (List.range nF).map fun j => ConLeche.Expr.proj S j cd
  have hcdcl : cd.looseBVarsBounded 0 = true := hcl cd (List.mem_of_getElem? hk)
  have hcdfv : cd.hasFvar = false := hfv cd (List.mem_of_getElem? hk)
  have hcplen : cprojs.length = nF := by simp [cprojs]
  have hcpl : ∀ x ∈ cprojs, x.looseBVarsBounded 0 = true := by
    intro x hx
    simp only [cprojs, List.mem_map] at hx
    obtain ⟨j, -, rfl⟩ := hx
    simpa [ConLeche.Expr.looseBVarsBounded] using hcdcl
  have hcpfv : ∀ x ∈ cprojs, x.hasFvar = false := by
    intro x hx
    simp only [cprojs, List.mem_map] at hx
    obtain ⟨j, -, rfl⟩ := hx
    simpa [ConLeche.Expr.hasFvar] using hcdfv
  let vals := (rargs.map inst).take rP ++ cprojs
  have hvlen : vals.length = rP + nF := by simp [vals, hrlen, hcplen]; omega
  let ihs'' := ihs'.map fun x =>
    (x.instantiateLevelParams cvR.levelParams usR).instantiateList vals.reverse 0
  have hwcl : (inst w).looseBVarsBounded 0 = true := hinstcl w (List.mem_of_getElem? hw)
  have hreduct : rl.iotaReduct cvR.levelParams usR rP vals =
      ConLeche.Expr.mkAppN (inst w) (cprojs ++ ihs'') := by
    unfold ConLeche.RecRule.iotaReduct
    rw [hnf, lamBody_of_clLams _ hrhs, ConLeche.instantiateLevelParams_mkAppN, instantiateList_mkAppN,
      List.map_append, List.map_append, fbv_instLP, List.map_map]
    congr 1
    · show (ConLeche.Expr.bvar (nF + (rP - 1 - pos))).instantiateList vals.reverse 0 = inst w
      refine instantiateList_rev_bvar (by omega) ?_ hwcl
      rw [hvlen, show rP + nF - 1 - (nF + (rP - 1 - pos)) = pos by omega]
      simp only [vals, List.getElem?_append_left (show pos < ((rargs.map inst).take rP).length by
        simp; omega), List.getElem?_take, hpos, ite_true, List.getElem?_map, hw, Option.map_some]
    · congr 1
      refine fbv_instantiateList hcplen hcpl fun f hf => ?_
      rw [List.getElem?_reverse (by omega), hvlen,
        show rP + nF - 1 - (nF - 1 - f) = (rP + f) by omega,
        List.getElem?_append_right (by simp; omega)]
      simp only [List.length_take, List.length_map, hrlen, show min rP (mI + 1) = rP by omega,
        show rP + f - rP = f by omega, List.getElem?_eq_getElem (show f < cprojs.length by omega)]
  -- β over the wrapper
  have hlw : (cprojs ++ ihs'').length = nF + ihs.length := by simp [ihs'', hcplen, hihs']
  have hβ₂ := red_betas (env := env) (d := 0) (nF + ihs.length)
    (w.instantiateLevelParams cvD.levelParams us)
    ((ConLeche.Expr.mkAppN (.bvar (nF + ihs.length + (D - 1 - (k + 1))))
      (fbv nF (nF + ihs.length))).instantiateLevelParams cvD.levelParams us)
    (by rw [clLams_instLP, hwsh]) (cprojs ++ ihs'') args.reverse hlw
  rw [ConLeche.instantiateLevelParams_mkAppN, fbv_instLP, instantiateList_mkAppN] at hβ₂
  have hhead : (ConLeche.Expr.instantiateLevelParams cvD.levelParams us
      (.bvar (nF + ihs.length + (D - 1 - (k + 1))))).instantiateList
        ((cprojs ++ ihs'').reverse ++ args.reverse) 0 = calt := by
    show (ConLeche.Expr.bvar (nF + ihs.length + (D - 1 - (k + 1)))).instantiateList _ 0 = calt
    refine instantiateList_bvar0 ?_ (hcl calt (List.mem_of_getElem? halt))
    rw [List.getElem?_append_right (by rw [List.length_reverse, hlw]; omega), List.length_reverse, hlw,
      show nF + ihs.length + (D - 1 - (k + 1)) - (nF + ihs.length) = D - 1 - (k + 1) by omega,
      List.getElem?_reverse (by omega), hlen, show D - 1 - (D - 1 - (k + 1)) = k + 1 by omega]
    exact halt
  have hfields : (fbv nF (nF + ihs.length)).map
      (·.instantiateList ((cprojs ++ ihs'').reverse ++ args.reverse) 0) = cprojs := by
    refine fbv_instantiateList hcplen hcpl fun f hf => ?_
    rw [List.getElem?_append_left (by rw [List.length_reverse, hlw]; omega),
      List.getElem?_reverse (by rw [hlw]; omega),
      hlw, show nF + ihs.length - 1 - (nF + ihs.length - 1 - f) = f by omega,
      List.getElem?_append_left (by omega), List.getElem?_eq_getElem (by omega)]
  rw [hhead, hfields] at hβ₂
  -- ι, the major built for the step
  have hpisE : (ConLeche.Expr.peelPis e.getAppArgs.length
      (cvR.type.instantiateLevelParams cvR.levelParams usR)).isSome = true := by
    rw [hargsE, List.length_map, hrlen]
    exact ConLeche.Rules.peelPis_isSome_instantiateLevelParams _ _ _ (peelPis_of_clPis hpis)
  have hhe : e.getAppFn = .const R usR := by simp [e, ConLeche.Expr.getAppFn_mkAppN, ConLeche.Expr.getAppFn]
  have hle : e.getAppArgs.length = mI + 1 := by rw [hargsE, List.length_map, hrlen]
  have husR : usR.length = cvR.levelParams.length := by simp [usR, hlpR]
  have hfin : ∀ (usj : List ConLeche.Level) (P : List ConLeche.Expr), P.length = nP →
      RedSem m.base2 φ 0 e (rl.iotaReduct cvR.levelParams usR rP
        (e.getAppArgs.take rP ++ (ConLeche.Expr.mkAppN (.const cj usj) (P ++ cprojs)).getAppArgs.drop nP)) →
      RedSem m.base2 φ 0 (ConLeche.Expr.mkAppN (.const cC us) args) (ConLeche.Expr.mkAppN calt cprojs) := by
    intro usj P hP hι
    have hvals : e.getAppArgs.take rP ++ (ConLeche.Expr.mkAppN (.const cj usj) (P ++ cprojs)).getAppArgs.drop nP
        = vals := by
      rw [hargsE]
      simp [vals, ConLeche.Expr.getAppArgs_mkAppN, ConLeche.Expr.getAppArgs, List.drop_left' hP]
    rw [hvals, hreduct] at hι
    exact Red.trans_sound (red_sound hin (.trans hδ hβ)) (Red.trans_sound hι (red_sound hin hβ₂))
  have hhd : ∀ (usj : List ConLeche.Level) (P : List ConLeche.Expr),
      (ConLeche.Expr.mkAppN (.const cj usj) (P ++ cprojs)).getAppFn = .const cj usj := by
    intro usj P; simp [ConLeche.Expr.getAppFn_mkAppN, ConLeche.Expr.getAppFn]
  have hal : ∀ (usj : List ConLeche.Level) (P : List ConLeche.Expr),
      (ConLeche.Expr.mkAppN (.const cj usj) (P ++ cprojs)).getAppArgs = P ++ cprojs := by
    intro usj P; simp [ConLeche.Expr.getAppArgs_mkAppN, ConLeche.Expr.getAppArgs]
  -- the major built for the step reads and is closed
  have hfab : ∀ (usj : List ConLeche.Level) (P : List ConLeche.Expr), usj.length = cvj.levelParams.length →
      (∀ x ∈ P, x.hasFvar = false ∧ x.looseBVarsBounded 0 = true) →
      (∀ ea, denote m.base2.acval env φ 0 cd = some ea →
        ∀ x ∈ P ++ cprojs, ∃ xa, denote m.base2.acval env φ 0 x = some xa) →
      RedSem m.base2 φ 0 (e.getAppArgs.getD mI (.bvar 0))
        (ConLeche.Expr.mkAppN (.const cj usj) (P ++ cprojs)) := by
    intro usj P husj hP hden
    rw [hmajE]
    have hall : ∀ x ∈ P ++ cprojs, x.hasFvar = false ∧ x.looseBVarsBounded 0 = true := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hP x hx
      · exact ⟨hcpfv x hx, hcpl x hx⟩
    refine major_pt m φ hpt (hasFvar_mkAppN _ (by rfl) fun x hx => (hall x hx).1)
      ((mkAppN_bounded_iff _ _).mpr ⟨by rfl, fun x hx => (hall x hx).2⟩) fun ea hea => ?_
    obtain ⟨vs, hvs⟩ := denoteSpine_of m φ _ (hden ea hea)
    exact ⟨_, denote_mkAppN hvs (denote_const hfj (show usj.length = _ from husj))⟩
  rcases Nat.eq_zero_or_pos nF with h0 | hnF
  · -- no fields: case 2, by the stored facts
    have hι := Red.iota_sound hin (residual := .bvar 0) (c3 := false) hhe hfR hle husR
      (hfab (cvj.levelParams.map .param) (List.replicate nP cd) (by simp)
        (fun x hx => by rw [List.eq_of_mem_replicate hx]; exact ⟨hcdfv, hcdcl⟩)
        (fun ea hea x hx => by
          rcases List.mem_append.mp hx with hx | hx
          · rw [List.eq_of_mem_replicate hx]; exact ⟨ea, hea⟩
          · simp [cprojs, h0] at hx))
      (hhd _ _) hfj hrl (by rw [hal]; simp [hcplen, hnf])
      (iotaCaseS_sound hin (m.base2.wf.ctorHead hfj).choose_spec
        (.stored (by rw [ConLeche.recFireComparands_fst_length]; exact hK h0)))
      (fun h => nomatch h) (fun h => nomatch h) (teleArity_sound hpisE) (fun h => nomatch h)
      (fun h => nomatch h) (fun h => nomatch h)
    exact hfin _ _ (by simp) hι
  · -- fields: case 3, by the certificate
    obtain ⟨hmI, hnd, hPk, hpar, hfire⟩ := hF hnF
    obtain ⟨cvR', mI', rP', isK', rules', rl', cvC, nP', nF', ind', F, hfR', hrl', hfj', hc⟩ :=
      hcert hnF
    rw [hfR] at hfR'
    obtain ⟨⟩ := hfR'
    rw [hrl] at hrl'
    obtain ⟨⟩ := hrl'
    rw [hfj] at hfj'
    obtain ⟨⟩ := hfj'
    have hus' : usR = us := subst_params hnd husl
    have hPD : nP ≤ D := by omega
    have htake : e.getAppArgs.take nP = args.take nP := by
      rw [hargsE]
      refine List.ext_getElem? fun i => ?_
      by_cases hi : i < nP
      · have hx : args[i]? = some (args[i]'(by omega)) := List.getElem?_eq_getElem (by omega)
        simp only [List.getElem?_take, hi, ↓reduceIte, List.getElem?_map, hpar i hi, Option.map_some,
          hx]
        rw [hvar (by omega) hx]
      · simp only [List.getElem?_take, hi, ↓reduceIte]
    have hcmp : ∀ a : List ConLeche.Expr, ConLeche.recFireComparands rl nP cvR.levelParams us
        cvj.levelParams a rP = (cvj.levelParams.map fun p =>
          ConLeche.Level.subst cvR.levelParams us (.param p), a.take nP) := by
      intro a
      unfold ConLeche.recFireComparands
      rw [hfire]
    have hcmpR : ∀ a : List ConLeche.Expr, ConLeche.recFireComparands rl nP cvR.levelParams usR
        cvj.levelParams a rP = (cvj.levelParams.map fun p =>
          ConLeche.Level.subst cvR.levelParams us (.param p), a.take nP) := by
      intro a
      rw [hus']
      exact hcmp a
    have hctake : (args.take nP).take nP = args.take nP := by rw [List.take_take, Nat.min_self]
    rw [hcmp, hctake] at hc
    dsimp only at hc
    have hPlen : (args.take nP).length = nP := by rw [List.length_take]; omega
    have hPx : ∀ x ∈ args.take nP, x.hasFvar = false ∧ x.looseBVarsBounded 0 = true :=
      fun x hx => ⟨hfv x (List.mem_of_mem_take hx), hcl x (List.mem_of_mem_take hx)⟩
    have hrd := reads_of_certs m φ hc (fun x hx => by
        rcases List.mem_append.mp hx with hx | hx
        · exact (hPx x hx).1
        · exact hcpfv x hx)
      (fun x hx => by
        rcases List.mem_append.mp hx with hx | hx
        · exact (hPx x hx).2
        · exact hcpl x hx)
    have hι := Red.iota_sound hin (residual := .bvar 0) (c3 := true) hhe hfR hle husR
      (hfab (cvj.levelParams.map fun p => ConLeche.Level.subst cvR.levelParams us (.param p))
        (args.take nP) (by simp) hPx (fun _ _ => hrd))
      (hhd _ _) hfj hrl (by rw [hal]; simp [hcplen, hnf]; omega)
      (fun h => nomatch h)
      (fun _ => by rw [hcmpR]; exact ConLeche.isEquivList_self _)
      (fun _ => by
        rw [hal, hcmpR, htake, List.take_append_of_le_length (by omega), hctake]
        exact defEqList_sound hin (defEqList_refl _))
      (teleArity_sound hpisE)
      (fun _ => by
        rw [hal]
        exact certsF_sound hin (ConLeche.Rules.iotaCertsFull_bridge (ConLeche.Rules.bridge env F).2.2.1
          (ConLeche.Rules.bridge env F).2.2.2.1 hc))
      (fun _ hne => absurd hmI hne) (fun _ hne => absurd hmI hne)
    exact hfin _ _ hPlen hι

/-! ## The source rule -/

/-- Related lists over one list, mapped pointwise. -/
theorem forall₂_map_same {α β γ : Type} {R : β → γ → Prop} {f : α → β} {g : α → γ}
    (h : ∀ x, R (f x) (g x)) : ∀ l : List α, List.Forall₂ R (l.map f) (l.map g)
  | [] => .nil
  | x :: l => .cons (h x) (forall₂_map_same h l)

/-- The readings of a prefix of a spine's arguments, unmarked. -/
theorem mapM_unmark_take {as : List Expr} {cas : List ConLeche.Expr}
    (h : List.Forall₂ (fun a ca => toCL? (unmark a) = some ca) as cas) :
    ∀ n : Nat, ((as.take n).map unmark).mapM toCL? = some (cas.take n) := by
  induction h with
  | nil => intro n; simp
  | @cons a ca _ _ ha _ ih =>
    intro n
    cases n with
    | zero => rfl
    | succ n =>
      rw [List.take_succ_cons, List.map_cons, List.mapM_cons, ha, ih n]
      rfl

/-- The members of the second of two related lists are related to some member of the first. -/
theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) : ∀ b ∈ l₂, ∃ a, R a b := by
  induction h with
  | nil => intro b hb; simp at hb
  | @cons a b' _ _ hab _ ih =>
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨a, hab⟩
    · exact ih b hb

/-- The `casesFrozen` case of `srcEval_sound`: the ι chain on the frozen discriminant
(`casesFrozen_redSem`) from the `casesOn` spine to its alternative `alt` applied to the frozen
projections of the discriminant, on the `unmark` readings; `hat`: the stored records the chain
reads; `hpf`: con-leche types the unmarked discriminant as a proof, so it denotes the point
(`proof_pt`); `hcert`: for a constructor with fields, the certificate of the ι step's telescope at
the unmarked parameters and discriminant. Reference: `eval_iota_sing` (`MR E/EWcbvEval.v:162`);
DV-25, DV-33. -/
theorem srcEval_sound_casesFrozen {c T C : Name} {us : List Level} {as : List Expr}
    {k nP nF : Nat} {d alt v : Expr}
    (hat : CasesFrozenAt env (Name.toCL c) (Name.toCL (mkRecName T)) (Name.toCL C) as.length k nP nF)
    (hm : as[k]? = some (markReduced d)) (halt : as[k + 1]? = some alt)
    (hpf : CLProofTerm env (unmark d))
    (hcert : 0 < nF → FrozenFieldsCert env T C us ((as.take nP).map unmark) (unmark d))
    (ihb : SemSim.{w} env
      (mkAppN alt ((List.range nF).map fun j => markErase (.proj T j d)).toArray) v) :
    SemSim.{w} env (mkAppN (.const c us) as.toArray) v := by
  rw [mkAppN_toArray] at ihb ⊢
  refine semSim_trans (fun hη => ?_) ihb
  obtain ⟨-, hηas⟩ := etaLams_foldl as _ hη
  have hηd : EtaLams d := (hηas _ (List.mem_of_getElem? hm)).2
  refine ⟨etaLams_foldl_of _ alt (hηas alt (List.mem_of_getElem? halt)) fun x hx => ?_,
    fun {c₀} hc hb => ?_⟩
  · simp only [List.mem_map] at hx
    obtain ⟨j, -, rfl⟩ := hx
    exact ⟨fun h => absurd h (by simp [markMD]), hηd⟩
  obtain ⟨cf, cargs, hcf, hall, rfl⟩ := toCL?_unmark_foldl as _ hc
  simp only [unmark, toCL?, Option.map_eq_map, Option.map_eq_some_iff] at hcf
  obtain ⟨cus, hcus, rfl⟩ := hcf
  have hfv0 := toCL?_hasFvar hc
  have hb0 := hb
  rw [mkAppN_bounded_iff] at hb
  obtain ⟨cd, hcd, hrd⟩ := forall₂_getElem? hall hm
  obtain ⟨calt, hcalt, hralt⟩ := forall₂_getElem? hall halt
  have hrd' : toCL? (unmark d) = some cd := by simpa [unmark] using hrd
  have hcdcl := hb.2 cd (List.mem_of_getElem? hcd)
  have hprojs : List.Forall₂ (fun a ca => toCL? (unmark a) = some ca)
      ((List.range nF).map fun j => markErase (.proj T j d))
      ((List.range nF).map fun j => ConLeche.Expr.proj (Name.toCL T) j cd) :=
    forall₂_map_same (fun j => by simp [unmark, toCL?, hrd']) _
  refine ⟨_, toCL?_unmark_foldl_of hprojs hralt,
    (mkAppN_bounded_iff _ _).mpr ⟨hb.2 calt (List.mem_of_getElem? hcalt), fun x hx => by
      simp only [List.mem_map] at hx
      obtain ⟨j, -, rfl⟩ := hx
      simpa [ConLeche.Expr.looseBVarsBounded] using hcdcl⟩, fun V _ m φ ta hta => ?_⟩
  obtain ⟨⟨fa, hfa⟩, -⟩ := denote_mkAppN_inv m φ cargs hta
  have hfvA : ∀ a ∈ cargs, a.hasFvar = false := fun a ha => by
    obtain ⟨x, hx⟩ := forall₂_mem_right hall a ha
    exact toCL?_hasFvar hx
  obtain ⟨cd', F, Td, hcd', hinf, hpr⟩ := hpf
  rw [hrd'] at hcd'
  obtain ⟨⟩ := hcd'
  have hr := casesFrozen_redSem m φ (S := Name.toCL T) hat (forall₂_length hall).symm hb.2 hfvA
    (fun cvD val hint hf => denote_const_len m φ hf ⟨fa, hfa⟩) hcd hcalt
    (fun ea hea ρ => proof_pt m φ hinf hpr (toCL?_hasFvar hrd') hcdcl hea ρ)
    (fun hnF => by
      obtain ⟨cvR, mI, rP, isK, rules, rl, cvC, nP', nF', ind, cus', cps, cd'', F', hfR, hrl, hfC,
        hcus', hcps, hcd'', hc⟩ := hcert hnF
      rw [hcus] at hcus'
      obtain ⟨⟩ := hcus'
      rw [mapM_unmark_take hall nP] at hcps
      obtain ⟨⟩ := hcps
      rw [hrd'] at hcd''
      obtain ⟨⟩ := hcd''
      exact ⟨cvR, mI, rP, isK, rules, rl, cvC, nP', nF', ind, F', hfR, hrl, hfC, hc⟩)
  have hnil := ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hfv0
  have hnc : ∀ l, l ∉ (ConLeche.Expr.mkAppN (.const (Name.toCL c) cus) cargs).fvarLeaves :=
    fun l hl => by rw [hnil] at hl; cases hl
  obtain ⟨-, -, va, hva, hs⟩ := hr ⟨ConLeche.Expr.WScoped.of_not_hasFvar hfv0, hb0,
    fun l hl => absurd hl (hnc l)⟩ (ctx0 m φ hnc).1 hta
  exact ⟨va, hva, fun ρ hwd hne => hs ρ (Sat_nil V ρ) ((ctx0 m φ hnc).2 ρ) hwd hne⟩

end SemCases

end EraseProof
