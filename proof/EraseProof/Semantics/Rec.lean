import EraseProof.Semantics.Iota
import ConLeche.Kernel.Basis

/-!
# The meaning of source evaluation: the recursor ι and the quotient

The cases `recIota`, `quotLift` and `quotMk` of `srcEval_sound`, in the form of
`EraseProof.Semantics.Iota`: the congruence at the evaluated arguments, then con-leche's ι
(`CL ConLeche/Rules/Rel.lean:207 Red.iota`, case 2 of its case split) at the stored rule of the
major's constructor, on the `unmark` readings. A recursor's stored rule (`RecIotaAt`) applies its
constructor's minor premise to the fields and to one recursive call per recursive field, which
the source semantics evaluates before the minor premise runs. The quotient's lift is the stored
recursor of con-leche's `Quot` basis pin (`CL ConLeche/Kernel/Basis/Quot.lean:58 quotLiftA`),
whose one rule applies the function to the packed element.
-/

open Lean Erasure
open ConLeche.Semantics ConLeche.SetModel ConLeche.SetTheory ConLeche.Verify ConLeche.Model
  ConLeche.Model.Rules

namespace EraseProof

universe w

namespace SemCases

variable {env : ConLeche.Env}

/-! ## con-leche syntax -/

/-- The stored records the ι step of the recursor `R` reads at the constructor `cj` with `nP`
parameters and `nF` fields: `R` is a recursor without indices whose rule prefix (parameters,
motives, minor premises) has length `rP`, with `rP + 1` leading Π in its type and distinct level
parameters; `cj` is a stored constructor; the rule for `cj` has `nF` fields and its right-hand side
is `rP + nF` λs over the prefix variable at position `pos` (the constructor's minor premise)
applied to the field variables and then to one recursive call per entry `f` of `ihf`, the recursor
at its own level parameters applied to the prefix variables and the field variable `f`; the ι case
split's case 2 holds by the stored facts (`CL ConLeche/Kernel/CoreDefs.lean:1040 iotaNoCert`: a K
rule, or a family never `Prop`). Reference: the rule shape of
`CL ConLeche/Kernel/Inductives/GenRec.lean:189 classGenRule`, which `RulesCanonical` checks. -/
def RecIotaAt (env : ConLeche.Env) (R cj : ConLeche.Name) (rP pos nP nF : Nat) (ihf : List Nat) :
    Prop :=
  ∃ (cvR : ConLeche.ConstantVal) (isK : Bool) (rules : List ConLeche.RecRule)
    (cvj : ConLeche.ConstantVal) (induct : ConLeche.Name) (rl : ConLeche.RecRule),
    env.find? R = some (.recInfo cvR rP rP isK rules) ∧ cvR.levelParams.Nodup ∧
    clPis cvR.type = rP + 1 ∧ pos < rP ∧
    env.find? cj = some (.ctorInfo cvj nP nF induct) ∧
    rules.find? (fun r => r.ctor == cj) = some rl ∧ rl.nfields = nF ∧
    clLams rl.rhs = (rP + nF, ConLeche.Expr.mkAppN (.bvar (nF + (rP - 1 - pos)))
      (fbv nF nF ++ ihf.map fun f => ConLeche.Expr.mkAppN (.const R (cvR.levelParams.map .param))
        (fbv rP (rP + nF) ++ [.bvar (nF - 1 - f)]))) ∧
    ConLeche.iotaNoCert env.find? isK induct (ConLeche.recFireLevelCount rl cvj.levelParams) = true

/-- A recursor at its own level parameters, instantiated at levels of their number: the levels.
Reference: none. -/
theorem subst_params : ∀ {lps : List ConLeche.Name} {us : List ConLeche.Level}, lps.Nodup →
    us.length = lps.length → (lps.map .param).map (ConLeche.Level.subst lps us) = us
  | [], [], _, _ => rfl
  | p :: ps, u :: us, hnd, hl => by
    obtain ⟨hp, hnd'⟩ := List.nodup_cons.mp hnd
    simp only [List.map_cons, List.cons.injEq]
    refine ⟨by simp [ConLeche.Level.subst, ConLeche.Level.subst.go],
      Eq.trans ?_ (subst_params hnd' (by simpa using hl))⟩
    simp only [List.map_map]
    refine List.map_congr_left fun q hq => ?_
    have hpq : p ≠ q := fun h => hp (h ▸ hq)
    simp [ConLeche.Level.subst, ConLeche.Level.subst.go, hpq]
  | [], _ :: _, _, hl | _ :: _, [], _, hl => by simp at hl

/-- Entries read off a list by indices are entries of the list. -/
theorem mem_of_mapM_getElem {α : Type} {l : List α} : ∀ {is : List Nat} {r : List α},
    (is.mapM fun i => l[i]?) = some r → ∀ x ∈ r, x ∈ l
  | [], r, h, x, hx => by simp at h; subst h; simp at hx
  | i :: is, r, h, x, hx => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨a, ha, as, has, rfl⟩ := h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_of_getElem? ha
    · exact mem_of_mapM_getElem has x hx

/-- Indices read off related lists give related lists. -/
theorem mapM_getElem_forall₂ {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) : ∀ {is : List Nat} {r₁ : List α},
      (is.mapM fun i => l₁[i]?) = some r₁ →
      ∃ r₂, (is.mapM fun i => l₂[i]?) = some r₂ ∧ List.Forall₂ R r₁ r₂
  | [], r₁, hr => by simp at hr; subst hr; exact ⟨[], rfl, .nil⟩
  | i :: is, r₁, hr => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at hr
    obtain ⟨a, ha, as, has, rfl⟩ := hr
    obtain ⟨b, hb, hab⟩ := forall₂_getElem? h ha
    obtain ⟨bs, hbs, habs⟩ := mapM_getElem_forall₂ h has
    exact ⟨b :: bs, by simp [List.mapM_cons, hb, hbs], .cons hab habs⟩

/-- A map along indices read off a list. -/
theorem map_of_mapM {α β : Type} {l : List α} {F : Nat → β} {G : α → β}
    (hFG : ∀ i x, l[i]? = some x → F i = G x) : ∀ {is : List Nat} {r : List α},
      (is.mapM fun i => l[i]?) = some r → is.map F = r.map G
  | [], r, h => by simp at h; subst h; rfl
  | i :: is, r, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨a, ha, as, has, rfl⟩ := h
    simp [hFG i a ha, map_of_mapM hFG has]

/-- Related lists, mapped. -/
theorem forall₂_map {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop} {g : α → γ}
    {g' : β → δ} (hg : ∀ a b, R a b → S (g a) (g' b)) {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) : List.Forall₂ S (l₁.map g) (l₂.map g') := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (hg _ _ hab) ih

/-- ι at a stored recursor without indices whose major prepares to a constructor application, the
ι case split at case 2: `CL ConLeche/Rules/Rel.lean:207 Red.iota`, the reduct
`CL ConLeche/Kernel/CoreDefs.lean:1016 RecRule.iotaReduct` at the leading arguments and the
fields. Reference: `eval_iota` (`MR P/PCUICWcbvEval.v:253`). -/
theorem iota_red {R cj induct : ConLeche.Name} {cvR cvj : ConLeche.ConstantVal} {mI rP nP nF : Nat}
    {isK : Bool} {rules : List ConLeche.RecRule} {rl : ConLeche.RecRule}
    (hfR : env.find? R = some (.recInfo cvR mI rP isK rules))
    (hpis : (ConLeche.Expr.peelPis (mI + 1) cvR.type).isSome = true) (hrP : rP ≤ mI)
    (hfj : env.find? cj = some (.ctorInfo cvj nP nF induct))
    (hrl : rules.find? (fun r => r.ctor == cj) = some rl) (hnf : rl.nfields = nF)
    {us usj : List ConLeche.Level} {args cps cfs : List ConLeche.Expr} {cmaj : ConLeche.Expr}
    (hlen : args.length = mI) (hus : us.length = cvR.levelParams.length)
    (hmaj : ConLeche.Rules.Red env 0 cmaj (ConLeche.Expr.mkAppN (.const cj usj) (cps ++ cfs)))
    (hcps : cps.length = nP) (hcfs : cfs.length = nF)
    (hcase : ConLeche.Rules.IotaCaseS env isK induct (ConLeche.recFireComparands rl nP
      cvR.levelParams us cvj.levelParams (args ++ [cmaj]) rP).1 false) :
    ConLeche.Rules.Red env 0 (ConLeche.Expr.mkAppN (.const R us) (args ++ [cmaj]))
      (rl.iotaReduct cvR.levelParams us rP (args.take rP ++ cfs)) := by
  have hargs : (ConLeche.Expr.mkAppN (.const R us) (args ++ [cmaj])).getAppArgs = args ++ [cmaj] := by
    simp [ConLeche.Expr.getAppArgs_mkAppN, ConLeche.Expr.getAppArgs]
  have hmajE : (ConLeche.Expr.mkAppN (.const R us) (args ++ [cmaj])).getAppArgs.getD mI (.bvar 0) =
      cmaj := by
    rw [hargs, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    simp [hlen]
  have hι := @ConLeche.Rules.Red.iota env 0 _ R us cvR mI rP isK rules
    (ConLeche.Expr.mkAppN (.const cj usj) (cps ++ cfs)) cj usj cvj nP nF induct rl (.bvar 0) false
    (by simp [ConLeche.Expr.getAppFn_mkAppN, ConLeche.Expr.getAppFn]) hfR
    (by rw [hargs]; simp [hlen]) hus (hmajE ▸ hmaj)
    (by simp [ConLeche.Expr.getAppFn_mkAppN, ConLeche.Expr.getAppFn]) hfj hrl
    (by simp [ConLeche.Expr.getAppArgs_mkAppN, ConLeche.Expr.getAppArgs, hcps, hcfs, hnf])
    (by rw [hargs]; exact hcase) (fun h => nomatch h) (fun h => nomatch h)
    (by rw [hargs, List.length_append, hlen]
        exact ConLeche.Rules.peelPis_isSome_instantiateLevelParams _ _ _ hpis)
    (fun h => nomatch h) (fun h => nomatch h) (fun h => nomatch h)
  have hvals : (ConLeche.Expr.mkAppN (.const R us) (args ++ [cmaj])).getAppArgs.take rP ++
      (ConLeche.Expr.mkAppN (.const cj usj) (cps ++ cfs)).getAppArgs.drop nP = args.take rP ++ cfs := by
    rw [hargs, List.take_append_of_le_length (by omega)]
    simp [ConLeche.Expr.getAppArgs_mkAppN, ConLeche.Expr.getAppArgs, List.drop_left' hcps]
  rwa [hvals] at hι

/-- The ι chain of a recursor without indices on the readings: the spine `R us (pre ++ [cmaj])`
whose major reduces to the constructor application `cj usj (cps ++ cfs)` reduces to the minor
premise `pre[pos]` applied to the fields `cfs` and to the recursive calls `R us (pre ++ [x])` on
the fields `crfs` the rule names (`iota_red` at the stored rule, its reduct computed). Reference:
`eval_iota` (`MR P/PCUICWcbvEval.v:253`); DV-30. -/
theorem recIota_red {R cj : ConLeche.Name} {rP pos nP nF : Nat} {ihf : List Nat}
    (hat : RecIotaAt env R cj rP pos nP nF ihf) {us usj : List ConLeche.Level}
    {pre cps cfs crfs : List ConLeche.Expr} {cmaj cmk : ConLeche.Expr}
    (hlen : pre.length = rP) (hcl : ∀ a ∈ pre, a.looseBVarsBounded 0 = true)
    (hus : ∀ ci, env.find? R = some ci → us.length = ci.toConstantVal.levelParams.length)
    (hk : pre[pos]? = some cmk)
    (hmaj : ConLeche.Rules.Red env 0 cmaj (ConLeche.Expr.mkAppN (.const cj usj) (cps ++ cfs)))
    (hcps : cps.length = nP) (hcfs : cfs.length = nF)
    (hcfl : ∀ x ∈ cfs, x.looseBVarsBounded 0 = true)
    (hrfs : (ihf.mapM fun f => cfs[f]?) = some crfs) :
    ConLeche.Rules.Red env 0 (ConLeche.Expr.mkAppN (.const R us) (pre ++ [cmaj]))
      (ConLeche.Expr.mkAppN cmk
        (cfs ++ crfs.map fun x => ConLeche.Expr.mkAppN (.const R us) (pre ++ [x]))) := by
  obtain ⟨cvR, isK, rules, cvj, induct, rl, hfR, hnd, hpis, hpos, hfj, hrl, hnf, hrhs, hnc⟩ := hat
  have husl : us.length = cvR.levelParams.length := hus _ hfR
  have hι := iota_red hfR (peelPis_of_clPis hpis) (Nat.le_refl rP) hfj hrl hnf hlen husl hmaj hcps
    hcfs (.stored (by rw [ConLeche.recFireComparands_fst_length]; exact hnc))
  rw [List.take_of_length_le (by omega)] at hι
  have hvlen : (pre ++ cfs).length = rP + nF := by simp [hlen, hcfs]
  have hpre : ∀ q (hq : q < rP), (pre ++ cfs).reverse[rP + nF - 1 - q]? = some pre[q] := by
    intro q hq
    rw [List.getElem?_reverse (by omega), hvlen, show rP + nF - 1 - (rP + nF - 1 - q) = q by omega,
      List.getElem?_append_left (by omega), List.getElem?_eq_getElem (by omega)]
  have hc : ((ConLeche.Expr.const R (cvR.levelParams.map .param)).instantiateLevelParams
      cvR.levelParams us).instantiateList (pre ++ cfs).reverse 0 = .const R us := by
    rw [ConLeche.Expr.instantiateLevelParams, ConLeche.Expr.instantiateList, subst_params hnd husl]
  have hfld : ∀ f x, cfs[f]? = some x → ((ConLeche.Expr.bvar (nF - 1 - f)).instantiateLevelParams
      cvR.levelParams us).instantiateList (pre ++ cfs).reverse 0 = x := by
    intro f x hx
    show (ConLeche.Expr.bvar _).instantiateList _ 0 = x
    have hf : f < nF := hcfs ▸ (List.getElem?_eq_some_iff.mp hx).1
    refine instantiateList_rev_bvar (by omega) ?_ (hcfl x (List.mem_of_getElem? hx))
    rw [hvlen, show rP + nF - 1 - (nF - 1 - f) = rP + f by omega,
      List.getElem?_append_right (by omega), hlen, show rP + f - rP = f by omega]
    exact hx
  have hred : rl.iotaReduct cvR.levelParams us rP (pre ++ cfs) = ConLeche.Expr.mkAppN cmk
      (cfs ++ crfs.map fun x => ConLeche.Expr.mkAppN (.const R us) (pre ++ [x])) := by
    unfold ConLeche.RecRule.iotaReduct
    rw [hnf, lamBody_of_clLams _ hrhs, ConLeche.instantiateLevelParams_mkAppN, instantiateList_mkAppN,
      List.map_append, List.map_append, fbv_instLP, List.map_map, List.map_map]
    congr 1
    · show (ConLeche.Expr.bvar (nF + (rP - 1 - pos))).instantiateList _ 0 = cmk
      refine instantiateList_rev_bvar (by omega) ?_ (hcl cmk (List.mem_of_getElem? hk))
      rw [hvlen, show rP + nF - 1 - (nF + (rP - 1 - pos)) = pos by omega,
        List.getElem?_append_left (by omega)]
      exact hk
    · congr 1
      · exact fbv_instantiateList hcfs hcfl fun f hf => by
          rw [List.getElem?_reverse (by omega), hvlen,
            show rP + nF - 1 - (nF - 1 - f) = rP + f by omega,
            List.getElem?_append_right (by omega), hlen, show rP + f - rP = f by omega,
            List.getElem?_eq_getElem (by omega)]
      · refine map_of_mapM (fun f x hx => ?_) hrfs
        simp only [Function.comp]
        rw [ConLeche.instantiateLevelParams_mkAppN, instantiateList_mkAppN, List.map_append,
          List.map_append, fbv_instLP, List.map_singleton, List.map_singleton, hc,
          fbv_instantiateList hlen hcl hpre, hfld f x hx]
  rw [hred] at hι
  exact hι

/-! ## Readings of recursor spines -/

/-- A spine with a constant as its value has no arguments. -/
theorem foldl_app_const {f : Expr} {n : Name} {ls : List Level} {as : List Expr}
    (h : as.foldl .app f = .const n ls) : as = [] ∧ f = .const n ls := by
  rcases List.eq_nil_or_concat as with rfl | ⟨L, b, rfl⟩
  · exact ⟨rfl, h⟩
  · simp at h

/-- The major premise's value in constructor form (`natLitCtor`) is a constructor application
`C (ps ++ fs)`: its fields' `eta` marks sit on λs where the value's do, and the value's reading
reduces to the constructor application of the readings, by `Red.refl`, or at a `Nat` literal by
`CL ConLeche/Rules/Rel.lean:149 Red.natLit` (the `Nat` basis stored since the literal reads).
Reference: none. -/
theorem natLitCtor_maj {mj : Expr} {C : Name} {usC : List Level} {ps fs : List Expr}
    (hmv : natLitCtor mj = mkAppN (.const C usC) (ps ++ fs).toArray) :
    (EtaLams mj → ∀ x ∈ fs, EtaLams x) ∧
    ∀ cmj : ConLeche.Expr, toCL? (unmark mj) = some cmj → cmj.looseBVarsBounded 0 = true →
      ∃ usj cps cfs, cps.length = ps.length ∧
        List.Forall₂ (fun a ca => toCL? (unmark a) = some ca) fs cfs ∧
        (∀ x ∈ cfs, x.looseBVarsBounded 0 = true) ∧
        ∀ (V : Type w) [ConLeche.SetTheory V] (m : EnvModelM V env) (φ : ConLeche.Name → Nat),
          (∃ ta, denote m.base2.acval env φ 0 cmj = some ta) →
          ConLeche.Rules.Red env 0 cmj
            (ConLeche.Expr.mkAppN (.const (Name.toCL C) usj) (cps ++ cfs)) := by
  rw [mkAppN_toArray] at hmv
  cases hl : mj.rawNatLit? with
  | none =>
    simp only [natLitCtor, hl] at hmv
    subst hmv
    refine ⟨fun hη x hx => ?_, fun cmj hcmj hcl => ?_⟩
    · rw [List.foldl_append] at hη; exact (etaLams_foldl _ _ hη).2 x hx
    · rw [List.foldl_append] at hcmj
      obtain ⟨cf, cfs, hcf, hfs, rfl⟩ := toCL?_unmark_foldl fs _ hcmj
      obtain ⟨cc, cps, hcc, hps, rfl⟩ := toCL?_unmark_foldl ps _ hcf
      simp only [unmark, toCL?, Option.map_eq_map, Option.map_eq_some_iff] at hcc
      obtain ⟨usC', -, rfl⟩ := hcc
      refine ⟨usC', cps, cfs, (forall₂_length hps).symm, hfs, ((mkAppN_bounded_iff _ _).mp hcl).2,
        fun _ _ _ _ _ => ?_⟩
      rw [clMkAppN_append]; exact .refl
  | some n =>
    have hmj : mj = .lit (.natVal n) := by
      cases mj with
      | lit l => cases l with
        | natVal k => simp only [Expr.rawNatLit?, Option.some.injEq] at hl; rw [hl]
        | strVal _ => simp [Expr.rawNatLit?] at hl
      | _ => simp [Expr.rawNatLit?] at hl
    subst hmj
    have hcmj : ∀ cmj, toCL? (unmark (Expr.lit (.natVal n))) = some cmj → cmj = .lit (.natVal n) :=
      fun cmj h => by simp only [unmark, toCL?, Option.some.injEq] at h; exact h.symm
    cases n with
    | zero =>
      have hmv' : Expr.const ``Nat.zero [] = (ps ++ fs).foldl .app (.const C usC) := hmv
      obtain ⟨h, hc⟩ := foldl_app_const hmv'.symm
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp h
      cases hc
      refine ⟨fun _ x hx => by simp at hx, fun cmj h _ => ?_⟩
      rw [hcmj cmj h]
      exact ⟨[], [], [], rfl, .nil, fun _ h => by simp at h,
        fun V _ m φ hd => .natLit (natLitStored_of_denote m φ hd)⟩
    | succ k =>
      have hmv' : Expr.app (.const ``Nat.succ []) (.lit (.natVal k)) =
          (ps ++ fs).foldl .app (.const C usC) := hmv
      rcases List.eq_nil_or_concat (ps ++ fs) with h | ⟨L, b, h⟩
      · rw [h] at hmv'; cases hmv'
      rw [h, List.concat_eq_append, List.foldl_append] at hmv'
      simp only [List.foldl_cons, List.foldl_nil, Expr.app.injEq] at hmv'
      obtain ⟨hL, hc⟩ := foldl_app_const hmv'.1.symm
      subst hL
      cases hc
      rw [List.concat_eq_append, List.nil_append, ← hmv'.2] at h
      refine ⟨fun _ x hx => ?_, fun cmj h' _ => ?_⟩
      · have : x ∈ ps ++ fs := List.mem_append_right _ hx
        rw [h, List.mem_singleton] at this
        subst this; trivial
      rw [hcmj cmj h']
      rcases List.append_eq_singleton_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨[], [], [.lit (.natVal k)], rfl, .cons rfl .nil,
          fun x hx => by simp at hx; subst hx; rfl,
          fun V _ m φ hd => .natLit (natLitStored_of_denote m φ hd)⟩
      · exact ⟨[], [.lit (.natVal k)], [], rfl, .nil, fun _ h => by simp at h,
          fun V _ m φ hd => .natLit (natLitStored_of_denote m φ hd)⟩

/-- The reduction of a recursor spine whose major value `mj` reads as a spine that reduces to the
constructor `cj` applied to parameters and the readings of the fields `fs` (`recIota_red`): to the
minor premise `pre[pos]` applied to the fields and to the recursive calls on the fields `rfs` the
rule names. Reference: `eval_iota` (`MR P/PCUICWcbvEval.v:253`); DV-30. -/
theorem recSim {c : Name} {us : List Level} {cj : ConLeche.Name} {pre fs rfs : List Expr}
    {pos nP : Nat} {ihf : List Nat} {mj mk : Expr}
    (hat : RecIotaAt env (Name.toCL c) cj pre.length pos nP fs.length ihf)
    (hk : pre[pos]? = some mk) (hrfs : (ihf.mapM fun f => fs[f]?) = some rfs)
    (hηfs : EtaLams mj → ∀ x ∈ fs, EtaLams x)
    (hmaj : ∀ cmj : ConLeche.Expr, toCL? (unmark mj) = some cmj → cmj.looseBVarsBounded 0 = true →
      ∃ usj cps cfs, cps.length = nP ∧
        List.Forall₂ (fun a ca => toCL? (unmark a) = some ca) fs cfs ∧
        (∀ x ∈ cfs, x.looseBVarsBounded 0 = true) ∧
        ∀ (V : Type w) [ConLeche.SetTheory V] (m : EnvModelM V env) (φ : ConLeche.Name → Nat),
          (∃ ta, denote m.base2.acval env φ 0 cmj = some ta) →
          ConLeche.Rules.Red env 0 cmj (ConLeche.Expr.mkAppN (.const cj usj) (cps ++ cfs))) :
    SemSim.{w} env ((pre ++ [mj]).foldl .app (.const c us))
      ((fs ++ rfs.map fun f : Expr => (pre ++ [f]).foldl Expr.app (Expr.const c us)).foldl .app mk) := by
  refine semSim_of_redD fun hη => ?_
  obtain ⟨-, hηas⟩ := etaLams_foldl _ _ hη
  have hηpre : ∀ x ∈ pre, EtaLams x := fun x hx => hηas x (List.mem_append_left _ hx)
  have hηfs' := hηfs (hηas mj (by simp))
  refine ⟨etaLams_foldl_of _ _ (hηpre mk (List.mem_of_getElem? hk)) fun x hx => ?_,
    fun c₀ hc hb => ?_⟩
  · rcases List.mem_append.mp hx with hx | hx
    · exact hηfs' x hx
    · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hx
      refine etaLams_foldl_of (pre ++ [f]) (.const c us) trivial fun y hy => ?_
      rcases List.mem_append.mp hy with hy | hy
      · exact hηpre y hy
      · rw [List.mem_singleton.mp hy]; exact hηfs' f (mem_of_mapM_getElem hrfs f hf)
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil] at hc
  obtain ⟨cx, cmj, hcx, hcmj, rfl⟩ := toCL?_unmark_app hc
  obtain ⟨cf, cpre, hcf, hpre, rfl⟩ := toCL?_unmark_foldl pre _ hcx
  have hcf' := hcf
  simp only [unmark, toCL?, Option.map_eq_map, Option.map_eq_some_iff] at hcf'
  obtain ⟨us', -, rfl⟩ := hcf'
  simp only [ConLeche.Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hclpre := ((mkAppN_bounded_iff _ _).mp hb.1).2
  obtain ⟨usj, cps, cfs, hcps, hfs, hcfl, hred⟩ := hmaj cmj hcmj hb.2
  obtain ⟨crfs, hcrfs, hrc⟩ := mapM_getElem_forall₂ hfs hrfs
  obtain ⟨cmk, hcmk, hrmk⟩ := forall₂_getElem? hpre hk
  have hih : ∀ f cf', toCL? (unmark f) = some cf' →
      toCL? (unmark ((pre ++ [f]).foldl .app (.const c us))) =
        some (ConLeche.Expr.mkAppN (.const (Name.toCL c) us') (cpre ++ [cf'])) := fun f cf' h => by
    rw [List.foldl_append, clMkAppN_append]; exact toCL?_unmark_foldl_of (.cons h .nil) hcx
  refine ⟨ConLeche.Expr.mkAppN cmk
      (cfs ++ crfs.map fun x => ConLeche.Expr.mkAppN (.const (Name.toCL c) us') (cpre ++ [x])), ?_,
    (mkAppN_bounded_iff _ _).mpr ⟨hclpre cmk (List.mem_of_getElem? hcmk), fun x hx => ?_⟩,
    fun V _ m φ ta hta => ?_⟩
  · rw [List.foldl_append, clMkAppN_append]
    exact toCL?_unmark_foldl_of (forall₂_map (S := fun a ca => toCL? (unmark a) = some ca)
      (g := fun f : Expr => (pre ++ [f]).foldl Expr.app (Expr.const c us))
      (g' := fun x => ConLeche.Expr.mkAppN (.const (Name.toCL c) us') (cpre ++ [x]))
      (fun a b h => hih a b h) hrc) (toCL?_unmark_foldl_of hfs hrmk)
  · rcases List.mem_append.mp hx with hx | hx
    · exact hcfl x hx
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      refine (mkAppN_bounded_iff _ _).mpr ⟨rfl, fun z hz => ?_⟩
      rcases List.mem_append.mp hz with hz | hz
      · exact hclpre z hz
      · rw [List.mem_singleton.mp hz]; exact hcfl y (mem_of_mapM_getElem hcrfs y hy)
  · have hta' : denote m.base2.acval env φ 0
        (ConLeche.Expr.mkAppN (.const (Name.toCL c) us') (cpre ++ [cmj])) = some ta := by
      rw [clMkAppN_append]; exact hta
    obtain ⟨⟨fa, hfa⟩, hargs⟩ := denote_mkAppN_inv m φ _ hta'
    have := recIota_red hat (forall₂_length hpre).symm hclpre
      (fun ci hf => denote_const_len m φ hf ⟨fa, hfa⟩) hcmk
      (hred V m φ (hargs cmj (by simp))) hcps (forall₂_length hfs).symm hcfl hcrfs
    rw [clMkAppN_append _ cpre [cmj]] at this
    exact this

/-- Pointwise evaluations of two concatenations, from those of their parts. -/
theorem simAt_append {as₁ vs₁ as₂ vs₂ : List Expr} (hl : as₁.length = vs₁.length)
    (h₁ : ∀ (i : Nat) a v, as₁[i]? = some a → vs₁[i]? = some v → SemSim.{w} env a v)
    (h₂ : ∀ (i : Nat) a v, as₂[i]? = some a → vs₂[i]? = some v → SemSim.{w} env a v) :
    ∀ (i : Nat) a v, (as₁ ++ as₂)[i]? = some a → (vs₁ ++ vs₂)[i]? = some v →
      SemSim.{w} env a v := by
  intro i a v ha hv
  by_cases hi : i < as₁.length
  · rw [List.getElem?_append_left hi] at ha
    rw [List.getElem?_append_left (hl ▸ hi)] at hv
    exact h₁ i a v ha hv
  · rw [List.getElem?_append_right (by omega)] at ha
    rw [List.getElem?_append_right (by omega), ← hl] at hv
    exact h₂ _ a v ha hv

/-- Pointwise evaluations of a list to itself. -/
theorem simAt_refl (as : List Expr) :
    ∀ (i : Nat) a v, as[i]? = some a → as[i]? = some v → SemSim.{w} env a v :=
  fun _ a _ ha hv => by rw [ha] at hv; cases hv; exact semSim_refl a

/-- Pointwise evaluation of a singleton. -/
theorem simAt_single {a v : Expr} (h : SemSim.{w} env a v) :
    ∀ (i : Nat) a' v', [a][i]? = some a' → [v][i]? = some v' → SemSim.{w} env a' v'
  | 0, _, _, ha, hv => by simp at ha hv; subst ha hv; exact h
  | _ + 1, _, _, ha, _ => by simp at ha

/-! ## The cases -/

/-- The `recIota` case of `srcEval_sound`: the congruence at the minor premises and the major
premise to the recursor spine of their values (`spineSim`, the spine graded, `hok`), the ι chain
(`recSim`) at the constructor form `C ps' fs` of the major's value (`natLitCtor`: a `Nat` literal
in constructor form), then the congruence at the recursive calls to their values (`spineSim`, the
minor premise applied to the fields and the values graded, `hok'`); `hat`: the stored records the
chain reads. Reference: `eval_iota` (`MR P/PCUICWcbvEval.v:253`) at a recursor under call by
value; DV-30, DV-33. -/
theorem srcEval_sound_recIota {c : Name} {us : List Level} {ps ms mins mvs : List Expr}
    {maj mj mk v : Expr} {C : Name} {usC : List Level} {ps' fs rfs ihvs : List Expr} {k : Nat}
    {ihf : List Nat}
    (hat : RecIotaAt env (Name.toCL c) (Name.toCL C) (ps.length + ms.length + mvs.length)
      (ps.length + ms.length + k) ps'.length fs.length ihf)
    (hlen : mins.length = mvs.length) (hmk : mvs[k]? = some mk)
    (hmv : natLitCtor mj = mkAppN (.const C usC) (ps' ++ fs).toArray)
    (hrfs : (ihf.mapM fun f => fs[f]?) = some rfs) (hihl : rfs.length = ihvs.length)
    (hok : GradedU.{w} env (mkAppN (.const c us) (ps ++ ms ++ mvs ++ [mj]).toArray))
    (hok' : GradedU.{w} env (mkAppN mk (fs ++ ihvs).toArray))
    (ihmin : ∀ (i : Nat) m mv, mins[i]? = some m → mvs[i]? = some mv → SemSim.{w} env m mv)
    (ihmaj : SemSim.{w} env maj mj)
    (ihih : ∀ (i : Nat) f w', rfs[i]? = some f → ihvs[i]? = some w' →
      SemSim.{w} env (mkAppN (.const c us) (ps ++ ms ++ mvs ++ [f]).toArray) w')
    (ihb : SemSim.{w} env (mkAppN mk (fs ++ ihvs).toArray) v) :
    SemSim.{w} env (mkAppN (.const c us) (ps ++ ms ++ mins ++ [maj]).toArray) v := by
  simp only [mkAppN_toArray] at hok hok' ihih ihb ⊢
  have h₁ : SemSim.{w} env ((ps ++ ms ++ mins ++ [maj]).foldl .app (.const c us))
      ((ps ++ ms ++ mvs ++ [mj]).foldl .app (.const c us)) :=
    spineSim (by simp [hlen]) (simAt_append (by simp [hlen])
      (simAt_append rfl (simAt_refl (ps ++ ms)) ihmin) (simAt_single ihmaj)) hok (semSim_refl _)
  have h₃ : SemSim.{w} env
      ((fs ++ rfs.map fun f : Expr => ((ps ++ ms ++ mvs) ++ [f]).foldl Expr.app (Expr.const c us)).foldl
        .app mk)
      ((fs ++ ihvs).foldl .app mk) :=
    spineSim (by simp [hihl]) (simAt_append rfl (simAt_refl fs) fun i a w' ha hw => by
      rw [List.getElem?_map] at ha
      obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.mp ha
      exact ihih i f w' hf hw) hok' (semSim_refl _)
  obtain ⟨hηfs, hmaj⟩ := natLitCtor_maj (env := env) hmv
  have hl : (ps ++ ms ++ mvs).length = ps.length + ms.length + mvs.length := by
    simp [Nat.add_assoc]
  rw [← hl] at hat
  have hk : (ps ++ ms ++ mvs)[ps.length + ms.length + k]? = some mk := by
    rw [List.getElem?_append_right (by simp)]
    simpa using hmk
  have h₂ := recSim (us := us) hat hk hrfs hηfs hmaj
  exact semSim_trans h₁ (semSim_trans h₂ (semSim_trans h₃ ihb))

/-! ## The quotient -/

/-- The stored records of the quotient package's lift and constructor: `cL` is stored as the pin
`Quot.lift` (`CL ConLeche/Kernel/Basis/Quot.lean:58 quotLiftA`) at its record's level-parameter
names, two and distinct (`CL ConLeche/Kernel/Basis.lean:175 quotPinHit`), and `cM` as the pin
`Quot.mk` (`CL ConLeche/Kernel/Basis/Quot.lean:38 quotMkA`) at its record's: what con-leche stores
of an accepted quotient record (`CL ConLeche/Kernel/Basis.lean:169 quotAt`). Reference: none. -/
def QuotLiftAt (env : ConLeche.Env) (cL cM : ConLeche.Name) : Prop :=
  ∃ cvL cvM, env.find? cL = some (ConLeche.quotAt .lift cvL) ∧
    ConLeche.quotPinHit .lift cvL = true ∧ env.find? cM = some (ConLeche.quotAt .ctor cvM)

/-- The quotient's ι on the readings: the stored lift applied to `α r β f h` and the packed
element `Quot.mk α' r' a` reduces to `f a`, by `iota_red` at the pin's one rule (the function slot
applied to the element), the ι case split at case 2 (`hcase`, at the comparand level, the
quotient's universe). Its meaning in the model is the pin's lift law
(`CL ConLeche/Model/BasisQuot.lean:2301 quotLiftLaw`), which `red_sound` reads. Reference: none
(DV-29). -/
theorem quotLift_red {cL cM : ConLeche.Name} (hat : QuotLiftAt env cL cM)
    {us usM : List ConLeche.Level} {cα cr cβ cf ch cα' cr' ca : ConLeche.Expr}
    (hus : ∀ ci, env.find? cL = some ci → us.length = ci.toConstantVal.levelParams.length)
    (hcase : ConLeche.Rules.IotaCaseS env false ConLeche.quotName (us.take 1) false)
    (hcf : cf.looseBVarsBounded 0 = true) (hca : ca.looseBVarsBounded 0 = true) :
    ConLeche.Rules.Red env 0 (ConLeche.Expr.mkAppN (.const cL us)
      [cα, cr, cβ, cf, ch, ConLeche.Expr.mkAppN (.const cM usM) [cα', cr', ca]]) (.app cf ca) := by
  obtain ⟨cvL, cvM, hfL, hpin, hfM⟩ := hat
  have hcM : cM = ConLeche.quotMkName := (ConLeche.Env.find?_name hfM).symm
  subst hcM
  obtain ⟨cv, rl, hq, hctor, hnf, hlps, hfire, hrhs, hpis⟩ : ∃ cv rl,
      ConLeche.quotAt .lift cvL = .recInfo cv 5 5 false [rl] ∧ rl.ctor = ConLeche.quotMkName ∧
      rl.nfields = 1 ∧ cv.levelParams = cvL.levelParams ∧
      rl.fire = .levels [ConLeche.Level.subst [ConLeche.uN, ConLeche.vN]
        (cvL.levelParams.map .param) (.param ConLeche.uN)] ∧
      clLams rl.rhs = (6, .app (.bvar 2) (.bvar 0)) ∧
      (ConLeche.Expr.peelPis 6 cv.type).isSome = true := by
    refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · rw [clLams_instLP]; rfl
    · exact ConLeche.Rules.peelPis_isSome_instantiateLevelParams _ _ _ rfl
  obtain ⟨cvj, hcj⟩ : ∃ cvj, ConLeche.quotAt .ctor cvM = .ctorInfo cvj 2 1 ConLeche.quotName :=
    ⟨_, rfl⟩
  rw [hq] at hfL
  rw [hcj] at hfM
  simp only [ConLeche.quotPinHit, Bool.and_eq_true, beq_iff_eq] at hpin
  have hl2 : cvL.levelParams.length = 2 := hpin.1.2
  have husl : us.length = 2 := by rw [hus _ hfL]; exact hlps ▸ hl2
  obtain ⟨p₀, p₁, hps⟩ : ∃ p₀ p₁, cvL.levelParams = [p₀, p₁] := by
    rcases h : cvL.levelParams with _ | ⟨p₀, _ | ⟨p₁, _ | _⟩⟩
    · rw [h] at hl2; simp at hl2
    · rw [h] at hl2; simp at hl2
    · exact ⟨p₀, p₁, rfl⟩
    · rw [h] at hl2; simp at hl2
  obtain ⟨u₀, u₁, rfl⟩ : ∃ u₀ u₁, us = [u₀, u₁] := by
    rcases us with _ | ⟨u₀, _ | ⟨u₁, _ | _⟩⟩
    · simp at husl
    · simp at husl
    · exact ⟨u₀, u₁, rfl⟩
    · simp at husl
  have hι := iota_red (us := [u₀, u₁]) (usj := usM) (args := [cα, cr, cβ, cf, ch])
    (cps := [cα', cr']) (cfs := [ca])
    (cmaj := ConLeche.Expr.mkAppN (.const ConLeche.quotMkName usM) ([cα', cr'] ++ [ca])) hfL hpis
    (Nat.le_refl 5) hfM (by simp [hctor]) hnf rfl (by rw [hlps, hps]; rfl) .refl rfl rfl (by
      have : (ConLeche.recFireComparands rl 2 cv.levelParams [u₀, u₁] cvj.levelParams
          ([cα, cr, cβ, cf, ch] ++ [ConLeche.Expr.mkAppN (.const ConLeche.quotMkName usM)
            ([cα', cr'] ++ [ca])]) 5).1 = [u₀] := by
        simp [ConLeche.recFireComparands, hfire, hlps, hps, ConLeche.Level.subst,
          ConLeche.Level.subst.go]
      rw [this]; exact hcase)
  have hred : rl.iotaReduct cv.levelParams [u₀, u₁] 5 ([cα, cr, cβ, cf, ch].take 5 ++ [ca]) =
      .app cf ca := by
    unfold ConLeche.RecRule.iotaReduct
    rw [hnf, lamBody_of_clLams _ hrhs]
    show ConLeche.Expr.instantiateList (.app (.bvar 2) (.bvar 0)) _ 0 = _
    rw [ConLeche.Expr.instantiateList, instantiateList_bvar0 (v := cf) rfl hcf,
      instantiateList_bvar0 (v := ca) rfl hca]
  rw [hred] at hι
  exact hι

/-- The `quotLift` case of `srcEval_sound`: the congruence at the function and the quotient
argument to the lift of their values (`spineSim`, the spine graded, `hok`), the quotient's ι
(`quotLift_red`: the function applied to the packed element), then β (`betaRed`); `hat`: the
stored pins, `hcase`: the ι case split's case 2 at the quotient's universe. Reference: `eval_beta`
(`MR P/PCUICWcbvEval.v:234`) after the quotient's ι; DV-29, DV-33. -/
theorem srcEval_sound_quotLift {c c' : Name} {us us' : List Level}
    {α r β f h q α' r' a A b v : Expr} {x : Name} {bi : BinderInfo}
    (hat : QuotLiftAt env (Name.toCL c) (Name.toCL c'))
    (hcase : ∀ usL, us.mapM Level.toCL = some usL →
      ConLeche.Rules.IotaCaseS env false ConLeche.quotName (usL.take 1) false)
    (hok : GradedU.{w} env (mkAppN (.const c us)
      [α, r, β, .lam x A b bi, h, mkAppN (.const c' us') [α', r', a].toArray].toArray))
    (ihf : SemSim.{w} env f (.lam x A b bi))
    (ihq : SemSim.{w} env q (mkAppN (.const c' us') [α', r', a].toArray))
    (ihb : SemSim.{w} env (b.instantiate1' a) v) :
    SemSim.{w} env (mkAppN (.const c us) [α, r, β, f, h, q].toArray) v := by
  simp only [mkAppN_toArray] at hok ihq ⊢
  refine semSim_trans (spineSim (vs := [α, r, β, .lam x A b bi, h,
      [α', r', a].foldl .app (.const c' us')]) rfl (simAt_append (as₁ := [α, r, β]) rfl (simAt_refl _)
    (simAt_append (as₁ := [f]) (vs₁ := [.lam x A b bi]) rfl (simAt_single ihf) (simAt_append (as₁ := [h]) rfl (simAt_refl _)
      (simAt_single ihq)))) hok (semSim_refl _)) (semSim_trans ?_ (semSim_trans (betaRed (n := x) (A := A) (bi := bi)) ihb))
  refine semSim_of_redD fun hη => ?_
  obtain ⟨-, hηas⟩ := etaLams_foldl _ _ hη
  refine ⟨⟨hηas (.lam x A b bi) (by simp),
    (etaLams_foldl [α', r', a] (.const c' us') (hηas _ (by simp))).2 a (by simp)⟩,
    fun c₀ hc hb => ?_⟩
  obtain ⟨cc, cargs, hcc, hall, rfl⟩ := toCL?_unmark_foldl _ _ hc
  rcases hall with _ | ⟨-, _ | ⟨-, _ | ⟨-, _ | @⟨_, cl, _, _, hcl, _ | ⟨-, _ | ⟨hcq, _ | _⟩⟩⟩⟩⟩⟩
  obtain ⟨cq, cqargs, hcq', hallq, rfl⟩ := toCL?_unmark_foldl _ _ hcq
  rcases hallq with _ | ⟨-, _ | ⟨-, _ | @⟨_, ca, _, _, hca, _ | _⟩⟩⟩
  simp only [unmark, toCL?, Option.map_eq_map, Option.map_eq_some_iff] at hcc hcq'
  obtain ⟨usL, husL, rfl⟩ := hcc
  obtain ⟨usM, -, rfl⟩ := hcq'
  rw [mkAppN_bounded_iff] at hb
  have hbl := hb.2 cl (by simp)
  have hbq := ((mkAppN_bounded_iff _ _).mp (hb.2 _ (List.mem_of_getElem? (i := 5) rfl))).2 ca
    (by simp)
  refine ⟨.app _ _, toCL?_unmark_foldl_of (.cons hca .nil) hcl,
    by simp [ConLeche.Expr.looseBVarsBounded, hbl, hbq], fun V _ m φ ta hta => ?_⟩
  obtain ⟨⟨fa, hfa⟩, -⟩ := denote_mkAppN_inv m φ _ hta
  exact quotLift_red hat (fun ci hf => denote_const_len m φ hf ⟨fa, hfa⟩) (hcase usL husL) hbl hbq

/-- The `quotMk` case of `srcEval_sound`: as `ctor`, the congruence at the element (`spineSim`),
the packed value graded (`hok`). Reference: `eval_construct` (`MR P/PCUICWcbvEval.v:303`); DV-29,
DV-33. -/
theorem srcEval_sound_quotMk {c : Name} {us : List Level} {α r a a' : Expr}
    (hok : GradedU.{w} env (mkAppN (.const c us) [α, r, a'].toArray)) (ih : SemSim.{w} env a a') :
    SemSim.{w} env (mkAppN (.const c us) [α, r, a].toArray) (mkAppN (.const c us) [α, r, a'].toArray) := by
  simp only [mkAppN_toArray] at hok ⊢
  exact spineSim rfl (simAt_append (as₁ := [α, r]) rfl (simAt_refl _) (simAt_single ih)) hok
    (semSim_refl _)

end SemCases

end EraseProof
