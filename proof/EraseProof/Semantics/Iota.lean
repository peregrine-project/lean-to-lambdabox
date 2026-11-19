import EraseProof.Semantics.Cases
import ConLeche.Verify.InstList
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.InstLevels
import ConLeche.Verify.Rules.RedBridge
import ConLeche.Verify.Denote.Lemmas
import ConLeche.SetTheory.Derive.Sigma

/-!
# The meaning of source evaluation: ι and projections

The cases `casesIota`, `casesLitZero`, `casesLitSucc`, `proj` and `projFrozen` of
`srcEval_sound`, in the form of `EraseProof.Semantics.Cases`: the congruence at the evaluated
major premise (or projected term), then a reduction of con-leche's rules tier
(`CL ConLeche/Rules/Rel.lean:106 Red`) on the `unmark` readings, built from the stored records:
δ of the recognized `casesOn`, β over its λs, ι at the recursor's rule for the major's
constructor (`CL ConLeche/Rules/Rel.lean:207 Red.iota`, case 2 of its case split), β over the
alternative's wrapper; for a projection the structural projection rule
(`CL ConLeche/Rules/Rel.lean:179 Red.proj`). The records are taken at con-leche's syntax
(`CasesIotaAt`, `ProjAt`): the stored shapes the steps read.
-/

open Lean Erasure
open ConLeche.Semantics ConLeche.SetModel ConLeche.SetTheory ConLeche.Verify ConLeche.Model
  ConLeche.Model.Rules

namespace EraseProof

universe w

namespace SemCases

variable {env : ConLeche.Env}

/-! ## con-leche syntax -/

/-- The field variables of a minor premise: `bvar (L-1), …, bvar (L-n)`, the first `n` of `L`
binders, outermost first. Reference: none. -/
def fbv (n L : Nat) : List ConLeche.Expr := (List.range n).map fun f => .bvar (L - 1 - f)

/-- The stored records the ι step of the recognized `casesOn` constant `cC` reads, at a constructor
`cj` with `nP` parameters and `nF` fields, the major at position `k` of the `D` arguments and the
constructor's alternative at `k + 1 + j`: `cC` is a definition whose value is `D` λs over its
recursor `R` (at the definition's own level parameters) applied to `rargs`, the major argument the
major's variable; the recursor's type has `mI + 1` leading Π (`RulesCanonical`); the rule for `cj`
has `nF` fields and its right-hand side is `rP + nF` λs over the prefix variable of the argument
`w` at position `pos`, applied to the field variables and `ihs'.length` further arguments; `w` is
the wrapper of the alternative: `nF + ihs'.length` λs over the alternative's variable applied to the
field variables (the minor `fun fs ihs => alt fs` of `Lean.mkCasesOn`); the ι case split's case 2
holds by the stored facts (`CL ConLeche/Kernel/CoreDefs.lean:1040 iotaNoCert`: a K rule, or a family
never `Prop`). Reference: `casesInfo?` (`LeanToLambdaBox/Erasure/Pure.lean:107`) on the stored
records, the rule shape of `CL ConLeche/Kernel/Inductives/GenRec.lean:189 classGenRule`. -/
def CasesIotaAt (env : ConLeche.Env) (cC cj : ConLeche.Name) (D k j nP nF : Nat) : Prop :=
  ∃ (cvD : ConLeche.ConstantVal) (val : ConLeche.Expr) (hint : ConLeche.ReducibilityHint)
    (R : ConLeche.Name) (rargs : List ConLeche.Expr) (cvR : ConLeche.ConstantVal) (mI rP : Nat)
    (isK : Bool) (rules : List ConLeche.RecRule) (cvj : ConLeche.ConstantVal) (induct : ConLeche.Name)
    (rl : ConLeche.RecRule) (pos : Nat) (w : ConLeche.Expr) (ihs : List ConLeche.Expr),
    env.find? cC = some (.defnInfo cvD val hint) ∧ val.looseBVarsBounded 0 = true ∧
    clLams val = (D, ConLeche.Expr.mkAppN (.const R (cvD.levelParams.map .param)) rargs) ∧
    env.find? R = some (.recInfo cvR mI rP isK rules) ∧
    cvR.levelParams.length = cvD.levelParams.length ∧ clPis cvR.type = mI + 1 ∧ rP ≤ mI ∧
    rargs.length = mI + 1 ∧ rargs[mI]? = some (.bvar (D - 1 - k)) ∧
    pos < rP ∧ rargs[pos]? = some w ∧
    clLams w = (nF + ihs.length, ConLeche.Expr.mkAppN
      (.bvar (nF + ihs.length + (D - 1 - (k + 1 + j)))) (fbv nF (nF + ihs.length))) ∧
    env.find? cj = some (.ctorInfo cvj nP nF induct) ∧
    rules.find? (fun r => r.ctor == cj) = some rl ∧ rl.nfields = nF ∧
    (∃ ihs' : List ConLeche.Expr, ihs'.length = ihs.length ∧
      clLams rl.rhs = (rP + nF, ConLeche.Expr.mkAppN (.bvar (nF + (rP - 1 - pos))) (fbv nF nF ++ ihs'))) ∧
    ConLeche.iotaNoCert env.find? isK induct (ConLeche.recFireLevelCount rl cvj.levelParams) = true

/-- The stored projection table of `S` at field `i` names the constructor `C`, with its `nP`
parameters and `nF` fields at its level parameters, and `C`'s stored type has `nP + nF` leading Π.
Reference: the table of `CL ConLeche/Kernel/Env.lean:482 findProj?`, as the direct-structure
install stores it (`CL ConLeche/Model/Env/Laws.lean:937 TowerOk`). -/
def ProjAt (env : ConLeche.Env) (S : ConLeche.Name) (i : Nat) (C : ConLeche.Name) (nP nF : Nat) :
    Prop :=
  ∃ (entry : ConLeche.ProjEntry) (cvC : ConLeche.ConstantVal) (nP' nF' : Nat) (ind : ConLeche.Name),
    env.findProj? S i = some entry ∧ entry.ctor = C ∧ entry.numParams = nP ∧
    entry.numFields = nF ∧ entry.levelParams = cvC.levelParams ∧
    env.find? C = some (.ctorInfo cvC nP' nF' ind) ∧ (ConLeche.Expr.peelPis (nP + nF) cvC.type).isSome

/-- A reduction of the head of a spine. -/
theorem red_mkAppN_fn {d : Nat} : ∀ (as : List ConLeche.Expr) {f f' : ConLeche.Expr},
    ConLeche.Rules.Red env d f f' →
    ConLeche.Rules.Red env d (ConLeche.Expr.mkAppN f as) (ConLeche.Expr.mkAppN f' as)
  | [], _, _, h => h
  | _ :: as, _, _, h => red_mkAppN_fn as (.appFn h)

/-- `clLams` on a λ. -/
theorem clLams_succ {e b : ConLeche.Expr} {n : Nat} (h : clLams e = (n + 1, b)) :
    ∃ t e', e = .lam t e' ∧ clLams e' = (n, b) := by
  cases e with
  | lam t e' =>
    simp only [clLams, Prod.mk.injEq, Nat.add_right_cancel_iff] at h
    exact ⟨t, e', rfl, Prod.ext h.1 h.2⟩
  | _ => simp [clLams] at h

/-- `clLams` at zero. -/
theorem clLams_zero {e b : ConLeche.Expr} (h : clLams e = (0, b)) : e = b := by
  cases e <;> simp_all [clLams]

/-- β over the leading λs of a term, the outer arguments `acc` substituted at once: `Red.beta`
under the spine, `CL ConLeche/Kernel/ExprOps.lean:603 instantiateList_cons`. -/
theorem red_betas {d : Nat} : ∀ (n : Nat) (e b : ConLeche.Expr), clLams e = (n, b) →
    ∀ (args acc : List ConLeche.Expr), args.length = n →
    ConLeche.Rules.Red env d (ConLeche.Expr.mkAppN (e.instantiateList acc 0) args)
      (b.instantiateList (args.reverse ++ acc) 0)
  | 0, e, b, h, [], acc, _ => by rw [clLams_zero h]; exact .refl
  | n + 1, e, b, h, a :: as, acc, hl => by
    obtain ⟨t, e', rfl, h'⟩ := clLams_succ h
    have hb : ConLeche.Rules.Red env d (ConLeche.Expr.mkAppN ((ConLeche.Expr.lam t e').instantiateList acc 0) (a :: as))
        (ConLeche.Expr.mkAppN (e'.instantiateList (a :: acc) 0) as) := by
      rw [ConLeche.Expr.instantiateList_cons]
      exact red_mkAppN_fn as (by rw [ConLeche.Expr.instantiateList]; exact .beta)
    have := red_betas (d := d) n e' b h' as (a :: acc) (by simpa using hl)
    rw [List.reverse_cons, List.append_assoc]
    exact .trans hb this
  | 0, _, _, _, _ :: _, _, hl | _ + 1, _, _, _, [], _, hl => by simp at hl

/-- `clLams` under level instantiation. -/
theorem clLams_instLP (ks : List ConLeche.Name) (us : List ConLeche.Level) :
    ∀ (e : ConLeche.Expr), clLams (e.instantiateLevelParams ks us) =
      ((clLams e).1, (clLams e).2.instantiateLevelParams ks us)
  | .lam t b => by
    simp only [ConLeche.Expr.instantiateLevelParams, clLams, clLams_instLP ks us b]
  | .bvar _ | .fvar .. | .sort _ | .const .. | .app .. | .forallE .. | .letE .. | .lit _ | .proj .. => by
    simp [ConLeche.Expr.instantiateLevelParams, clLams]

/-- The body `clLams` finds is the one `lamBody` peels. -/
theorem lamBody_of_clLams : ∀ (n : Nat) {e b : ConLeche.Expr}, clLams e = (n, b) → e.lamBody n = b
  | 0, e, b, h => by rw [clLams_zero h]; cases b <;> rfl
  | n + 1, e, b, h => by
    obtain ⟨t, e', rfl, h'⟩ := clLams_succ h
    exact lamBody_of_clLams n h'

/-- The body under `n` λs is bounded by `n` more. -/
theorem clLams_bounded : ∀ (n : Nat) {e b : ConLeche.Expr} {k : Nat}, clLams e = (n, b) →
    e.looseBVarsBounded k = true → b.looseBVarsBounded (k + n) = true
  | 0, e, b, k, h, hb => by rw [clLams_zero h] at hb; simpa using hb
  | n + 1, e, b, k, h, hb => by
    obtain ⟨t, e', rfl, h'⟩ := clLams_succ h
    simp only [ConLeche.Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    have := clLams_bounded n h' hb.2
    rwa [Nat.add_assoc, Nat.add_comm 1 n] at this

/-- A spine is bounded exactly when its head and its arguments are. -/
theorem mkAppN_bounded_iff {k : Nat} : ∀ (as : List ConLeche.Expr) (f : ConLeche.Expr),
    (ConLeche.Expr.mkAppN f as).looseBVarsBounded k = true ↔
      f.looseBVarsBounded k = true ∧ ∀ a ∈ as, a.looseBVarsBounded k = true
  | [], f => by simp [ConLeche.Expr.mkAppN]
  | a :: as, f => by
    rw [show ConLeche.Expr.mkAppN f (a :: as) = ConLeche.Expr.mkAppN (.app f a) as from rfl,
      mkAppN_bounded_iff as (.app f a)]
    simp [ConLeche.Expr.looseBVarsBounded, and_assoc]

/-- Bulk instantiation by closed terms closes the instantiated range. -/
theorem bounded_instantiateList : ∀ (vs : List ConLeche.Expr) (e : ConLeche.Expr) (d : Nat),
    (∀ v ∈ vs, v.looseBVarsBounded 0 = true) → e.looseBVarsBounded (d + vs.length) = true →
    (e.instantiateList vs d).looseBVarsBounded d = true
  | [], e, d, _, h => by rw [ConLeche.Expr.instantiateList_nil]; simpa using h
  | v :: vs, e, d, hv, h => by
    rw [ConLeche.Expr.instantiateList_cons]
    exact ConLeche.Expr.looseBVarsBounded_instantiate1_gen (hv v (List.mem_cons_self ..))
      (bounded_instantiateList vs e (d + 1) (fun x hx => hv x (List.mem_cons_of_mem _ hx))
        (by simpa [Nat.add_assoc, Nat.add_comm 1] using h))

/-- A variable of the instantiated range is replaced by its closed value. -/
theorem instantiateList_bvar {vs : List ConLeche.Expr} {d j : Nat} {v : ConLeche.Expr}
    (h : vs[j]? = some v) (hv : v.looseBVarsBounded 0 = true) :
    (ConLeche.Expr.bvar (d + j)).instantiateList vs d = v := by
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp h
  rw [ConLeche.Expr.instantiateList]
  simp only [show ¬ d + j < d by omega, ↓reduceIte, Nat.add_sub_cancel_left, hj, ↓reduceDIte]
  exact ConLeche.Expr.instantiateList_eq_self
    (ConLeche.Expr.looseBVarsBounded_mono (Nat.zero_le d) hv)

/-- A variable of the instantiated range at depth `0`. -/
theorem instantiateList_bvar0 {vs : List ConLeche.Expr} {j : Nat} {v : ConLeche.Expr}
    (h : vs[j]? = some v) (hv : v.looseBVarsBounded 0 = true) :
    (ConLeche.Expr.bvar j).instantiateList vs 0 = v := by
  simpa using instantiateList_bvar (d := 0) h hv

/-- Bulk instantiation distributes over a spine. -/
theorem instantiateList_mkAppN (vs : List ConLeche.Expr) (k : Nat) :
    ∀ (as : List ConLeche.Expr) (f : ConLeche.Expr),
      (ConLeche.Expr.mkAppN f as).instantiateList vs k =
        ConLeche.Expr.mkAppN (f.instantiateList vs k) (as.map (·.instantiateList vs k))
  | [], _ => rfl
  | a :: as, f => by
    show (ConLeche.Expr.mkAppN (.app f a) as).instantiateList vs k = _
    rw [instantiateList_mkAppN vs k as (.app f a), ConLeche.Expr.instantiateList]
    rfl

/-- Field variables carry no levels. -/
theorem fbv_instLP (ks : List ConLeche.Name) (us : List ConLeche.Level) (n L : Nat) :
    (fbv n L).map (·.instantiateLevelParams ks us) = fbv n L := by
  simp [fbv, ConLeche.Expr.instantiateLevelParams]

/-- The field variables, instantiated by a list whose entries `L-1-f` are the closed fields. -/
theorem fbv_instantiateList {n L : Nat} {vs fs : List ConLeche.Expr} (hfs : fs.length = n) (hcl : ∀ x ∈ fs, x.looseBVarsBounded 0 = true)
    (hv : ∀ f (hf : f < n), vs[L - 1 - f]? = some fs[f]) :
    (fbv n L).map (·.instantiateList vs 0) = fs := by
  apply List.ext_getElem (by simp [fbv, hfs])
  intro f h₁ h₂
  simp only [fbv, List.map_map, List.getElem_map, List.getElem_range, Function.comp]
  have hf : f < n := by simpa [fbv] using h₁
  have := instantiateList_bvar (d := 0) (hv f hf) (hcl _ (List.getElem_mem _))
  simpa using this

/-- `clPis` counts syntactic Π. -/
theorem peelPis_of_clPis : ∀ {e : ConLeche.Expr} {n : Nat}, clPis e = n →
    (ConLeche.Expr.peelPis n e).isSome = true
  | .forallE _ b, n, h => by
    simp only [clPis] at h; subst h
    exact peelPis_of_clPis (e := b) rfl
  | .bvar _, n, h | .fvar .., n, h | .sort _, n, h | .const .., n, h | .app .., n, h
  | .lam .., n, h | .letE .., n, h | .lit _, n, h | .proj .., n, h => by
    simp only [clPis] at h; subst h; rfl

/-- A variable of the instantiated range, read off the reversed list. -/
theorem instantiateList_rev_bvar {vs : List ConLeche.Expr} {q : Nat} {v : ConLeche.Expr}
    (hq : q < vs.length) (h : vs[vs.length - 1 - q]? = some v) (hv : v.looseBVarsBounded 0 = true) :
    (ConLeche.Expr.bvar q).instantiateList vs.reverse 0 = v := by
  have := instantiateList_bvar (d := 0) (vs := vs.reverse) (j := q)
    (by rw [List.getElem?_reverse hq]; exact h) hv
  simpa using this

/-- The ι chain of a recognized `casesOn` on the readings: δ of the `casesOn` constant
(`CL ConLeche/Kernel/CoreDefs.lean:115 unfoldDefinition`), β over its `D` λs (`red_betas`), ι at
the recursor's rule for the major's constructor (`CL ConLeche/Rules/Rel.lean:207 Red.iota`, case 2
by `IotaCaseS.stored`; the reduct `CL ConLeche/Kernel/CoreDefs.lean:1016 RecRule.iotaReduct`), β
over the alternative's wrapper: the spine `cC us args` whose major `args[k]` reduces to the
constructor application `cj usj (cps ++ cfs)` reduces to the alternative `args[k+1+j]` applied to
the fields `cfs`. Reference: `eval_iota` (`MR P/PCUICWcbvEval.v:253`). -/
theorem casesIota_red {cC cj : ConLeche.Name} {D k j nP nF : Nat}
    (hat : CasesIotaAt env cC cj D k j nP nF) {us usj : List ConLeche.Level}
    {args cps cfs : List ConLeche.Expr} {maj calt : ConLeche.Expr}
    (hlen : args.length = D) (hcl : ∀ a ∈ args, a.looseBVarsBounded 0 = true)
    (hus : ∀ cvD val hint, env.find? cC = some (.defnInfo cvD val hint) →
      us.length = cvD.levelParams.length)
    (hk : args[k]? = some maj)
    (hmaj : ConLeche.Rules.Red env 0 maj (ConLeche.Expr.mkAppN (.const cj usj) (cps ++ cfs)))
    (hcps : cps.length = nP) (hcfs : cfs.length = nF)
    (hcfl : ∀ x ∈ cfs, x.looseBVarsBounded 0 = true) (halt : args[k + 1 + j]? = some calt) :
    ConLeche.Rules.Red env 0 (ConLeche.Expr.mkAppN (.const cC us) args)
      (ConLeche.Expr.mkAppN calt cfs) := by
  obtain ⟨cvD, val, hint, R, rargs, cvR, mI, rP, isK, rules, cvj, induct, rl, pos, w, ihs,
    hfD, hvcl, hval, hfR, hlpR, hpis, hrP, hrlen, hrmaj, hpos, hw, hwsh, hfj, hrl, hnf,
    ⟨ihs', hihs', hrhs⟩, hnc⟩ := hat
  have husl := hus cvD val hint hfD
  have hkD : k < D := by have := (List.getElem?_eq_some_iff.mp hk).1; omega
  have hjD : k + 1 + j < D := by have := (List.getElem?_eq_some_iff.mp halt).1; omega
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
  -- ι
  have hargsE : e.getAppArgs = rargs.map inst := by
    simp [e, ConLeche.Expr.getAppArgs_mkAppN, ConLeche.Expr.getAppArgs]
  have hmajE : e.getAppArgs.getD mI (.bvar 0) = maj := by
    rw [hargsE, List.getD_eq_getElem?_getD, List.getElem?_map, hrmaj]
    show (ConLeche.Expr.bvar (D - 1 - k)).instantiateList args.reverse 0 = maj
    exact instantiateList_rev_bvar (by omega) (by rw [hlen, show D - 1 - (D - 1 - k) = k by omega]; exact hk)
      (hcl maj (List.mem_of_getElem? hk))
  let major := ConLeche.Expr.mkAppN (.const cj usj) (cps ++ cfs)
  have hι := @ConLeche.Rules.Red.iota env 0 e R usR cvR mI rP isK rules major cj usj cvj nP nF induct rl
    (.bvar 0) false
    (by simp [e, ConLeche.Expr.getAppFn_mkAppN, ConLeche.Expr.getAppFn]) hfR
    (by rw [hargsE, List.length_map, hrlen]) (by simp [usR, hlpR]) (hmajE ▸ hmaj)
    (by simp [major, ConLeche.Expr.getAppFn_mkAppN, ConLeche.Expr.getAppFn]) hfj hrl
    (by simp [major, ConLeche.Expr.getAppArgs_mkAppN, ConLeche.Expr.getAppArgs, hcps, hcfs, hnf])
    (.stored (by rw [ConLeche.recFireComparands_fst_length]; exact hnc))
    (fun h => nomatch h) (fun h => nomatch h)
    (by rw [hargsE, List.length_map, hrlen]
        exact ConLeche.Rules.peelPis_isSome_instantiateLevelParams _ _ _ (peelPis_of_clPis hpis))
    (fun h => nomatch h) (fun h => nomatch h) (fun h => nomatch h)
  have hvals : e.getAppArgs.take rP ++ major.getAppArgs.drop nP = (rargs.map inst).take rP ++ cfs := by
    rw [hargsE]
    simp [major, ConLeche.Expr.getAppArgs_mkAppN, ConLeche.Expr.getAppArgs, List.drop_left' hcps]
  rw [hvals] at hι
  -- the reduct
  let vals := (rargs.map inst).take rP ++ cfs
  have hvlen : vals.length = rP + nF := by simp [vals, hrlen, hcfs]; omega
  let ihs'' := ihs'.map fun x =>
    (x.instantiateLevelParams cvR.levelParams usR).instantiateList vals.reverse 0
  have hwcl : (inst w).looseBVarsBounded 0 = true := hinstcl w (List.mem_of_getElem? hw)
  have hreduct : rl.iotaReduct cvR.levelParams usR rP vals =
      ConLeche.Expr.mkAppN (inst w) (cfs ++ ihs'') := by
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
      refine fbv_instantiateList hcfs hcfl fun f hf => ?_
      rw [List.getElem?_reverse (by omega), hvlen,
        show rP + nF - 1 - (nF - 1 - f) = (rP + f) by omega,
        List.getElem?_append_right (by simp; omega)]
      simp only [List.length_take, List.length_map, hrlen, show min rP (mI + 1) = rP by omega,
        show rP + f - rP = f by omega, List.getElem?_eq_getElem (show f < cfs.length by omega)]
  rw [hreduct] at hι
  -- β over the wrapper
  have hlw : (cfs ++ ihs'').length = nF + ihs.length := by simp [ihs'', hcfs, hihs']
  have hβ₂ := red_betas (env := env) (d := 0) (nF + ihs.length)
    (w.instantiateLevelParams cvD.levelParams us)
    ((ConLeche.Expr.mkAppN (.bvar (nF + ihs.length + (D - 1 - (k + 1 + j))))
      (fbv nF (nF + ihs.length))).instantiateLevelParams cvD.levelParams us)
    (by rw [clLams_instLP, hwsh]) (cfs ++ ihs'') args.reverse hlw
  rw [ConLeche.instantiateLevelParams_mkAppN, fbv_instLP, instantiateList_mkAppN] at hβ₂
  have hhead : (ConLeche.Expr.instantiateLevelParams cvD.levelParams us
      (.bvar (nF + ihs.length + (D - 1 - (k + 1 + j))))).instantiateList
        ((cfs ++ ihs'').reverse ++ args.reverse) 0 = calt := by
    show (ConLeche.Expr.bvar (nF + ihs.length + (D - 1 - (k + 1 + j)))).instantiateList _ 0 = calt
    refine instantiateList_bvar0 ?_ (hcl calt (List.mem_of_getElem? halt))
    rw [List.getElem?_append_right (by rw [List.length_reverse, hlw]; omega), List.length_reverse, hlw,
      show nF + ihs.length + (D - 1 - (k + 1 + j)) - (nF + ihs.length) = D - 1 - (k + 1 + j) by omega,
      List.getElem?_reverse (by omega), hlen, show D - 1 - (D - 1 - (k + 1 + j)) = k + 1 + j by omega]
    exact halt
  have hfields : (fbv nF (nF + ihs.length)).map
      (·.instantiateList ((cfs ++ ihs'').reverse ++ args.reverse) 0) = cfs := by
    refine fbv_instantiateList hcfs hcfl fun f hf => ?_
    rw [List.getElem?_append_left (by rw [List.length_reverse, hlw]; omega),
      List.getElem?_reverse (by rw [hlw]; omega),
      hlw, show nF + ihs.length - 1 - (nF + ihs.length - 1 - f) = f by omega,
      List.getElem?_append_left (by omega), List.getElem?_eq_getElem (by omega)]
  rw [hhead, hfields] at hβ₂
  exact .trans hδ (.trans hβ (.trans hι hβ₂))

/-! ## Readings of spines and projections -/

/-- A step whose reading is a reduction wherever the subject reads in some model: `red0`. As
`semSim_of_red`, with the reduction built from the subject's reading's existence (the level count
of a constant, the `Nat` basis of a literal). Reference: none (DV-34). -/
theorem semSim_of_redD {t u : Expr}
    (hred : EtaLams t → EtaLams u ∧ ∀ c : ConLeche.Expr, toCL? (unmark t) = some c →
      c.looseBVarsBounded 0 = true →
      ∃ c', toCL? (unmark u) = some c' ∧ c'.looseBVarsBounded 0 = true ∧
        ∀ (V : Type w) [ConLeche.SetTheory V] (m : EnvModelM V env) (φ : ConLeche.Name → Nat)
          (ta : ConLeche.Term.Term), denote m.base2.acval env φ 0 c = some ta →
          ConLeche.Rules.Red env 0 c c') :
    SemSim.{w} env t u := by
  intro hη
  obtain ⟨hηu, hred⟩ := hred hη
  refine ⟨hηu, fun {c} hc hb => ?_⟩
  obtain ⟨c', hc', hb', hr⟩ := hred c hc hb
  exact ⟨c', hc', hb', fun V _ m φ ta hta => red0 m φ (hr V m φ ta hta) (toCL?_hasFvar hc) hb hta⟩

/-- The reading of a spine is the spine of the readings. -/
theorem toCL?_unmark_foldl : ∀ (as : List Expr) (f : Expr) {c : ConLeche.Expr},
    toCL? (unmark (as.foldl .app f)) = some c →
    ∃ cf cas, toCL? (unmark f) = some cf ∧
      List.Forall₂ (fun a ca => toCL? (unmark a) = some ca) as cas ∧ c = ConLeche.Expr.mkAppN cf cas
  | [], _, c, h => ⟨c, [], h, .nil, rfl⟩
  | a :: as, f, _, h => by
    obtain ⟨cf', cas, hf', hall, rfl⟩ := toCL?_unmark_foldl as (.app f a) h
    obtain ⟨cf, ca, hcf, hca, rfl⟩ := toCL?_unmark_app hf'
    exact ⟨cf, ca :: cas, hcf, .cons hca hall, rfl⟩

/-- The spine of the readings is the reading of a spine. -/
theorem toCL?_unmark_foldl_of {as : List Expr} {cas : List ConLeche.Expr}
    (hall : List.Forall₂ (fun a ca => toCL? (unmark a) = some ca) as cas) :
    ∀ {f : Expr} {cf : ConLeche.Expr}, toCL? (unmark f) = some cf →
      toCL? (unmark (as.foldl .app f)) = some (ConLeche.Expr.mkAppN cf cas) := by
  induction hall with
  | nil => exact fun h => h
  | @cons a ca _ _ ha _ ih =>
    intro f cf h
    exact ih (f := .app f a) (cf := .app cf ca) (by simp [unmark, toCL?, h, ha])

/-- Related lists, read pointwise. -/
theorem forall₂_getElem? {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) : ∀ {i : Nat} {a : α}, l₁[i]? = some a →
      ∃ b, l₂[i]? = some b ∧ R a b := by
  induction h with
  | nil => intro i a h; simp at h
  | @cons x y _ _ hxy _ ih =>
    intro i a h
    cases i with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h; exact ⟨y, rfl, hxy⟩
    | succ i => exact ih (by simpa using h)

/-- Related lists have one length. -/
theorem forall₂_length {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) : l₁.length = l₂.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- A spine of con-leche syntax over a spine. -/
theorem clMkAppN_append (f : ConLeche.Expr) : ∀ (as bs : List ConLeche.Expr),
    ConLeche.Expr.mkAppN f (as ++ bs) = ConLeche.Expr.mkAppN (ConLeche.Expr.mkAppN f as) bs
  | [], _ => rfl
  | a :: as, bs => clMkAppN_append (.app f a) as bs

/-- `EtaLams` of a spine. -/
theorem etaLams_foldl : ∀ (as : List Expr) (f : Expr), EtaLams (as.foldl .app f) →
    EtaLams f ∧ ∀ a ∈ as, EtaLams a
  | [], _, h => ⟨h, fun _ h => by simp at h⟩
  | a :: as, f, h => by
    obtain ⟨⟨hf, ha⟩, has⟩ := etaLams_foldl as (.app f a) h
    exact ⟨hf, fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ha
      · exact has x hx⟩

/-- `EtaLams` of a spine, from its parts. -/
theorem etaLams_foldl_of : ∀ (as : List Expr) (f : Expr), EtaLams f → (∀ a ∈ as, EtaLams a) →
    EtaLams (as.foldl .app f)
  | [], _, h, _ => h
  | a :: as, f, hf, has => etaLams_foldl_of as (.app f a) ⟨hf, has a (List.mem_cons_self ..)⟩
      fun x hx => has x (List.mem_cons_of_mem _ hx)

/-- A spine with a reading has readings of its head and its arguments. -/
theorem denote_mkAppN_inv {V : Type w} [ConLeche.SetTheory V] (m : EnvModelM V env)
    (φ : ConLeche.Name → Nat) : ∀ (as : List ConLeche.Expr) {f : ConLeche.Expr} {ta : ConLeche.Term.Term},
    denote m.base2.acval env φ 0 (ConLeche.Expr.mkAppN f as) = some ta →
    (∃ fa, denote m.base2.acval env φ 0 f = some fa) ∧
      ∀ a ∈ as, ∃ aa, denote m.base2.acval env φ 0 a = some aa
  | [], _, _, h => ⟨⟨_, h⟩, fun _ h => by simp at h⟩
  | a :: as, f, _, h => by
    obtain ⟨⟨fa, hfa⟩, has⟩ := denote_mkAppN_inv m φ as h
    obtain ⟨ga, aa, hga, haa, rfl⟩ := denote_app_inv hfa
    exact ⟨⟨ga, hga⟩, fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨aa, haa⟩
      · exact has x hx⟩

/-- A constant with a reading is applied to its number of level parameters. -/
theorem denote_const_len {V : Type w} [ConLeche.SetTheory V] (m : EnvModelM V env)
    (φ : ConLeche.Name → Nat) {n : ConLeche.Name} {us : List ConLeche.Level} {ci : ConLeche.ConstantInfo}
    (hf : env.find? n = some ci) (h : ∃ ta, denote m.base2.acval env φ 0 (.const n us) = some ta) :
    us.length = ci.toConstantVal.levelParams.length := by
  obtain ⟨ta, h⟩ := h
  rw [denote, hf] at h
  by_cases hne : us.length = ci.toConstantVal.levelParams.length
  · exact hne
  · simp [hne] at h

/-- A literal with a reading has the stored `Nat` basis. -/
theorem natLitStored_of_denote {V : Type w} [ConLeche.SetTheory V] (m : EnvModelM V env)
    (φ : ConLeche.Name → Nat) {n : Nat}
    (h : ∃ ta, denote m.base2.acval env φ 0 (.lit (.natVal n)) = some ta) :
    ConLeche.natLitStored env = true := by
  obtain ⟨ta, h⟩ := h
  rw [denote] at h
  split at h
  · rename_i hs
    simp only [ConLeche.natLitSupported, Bool.and_eq_true] at hs
    obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hs
    simp only [ConLeche.natLitStored, Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · revert h₁; cases env.find? ConLeche.natName <;> simp [ConLeche.natIndOk]
    · revert h₂; cases env.find? ConLeche.natZeroName <;> simp [ConLeche.natZeroOk]
    · revert h₃; cases env.find? ConLeche.natSuccName <;> simp [ConLeche.natSuccOk]
  · cases h

/-- The congruence at one argument of a spine, the spine of the values graded (`spineSim`).
Reference: `eval_iota` (`MR P/PCUICWcbvEval.v:253`, the discriminant evaluated); DV-33. -/
theorem spineSim_set {as : List Expr} {k : Nat} {m mv f : Expr} (hm : as[k]? = some m)
    (hok : GradedU.{w} env ((as.set k mv).foldl .app f)) (ih : SemSim.{w} env m mv) :
    SemSim.{w} env (as.foldl .app f) ((as.set k mv).foldl .app f) := by
  refine spineSim (by simp) (fun i a v ha hv => ?_) hok (semSim_refl f)
  rw [List.getElem?_set] at hv
  by_cases hik : k = i
  · subst hik
    rw [hm] at ha; cases ha
    simp only [ite_true, (List.getElem?_eq_some_iff.mp hm).1] at hv
    cases hv; exact ih
  · simp only [hik, ite_false, ha] at hv
    cases hv; exact semSim_refl a

/-- The reduction of a recognized `casesOn` spine whose major value `mv` at `k` reads as a spine
that reduces to the constructor `cj` applied to parameters and the readings of the fields `fs`
(`casesIota_red`), to the alternative at `k + 1 + j` applied to `fs`. Reference: `eval_iota`
(`MR P/PCUICWcbvEval.v:253`); DV-25. -/
theorem casesSim {c : Name} {us : List Level} {cj : ConLeche.Name} {as : List Expr} {k j nP : Nat}
    {mv alt : Expr} {fs : List Expr}
    (hat : CasesIotaAt env (Name.toCL c) cj as.length k j nP fs.length)
    (hk : as[k]? = some mv) (halt : as[k + 1 + j]? = some alt)
    (hηfs : EtaLams mv → ∀ x ∈ fs, EtaLams x)
    (hmaj : ∀ cmv : ConLeche.Expr, toCL? (unmark mv) = some cmv → cmv.looseBVarsBounded 0 = true →
      ∃ usj cps cfs, cps.length = nP ∧ List.Forall₂ (fun a ca => toCL? (unmark a) = some ca) fs cfs ∧
        (∀ x ∈ cfs, x.looseBVarsBounded 0 = true) ∧
        ∀ (V : Type w) [ConLeche.SetTheory V] (m : EnvModelM V env) (φ : ConLeche.Name → Nat),
          (∃ ta, denote m.base2.acval env φ 0 cmv = some ta) →
          ConLeche.Rules.Red env 0 cmv (ConLeche.Expr.mkAppN (.const cj usj) (cps ++ cfs))) :
    SemSim.{w} env (as.foldl .app (.const c us)) (fs.foldl .app alt) := by
  refine semSim_of_redD fun hη => ?_
  obtain ⟨-, hηas⟩ := etaLams_foldl as _ hη
  have hηalt := hηas alt (List.mem_of_getElem? halt)
  refine ⟨etaLams_foldl_of fs alt hηalt (hηfs (hηas mv (List.mem_of_getElem? hk))), fun c₀ hc hb => ?_⟩
  obtain ⟨cf, cargs, hcf, hall, rfl⟩ := toCL?_unmark_foldl as _ hc
  simp only [unmark, toCL?, Option.map_eq_map, Option.map_eq_some_iff] at hcf
  obtain ⟨us', -, rfl⟩ := hcf
  rw [mkAppN_bounded_iff] at hb
  obtain ⟨cmv, hcmv, hrmv⟩ := forall₂_getElem? hall hk
  obtain ⟨calt, hcalt, hralt⟩ := forall₂_getElem? hall halt
  have hcmvcl := hb.2 cmv (List.mem_of_getElem? hcmv)
  have hcaltcl := hb.2 calt (List.mem_of_getElem? hcalt)
  obtain ⟨usj, cps, cfs, hcps, hfs, hcfl, hred⟩ := hmaj cmv hrmv hcmvcl
  refine ⟨ConLeche.Expr.mkAppN calt cfs, toCL?_unmark_foldl_of hfs hralt,
    (mkAppN_bounded_iff _ _).mpr ⟨hcaltcl, hcfl⟩, fun V _ m φ ta hta => ?_⟩
  obtain ⟨⟨fa, hfa⟩, hargs⟩ := denote_mkAppN_inv m φ cargs hta
  refine casesIota_red hat (forall₂_length hall).symm hb.2 (fun cvD val hint hf =>
      denote_const_len m φ hf ⟨fa, hfa⟩) hcmv
    (hred V m φ (hargs cmv (List.mem_of_getElem? hcmv))) hcps (forall₂_length hfs).symm hcfl hcalt

/-! ## The cases -/

/-- The `casesIota` case of `srcEval_sound`: the congruence at the major premise to the `casesOn`
spine of its value (`spineSim_set`, the spine graded, `hok`), then the ι chain (`casesSim`) at the
constructor value `mv = C ps fs`, its alternative `alt`; `hat`: the stored records the chain reads.
Reference: `eval_iota` (`MR P/PCUICWcbvEval.v:253`); DV-25, DV-33. -/
theorem srcEval_sound_casesIota {c : Name} {us : List Level} {as : List Expr} {k j : Nat}
    {m mv alt v : Expr} {C : Name} {usC : List Level} {ps fs : List Expr}
    (hat : CasesIotaAt env (Name.toCL c) (Name.toCL C) as.length k j ps.length fs.length)
    (hm : as[k]? = some m) (halt : as[k + 1 + j]? = some alt)
    (hmv : mv = mkAppN (.const C usC) (ps ++ fs).toArray)
    (hok : GradedU.{w} env (mkAppN (.const c us) (as.set k mv).toArray))
    (ihm : SemSim.{w} env m mv) (ihb : SemSim.{w} env (mkAppN alt fs.toArray) v) :
    SemSim.{w} env (mkAppN (.const c us) as.toArray) v := by
  rw [mkAppN_toArray] at hok ihb ⊢
  have hk : (as.set k mv)[k]? = some mv := by
    simp [(List.getElem?_eq_some_iff.mp hm).1]
  have halt' : (as.set k mv)[k + 1 + j]? = some alt := by
    rw [List.getElem?_set]; simp [show k ≠ k + 1 + j by omega, halt]
  refine semSim_trans (spineSim_set hm hok ihm) (semSim_trans ?_ ihb)
  subst hmv
  rw [mkAppN_toArray] at hk halt' ⊢
  refine casesSim (by simpa using hat) hk halt' ?_ ?_
  · intro hη x hx
    rw [List.foldl_append] at hη
    exact (etaLams_foldl _ _ hη).2 x hx
  · intro cmv hcmv hcmvcl
    rw [List.foldl_append] at hcmv
    obtain ⟨cf, cfs, hcf, hfs, rfl⟩ := toCL?_unmark_foldl fs _ hcmv
    obtain ⟨cc, cps, hcc, hps, rfl⟩ := toCL?_unmark_foldl ps _ hcf
    simp only [unmark, toCL?, Option.map_eq_map, Option.map_eq_some_iff] at hcc
    obtain ⟨usC', -, rfl⟩ := hcc
    refine ⟨usC', cps, cfs, (forall₂_length hps).symm, hfs, ?_, fun _ _ _ _ _ => ?_⟩
    · exact ((mkAppN_bounded_iff _ _).mp hcmvcl).2
    · rw [clMkAppN_append]; exact .refl

/-- The `casesLitZero` case of `srcEval_sound`: as `casesIota`, the major a `Nat` literal `0`
converted to `Nat.zero` (`CL ConLeche/Rules/Rel.lean:149 Red.natLit`, the basis stored since the
literal reads); `hok`: the `casesOn` spine at the literal graded. Reference: `eval_iota`
(`MR P/PCUICWcbvEval.v:253`); DV-25, DV-33. -/
theorem srcEval_sound_casesLitZero {c : Name} {us : List Level} {as : List Expr} {k : Nat}
    {m alt v : Expr}
    (hat : CasesIotaAt env (Name.toCL c) ConLeche.natZeroName as.length k 0 0 0)
    (hm : as[k]? = some m) (halt : as[k + 1]? = some alt)
    (hok : GradedU.{w} env (mkAppN (.const c us) (as.set k (.lit (.natVal 0))).toArray))
    (ihm : SemSim.{w} env m (.lit (.natVal 0))) (ihb : SemSim.{w} env alt v) :
    SemSim.{w} env (mkAppN (.const c us) as.toArray) v := by
  rw [mkAppN_toArray] at hok ⊢
  have hk : (as.set k (.lit (.natVal 0)))[k]? = some (.lit (.natVal 0)) := by
    simp [(List.getElem?_eq_some_iff.mp hm).1]
  have halt' : (as.set k (.lit (.natVal 0)))[k + 1 + 0]? = some alt := by
    rw [List.getElem?_set]; simp [halt]
  refine semSim_trans (spineSim_set hm hok ihm) (semSim_trans ?_ ihb)
  refine casesSim (fs := []) (by simpa using hat) hk halt' (fun _ _ h => by simp at h) ?_
  intro cmv hcmv _
  simp only [unmark, toCL?, Option.some.injEq] at hcmv
  subst hcmv
  exact ⟨[], [], [], rfl, .nil, fun _ h => by simp at h,
    fun V _ m φ hd => .natLit (natLitStored_of_denote m φ hd)⟩

/-- The `casesLitSucc` case of `srcEval_sound`: as `casesIota`, the major a `Nat` literal `n + 1`
converted to `Nat.succ n` (`Red.natLit`), the field the literal `n`; `hok`: the `casesOn` spine at
the literal graded. Reference: `eval_iota` (`MR P/PCUICWcbvEval.v:253`); DV-25, DV-33. -/
theorem srcEval_sound_casesLitSucc {c : Name} {us : List Level} {as : List Expr} {k n : Nat}
    {m alt v : Expr}
    (hat : CasesIotaAt env (Name.toCL c) ConLeche.natSuccName as.length k 1 0 1)
    (hm : as[k]? = some m) (halt : as[k + 2]? = some alt)
    (hok : GradedU.{w} env (mkAppN (.const c us) (as.set k (.lit (.natVal (n + 1)))).toArray))
    (ihm : SemSim.{w} env m (.lit (.natVal (n + 1))))
    (ihb : SemSim.{w} env (.app alt (.lit (.natVal n))) v) :
    SemSim.{w} env (mkAppN (.const c us) as.toArray) v := by
  rw [mkAppN_toArray] at hok ⊢
  have hk : (as.set k (.lit (.natVal (n + 1))))[k]? = some (.lit (.natVal (n + 1))) := by
    simp [(List.getElem?_eq_some_iff.mp hm).1]
  have halt' : (as.set k (.lit (.natVal (n + 1))))[k + 1 + 1]? = some alt := by
    rw [List.getElem?_set]; simpa [show k ≠ k + 1 + 1 by omega] using halt
  refine semSim_trans (spineSim_set hm hok ihm) (semSim_trans ?_ ihb)
  refine casesSim (fs := [.lit (.natVal n)]) (by simpa using hat) hk halt'
    (fun _ x hx => by simp at hx; subst hx; trivial) ?_
  intro cmv hcmv _
  simp only [unmark, toCL?, Option.some.injEq] at hcmv
  subst hcmv
  exact ⟨[], [], [.lit (.natVal n)], rfl, .cons rfl .nil, fun x hx => by simp at hx; subst hx; rfl,
    fun V _ m φ hd => .natLit (natLitStored_of_denote m φ hd)⟩

section
variable {V : Type w} [ConLeche.SetTheory V] {ρ : Nat → V}

/-- A projection of the point is the point (`CL ConLeche/SetTheory/Derive/Sigma.lean:105
sfst_pt`, `:111 ssnd_pt`). -/
theorem interp_projNV_pt : ∀ (n : Nat) {x : ConLeche.Term.Term}, interp V ρ x = pt →
    interp V ρ (projNV n x) = pt
  | 0, _, h => by simp [projNV, h, sfst_pt]
  | n + 1, x, h => interp_projNV_pt n (x := .snd x) (by simp [h, ssnd_pt])

/-- Projections of equal values are equal. -/
theorem interp_projNV_congr : ∀ (n : Nat) {x y : ConLeche.Term.Term}, interp V ρ x = interp V ρ y →
    interp V ρ (projNV n x) = interp V ρ (projNV n y)
  | 0, _, _, h => by simp [projNV, h]
  | n + 1, x, y, h => interp_projNV_congr n (x := .snd x) (y := .snd y) (by simp [h])

/-- A graded projection has a graded subject. -/
theorem wd_projNV_arg : ∀ (n : Nat) {x : ConLeche.Term.Term}, WellDenoted V ρ (projNV n x) →
    WellDenoted V ρ x
  | 0, _, h => by rw [projNV, WellDenoted_fst] at h; exact h.1
  | n + 1, x, h => by
    have h' := wd_projNV_arg n (x := .snd x) h
    rw [WellDenoted_snd] at h'; exact h'.1

/-- The grading of a projection depends on its subject's value only, the subject graded. -/
theorem wd_projNV_congr : ∀ (n : Nat) {x y : ConLeche.Term.Term}, interp V ρ x = interp V ρ y →
    WellDenoted V ρ y → WellDenoted V ρ (projNV n x) → WellDenoted V ρ (projNV n y)
  | 0, _, _, he, hy, h => by
    rw [projNV, WellDenoted_fst] at h ⊢; exact ⟨hy, he ▸ h.2⟩
  | n + 1, x, y, he, hy, h => by
    have hs := wd_projNV_arg n (x := .snd x) h
    rw [WellDenoted_snd] at hs
    exact wd_projNV_congr n (x := .snd x) (y := .snd y) (by simp [he])
      (by rw [WellDenoted_snd]; exact ⟨hy, he ▸ hs.2⟩) h
end

/-- The projection congruence: a projection reads its subject's value behind the constructor's tag
(`CL ConLeche/Verify/Denote.lean:130 projNV`), so the projections of two subjects that agree away
from the point agree, and the projection of the point is the point. No grading of the projected
value is needed. Reference: `eval_proj` (`MR P/PCUICWcbvEval.v:264`, the subject evaluated);
DV-33. -/
theorem projSim {S : Name} {i : Nat} {e e' : Expr} (ih : SemSim.{w} env e e') :
    SemSim.{w} env (.proj S i e) (.proj S i e') := by
  intro hη
  obtain ⟨hη', ih⟩ := ih hη
  refine ⟨hη', fun {c} hc hb => ?_⟩
  simp only [unmark, toCL?, Option.map_eq_map, Option.map_eq_some_iff] at hc
  obtain ⟨ce, hce, rfl⟩ := hc
  obtain ⟨ce', hce', hb', hm⟩ := ih hce hb
  refine ⟨.proj (Name.toCL S) i ce', by simp [unmark, toCL?, hce'], hb', fun V _ m φ ta hta => ?_⟩
  obtain ⟨ea, entry, hea, hfp, rfl⟩ := denote_proj_inv hta
  obtain ⟨ea', hea', hρ⟩ := hm V m φ hea
  refine ⟨projNV (i + 1) ea', by rw [denote_proj, hea']; simp [hfp], fun ρ hwd hne => ?_⟩
  have hne' : interp V ρ ea ≠ pt := fun h => hne (interp_projNV_pt _ h)
  obtain ⟨hwd', heq⟩ := hρ ρ (wd_projNV_arg _ hwd) hne'
  exact ⟨wd_projNV_congr _ heq hwd' hwd, interp_projNV_congr _ heq⟩

/-- The `proj` case of `srcEval_sound`: the projection congruence (`projSim`) to the projection of
the constructor value `C ps fs`, then the structural projection rule
(`CL ConLeche/Rules/Rel.lean:179 Red.proj`) at the stored table entry (`hat`) to the field.
Reference: `eval_proj` (`MR P/PCUICWcbvEval.v:264`); DV-33. -/
theorem srcEval_sound_proj {S : Name} {i : Nat} {e mv a : Expr} {C : Name} {usC : List Level}
    {ps fs : List Expr} (hat : ProjAt env (Name.toCL S) i (Name.toCL C) ps.length fs.length)
    (hmv : mv = mkAppN (.const C usC) (ps ++ fs).toArray) (ha : fs[i]? = some a)
    (ih : SemSim.{w} env e mv) : SemSim.{w} env (.proj S i e) a := by
  refine semSim_trans (projSim ih) (semSim_of_redD fun hη => ?_)
  obtain ⟨entry, cvC, nP', nF', ind, hfp, hctor, hnP, hnF, hlps, hfC, hpis⟩ := hat
  subst hmv
  rw [mkAppN_toArray, List.foldl_append] at hη
  refine ⟨(etaLams_foldl fs _ hη).2 a (List.mem_of_getElem? ha), fun c hc hb => ?_⟩
  simp only [unmark, toCL?, Option.map_eq_map, Option.map_eq_some_iff] at hc
  obtain ⟨cmv, hcmv, rfl⟩ := hc
  rw [mkAppN_toArray, List.foldl_append] at hcmv
  obtain ⟨cf, cfs, hcf, hfs, rfl⟩ := toCL?_unmark_foldl fs _ hcmv
  obtain ⟨cc, cps, hcc, hps, rfl⟩ := toCL?_unmark_foldl ps _ hcf
  simp only [unmark, toCL?, Option.map_eq_map, Option.map_eq_some_iff] at hcc
  obtain ⟨usC', -, rfl⟩ := hcc
  obtain ⟨ca, hca, hra⟩ := forall₂_getElem? hfs ha
  have hbm : (ConLeche.Expr.mkAppN (ConLeche.Expr.mkAppN (.const (Name.toCL C) usC') cps) cfs).looseBVarsBounded 0
    = true := hb
  have hcacl := ((mkAppN_bounded_iff _ _).mp hbm).2 ca (List.mem_of_getElem? hca)
  refine ⟨ca, hra, hcacl, fun V _ m φ ta hta => ?_⟩
  obtain ⟨ea, -, hea, -, -⟩ := denote_proj_inv hta
  obtain ⟨⟨fa, hfa⟩, -⟩ := denote_mkAppN_inv m φ (cps ++ cfs) (f := .const (Name.toCL C) usC')
    (by rw [clMkAppN_append]; exact hea)
  have hlenps := forall₂_length hps
  have hlenfs := forall₂_length hfs
  have hi : i < fs.length := (List.getElem?_eq_some_iff.mp ha).1
  have hargs : (ConLeche.Expr.mkAppN (ConLeche.Expr.mkAppN (.const (Name.toCL C) usC') cps)
      cfs).getAppArgs = cps ++ cfs := by
    rw [← clMkAppN_append, ConLeche.Expr.getAppArgs_mkAppN]; rfl
  have hred := @ConLeche.Rules.Red.proj env 0 (Name.toCL S) i
    (ConLeche.Expr.mkAppN (ConLeche.Expr.mkAppN (.const (Name.toCL C) usC') cps) cfs) entry usC' cvC
    nP' nF' ind hfp
    (by rw [← clMkAppN_append, ConLeche.Expr.getAppFn_mkAppN, hctor]; rfl) (by omega)
    (by rw [hargs]; simp [hnP, hnF, hlenps, hlenfs])
    (by rw [hlps]; exact denote_const_len m φ hfC ⟨fa, hfa⟩)
    (by rw [hctor]; exact hfC)
    (by rw [hargs, List.length_append, ← hlenps, ← hlenfs]
        exact ConLeche.Rules.peelPis_isSome_instantiateLevelParams _ _ _ hpis)
  rw [hargs, hnP, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
    show ps.length + i - cps.length = i by omega, hca, Option.getD_some] at hred
  exact hred

/-- The `projFrozen` case of `srcEval_sound`: the projection congruence (`projSim`); the frozen
projection reads as the projection (marks are transparent). Reference: `eval_proj_prop`
(`MR E/EWcbvEval.v:238`); DV-32, DV-33. -/
theorem srcEval_sound_projFrozen {S : Name} {i : Nat} {e d : Expr}
    (ih : SemSim.{w} env e (markErase d)) :
    SemSim.{w} env (.proj S i e) (markErase (.proj S i d)) :=
  semSim_trans (projSim ih) (semSim_of_red fun hη => ⟨⟨fun h => absurd h (by simp [markMD]), hη.2⟩,
    fun c hc hb => ⟨c, by simpa [unmark] using hc, hb, .refl⟩⟩)

/-! ## The value of a `let` (the premise `hpt` of `srcEval_sound_zeta`) -/

/-- A type with the point as a member has only the point (a truth value; a strict type has no
point, `CL ConLeche/SetTheory/Derive/TypeU.lean:114 ne_pt_of_mem_strict`, `:61 IsTy`). -/
theorem IsTy.pt_of_pt {V : Type w} [ConLeche.SetTheory V] {T x y : V} (hT : IsTy T) (hx : x ∈ˢ T)
    (hy : y ∈ˢ T) (h : x = pt) : y = pt := by
  rcases hT with hT | hT
  · exact eq_pt_of_mem_univZero hT hy
  · exact absurd h (ne_pt_of_mem_strict hT hx)

/-- A term without free-variable leaves sits in the empty context at depth `0`. -/
theorem ctx0 {V : Type w} [ConLeche.SetTheory V] (m : EnvModelM V env) (φ : ConLeche.Name → Nat)
    {e : ConLeche.Expr} (h : ∀ l, l ∉ e.fvarLeaves) :
    CtxOkS m.base2 φ 0 [] e ∧ ∀ ρ : Nat → V, LeavesGr m.base2 φ 0 e ρ :=
  ⟨⟨rfl, fun l hl => absurd hl (h l)⟩, fun _ l hl _ _ => absurd hl (h l)⟩

/-- The value of a `let` that con-leche types at depth `0` lies in the reading of the `let`'s type
annotation, a type: inverting the `let` rule of the derivation
(`CL ConLeche/Rules/Rel.lean:642 Infer.letE`; `CL ConLeche/Verify/Rules/Bridge.lean:67
inferTypeCore_bridge`), the value's inferred type is the annotation's reading where neither is the
point (`CL ConLeche/Model/Rules/Sound.lean:121 defeq_sound`), the annotation a member of a sort
(`infer_sound`, `red_sound`, `CL ConLeche/SetTheory/Derive/Univ.lean:42 IsTy_of_mem_univ`).
Reference: `type_LetIn` (`MR P/PCUICTyping.v`). -/
theorem letVal_mem {V : Type w} [ConLeche.SetTheory V] (m : EnvModelM V env)
    (φ : ConLeche.Name → Nat) {cT cv cb t : ConLeche.Expr} {F : Nat}
    (h : ConLeche.inferTypeCore .verified false env F 0 (.letE cT cv cb) = .ok t)
    (hfv : (ConLeche.Expr.letE cT cv cb).hasFvar = false)
    (hb : (ConLeche.Expr.letE cT cv cb).looseBVarsBounded 0 = true) {va : ConLeche.Term.Term}
    (hva : denote m.base2.acval env φ 0 cv = some va) :
    ∃ Ta, denote m.base2.acval env φ 0 cT = some Ta ∧
      ∀ ρ : Nat → V, IsTy (interp V ρ Ta) ∧ interp V ρ va ∈ˢ interp V ρ Ta := by
  have hin := Rules.RulesInputs.ofSem m φ
  have hnil := ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hfv
  have hws := ConLeche.Expr.WScoped.of_not_hasFvar (d := 0) hfv
  obtain ⟨ea, hea⟩ := acceptedReads_of m.base2 φ h hws hb (fun l hl => by rw [hnil] at hl; cases hl)
  obtain ⟨Ta, va₀, -, hTa, hva₀, -, rfl⟩ := denote_letE_inv hea
  rw [hva] at hva₀; cases hva₀
  simp only [ConLeche.Expr.hasFvar, Bool.or_eq_false_iff] at hfv
  simp only [ConLeche.Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have frame : ∀ {x : ConLeche.Expr}, x.hasFvar = false → x.looseBVarsBounded 0 = true →
      Frame 0 x ∧ ∀ l, l ∉ x.fvarLeaves := fun {x} hx hxb =>
    have hn := ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hx
    ⟨⟨ConLeche.Expr.WScoped.of_not_hasFvar hx, hxb, fun l hl => by rw [hn] at hl; cases hl⟩,
      fun l hl => by rw [hn] at hl; cases hl⟩
  obtain ⟨hfT, hnT⟩ := frame hfv.1.1 hb.1.1
  obtain ⟨hfV, hnV⟩ := frame hfv.1.2 hb.1.2
  cases ConLeche.Rules.inferTypeCore_bridge h with
  | letE hTs hsu hvt hd _ =>
    obtain ⟨hfs, hss, sa, hsa, hTsem⟩ :=
      infer_sound hin (hTs rfl) hfT (ctx0 m φ hnT).1 hTa
    obtain ⟨hftv, hstv, ta, hta, hvsem⟩ :=
      infer_sound hin (hvt rfl) hfV (ctx0 m φ hnV).1 hva
    have hns : ∀ l, l ∉ _ := fun l hl => hnT l (hss l hl)
    have hntv : ∀ l, l ∉ _ := fun l hl => hnV l (hstv l hl)
    obtain ⟨-, -, ua, hua, husem⟩ := red_sound hin (hsu rfl) hfs (ctx0 m φ hns).1 hsa
    simp only [denote, Option.some.injEq] at hua
    subst hua
    refine ⟨Ta, hTa, fun ρ => ?_⟩
    obtain ⟨hwT, hwsa, hTmem⟩ := hTsem ρ (Sat_nil V ρ) ((ctx0 m φ hnT).2 ρ)
    obtain ⟨hwva, hwta, hvmem⟩ := hvsem ρ (Sat_nil V ρ) ((ctx0 m φ hnV).2 ρ)
    obtain ⟨-, hseq⟩ := husem ρ (Sat_nil V ρ) ((ctx0 m φ hns).2 ρ) hwsa.1 hwsa.2.ne_pt
    rw [hseq, interp_sort] at hTmem
    have hTty := IsTy_of_mem_univ hTmem
    have heq := defeq_sound hin (hd rfl) hftv hfT (ctx0 m φ hntv).1 (ctx0 m φ hnT).1 hta hTa ρ
      (Sat_nil V ρ) ((ctx0 m φ hntv).2 ρ) ((ctx0 m φ hnT).2 ρ) hwta.1 hwT hwta.2.ne_pt hTty.ne_pt
    exact ⟨hTty, heq ▸ hvmem⟩

/-- The premise `hpt` of `srcEval_sound_zeta`, from the certificates of the `let` before and after
its value is evaluated (`SrcEval.zeta`): both values lie in the reading of the one annotation, a
type (`letVal_mem`), so where the first is the point the second is (`IsTy.pt_of_pt`). Reference:
none (DV-33). -/
theorem zeta_hpt {n : Name} {T val val' b : Expr} {nd : Bool}
    (hok : CLTyped env (unmark (.letE n T val b nd))) (hok' : CLTyped env (unmark (.letE n T val' b nd))) :
    ∀ (V : Type w) [ConLeche.SetTheory V] (m : EnvModelM V env) (φ : ConLeche.Name → Nat)
      (cv cv' : ConLeche.Expr) (va va' : ConLeche.Term.Term), toCL? (unmark val) = some cv →
      toCL? (unmark val') = some cv' → denote m.base2.acval env φ 0 cv = some va →
      denote m.base2.acval env φ 0 cv' = some va' → ∀ ρ : Nat → V,
        interp V ρ va = pt → interp V ρ va' = pt := by
  intro V _ m φ cv cv' va va' hcv hcv' hva hva' ρ hpt
  have read : ∀ {x : Expr} {cx : ConLeche.Expr}, toCL? (unmark x) = some cx →
      CLTyped env (unmark (.letE n T x b nd)) →
      ∃ cT cb F t, toCL? (unmark T) = some cT ∧
        ConLeche.inferTypeCore .verified false env F 0 (.letE cT cx cb) = .ok t ∧
        (ConLeche.Expr.letE cT cx cb).hasFvar = false ∧
        (ConLeche.Expr.letE cT cx cb).looseBVarsBounded 0 = true := fun {x cx} hx hty => by
    obtain ⟨c, F, t, hc, hinf⟩ := hty
    have hcl := CLTyped.closed ⟨c, F, t, hc, hinf⟩ hc
    have hfv := toCL?_hasFvar hc
    simp only [unmark, toCL?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at hc
    obtain ⟨cT, hcT, cx', hcx', cb, -, rfl⟩ := hc
    rw [hx] at hcx'; cases hcx'
    exact ⟨cT, cb, F, t, hcT, hinf, hfv, hcl⟩
  obtain ⟨cT, cb, F, t, hcT, hinf, hfv, hb⟩ := read hcv hok
  obtain ⟨cT', cb', F', t', hcT', hinf', hfv', hb'⟩ := read hcv' hok'
  rw [hcT] at hcT'; cases hcT'
  obtain ⟨Ta, hTa, hm⟩ := letVal_mem m φ hinf hfv hb hva
  obtain ⟨Ta', hTa', hm'⟩ := letVal_mem m φ hinf' hfv' hb' hva'
  rw [hTa] at hTa'; cases hTa'
  exact IsTy.pt_of_pt (hm ρ).1 (hm ρ).2 (hm' ρ).2 hpt

end SemCases

end EraseProof
