import EraseProof.Core.StepsCtor
import EraseProof.Bridge.CLNames

/-!
# The oracle boxes the constructors of inductives declared in `Prop`

`ctorPropBoxed_of`: on a closure that is part of a program con-leche accepts, the shipping oracle
never answers `false` on a spine of a constructor of an inductive declared in `Prop`
(`Steps.CtorPropBoxed`). The constructor's type is an evident proposition (`OracleAtom.PropShape`):
con-leche checks that, past its parameters and fields, it concludes in a member of its block at the
block's level parameters, applied to the parameters and to as many index expressions as the
member's type has indices (`CL ConLeche/Kernel/Inductives/SumInstall.lean:87 structCtorResidOk`,
read back as `CL ConLeche/Verify/Inductives/DirectInv.lean:340 SumCtorRun`; the member's telescope
`CL ConLeche/Verify/Inductives/BlockInv.lean:57 checkBlockTele_shape`), and `DeclsOf?` checks that
this member is the inductive that lists the constructor (`blockShapeOK`). con-leche reads the type
without its `mdata` (`toCL?`), so the conclusion is a spine up to `mdata` (`OracleAtom.MSpine`).
The oracle then answers `true` or fails (`OracleAtom.isErasable_propShape`). Port of
`ML-V Oracle/Atom.lean:515 Pure.isErasable_ctorProp` and `ML-V Source/ProofSound.lean:497
ctor_evidentProp`, with con-leche's checks where those files have Metalean's inductive blocks.
-/

open Lean Erasure

namespace EraseProof

namespace CtorProp

open OracleAtom

/-! ## con-leche's reading of a type -/

/-- con-leche's head and arguments of a spine extended by `as`. -/
theorem getApp_mkAppN : ∀ (f : ConLeche.Expr) (as : List ConLeche.Expr),
    (ConLeche.Expr.mkAppN f as).getAppArgs = f.getAppArgs ++ as ∧
      (ConLeche.Expr.mkAppN f as).getAppFn = f.getAppFn
  | f, [] => by simp [ConLeche.Expr.mkAppN]
  | f, a :: as => by
    obtain ⟨h1, h2⟩ := getApp_mkAppN (.app f a) as
    rw [ConLeche.Expr.mkAppN, h1, h2]
    simp [ConLeche.Expr.getAppArgs, ConLeche.Expr.getAppFn]

/-- Peeling `j` binders of the reading peels `j` binders of the term (`mdata` transparent). -/
theorem toCL?_piResult : ∀ {T : Expr} {j : Nat} {c : ConLeche.Expr} {bs : List ConLeche.Expr}
    {body : ConLeche.Expr}, toCL? T = some c → c.stripPis j = some (bs, body) →
      toCL? (piResult j T) = some body := by
  intro T
  induction T with
  | forallE x t b bi _ ihb =>
    intro j c bs body hT hs
    cases j with
    | zero =>
      simp only [ConLeche.Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
      rw [← hs.2]; exact hT
    | succ j =>
      simp only [toCL?, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hT
      obtain ⟨ct, -, cb, hb, rfl⟩ := hT
      simp only [ConLeche.Expr.stripPis, Option.map_eq_some_iff] at hs
      obtain ⟨⟨bs', body'⟩, hs', he⟩ := hs
      simp only [Prod.mk.injEq] at he
      obtain ⟨-, rfl⟩ := he
      exact ihb hb hs'
  | mdata m e ih => intro j c bs body hT hs; cases j <;> exact ih hT hs
  | lit l =>
    intro j c bs body hT hs
    cases j with
    | zero =>
      simp only [ConLeche.Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
      rw [← hs.2]; exact hT
    | succ j => cases l <;> simp only [toCL?, Option.some.injEq] at hT <;> subst hT <;>
        simp [ConLeche.Expr.stripPis] at hs
  | _ =>
    intro j c bs body hT hs
    cases j with
    | zero =>
      simp only [ConLeche.Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
      rw [← hs.2]; exact hT
    | succ j =>
      obtain ⟨ct, cb, rfl⟩ : ∃ ct cb, c = .forallE ct cb := by
        cases c <;> simp [ConLeche.Expr.stripPis] at hs ⊢
      simp [toCL?, bind, Option.bind_eq_some_iff] at hT

/-- A reading whose head is a constant is a spine of that constant up to `mdata`. -/
theorem toCL?_mspine : ∀ {e : Expr} {c : ConLeche.Expr} {T : ConLeche.Name}
    {us : List ConLeche.Level}, toCL? e = some c → c.getAppFn = .const T us →
      ∃ h vs, Name.toCL h = T ∧ MSpine h vs c.getAppArgs.length e := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro c T us he hf
    simp only [toCL?, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at he
    obtain ⟨cf, hcf, ca, -, rfl⟩ := he
    obtain ⟨h, vs, hT, hs⟩ := ihf hcf hf
    exact ⟨h, vs, hT, by simpa [ConLeche.Expr.getAppArgs] using hs.app⟩
  | mdata m e ih =>
    intro c T us he hf
    obtain ⟨h, vs, hT, hs⟩ := ih he hf
    exact ⟨h, vs, hT, hs.mdata⟩
  | const h vs =>
    intro c T us he hf
    simp only [toCL?, Option.map_eq_map, Option.map_eq_some_iff] at he
    obtain ⟨us', -, rfl⟩ := he
    simp only [ConLeche.Expr.getAppFn, ConLeche.Expr.const.injEq] at hf
    exact ⟨h, vs, hf.1, .const⟩
  | lit l =>
    intro c T us he hf
    cases l <;> simp only [toCL?, Option.some.injEq] at he <;> subst he <;>
      simp [ConLeche.Expr.getAppFn] at hf
  | _ =>
    intro c T us he hf
    cases c <;> simp [toCL?, bind, Option.bind_eq_some_iff, ConLeche.Expr.getAppFn] at he hf

/-- The reading of a syntactic arity `Π x₁…xₖ, Sort u` ends in a sort, after exactly `k`
binders. -/
theorem toCL?_arity : ∀ {T : Expr} {k : Nat} {u : Level} {c : ConLeche.Expr},
    arityShape T = some (k, u) → toCL? T = some c →
      (∃ s, c.piResult = .sort s) ∧
        ∀ {j : Nat} {bs : List ConLeche.Expr} {s : ConLeche.Level},
          c.stripPis j = some (bs, .sort s) → j = k := by
  intro T
  induction T with
  | sort u' =>
    intro k u c ha hT
    simp only [arityShape, Option.some.injEq, Prod.mk.injEq] at ha
    obtain ⟨rfl, -⟩ := ha
    simp only [toCL?, Option.map_eq_map, Option.map_eq_some_iff] at hT
    obtain ⟨s, -, rfl⟩ := hT
    refine ⟨⟨s, rfl⟩, fun {j bs s'} hs => ?_⟩
    cases j with
    | zero => rfl
    | succ j => simp [ConLeche.Expr.stripPis] at hs
  | forallE x t b bi _ ihb =>
    intro k u c ha hT
    simp only [arityShape, Option.map_eq_some_iff] at ha
    obtain ⟨⟨k', u'⟩, ha', he⟩ := ha
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    simp only [toCL?, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hT
    obtain ⟨ct, -, cb, hb, rfl⟩ := hT
    obtain ⟨⟨s, hs⟩, hj⟩ := ihb ha' hb
    refine ⟨⟨s, hs⟩, fun {j bs s'} h => ?_⟩
    cases j with
    | zero => simp [ConLeche.Expr.stripPis] at h
    | succ j =>
      simp only [ConLeche.Expr.stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs', b'⟩, h', he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨-, rfl⟩ := he
      rw [hj h']
  | mdata m e ih => intro k u c ha hT; exact ih ha hT
  | _ => intro k u c ha; simp [arityShape] at ha

/-- The head constant of a spine up to `mdata`. -/
theorem appHeadConst_of_mspine {h : Name} {vs : List Level} {k : Nat} {e : Expr}
    (H : MSpine h vs k e) : EraseProof.appHeadConst e = some h := by
  induction H with
  | const => rfl
  | app _ ih => exact ih
  | mdata _ ih => exact ih

/-- An evident proposition after `j` binders is one before them. -/
theorem PropShape.of_piResult {D : List ConstantInfo} : ∀ {T : Expr} {j : Nat},
    PropShape D (piResult j T) → PropShape D T := by
  intro T
  induction T with
  | forallE x t b bi _ ihb =>
    intro j h
    cases j with
    | zero => exact h
    | succ j => exact .forallE (ihb h)
  | mdata m e ih => intro j h; cases j <;> exact .mdata (ih h)
  | _ => intro j h; cases j <;> exact h

/-! ## The constructor's conclusion, from con-leche's block check -/

/-- Every member's former is a telescope of its parameters and indices over a sort: the stage
`checkBlockInds` of con-leche's block check (`CL ConLeche/Verify/Inductives/BlockInv.lean:199
checkBlockInds_shape`). -/
theorem checkBlockInds_teleSort {F : Nat} {env envI : ConLeche.Env} {p p₁ : ConLeche.BlockShape}
    {isRec : Bool}
    (h : ConLeche.checkBlockInds (m := ConLeche.CheckM) (ConLeche.fueledOps .verified F) env p isRec
      = .ok (envI, p₁)) :
    ∀ m ∈ p.members, ∃ bs s, m.cvT.type.stripPis (p.nP + m.nIdx) = some (bs, .sort s) := by
  obtain ⟨ms0, rest, cvTa0, s0, cvs, hm, -, -, hq, hcvs, -⟩ := ConLeche.checkBlockInds_shape h
  have hf := ConLeche.checkBlockInds_teles hm hq hcvs
  rw [ConLeche.BlockShape.formers, hm, List.map_cons, List.cons.injEq] at hf
  obtain ⟨h0, hr⟩ := hf
  obtain ⟨-, hall⟩ := ConLeche.checkBlockTeles_inv hcvs
  intro m hmm
  rw [hm] at hmm
  rcases List.mem_cons.mp hmm with rfl | hmr
  · obtain ⟨-, -, -, -, -, bs, hbs⟩ := ConLeche.checkBlockTele_shape hq
    exact ⟨bs, s0, h0 ▸ hbs⟩
  · obtain ⟨i, hi⟩ := List.getElem?_of_mem hmr
    obtain ⟨⟨cvq, sq⟩, hq', hqt⟩ := hall i m hi
    obtain ⟨-, -, -, -, -, bs, hbs⟩ := ConLeche.checkBlockTele_shape hqt
    have he : cvq = m.cvT := by
      have := congrArg (·[i]?) hr
      simp only [List.getElem?_map, hq', hi, Option.map_some, Option.some.injEq] at this
      exact this
    exact ⟨bs, sq, he ▸ hbs⟩

/-- The block run of the block of `P` headed by `H` (`CL ConLeche/Semantics/Bridge/Sound.lean:41
checkDeclRun_ofEnvFactsK`). -/
theorem ConLecheAccepts.blockRun {P : List ConstantInfo} {env : ConLeche.Env}
    (h : ConLecheAccepts P env) {n : Name} {H : InductiveVal}
    (hH : findDecl P n = some (.inductInfo H)) (hhead : H.all.head? = some n) :
    ∃ block p e e', blockOf? P H = some (.indDecl block H.numParams) ∧
      ConLeche.readBlock H.numParams block = .ok p ∧
      ConLeche.Semantics.BlockRun ConLeche.checkFuel e block p e' := by
  obtain ⟨hmem, hn⟩ := findDecl_mem hH
  have hs := h.ind_safe hmem
  obtain ⟨block, p, hb, hdf, -⟩ := h.block hH hhead hs
  have hhn : H.all.head? = some H.name := by rw [← hn] at hhead; exact hhead
  have hd : declOf? P (.inductInfo H) = some [.indDecl block H.numParams] := by
    simp [declOf?, hs, hhn, hb]
  obtain ⟨⟨e, e', hrun⟩, -⟩ := h.stored hmem hd
  obtain ⟨-, hk⟩ := ConLeche.Semantics.checkDeclRun_ofEnvFactsK hrun
  have hk' : ConLeche.Semantics.DeclIndRunDispatchK _ e block H.numParams e' := hk
  unfold ConLeche.Semantics.DeclIndRunDispatchK at hk'
  rw [hdf] at hk'
  exact ⟨block, p, e, e', hb, hdf, hk'⟩

/-- The block of an inductive of `P` (`declOf?`): its head is an inductive of `P`, first in its
own `all`, whose `all` lists the inductive. -/
theorem ConLecheAccepts.blockHead {P : List ConstantInfo} {env : ConLeche.Env}
    (h : ConLecheAccepts P env) {iv : InductiveVal} (hiv : .inductInfo iv ∈ P) :
    ∃ n H, findDecl P n = some (.inductInfo H) ∧ H.all.head? = some n ∧ iv.name ∈ H.all := by
  obtain ⟨ds, hds, -⟩ := h
  obtain ⟨L, hL, -⟩ := DeclsOf?.mem hds hiv
  have hnd := DeclsOf?.nodup hds
  have hs : iv.isUnsafe = false := by
    cases hu : iv.isUnsafe with
    | false => rfl
    | true => simp [declOf?, hu] at hL
  by_cases hhd : iv.all.head? = some iv.name
  · exact ⟨iv.name, iv, findDecl_self hnd hiv, hhd, List.mem_of_head? hhd⟩
  · simp only [declOf?, hs, Bool.false_eq_true, ↓reduceIte, beq_iff_eq, hhd] at hL
    cases hn : iv.all.head? with
    | none => simp [hn] at hL
    | some n =>
      rw [hn] at hL
      simp only [Option.bind_some] at hL
      split at hL
      · rename_i H hH
        split at hL
        · rename_i hc
          simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hc
          exact ⟨n, H, hH, by rw [hc.1]; exact hn, hc.1 ▸ hc.2⟩
        · exact nomatch hL
      · exact nomatch hL

/-- What `blockShapeOK` checks of a constructor of a member `t` of the block headed by `H`: its
parameter count is the block's, and its conclusion past its parameters and fields is headed by
`t`. -/
theorem blockOf?_ctorHead {P : List ConstantInfo} {H : InductiveVal} {d : ConLeche.Declaration}
    (h : blockOf? P H = some d) {n : Name} {t : InductiveVal} {cn : Name} {c : ConstructorVal}
    (hn : n ∈ H.all) (ht : findConst P n = some (.inductInfo t)) (hcn : cn ∈ t.ctors)
    (hc : findConst P cn = some (.ctorInfo c)) :
    c.numParams = H.numParams ∧
      appHeadConst (piResult (H.numParams + c.numFields) c.type) = some t.name := by
  simp only [blockOf?, Option.bind_eq_some_iff, bind, pure] at h
  obtain ⟨tys, htys, cvs, hcvs, u, hg, -⟩ := h
  unfold guard at hg
  split at hg
  case isFalse => simp [failure] at hg
  rename_i hok
  have htm : t ∈ tys := by
    have hm := mapM_eq_some htys ▸ List.mem_map_of_mem (f := fun n => match findConst P n with
      | some (.inductInfo t) => some t
      | _ => none) hn
    obtain ⟨t', ht', he⟩ := List.mem_map.mp hm
    simp only [ht, Option.some.injEq] at he
    exact he ▸ ht'
  obtain ⟨cs, hcs', hz⟩ : ∃ cs, t.ctors.mapM (fun n => match findConst P n with
      | some (.ctorInfo c) => some c
      | _ => none) = some cs ∧ (t, cs) ∈ tys.zip cvs := by
    have hm₂ := mapM_eq_some hcvs ▸ List.mem_map_of_mem (f := fun (t : InductiveVal) =>
      t.ctors.mapM fun n => match findConst P n with
        | some (.ctorInfo c) => some c
        | _ => none) htm
    obtain ⟨cs, -, he₂⟩ := List.mem_map.mp hm₂
    exact ⟨cs, he₂.symm, mem_zip_of_mapM (mapM_eq_some hcvs) htm he₂.symm⟩
  have hcm : c ∈ cs := by
    have hm₃ := mapM_eq_some hcs' ▸ List.mem_map_of_mem (f := fun n => match findConst P n with
      | some (.ctorInfo c) => some c
      | _ => none) hcn
    obtain ⟨c', hc', he₃⟩ := List.mem_map.mp hm₃
    simp only [hc, Option.some.injEq] at he₃
    exact he₃ ▸ hc'
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hcm
  simp only [blockShapeOK, Bool.and_eq_true, List.all_eq_true] at hok
  have := hok.1.1.1.1.2 _ hz (c, j) (List.mem_zipIdx_iff_getElem?.mpr hj)
  simp only [beq_iff_eq] at this
  exact ⟨this.1.1.2, this.2⟩

/-- **A constructor of an inductive of `P` concludes in its inductive applied to as many arguments
as the inductive's type has binders**, up to `mdata`: con-leche's check of the constructor at its
member (`SumCtorRun`), the member's telescope (`checkBlockInds_teleSort`), and the member that
`DeclsOf?` names (`blockOf?_ctorHead`). Reference: the constructor's type
`Π (params) (fields), I params indices` (`MR common/theories/EnvironmentTyping.v:1502
cstr_concl`, `:1507 on_constructor`). -/
theorem ConLecheAccepts.ctor_mspine {P : List ConstantInfo} {env : ConLeche.Env}
    (h : ConLecheAccepts P env) {cv : ConstructorVal} {iv : InductiveVal} {k : Nat} {u : Level}
    (hc : .ctorInfo cv ∈ P) (hiv : findDecl P cv.induct = some (.inductInfo iv))
    (har : arityShape iv.type = some (k, u)) :
    ∃ vs, MSpine iv.name vs k (piResult (cv.numParams + cv.numFields) cv.type) := by
  obtain ⟨ds, hds, -⟩ := id h
  have hnd := DeclsOf?.nodup hds
  obtain ⟨hivm, hivn⟩ := findDecl_mem hiv
  have hfiv : findConst P iv.name = some (.inductInfo iv) := findDecl_self hnd hivm
  have hfc : findConst P cv.name = some (.ctorInfo cv) := findDecl_self hnd hc
  have hlist : cv.name ∈ iv.ctors := by
    obtain ⟨L, hL, -⟩ := DeclsOf?.mem hds hc
    simp only [declOf?] at hL
    rw [show findConst P cv.induct = findDecl P cv.induct from rfl, hiv] at hL
    simp only at hL
    split at hL
    · rename_i hcon; simpa using hcon
    · exact nomatch hL
  obtain ⟨n, H, hH, hhead, hmemH⟩ := ConLecheAccepts.blockHead h hivm
  obtain ⟨block, p, e, e', hb, hdf, hrun⟩ := ConLecheAccepts.blockRun h hH hhead
  obtain ⟨hnP, happ⟩ := blockOf?_ctorHead hb hmemH hfiv hlist hfc
  -- the records `blockOf?` writes for `iv` and `cv`
  obtain ⟨_, hbe, -, hspec⟩ := blockOf?_spec hb
  cases hbe
  obtain ⟨t, ht, ⟨cvIv, hcvIv, hIvb⟩, hctors⟩ := hspec iv.name hmemH
  rw [hfiv] at ht
  cases ht
  obtain ⟨c', hc', cvC, hcvC, hCb⟩ := hctors cv.name hlist
  rw [hfc] at hc'
  cases hc'
  obtain ⟨tyI, htyI, rfl⟩ := cvOf?_eq_some hcvIv
  obtain ⟨tyC, htyC, rfl⟩ := cvOf?_eq_some hcvC
  obtain ⟨⟨sI, hsI⟩, hkI⟩ := toCL?_arity har htyI
  -- the constructor's entry in a member of the block
  have hd := ConLeche.readBlock_declared hdf
  obtain ⟨hndA, hgr, -⟩ := blockRun_pins hd hrun
  obtain ⟨hpnP, -, -, -, -, -, -, cvTs, cs, rs, nIdxs, hsp, -, -, -, -, -, hmem, -⟩ :=
    ConLeche.readBlock_inv hdf
  obtain ⟨m, hm, hcm⟩ : ∃ m ∈ p.members,
      ((⟨Name.toCL cv.name, cv.levelParams.map Name.toCL, tyC⟩ : ConLeche.ConstantVal),
        cv.numFields) ∈ m.ctors := by
    have hcs := (blockSplit_mem hsp).2.1 hCb
    have hnames := hgr hsp
    have hin : Name.toCL cv.name ∈ p.allCtors.map (·.1.name) := by
      rw [hnames]; exact List.mem_map_of_mem (f := fun c => c.1.name) hcs
    obtain ⟨a, ha, han⟩ := List.mem_map.mp hin
    obtain ⟨L, hL, haL⟩ := List.mem_flatten.mp ha
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hL
    have hmg : m ∈ _ := hmem ▸ hm
    obtain ⟨-, hg⟩ := ConLeche.blockMembers_mem hmg
    obtain ⟨c', hc', rfl⟩ := List.mem_map.mp (ConLeche.mem_blockGroups hg haL)
    have hcc := eq_of_nodup_map (hnames ▸ hndA) hc' hcs han
    subst hcc
    exact ⟨m, hm, haL⟩
  -- the run at that member
  obtain ⟨ms, hms, hat, hdecl, hR⟩ := hrun
  obtain ⟨-, hndM, _, isRec, env₁, p₁, _, _, _, _, _, _, _, _, _, _, _, _, hInd, hCtors, -⟩ := hR
  obtain ⟨-, -, -, -, hctorsEq⟩ := ConLeche.reduceMembers_inv hd hms
  obtain ⟨ms', hms', hmc⟩ : ∃ ms' ∈ ms, ms'.ctors = m.ctors := by
    have : m.ctors ∈ ms.map (·.ctors) := hctorsEq ▸ List.mem_map_of_mem hm
    exact List.mem_map.mp this
  have hmem₁ := ConLeche.checkBlockInds_members hInd
  obtain ⟨_, _, _, s0, _, _, hq, -⟩ := ConLeche.checkBlockInds_shape hInd
  have hnP₁ : p₁.nP = p.nP := by rw [hq]; rfl
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hms'
  obtain ⟨-, hall⟩ := hCtors
  obtain ⟨sortss, -, hrunC⟩ := hall i ms' (by rw [hmem₁]; exact hi)
  obtain ⟨-, -, hrunJ⟩ := hrunC
  obtain ⟨jc, hjc⟩ := List.getElem?_of_mem (hmc ▸ hcm)
  obtain ⟨-, sorts, -, -, ⟨cbs, es, hstrip, hes⟩, -⟩ := hrunJ jc _ _ hjc hjc
  -- the reading of the conclusion
  dsimp only at hstrip
  rw [hnP₁, hpnP, ← hnP] at hstrip
  have hres := toCL?_piResult htyC hstrip
  obtain ⟨hargs, hfn⟩ := getApp_mkAppN (.const ms'.cvT.name (p₁.lps.map .param))
    (ConLeche.structPsAt cv.numFields cv.numParams ++ es)
  obtain ⟨hh, vs, hT, hsp'⟩ := toCL?_mspine hres hfn
  have hhn : hh = iv.name := by
    have := appHeadConst_of_mspine hsp'
    rw [hnP, happ, Option.some.injEq] at this
    exact this.symm
  subst hhn
  -- the member is `iv`'s, at its declared former
  obtain ⟨m₀, hm₀, hm₀d⟩ := (readBlock_former_mem hdf hIvb).2
  obtain ⟨msI, hmsI, hmsId⟩ : ∃ msI ∈ ms, msI.declared = ⟨Name.toCL iv.name,
      iv.levelParams.map Name.toCL, tyI⟩ := by
    have : m₀.declared ∈ ms.map (·.declared) := hdecl ▸ List.mem_map_of_mem hm₀
    obtain ⟨msI, h1, h2⟩ := List.mem_map.mp this
    exact ⟨msI, h1, h2.trans hm₀d⟩
  have hname : msI.cvT.name = ms'.cvT.name := by
    rw [(hat msI hmsI).name, hmsId, ← hT]
  have hII : ms' = msI := eq_of_nodup_map hndM hms' hmsI hname.symm
  subst hII
  have hcvT : ms'.cvT = ms'.declared := by
    rcases (hat ms' hmsI).how with ⟨-, h1⟩ | ⟨h1, -⟩
    · exact h1
    · simp [hmsId, ConLeche.formerDefHeaded, ConLeche.formerResSort, hsI] at h1
  obtain ⟨bs, s, hbs⟩ := checkBlockInds_teleSort hInd ms' (by exact hmsI)
  rw [hcvT, hmsId] at hbs
  have hk := hkI hbs
  refine ⟨vs, ?_⟩
  have hlen : (ConLeche.Expr.getAppArgs (ConLeche.Expr.mkAppN
      (.const ms'.cvT.name (p₁.lps.map .param))
      (ConLeche.structPsAt cv.numFields cv.numParams ++ es))).length = k := by
    rw [hargs]
    simp only at hk
    simp [ConLeche.Expr.getAppArgs, ConLeche.structPsAt, hes]
    omega
  exact hlen ▸ hsp'

end CtorProp

open CtorProp OracleAtom in
/-- **The oracle never answers `false` on a spine of a constructor of an inductive declared in
`Prop`**, on a closure that is part of a program con-leche accepts (`Steps.CtorPropBoxed`): the
constructor's type is an evident proposition (`ConLecheAccepts.ctor_mspine`, the inductive's sort
evidently zero by `EvalEnv.propInd`), so the spine's inferred type is one, whose sort is evidently
zero (`OracleAtom.isErasable_propShape`). Port of `ML-V Oracle/Atom.lean:515
Pure.isErasable_ctorProp` with `ML-V Source/ProofSound.lean:497 ctor_evidentProp`. Reference:
`isErasable` on propositional constructors (`MR E/Extract.v:106 erases_tConstruct`,
`~~ isPropositional`); DV-11. -/
theorem ctorPropBoxed_of {P decls : List ConstantInfo} {env : ConLeche.Env} {view : EnvView}
    {cfg : ErasureConfig} (h : ConLecheAccepts P env) (hsub : SubEnv decls P) :
    Steps.CtorPropBoxed view cfg decls := by
  intro ls c us as cv b hc hp hb
  obtain ⟨iv, k, u, hiv, har, hz⟩ : ∃ iv k u, findDecl decls cv.induct = some (.inductInfo iv) ∧
      arityShape iv.type = some (k, u) ∧ EvidentZero u = true := by
    simp only [EvalEnv.propInd, evalEnvOf] at hp
    split at hp
    · rename_i iv hiv
      split at hp
      · rename_i k u har
        exact ⟨iv, k, u, hiv, har, hp⟩
      · cases hp
    · cases hp
  obtain ⟨hcm, -⟩ := findDecl_mem hc
  obtain ⟨hivm, hivn⟩ := findDecl_mem hiv
  have hcP : findDecl P cv.induct = some (.inductInfo iv) := hivn ▸ hsub _ hivm
  obtain ⟨vs, hs⟩ := CtorProp.ConLecheAccepts.ctor_mspine h (findDecl_mem (hsub _ hcm)).1 hcP har
  have hiv' : findDecl decls iv.name = some (.inductInfo iv) := by
    rw [show iv.name = cv.induct from hivn]; exact hiv
  have hps : PropShape decls cv.type :=
    PropShape.of_piResult (.tail hiv' rfl har (EvidentZero.instLevel hz) hs)
  exact isErasable_propShape (cx := ⟨decls⟩) (ci := .ctorInfo cv) (ConstSpine.mkAppN c us as) hc
    rfl hps hb

end EraseProof
