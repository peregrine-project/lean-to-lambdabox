import EraseProof.Semantics.Iota
import EraseProof.Bridge.CLNames

/-!
# The stored records of a recognized `casesOn`, and the grading of a certified term

What the ι step of `srcEval_sound` reads of con-leche's environment, decoded from the program:
the shipping recognizer `Erasure.casesInfo?` (`LeanToLambdaBox/Erasure/Pure.lean:107`) accepts a
definition `T.casesOn` whose value is `D` λs over `T.rec` applied to the canonical arguments, and
con-leche's fold stores that value, the recursor and the constructors as their translated records
(`EraseProof.Bridge.CLStore`). Read through `toCL?`, the value has the shape `CasesIotaAt` names,
for an inductive alone in its block. Also: a term the run-time certificate `CLOk` types is graded
through its marks (`GradedU`).
-/

open Lean Erasure

namespace EraseProof

universe w

/-- A term `CLOk` certifies is graded through its marks: the certificate's second run types the
reading of `unmark t`, which is then closed (`CLTyped.closed`) and graded in every model
(`SemCases.infer0`). Reference: none (DV-33). -/
theorem CLOk.gradedU {env : ConLeche.Env} {t : Expr} (h : CLOk env t) : GradedU.{w} env t := by
  obtain ⟨c, F, T, hc, hinf⟩ := h.2
  have hb := CLTyped.closed h.2 hc
  exact ⟨c, hc, hb, fun V _ m φ => SemCases.infer0 m φ hinf (toCL?_hasFvar hc) hb⟩

namespace Decode

/-! ## The recognizer's syntax tests -/

/-- `isBVarAt`, read. -/
theorem isBVarAt_eq {args : List Expr} {i m : Nat} (h : isBVarAt args i m = true) :
    args[i]? = some (.bvar m) := by
  unfold isBVarAt at h
  split at h
  · rename_i j hj; rw [hj, beq_iff_eq.mp h]
  · exact nomatch h

/-- The level arguments `isConstAt` accepts are the level parameters. -/
theorem params_of_zip : ∀ {us : List Level} {lps : List Name}, us.length = lps.length →
    (∀ x ∈ us.zip lps, (match x with | (.param a, b) => a == b | _ => false) = true) →
    us = lps.map .param
  | [], [], _, _ => rfl
  | u :: us, l :: lps, hl, h => by
    have h0 := h (u, l) List.mem_cons_self
    have ih := params_of_zip (us := us) (lps := lps) (by simpa using hl)
      (fun x hx => h x (List.mem_cons_of_mem _ hx))
    cases u <;> simp at h0
    simp [h0, ih]
  | [], _ :: _, hl, _ | _ :: _, [], hl, _ => by simp at hl

/-- `isConstAt`, read. -/
theorem isConstAt_eq {e : Expr} {c : Name} {lps : List Name} (h : isConstAt e c lps = true) :
    e = .const c (lps.map .param) := by
  unfold isConstAt at h
  split at h
  · rename_i c' us
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨⟨rfl, hl⟩, hall⟩ := h
    rw [params_of_zip hl hall]
  · exact nomatch h

/-- A spine is its head applied to its arguments. -/
theorem spine_foldl {h : Expr} : ∀ {e : Expr} {as : List Expr}, spine e = (h, as) →
    e = as.foldl .app h := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro as hs
    rcases hsf : spine f with ⟨h', as'⟩
    simp only [spine, hsf, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    rw [List.foldl_append, ← ihf hsf]; rfl
  | _ => intro as hs; simp only [spine, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs; rfl

/-- `isMinorBody`, read: the variable `m` applied to `bvar (L-1), …, bvar (L-nf)`. -/
theorem isMinorBody_eq {e : Expr} {m L nf : Nat} (h : isMinorBody e m L nf = true) :
    ∃ as : List Expr, e = as.foldl .app (.bvar m) ∧ as.length = nf ∧
      ∀ f < nf, as[f]? = some (.bvar (L - 1 - f)) := by
  unfold isMinorBody at h
  split at h
  · rename_i hd as hs
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
    obtain ⟨⟨rfl, hl⟩, hb⟩ := h
    exact ⟨as, spine_foldl hs, hl, fun f hf => isBVarAt_eq (hb f hf)⟩
  · exact nomatch h

/-- `ctorAlts`, read: one alternative per constructor, with its field count. -/
theorem ctorAlts_spec {P : List ConstantInfo} : ∀ {cs : List Name} {alts : List CasesAltInfo},
    ctorAlts P cs = some alts → alts.length = cs.length ∧ ∀ {i : Nat} {c : Name} {cv : ConstructorVal},
      cs[i]? = some c → findConst P c = some (.ctorInfo cv) → altFields alts i = cv.numFields
  | [], alts, h => by
    simp only [ctorAlts, Option.some.injEq] at h; subst h; exact ⟨rfl, fun hi => by simp at hi⟩
  | c :: cs, alts, h => by
    unfold ctorAlts at h
    split at h
    · rename_i cv' as hc' has
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨hl, hi⟩ := ctorAlts_spec has
      refine ⟨by simp [hl], fun {i c'' cv} hci hf => ?_⟩
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hci; subst hci
        rw [hc', Option.some.injEq, ConstantInfo.ctorInfo.injEq] at hf; subst hf
        rfl
      | succ i => exact hi (by simpa using hci) hf
    · exact nomatch h

/-! ## Their readings in con-leche's syntax -/

/-- The reading of a spine is the spine of the readings. -/
theorem toCL?_foldl : ∀ (as : List Expr) (f : Expr) {c : ConLeche.Expr},
    toCL? (as.foldl .app f) = some c →
    ∃ cf cas, toCL? f = some cf ∧ List.Forall₂ (fun a ca => toCL? a = some ca) as cas ∧
      c = ConLeche.Expr.mkAppN cf cas
  | [], _, c, h => ⟨c, [], h, .nil, rfl⟩
  | a :: as, f, _, h => by
    obtain ⟨cf', cas, hf', hall, rfl⟩ := toCL?_foldl as (.app f a) h
    simp only [toCL?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at hf'
    obtain ⟨cf, hcf, ca, hca, rfl⟩ := hf'
    exact ⟨cf, ca :: cas, hcf, .cons hca hall, rfl⟩

/-- The reading of `n` λs is `n` λs over the reading of the body. -/
theorem toCL?_peelLams : ∀ (n : Nat) {e b : Expr} {ce : ConLeche.Expr}, peelLams n e = some b →
    toCL? e = some ce → ∃ cb, toCL? b = some cb ∧ clLams ce = (n + (clLams cb).1, (clLams cb).2)
  | 0, e, b, ce, h, hc => by
    simp only [peelLams, Option.some.injEq] at h; subst h; exact ⟨ce, hc, by simp⟩
  | n + 1, e, b, ce, h, hc => by
    cases e <;> simp only [peelLams, reduceCtorEq] at h
    rename_i t b' _
    simp only [toCL?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at hc
    obtain ⟨ct, -, cb', hcb', rfl⟩ := hc
    obtain ⟨cb, hcb, hl⟩ := toCL?_peelLams n h hcb'
    refine ⟨cb, hcb, ?_⟩
    simp only [clLams, hl, Prod.mk.injEq, and_true]
    omega

/-- A spine whose head is no λ has no leading λ. -/
theorem clLams_mkAppN : ∀ (as : List ConLeche.Expr) {f : ConLeche.Expr}, clLams f = (0, f) →
    clLams (ConLeche.Expr.mkAppN f as) = (0, ConLeche.Expr.mkAppN f as)
  | [], _, hf => hf
  | a :: as, f, _ => clLams_mkAppN as (f := .app f a) rfl

/-- Arguments that are the field variables read as `fbv`. -/
theorem forall₂_fbv {as : List Expr} {cas : List ConLeche.Expr} {n L : Nat}
    (hall : List.Forall₂ (fun a ca => toCL? a = some ca) as cas) (hl : as.length = n)
    (hb : ∀ f < n, as[f]? = some (.bvar (L - 1 - f))) : cas = SemCases.fbv n L := by
  have hl' := SemCases.forall₂_length hall
  apply List.ext_getElem?
  intro f
  by_cases hf : f < n
  · obtain ⟨ca, hca, hr⟩ := SemCases.forall₂_getElem? hall (hb f hf)
    simp only [toCL?, Option.some.injEq] at hr
    rw [hca, ← hr]
    simp [SemCases.fbv, hf]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp [SemCases.fbv]; omega)]

/-- The level parameters, read. -/
theorem mapM_param (lps : List Name) :
    (lps.map Level.param).mapM Level.toCL = some ((lps.map Name.toCL).map ConLeche.Level.param) := by
  induction lps with
  | nil => rfl
  | cons l lps ih => simp [List.mapM_cons, Level.toCL, ih]

/-! ## The program's blocks -/

/-- What `blockOf?` checks of the block headed by `H` (`blockShapeOK`): every member lists the
block, every recursor of the block has its parameter count, and a block of one type has the recursor
`H.rec`, of one motive, one minor premise per constructor and the
type's index count. -/
theorem blockOf?_shape {P : List ConstantInfo} {H : InductiveVal} {d : ConLeche.Declaration}
    (h : blockOf? P H = some d) :
    (∀ n ∈ H.all, ∀ t, findConst P n = some (.inductInfo t) → t.all = H.all) ∧
    (∀ r, .recInfo r ∈ P → r.all = H.all → r.numParams = H.numParams) ∧
    (H.all = [H.name] → findConst P H.name = some (.inductInfo H) →
      ∃ r, .recInfo r ∈ P ∧ r.all = H.all ∧ r.name = mkRecName H.name ∧ r.numMotives = 1 ∧
        r.numMinors = H.ctors.length ∧ r.numIndices = H.numIndices) := by
  simp only [blockOf?, Option.bind_eq_some_iff, Option.some.injEq, bind, pure] at h
  obtain ⟨tys, htys, cvs, hcvs, _, hg, -⟩ := h
  simp only [guard] at hg
  split at hg
  rotate_left; · exact nomatch hg
  rename_i hok
  have hty : ∀ n ∈ H.all, ∀ t, findConst P n = some (.inductInfo t) → t ∈ tys := fun n hn t ht => by
    have := mapM_eq_some htys ▸ List.mem_map_of_mem (f := fun n => match findConst P n with
      | some (.inductInfo t) => some t
      | _ => none) hn
    simp only [ht] at this
    obtain ⟨t', ht', he⟩ := List.mem_map.mp this
    cases he; exact ht'
  unfold blockShapeOK at hok
  simp only [Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq,
    bne_iff_ne, ne_eq] at hok
  have hrs : ∀ r, .recInfo r ∈ P → r.all = H.all → r ∈ P.reverse.filterMap (fun
      | .recInfo r => if r.all = H.all then some r else none
      | _ => none) := fun r hr hall =>
    List.mem_filterMap.mpr ⟨_, List.mem_reverse.mpr hr, by simp [hall]⟩
  obtain ⟨⟨⟨⟨⟨⟨hr, ht⟩, -⟩, -⟩, -⟩, -⟩, hany⟩ := hok
  refine ⟨fun n hn t hnt => (ht t (hty n hn t hnt)).1.1, fun r hr' hall => (hr r (hrs r hr' hall)).1.1.1,
    fun hall hH => ?_⟩
  have htys1 : tys = [H] := by
    rw [hall] at htys
    simpa [hH] using htys.symm
  subst htys1
  obtain ⟨cs, hcs, rfl⟩ : ∃ cs, H.ctors.mapM (fun n => match findConst P n with
      | some (.ctorInfo c) => some c
      | _ => none) = some cs ∧ cvs = [cs] := by
    simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind, Option.pure_def,
      Option.bind_eq_some_iff, Option.some.injEq] at hcvs
    obtain ⟨cs, hcs, _, rfl, rfl⟩ := hcvs
    exact ⟨cs, hcs, rfl⟩
  have hlen : cs.length = H.ctors.length := by
    simpa using (congrArg List.length (mapM_eq_some hcs)).symm
  obtain ⟨r, hr, ⟨⟨⟨⟨hname, -⟩, hmot⟩, hmin⟩, hidx⟩, -⟩ := hany H List.mem_cons_self
  obtain ⟨x, hx, hxr⟩ := List.mem_filterMap.mp hr
  cases x <;> simp only [reduceCtorEq, Option.ite_none_right_eq_some, Option.some.injEq] at hxr
  obtain ⟨hrall, rfl⟩ := hxr
  exact ⟨_, List.mem_reverse.mp hx, hrall, hname, by simpa using hmot, by simpa [hlen] using hmin,
    hidx⟩


/-! ## The decode -/

/-- **The stored records of a recognized `casesOn`**, at the constructor `C` of an inductive `iv`
alone in its block: the shipping recognizer `casesInfo?` (`LeanToLambdaBox/Erasure/Pure.lean:107`)
accepts `c = T.casesOn` with the value `fun ps motive is t ms => T.rec ps motive minors' is t`, the
own minor of `C` the wrapper `fun fs ihs => m_C fs` over the recursor's minor premise; con-leche's
fold stores that value at `c` (`ConLecheAccepts.find?_defn`, closed by
`CL ConLeche/Verify/EnvWF.lean:102 ConstWF`), the recursor `T.rec` with `RulesCanonical`'s
`Π`-count (`ConLecheAccepts.find?_rec`) and `C` with its counts (`ConLecheAccepts.find?_single`);
`DeclsOf?` (`blockShapeOK`) gives the recursor the inductive's counts. What the recognizer does not
check, and con-leche states nothing of, is the stored rule's selection: `hrule`, the rule for `C`
has `C`'s field count, `C`'s own minor premise at its head and as many inductive hypotheses as the
minor premise binds past the fields; `hnocert` is the ι case split's case 2. `hcl` (`CtorsListed`):
`C` is the constructor at its index; `hsafe`: the definition is safe, as `find?_defn` asks. Reference: `casesInfo?` on the stored records, the rule
shape of `CL ConLeche/Kernel/Inductives/GenRec.lean:189 classGenRule`. -/
theorem _root_.EraseProof.ConLecheAccepts.casesIotaAt {P : List ConstantInfo} {env : ConLeche.Env}
    (h : ConLecheAccepts P env) (hcl : CtorsListed P) {c : Name} {iv : InductiveVal}
    (hc : casesOnOf? P c = some iv) (hone : iv.all = [iv.name])
    (hsafe : ∀ d, findDecl P c = some (.defnInfo d) → d.safety = .safe)
    {C : Name} {cv : ConstructorVal} (hC : findDecl P C = some (.ctorInfo cv))
    (hCT : cv.induct = iv.name)
    (hrule : ∀ rv, findDecl P (mkRecName iv.name) = some (.recInfo rv) →
      ∀ {cvR mI rP isK rules}, env.find? (Name.toCL (mkRecName iv.name)) =
          some (.recInfo cvR mI rP isK rules) →
        ∃ (rl : ConLeche.RecRule) (ihs' : List ConLeche.Expr),
          rules.find? (fun r => r.ctor == Name.toCL C) = some rl ∧ rl.nfields = cv.numFields ∧
          ihs'.length + cv.numFields = minorArity rv.type (iv.numParams + 1 + cv.cidx) ∧
          clLams rl.rhs = (rP + cv.numFields, ConLeche.Expr.mkAppN
            (.bvar (cv.numFields + (rP - 1 - (iv.numParams + 1 + cv.cidx))))
            (SemCases.fbv cv.numFields cv.numFields ++ ihs')))
    (hnocert : ∀ {cvR mI rP isK rules} (rl : ConLeche.RecRule),
      env.find? (Name.toCL (mkRecName iv.name)) = some (.recInfo cvR mI rP isK rules) →
        rules.find? (fun r => r.ctor == Name.toCL C) = some rl →
        ConLeche.iotaNoCert env.find? isK (Name.toCL iv.name)
          (ConLeche.recFireLevelCount rl (cv.levelParams.map Name.toCL)) = true) :
    SemCases.CasesIotaAt env (Name.toCL c) (Name.toCL C) (casesArity iv) (casesMajor iv) cv.cidx
      cv.numParams cv.numFields := by
  obtain ⟨ds, hds, hfold, hrc, -⟩ := id h
  have hnd := DeclsOf?.nodup hds
  obtain ⟨ci, hci, hiv⟩ : ∃ ci, casesInfo? P c = some ci ∧
      findDecl P ci.indName = some (.inductInfo iv) := by
    unfold casesOnOf? at hc
    split at hc
    · rename_i ci hci
      split at hc
      · rename_i iv' hiv'; cases hc; exact ⟨ci, hci, hiv'⟩
      · exact nomatch hc
    · exact nomatch hc
  unfold casesInfo? at hci
  split at hci
  rotate_left; · exact nomatch hci
  rename_i T
  split at hci
  rotate_left; · exact nomatch hci
  rename_i d I R hd hI hR
  dsimp only at hci
  split at hci
  rotate_left; · exact nomatch hci
  rename_i j0 body alts before hj hb ha hbe
  split at hci
  rotate_left; · exact nomatch hci
  rename_i hok
  simp only [Option.some.injEq] at hci
  subst hci
  have hII : I = iv := by
    have h' : findConst P T = some (.inductInfo iv) := hiv
    rw [h'] at hI; simpa using hI.symm
  subst I
  have hTn : iv.name = T := (findDecl_mem hiv).2
  subst T
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, hlps⟩, -⟩, hmot⟩, hhd⟩, hlen⟩, -⟩, -⟩, hmin⟩, -⟩, hmaj⟩ := hok
  rw [hone, List.length_singleton] at hmot
  -- the recursor's block is the inductive's
  have hRmem := (findDecl_mem (P := P) hR).1
  have hRname : R.name = mkRecName iv.name := (findDecl_mem (P := P) hR).2
  have hRall : R.all = [iv.name] := by
    obtain ⟨LR, hLR, -⟩ := DeclsOf?.mem hds hRmem
    simp only [declOf?] at hLR
    split at hLR
    · rename_i t ht
      split at hLR
      rotate_left; · exact nomatch hLR
      rename_i htall
      rw [beq_iff_eq] at htall
      obtain ⟨n0, hn0, hft⟩ := Option.bind_eq_some_iff.mp ht
      have hft' : findDecl P n0 = some (.inductInfo t) := hft
      obtain ⟨htmem, -⟩ := findDecl_mem hft'
      obtain ⟨blk, p, hbt, -, -⟩ := h.block hft' (by rw [htall]; exact hn0) (h.ind_safe htmem)
      have hTin : iv.name ∈ R.all := Classical.byContradiction fun hn => by
        rw [← List.idxOf?_eq_none_iff] at hn; rw [hn] at hj; exact nomatch hj
      have hiv' : findConst P iv.name = some (.inductInfo iv) := hiv
      rw [← htall, ← (blockOf?_shape hbt).1 iv.name (htall ▸ hTin) iv hiv', hone]
    · exact nomatch hLR
  rw [hRall] at hj hbe
  simp only [List.idxOf?_cons, beq_self_eq_true, ite_true, Option.some.injEq] at hj
  subst hj
  simp only [List.idxOf_cons_self, List.take_zero, blockCtorCount, Option.some.injEq] at hbe
  subst hbe
  -- the inductive's block
  have hivmem := (findDecl_mem hiv).1
  have hivs := h.ind_safe hivmem
  have hivhead : iv.all.head? = some iv.name := by rw [hone]; rfl
  obtain ⟨blk, p, hbiv, -, -⟩ := h.block hiv hivhead hivs
  obtain ⟨-, hrpar, hone'⟩ := blockOf?_shape hbiv
  obtain ⟨r, hrmem, -, hrname, -, hrmin, hridx⟩ := hone' hone hiv
  have hRr : R = r := by
    have h1 : findDecl P r.name = some (.recInfo r) := findDecl_self hnd hrmem
    have h2 : findDecl P (mkRecName iv.name) = some (.recInfo R) := hR
    rw [hrname, h2] at h1; simpa using h1
  subst r
  have hRpar := hrpar R hRmem (hRall.trans hone.symm)
  -- the stored records
  have hd' : findDecl P (iv.name.str "casesOn") = some (.defnInfo d) := hd
  obtain ⟨cvD, val, hcvD, hval, hfD⟩ := h.find?_defn hd' (hsafe d hd')
  obtain ⟨cvR, rules, f, hcvR, -, hfR⟩ :=
    h.find?_rec hiv hivhead hivs hRmem (hRall.trans hone.symm)
  rw [hRname] at hfR
  obtain ⟨iv', hiv', hCidx, hCpar⟩ := hcl C cv hC
  rw [hCT, hiv, Option.some.injEq, ConstantInfo.inductInfo.injEq] at hiv'
  subst iv'
  obtain ⟨cvj, hcvj, hfC⟩ := (h.find?_single hiv hone hivs).2 (List.mem_of_getElem? hCidx) hC
  have hvcl := (((ConLeche.Semantics.checkDeclsPure_envWF hfold).consts _
    (ConLeche.Env.find?_mem hfD)).2.2.2.2.1 cvD val _ rfl).2.2.2
  have hpis : clPis cvR.type = R.numParams + R.numMotives + R.numMinors + R.numIndices + 1 := by
    have := List.all_eq_true.mp hrc _ (ConLeche.Env.find?_mem hfR)
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact this.1.1.1
  obtain ⟨tyD, -, rfl⟩ := cvOf?_eq_some hcvD
  obtain ⟨tyR, -, rfl⟩ := cvOf?_eq_some hcvR
  obtain ⟨tyj, -, rfl⟩ := cvOf?_eq_some hcvj
  -- the value's reading
  obtain ⟨cb, hcb, hlv⟩ := toCL?_peelLams _ hb hval
  rcases hsp : spine body with ⟨hd0, args⟩
  rw [hsp] at hhd hlen hmin hmaj
  dsimp only at hhd hlen hmin hmaj
  rw [spine_foldl hsp] at hcb
  obtain ⟨chd, rargs, hchd, hall, rfl⟩ := toCL?_foldl args hd0 hcb
  rw [isConstAt_eq hhd] at hchd
  simp only [toCL?, mapM_param, Option.map_eq_map, Option.map_some, Option.some.injEq] at hchd
  subst hchd
  rw [clLams_mkAppN rargs rfl] at hlv
  have hlen' := SemCases.forall₂_length hall
  -- the own minor of `C`
  have hjlt : cv.cidx < iv.ctors.length := (List.getElem?_eq_some_iff.mp hCidx).1
  obtain ⟨hal, haf⟩ := ctorAlts_spec ha
  have hmj := hmin cv.cidx (by omega)
  split at hmj
  rotate_left; · exact nomatch hmj
  rename_i w0 m hw0 hm
  rw [hw0, Option.getD_some] at hm
  rw [haf hCidx hC] at hmj
  obtain ⟨as, rfl, hasl, hasb⟩ := isMinorBody_eq hmj
  obtain ⟨w, hw, hrw⟩ := SemCases.forall₂_getElem? hall hw0
  obtain ⟨cm, hcm, hlw⟩ := toCL?_peelLams _ hm hrw
  obtain ⟨cbv, cas, hcbv, hcas, rfl⟩ := toCL?_foldl as _ hcm
  simp only [toCL?, Option.some.injEq] at hcbv
  subst hcbv
  rw [forall₂_fbv hcas hasl hasb, clLams_mkAppN _ rfl] at hlw
  -- the major
  obtain ⟨cmj, hcmj, hrmj⟩ := SemCases.forall₂_getElem? hall (isBVarAt_eq hmaj)
  simp only [toCL?, Option.some.injEq] at hrmj
  subst hrmj
  -- the rule
  obtain ⟨rl, ihs', hrl, hnf, hihs, hrhs⟩ := hrule R hR hfR
  have hnc := hnocert rl hfR hrl
  simp only [hmot, Nat.add_zero] at hlw hw hihs
  rw [← hihs] at hlw
  refine ⟨_, val, _, _, rargs, _, _, _, _, _, _, _, rl, iv.numParams + 1 + cv.cidx, w, ihs', hfD,
    hvcl, ?_, hfR, by simp [hlps], hpis, by omega, by omega, ?_, by omega, hw, ?_, hfC, hrl, hnf,
    ⟨ihs', rfl, hrhs⟩, hnc⟩
  · rw [hlv, hlps, hRname]; simp [casesArity, casesMajor]
  · rw [hridx, hRpar]; simpa [casesArity, casesMajor] using hcmj
  · rw [hlw, Nat.add_comm ihs'.length cv.numFields]; rfl


/-! ## The former's constructor list -/

/-- The name of a constructor record. Reference: none. -/
def ctorName? : ConLeche.ConstantInfo → Option ConLeche.Name
  | .ctorInfo cv .. => some cv.name
  | _ => none

/-- A tail of recursor records holds no constructor
(`CL ConLeche/Kernel/Inductives/BlockShape.lean:227 blockSplitRecs`). -/
theorem blockSplitRecs_ctors : ∀ {block : List ConLeche.ConstantInfo}
    {rs : List (ConLeche.ConstantVal × Nat × Nat × Bool × List ConLeche.RecRule)},
    ConLeche.blockSplitRecs block = some rs → block.filterMap ctorName? = []
  | [], _, _ => rfl
  | .recInfo .. :: _, _, h => by
    simp only [ConLeche.blockSplitRecs, Option.map_eq_some_iff] at h
    obtain ⟨_, h', -⟩ := h
    simpa [ctorName?] using blockSplitRecs_ctors h'
  | .axiomInfo .. :: _, _, h | .defnInfo .. :: _, _, h | .thmInfo .. :: _, _, h
  | .indInfo .. :: _, _, h | .ctorInfo .. :: _, _, h => nomatch h

/-- The constructors a block's split reads are its constructor records, in order
(`CL ConLeche/Kernel/Inductives/BlockShape.lean:235 blockSplitCtors`). -/
theorem blockSplitCtors_ctors : ∀ {block : List ConLeche.ConstantInfo}
    {cs : List (ConLeche.ConstantVal × Nat × Nat)}
    {rs : List (ConLeche.ConstantVal × Nat × Nat × Bool × List ConLeche.RecRule)},
    ConLeche.blockSplitCtors block = some (cs, rs) → cs.map (·.1.name) = block.filterMap ctorName?
  | .ctorInfo .. :: _, _, _, h => by
    simp only [ConLeche.blockSplitCtors, Option.map_eq_some_iff] at h
    obtain ⟨⟨cs', rs'⟩, h', he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    simp [ctorName?, blockSplitCtors_ctors h']
  | [], _, _, h | .recInfo .. :: _, _, _, h | .axiomInfo .. :: _, _, _, h
  | .defnInfo .. :: _, _, _, h | .thmInfo .. :: _, _, _, h | .indInfo .. :: _, _, _, h => by
    simp only [ConLeche.blockSplitCtors] at h
    obtain ⟨rs', h', he⟩ := Option.map_eq_some_iff.mp h
    cases he
    exact (blockSplitRecs_ctors h').symm

/-- The constructors a block's split reads are its constructor records, in order
(`CL ConLeche/Kernel/Inductives/BlockShape.lean:242 blockSplit`). -/
theorem blockSplit_ctors : ∀ {block : List ConLeche.ConstantInfo} {cvTs : List ConLeche.ConstantVal}
    {cs : List (ConLeche.ConstantVal × Nat × Nat)}
    {rs : List (ConLeche.ConstantVal × Nat × Nat × Bool × List ConLeche.RecRule)},
    ConLeche.blockSplit block = some (cvTs, cs, rs) → cs.map (·.1.name) = block.filterMap ctorName?
  | .indInfo .. :: _, _, _, _, h => by
    simp only [ConLeche.blockSplit, Option.map_eq_some_iff] at h
    obtain ⟨⟨cvTs', cs', rs'⟩, h', he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    simp only [List.filterMap_cons, ctorName?]
    exact blockSplit_ctors h'
  | [], _, _, _, h | .recInfo .. :: _, _, _, _, h | .axiomInfo .. :: _, _, _, _, h
  | .defnInfo .. :: _, _, _, _, h | .thmInfo .. :: _, _, _, _, h | .ctorInfo .. :: _, _, _, _, h => by
    simp only [ConLeche.blockSplit] at h
    obtain ⟨⟨cs', rs'⟩, h', he⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨-, rfl, rfl⟩ := he
    exact blockSplitCtors_ctors h'

/-- The constructor records `blockOf?` writes carry the translated names of the constructors. -/
theorem ctorRecords_names {T : ConLeche.Name} : ∀ {cs : List ConstructorVal}
    {L : List ConLeche.ConstantInfo},
    cs.map (fun c => (cvOf? c.toConstantVal).bind fun cv =>
      some (ConLeche.ConstantInfo.ctorInfo cv c.numParams c.numFields T)) = L.map some →
    L.filterMap ctorName? = cs.map (Name.toCL ·.name)
  | [], [], _ => rfl
  | c :: cs, x :: L, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨hx, hl⟩ := h
    cases hcv : cvOf? c.toConstantVal <;>
      simp only [hcv, Option.bind_none, Option.bind_some, Option.some.injEq, reduceCtorEq] at hx
    obtain ⟨ty, -, rfl⟩ := cvOf?_eq_some hcv
    subst hx
    simp [ctorName?, ctorRecords_names hl]
  | [], _ :: _, h | _ :: _, [], h => by simp at h

/-- The constructors `blockOf?` looks up by name have those names. -/
theorem ctorLookup_names {P : List ConstantInfo} : ∀ {ns : List Name} {cs : List ConstructorVal},
    ns.map (fun n => match findConst P n with
      | some (.ctorInfo c) => some c
      | _ => none) = cs.map some → cs.map (·.name) = ns
  | [], [], _ => rfl
  | n :: ns, c :: cs, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨hc, hl⟩ := h
    split at hc
    · rename_i c' hf
      cases hc
      simp only [List.map_cons, ctorLookup_names hl, List.cons.injEq, and_true]
      exact (findDecl_mem (P := P) hf).2
    · exact nomatch hc
  | [], _ :: _, h | _ :: _, [], h => by simp at h

/-- **The former of a one-member block lists its constructors**: con-leche stores the former of a
safe inductive `H` alone in its block at its translated record, with capabilities whose
constructor list is `H`'s, translated and in order (`CL ConLeche/Kernel/Install.lean:27
blockFormers`, `CL ConLeche/Kernel/Inductives/BlockInstall.lean:71 blockCapsAt`): the position of a
constructor there is its index. Reference: the constructor index
`MR P/PCUICWcbvEval.v:303 eval_construct` reads. -/
theorem _root_.EraseProof.ConLecheAccepts.find?_former {P : List ConstantInfo} {env : ConLeche.Env}
    (h : ConLecheAccepts P env) {n : Name} {H : InductiveVal}
    (hH : findDecl P n = some (.inductInfo H)) (hall : H.all = [n]) (hs : H.isUnsafe = false) :
    ∃ cvH caps, cvOf? H.toConstantVal = some cvH ∧
      env.find? (Name.toCL n) = some (.indInfo cvH caps) ∧ caps.ctors = H.ctors.map Name.toCL := by
  obtain ⟨-, hn⟩ := findDecl_mem hH
  obtain ⟨block, p, hb, hdf, hst⟩ := h.block hH (by rw [hall]; rfl) hs
  have hH' : findConst P H.name = some (.inductInfo H) := by rw [← hn] at hH; exact hH
  have hall' : H.all = [H.name] := by rw [hall, ← hn]; rfl
  simp only [blockOf?, Option.bind_eq_some_iff, Option.some.injEq, bind, pure] at hb
  obtain ⟨tys, htys, cvs, hcvs, -, -, types, htypes, ctors, hctors, recs, hrecs, hbe⟩ := hb
  rw [hall'] at htys
  simp only [List.mapM_cons, List.mapM_nil, hH', Option.bind_eq_bind, Option.bind_some,
    Option.pure_def, Option.some.injEq] at htys
  subst htys
  simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind, Option.pure_def,
    Option.bind_eq_some_iff, Option.some.injEq] at hcvs htypes
  obtain ⟨cs0, hcs0, _, rfl, rfl⟩ := hcvs
  obtain ⟨tH, ⟨cvH, hcvH, rfl⟩, _, rfl, rfl⟩ := htypes
  simp only [List.zip_cons_cons, List.zip_nil_right, List.mapM_cons, List.mapM_nil,
    Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq] at hctors
  obtain ⟨L, hL, _, rfl, rfl⟩ := hctors
  simp only [ConLeche.Declaration.indDecl.injEq, and_true] at hbe
  subst hbe
  obtain ⟨-, -, -, -, -, -, -, cvTs, cs, rs, nIdxs, hsp, hk, -, hnI, -, -, hmem, -⟩ :=
    ConLeche.readBlock_inv hdf
  obtain ⟨-, -, hT⟩ := blockSplit_mem hsp
  obtain rfl := hT rfl fun {cv caps} hx => by
    rcases List.mem_append.mp (by simpa using hx) with hx | hx
    · obtain ⟨c, -, he⟩ := List.mem_map.mp (mapM_eq_some hL ▸ List.mem_map_of_mem (f := some) hx)
      cases hcv : cvOf? c.toConstantVal <;> simp [hcv] at he
    · obtain ⟨r, -, he⟩ := List.mem_map.mp (mapM_eq_some hrecs ▸ List.mem_map_of_mem (f := some) hx)
      obtain ⟨_, _, -, -, he'⟩ := recOf?_eq_some he
      cases he'
  obtain ⟨n0, rfl⟩ : ∃ n0, nIdxs = [n0] := by
    match nIdxs, hnI, hk with
    | [n0], _, _ => exact ⟨n0, rfl⟩
    | [], h1, h2 => simp at h1 h2; omega
    | _ :: _ :: _, h1, h2 => simp at h1 h2; omega
  have hk1 : p.k = 1 := by simpa using hk.symm
  have hm : p.members = [⟨cvH, cvH, n0, cs.map fun c => (c.1, c.2.2)⟩] := by
    rw [hmem, hk1]; simp [ConLeche.blockGroups]
  have hF : ConLeche.ConstantInfo.indInfo cvH (ConLeche.blockCapsAt p 0 (ConLeche.blockIsRec p)) ∈
      ConLeche.blockConstants p :=
    List.mem_append_left _ (List.mem_append_left _ (by simp [ConLeche.blockFormers, hm]))
  have hfF := hst _ hF
  obtain ⟨ty, -, rfl⟩ := cvOf?_eq_some hcvH
  refine ⟨_, _, hcvH, by rw [← hn]; exact hfF, ?_⟩
  have hcs : cs.map (·.1.name) = H.ctors.map Name.toCL := by
    rw [blockSplit_ctors hsp]
    have hrc : recs.filterMap ctorName? = [] := List.filterMap_eq_nil_iff.mpr fun x hx => by
      obtain ⟨r, -, he⟩ := List.mem_map.mp (mapM_eq_some hrecs ▸ List.mem_map_of_mem (f := some) hx)
      obtain ⟨_, _, -, -, rfl⟩ := recOf?_eq_some he
      rfl
    simp only [List.filterMap_cons, ctorName?, List.singleton_append, List.flatten_cons,
      List.flatten_nil, List.append_nil, List.filterMap_append, ctorRecords_names (mapM_eq_some hL),
      hrc, ← ctorLookup_names (mapM_eq_some hcs0), List.map_map]
    rfl
  unfold ConLeche.blockCapsAt
  rw [hm]
  split
  · rename_i c _ heq
    simp only [List.getD_cons_zero] at heq
    obtain ⟨c', rfl⟩ : ∃ c', cs = [c'] := by
      cases cs with
      | nil => simp at heq
      | cons c' cs => cases cs <;> simp_all
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at heq hcs
    rw [← hcs, ← heq]
  · simp only [List.getD_cons_zero, List.map_map] at hcs ⊢
    exact hcs


/-! ## Quotient records -/

/-- **A quotient record of `P` is stored as its pin expects**: con-leche matches the translated
record to the quotient package's pin at its slot (`CL ConLeche/Kernel/Basis.lean:175
quotPinHit`) and stores the pin's constant at the record's level-parameter names
(`CL ConLeche/Kernel/Basis.lean:169 quotAt`, `CL ConLeche/Kernel/Checker.lean:467
checkQuotRecord`), under the translated name. Reference: the quotient constants
`MR P/PCUICWcbvEval.v:231 eval` treats as axioms of the environment. -/
theorem _root_.EraseProof.ConLecheAccepts.find?_quot {P : List ConstantInfo} {env : ConLeche.Env}
    (h : ConLecheAccepts P env) {c : Name} {v : QuotVal}
    (hv : findDecl P c = some (.quotInfo v)) :
    ∃ cv, cvOf? v.toConstantVal = some cv ∧ ConLeche.quotPinHit (quotKindOf v.kind) cv = true ∧
      env.find? (Name.toCL c) = some (ConLeche.quotAt (quotKindOf v.kind) cv) := by
  obtain ⟨hmem, hn⟩ := findDecl_mem hv
  obtain ⟨ds, hds, -⟩ := id h
  obtain ⟨L, hL, -⟩ := DeclsOf?.mem hds hmem
  cases hcv : cvOf? v.toConstantVal with
  | none => simp [declOf?, hcv] at hL
  | some cv =>
  have hd : declOf? P (.quotInfo v) = some [.quotDecl (quotKindOf v.kind) cv] := by
    simp [declOf?, hcv]
  obtain ⟨⟨e, e', hrun⟩, hst⟩ := h.stored hmem hd
  obtain ⟨-, hk⟩ := ConLeche.Semantics.checkDeclRun_ofEnvFactsK hrun
  have hpin : ConLeche.quotPinHit (quotKindOf v.kind) cv = true := hk.1
  have hf := find?_of_single rfl hst
  obtain ⟨ty, -, rfl⟩ := cvOf?_eq_some hcv
  refine ⟨_, rfl, hpin, ?_⟩
  rw [ConLeche.ConstantInfo.name, quotAt_cv hpin] at hf
  rw [← hn]; exact hf

end Decode

end EraseProof
