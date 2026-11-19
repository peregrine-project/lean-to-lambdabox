import EraseProof.Core.StepsApp
import EraseProof.Core.NonRec
import EraseProof.Core.CollectOk
import EraseProof.Semantics.Decode

/-!
# The traversal's environment invariant, from the premises of `erasePure_erases`

`coreEnv_of`: the closure a successful fragment test (`Erasure.collectDeps`) returns, part of a
program con-leche accepts (`ConLecheAccepts`, `SubEnv`), whose declarations have no compiled
pre-definition (`NoPreDefs`), satisfies `Steps.CoreEnv`. Two sources:

* the fragment test's own checks, on each declaration it scans (`Run`): `declExclusion` gives
  `PhaseIDecl` (`Run.phase`) and, on a recursor, the fragment's shape (`Run.rec_frag`);
  `exprConsts` gives closed `NatPlain` expressions (`exprConsts_plain`) whose recursors are
  covered (`Run.read`); `eliminatedUndecided` and the recognized `casesOn` decide the sorts;
* the program's records, which `DeclsOf?` and con-leche check: `blockShapeOK` on every block
  (`blockOf?_member`, `blockOf?_one`), the quotient's pins (`ConLecheAccepts.find?_quot`) and the
  reserved names of `Nat`'s block (`natBlock`, con-leche's `basisNamesOk`).

Adapted from `ML-V Core/CollectSpec.lean:1050-1500` (`Run`) and `ML-V Core/StepsB.lean:367
coreEnv_of_collectDeps`, with con-leche's records where those files have Metalean's environment.
-/

open Lean Erasure

namespace EraseProof

namespace CoreEnvOf

open CollectSub CollectSpec CollectOk Decls Steps

/-! ## What the fragment test scanned -/

/-- A term a successful `exprConsts` scanned has no free variable and, under `nat := .machine`, no
Nat literal and none of the machine-integer constants. Part of
`ML-V Core/CollectSpec.lean:81 exprConsts_ok` and `:161 exprConsts_machineFree`. -/
theorem exprConsts_plain {cfg : ErasureConfig} : ∀ {e : Expr} {cs : List Name},
    exprConsts cfg e = .ok cs → HasFVar e = false ∧ NatPlain cfg e
  | .bvar _, _, _ | .sort _, _, _ => ⟨rfl, trivial⟩
  | .fvar _, _, h | .mvar _, _, h | .lit (.strVal _), _, h => by rw [exprConsts] at h; cases h
  | .lit (.natVal _), _, h => by
    rw [exprConsts] at h
    refine ⟨rfl, ?_⟩
    show cfg.nat = .peano
    cases hn : cfg.nat <;> first | rfl | (rw [hn] at h; cases h)
  | .const c _, _, h => by
    rw [exprConsts] at h
    refine ⟨rfl, fun hm hc => ?_⟩
    split at h
    · cases h
    · rw [hm] at h
      dsimp only at h
      split at h
      · cases h
      · rename_i hn; exact hn (by simpa using hc)
  | .app f a, _, h | .lam _ f a _, _, h | .forallE _ f a _, _, h => by
    rw [exprConsts] at h
    obtain ⟨_, hf, h⟩ := ok_of_bind h
    obtain ⟨_, ha, -⟩ := ok_of_bind h
    obtain ⟨h1, h2⟩ := exprConsts_plain hf
    obtain ⟨h3, h4⟩ := exprConsts_plain ha
    exact ⟨by simp [HasFVar, h1, h3], h2, h4⟩
  | .letE _ t v b _, _, h => by
    rw [exprConsts] at h
    obtain ⟨_, ht, h⟩ := ok_of_bind h
    obtain ⟨_, hv, h⟩ := ok_of_bind h
    obtain ⟨_, hb, -⟩ := ok_of_bind h
    obtain ⟨h1, h2⟩ := exprConsts_plain ht
    obtain ⟨h3, h4⟩ := exprConsts_plain hv
    obtain ⟨h5, h6⟩ := exprConsts_plain hb
    exact ⟨by simp [HasFVar, h1, h3, h5], h2, h4, h6⟩
  | .mdata _ e, _, h => by
    rw [exprConsts] at h
    exact exprConsts_plain (e := e) h
  | .proj _ _ e, _, h => by
    rw [exprConsts] at h
    obtain ⟨_, he, -⟩ := ok_of_bind h
    exact exprConsts_plain (e := e) he

/-- A term with a con-leche form has no free variable (`toCL?` is `none` on `fvar`). -/
theorem toCL?_closed : ∀ {x : Expr} {c : ConLeche.Expr}, toCL? x = some c → HasFVar x = false
  | .bvar _, _, _ | .sort _, _, _ | .const .., _, _ | .lit _, _, _ => rfl
  | .fvar _, _, h | .mvar _, _, h => nomatch h
  | .app f a, _, h | .lam _ f a _, _, h | .forallE _ f a _, _, h => by
    simp only [toCL?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
    obtain ⟨_, hf, _, ha, -⟩ := h
    simp [HasFVar, toCL?_closed hf, toCL?_closed ha]
  | .letE _ t v b _, _, h => by
    simp only [toCL?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
    obtain ⟨_, ht, _, hv, _, hb, -⟩ := h
    simp [HasFVar, toCL?_closed ht, toCL?_closed hv, toCL?_closed hb]
  | .mdata _ e, _, h => toCL?_closed (x := e) h
  | .proj _ _ e, _, h => by
    simp only [toCL?, Option.map_eq_map, Option.map_eq_some_iff] at h
    obtain ⟨_, he, -⟩ := h
    exact toCL?_closed (x := e) he

/-- The sort test on an inductive it accepts reads an arity whose sort is zero, never zero, or
(answering `false`) may be both. Port of `ML-V Core/CollectSpec.lean:872`. -/
theorem sortDecided_ok {iv : InductiveVal} {b : Bool} (h : sortDecided iv = .ok b) :
    ∃ n u, arityShape iv.type = some (n, u) ∧
      (u = .zero ∨ u.isNeverZero = true ∨ (mayBeNonZero iv.levelParams u = true ∧ b = false)) := by
  unfold sortDecided at h
  split at h
  · rename_i n hs; exact ⟨n, .zero, hs, .inl rfl⟩
  · rename_i n u hs _
    refine ⟨n, u, by assumption, ?_⟩
    split at h
    · exact .inr (.inl ‹_›)
    · split at h
      · cases h; exact .inr (.inr ⟨‹_›, rfl⟩)
      · cases h
  · cases h

/-- What `eliminatedUndecided` answering `none` says of an inductive whose sort may be both zero
and not zero: its `casesOn` is not recognized and it has no single constructor with a field. Port
of `ML-V Core/CollectSpec.lean:929`. -/
theorem eliminatedUndecided_none {decls : List ConstantInfo} {cases : List Name}
    (h : eliminatedUndecided decls cases = none) {iv : InductiveVal}
    (hiv : .inductInfo iv ∈ decls) (hb : sortDecided iv = .ok false) :
    ¬ cases.contains (.str iv.name "casesOn") = true ∧
      ∀ cn cv, iv.ctors = [cn] → findDecl decls cn = some (.ctorInfo cv) → ¬ 0 < cv.numFields := by
  rw [eliminatedUndecided, List.findSome?_eq_none_iff] at h
  have h0 := h _ hiv
  dsimp only at h0
  rw [hb] at h0
  refine ⟨fun hc => ?_, fun cn cv hc hf hpos => ?_⟩
  · simp at h0 hc
    exact h0.1 hc
  · rw [hc] at h0
    have hf' : findConst decls cn = some (.ctorInfo cv) := hf
    simp [hf', hpos] at h0

/-- A list of length two is a pair. -/
theorem eq_pair_of_length {α : Type} {l : List α} (h : l.length = 2) : ∃ a b, l = [a, b] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · simp at h
  · simp at h
  · exact ⟨a, b, rfl⟩
  · simp at h <;> omega

/-- A `mapM` in `Option` that answers on every element succeeds. -/
theorem mapM_some_of {α β : Type} {f : α → Option β} :
    ∀ {l : List α}, (∀ a ∈ l, ∃ b, f a = some b) → ∃ l', l.mapM f = some l'
  | [], _ => ⟨[], rfl⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a List.mem_cons_self
    obtain ⟨l', hl⟩ := mapM_some_of (l := l) fun x hx => h x (List.mem_cons_of_mem _ hx)
    exact ⟨b :: l', by simp [List.mapM_cons, hb, hl]⟩

/-! ## What con-leche checked of the program's blocks -/

/-- The block of an inductive `t` of `P`: its head `H` passes `blockOf?`, lists `t`'s block, and
`P` finds `t` under its name. -/
theorem _root_.EraseProof.ConLecheAccepts.member {P : List ConstantInfo} {env : ConLeche.Env}
    (hP : ConLecheAccepts P env) {t : InductiveVal} (ht : .inductInfo t ∈ P) :
    ∃ H d, blockOf? P H = some d ∧ H.all = t.all ∧ t.name ∈ H.all ∧
      findConst P t.name = some (.inductInfo t) := by
  obtain ⟨ds, hds, -⟩ := id hP
  obtain ⟨Hn, H, hH, hhead, hall, hmem⟩ := hP.head ht
  obtain ⟨block, p, hblk, -, -⟩ := hP.block hH hhead (hP.ind_safe (findDecl_mem hH).1)
  exact ⟨H, _, hblk, hall, hmem, findDecl_self (DeclsOf?.nodup hds) ht⟩

/-- What `blockOf?` checks of a member `t` of the block headed by `H` (`blockShapeOK`): `t` lists
the block and has its parameter count, and each constructor of `t`, as `P` finds it, has `t` as
its inductive, its position as its index, the block's parameter count, and a type of `Π`s over the
parameters and the fields whose result is headed by `t`. -/
theorem blockOf?_member {P : List ConstantInfo} {H : InductiveVal} {d : ConLeche.Declaration}
    (h : blockOf? P H = some d) {n : Name} (hn : n ∈ H.all) {t : InductiveVal}
    (ht : findConst P n = some (.inductInfo t)) :
    t.all = H.all ∧ t.numParams = H.numParams ∧
      ∀ j cn, t.ctors[j]? = some cn → ∀ c, findConst P cn = some (.ctorInfo c) →
        c.induct = t.name ∧ c.cidx = j ∧ c.numParams = H.numParams ∧
        piLen c.type = H.numParams + c.numFields ∧
        appHeadConst (piResult (H.numParams + c.numFields) c.type) = some t.name := by
  simp only [blockOf?, Option.bind_eq_some_iff, Option.some.injEq, bind, pure] at h
  obtain ⟨tys, htys, cvs, hcvs, _, hg, -⟩ := h
  simp only [guard] at hg
  split at hg
  rotate_left; · exact nomatch hg
  rename_i hok
  have htm : t ∈ tys := by
    have := mapM_eq_some htys ▸ List.mem_map_of_mem (f := fun n => match findConst P n with
      | some (.inductInfo t) => some t
      | _ => none) hn
    simp only [ht] at this
    obtain ⟨t', ht', he⟩ := List.mem_map.mp this
    cases he; exact ht'
  unfold blockShapeOK at hok
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨-, ht⟩, hz⟩, -⟩, -⟩, -⟩, -⟩ := hok
  obtain ⟨⟨hta, htp⟩, -⟩ := ht t htm
  refine ⟨hta, htp, fun j cn hj c hc => ?_⟩
  obtain ⟨cs, hcs', hzm⟩ : ∃ cs, t.ctors.mapM (fun n => match findConst P n with
      | some (.ctorInfo c) => some c
      | _ => none) = some cs ∧ (t, cs) ∈ tys.zip cvs := by
    have hm₂ := mapM_eq_some hcvs ▸ List.mem_map_of_mem (f := fun (t : InductiveVal) =>
      t.ctors.mapM fun n => match findConst P n with
        | some (.ctorInfo c) => some c
        | _ => none) htm
    obtain ⟨cs, -, he₂⟩ := List.mem_map.mp hm₂
    exact ⟨cs, he₂.symm, mem_zip_of_mapM (mapM_eq_some hcvs) htm he₂.symm⟩
  have hcsj : cs[j]? = some c := by
    have h1 := congrArg (·[j]?) (mapM_eq_some hcs')
    simp only [List.getElem?_map, hj, Option.map_some, hc] at h1
    cases hcj : cs[j]? with
    | none => rw [hcj] at h1; simp at h1
    | some c' => rw [hcj] at h1; simpa using h1.symm
  have hcj := hz (t, cs) hzm (c, j) (List.mem_zipIdx_iff_getElem?.mpr (by simpa using hcsj))
  simp only at hcj
  obtain ⟨⟨⟨⟨hind, hcidx⟩, hnp⟩, hpl⟩, hhd⟩ := hcj
  exact ⟨hind, hcidx, hnp, hpl, hhd⟩

/-- What `blockOf?` checks of the recursors of a block of one type `H`: there is exactly one,
named `H.rec`, with one minor premise per constructor of `H`. -/
theorem blockOf?_one {P : List ConstantInfo} {H : InductiveVal} {d : ConLeche.Declaration}
    (h : blockOf? P H = some d) (hall : H.all = [H.name])
    (hH : findConst P H.name = some (.inductInfo H)) {r : RecursorVal} (hr : .recInfo r ∈ P)
    (hra : r.all = H.all) : r.name = mkRecName H.name ∧ r.numMinors = H.ctors.length := by
  simp only [blockOf?, Option.bind_eq_some_iff, Option.some.injEq, bind, pure] at h
  obtain ⟨tys, htys, cvs, hcvs, _, hg, -⟩ := h
  simp only [guard] at hg
  split at hg
  rotate_left; · exact nomatch hg
  rename_i hok
  rw [hall] at htys
  simp only [List.mapM_cons, List.mapM_nil, hH, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def, Option.some.injEq] at htys
  subst htys
  simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at hcvs
  obtain ⟨cs, hcs, _, rfl, rfl⟩ := hcvs
  have hlen : H.ctors.length = cs.length := by
    simpa using congrArg List.length (mapM_eq_some hcs)
  unfold blockShapeOK at hok
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq,
    List.mem_singleton, forall_eq, List.length_singleton] at hok
  obtain ⟨⟨-, hrl⟩, r', hr'm, ⟨⟨⟨⟨⟨hn, -⟩, -⟩, hmin⟩, -⟩, -⟩⟩ := hok
  have hrm : r ∈ P.reverse.filterMap (fun
      | .recInfo r => if r.all = H.all then some r else none
      | _ => none) := List.mem_filterMap.mpr ⟨_, List.mem_reverse.mpr hr, by simp [hra]⟩
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hrl
  have h1 : r ∈ [x] := by rw [← hx]; exact hrm
  have h2 : r' ∈ [x] := by rw [← hx]; exact hr'm
  rw [List.mem_singleton] at h1 h2
  subst h1 h2
  exact ⟨hn, by simpa [← hlen] using hmin⟩

/-- A recursor of `P` of a block of one type `T` is `T.rec`, with one minor premise per
constructor of `T` (`blockShapeOK` of the block `declOf?` puts it in). -/
theorem _root_.EraseProof.ConLecheAccepts.rec_one {P : List ConstantInfo} {env : ConLeche.Env}
    (hP : ConLecheAccepts P env) {R : RecursorVal} (hR : .recInfo R ∈ P) {T : Name}
    (hRall : R.all = [T]) :
    ∃ t, findConst P T = some (.inductInfo t) ∧ R.name = mkRecName T ∧
      R.numMinors = t.ctors.length := by
  obtain ⟨ds, hds, -⟩ := id hP
  obtain ⟨L, hL, -⟩ := DeclsOf?.mem hds hR
  simp only [declOf?, hRall, List.head?_cons, Option.bind_some] at hL
  split at hL
  · rename_i t ht
    have htall : t.all = [T] := by
      by_cases hne : t.all = [T]
      · exact hne
      · simp [hne] at hL
    have htm := (findDecl_mem (c := T) ht).1
    have htn : t.name = T := (findDecl_mem (c := T) ht).2
    have hhead : t.all.head? = some T := by rw [htall]; rfl
    obtain ⟨block, p, hblk, -, -⟩ := hP.block ht hhead (hP.ind_safe htm)
    have ht' : findConst P t.name = some (.inductInfo t) := by rw [htn]; exact ht
    obtain ⟨h1, h2⟩ := blockOf?_one hblk (by rw [htall, htn]) ht' hR (by rw [hRall, htall])
    exact ⟨t, ht, by rw [h1, htn], h2⟩
  · cases hL

/-! ## A run of the fragment test -/

/-- A run of the fragment test whose closure is part of a program con-leche accepts: the closure's
declarations are the view's, each scanned with its read names covered, and the closure is closed
under what the traversal reads (`DepClosed`). Adapted from `ML-V Core/CollectSpec.lean:1050`. -/
structure Run (P : List ConstantInfo) (env : ConLeche.Env) (view : EnvView) (cfg : ErasureConfig)
    (decls : List ConstantInfo) (cases : List Name) : Prop where
  acc : ConLecheAccepts P env
  sub : SubEnv decls P
  vw : ∀ y ∈ decls, view.find? y.name = some y
  scan : ∀ ci ∈ decls, Scanned view cfg (Covered view cfg decls) decls cases ci
  dep : DepClosed decls

namespace Run

variable {P : List ConstantInfo} {env : ConLeche.Env} {view : EnvView} {cfg : ErasureConfig}
  {decls : List ConstantInfo} {cases : List Name} (hr : Run P env view cfg decls cases)
include hr

/-- A declaration of the closure is the first of its name. Port of
`ML-V Core/CollectSpec.lean:1064`. -/
theorem fd {y : ConstantInfo} (hy : y ∈ decls) : findDecl decls y.name = some y := by
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 (findDecl_isSome_iff.2 (List.mem_map_of_mem hy))
  obtain ⟨hz1, hz2⟩ := findDecl_eq_some hz
  have e := hr.sub z hz1
  rw [hz2, hr.sub y hy] at e
  cases e; exact hz

/-- A declaration of the closure that is not a recursor was scanned by `closureStep`. Port of
`ML-V Core/CollectSpec.lean:1082`. -/
theorem scanned {ci : ConstantInfo} (hci : ci ∈ decls) (hnr : ∀ R, ci ≠ .recInfo R) :
    ∃ ns ro, closureStep view cfg ci = .ok (ns, ro) ∧ (∀ n ∈ ns, Covered view cfg decls n) ∧
      (∀ r, ro = some r → r ∈ decls) ∧
      (∀ r d, ro = some r → ci = .defnInfo d → ci.name ∈ cases) := by
  rcases hr.scan ci hci with h | ⟨R, rfl, -⟩
  · exact h
  · exact absurd rfl (hnr R)

/-- A `casesOn` of the closure that the view recognizes is recognized on the closure: its
inductive is read, its recursor is its companion, and `casesInfo?` answers on the closure as on the
view's declarations (`recog_cases`). Part of `ML-V Core/CollectSpec.lean:1125 Run.recog_ds`. -/
theorem recog_ds {d : DefinitionVal} (hd : .defnInfo d ∈ decls) {I : InductiveVal}
    {R : RecursorVal} {ctors : List ConstantInfo}
    (hrec : recognizeCasesOn view (.defnInfo d) = some (I, R, ctors)) :
    (casesOnOf? decls d.name).isSome := by
  obtain ⟨ns, ro, hcs, hns, hro, -⟩ := hr.scanned hd nofun
  rcases (closureStep_spec hcs).2.2.1 d rfl with ⟨hnone, -⟩ |
    ⟨I', R', ctors', hrec', hIns, hro'⟩
  · rw [hnone] at hrec; cases hrec
  rw [hrec] at hrec'
  simp only [Option.some.injEq, Prod.mk.injEq] at hrec'
  obtain ⟨rfl, rfl, rfl⟩ := hrec'
  have hRd := hro _ hro'
  obtain ⟨T, -, hI, -⟩ := recognize_spec hrec
  obtain ⟨hIf, hIn⟩ := viewFind_eq hI
  have hId : .inductInfo I ∈ decls :=
    mem_of_view hr.vw (hns _ hIns).mem (by rw [← hIn] at hIf; exact hIf)
  exact recog_cases hr.vw hd hrec fun x hx => by
    rcases hx with rfl | rfl | hx | hx
    · exact (hns _ hIns).mem
    · exact List.mem_map_of_mem (f := ConstantInfo.name) hRd
    · exact findDecl_isSome_iff.1 ((hr.dep _ hId).2.2.1 I rfl x hx)
    · exact findDecl_isSome_iff.1 ((hr.dep _ hRd).2.2.2.2 R rfl x hx)

/-- Every expression the traversal reads from the closure was scanned, its names covered. Port of
`ML-V Core/CollectSpec.lean:1171`. -/
theorem read {ci : ConstantInfo} (hci : ci ∈ decls) {x : Expr} (hx : ReadExpr decls ci x) :
    ∃ xs, exprConsts cfg x = .ok xs ∧ ∀ n ∈ xs, Covered view cfg decls n := by
  rcases hr.scan ci hci with ⟨ns, ro, hcs, hns, -, -⟩ | ⟨R, rfl, ⟨tys, htys, htc⟩, -⟩
  · have spec := closureStep_spec hcs
    rcases hx with rfl | ⟨d, rfl, rfl, hnone⟩ | ⟨o, rfl, rfl⟩
    · obtain ⟨ty, hty, hsub⟩ := spec.1
      exact ⟨ty, hty, fun n hn => hns n (hsub n hn)⟩
    · rcases spec.2.2.1 d rfl with ⟨-, vs, hvs, hsub⟩ | ⟨I, R, ctors, hrec, -⟩
      · exact ⟨vs, hvs, fun n hn => hns n (hsub n hn)⟩
      · have hc := hr.recog_ds hci hrec
        rw [Option.isNone_iff_eq_none] at hnone
        rw [hnone] at hc
        cases hc
    · obtain ⟨vs, hvs, hsub⟩ := spec.2.2.2.1 o rfl
      exact ⟨vs, hvs, fun n hn => hns n (hsub n hn)⟩
  · rcases hx with rfl | ⟨d, h, -⟩ | ⟨o, h, -⟩
    · exact ⟨tys, htys, htc⟩
    · cases h
    · cases h

/-- A recursor of the closure that `declExclusion` accepts has the fragment's shape over the
closure (`RecInFragment`): the block that `declExclusion` reads through the view is the closure's,
and the recursor is its type's `T.rec` (`ConLecheAccepts.rec_one`). Port of
`ML-V Core/CollectSpec.lean:1269`. -/
theorem rec_frag {R : RecursorVal} (hR : .recInfo R ∈ decls)
    (hd : declExclusion view cfg (.recInfo R) = .ok ()) : RecInFragment cfg decls R := by
  obtain ⟨hsc, hsh⟩ := (declExclusion_flags hd).1 R rfl
  have hsh' := hsh
  unfold recShapeInFragment at hsh'
  split at hsh'
  next T iv hRall hivs =>
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1
      ((hr.dep _ hR).2.2.2.2 R rfl T (by rw [hRall]; exact List.mem_singleton_self T))
    obtain ⟨hy1, hy2⟩ := findDecl_eq_some hy
    have hv : viewFind view T = [y] := viewFind_of (hy2 ▸ hr.vw y hy1) hy2
    have hI : recViewIvs view R = [iv] := hivs
    have hI' := hI
    rw [recViewIvs, hRall, List.flatMap_singleton, hv] at hI'
    cases y with
    | inductInfo I =>
      simp only [List.filterMap_cons, List.filterMap_nil, List.cons.injEq, and_true] at hI'
      subst hI'
      have hcv : ∀ n ∈ I.ctors, ∃ cv, findDecl decls n = some (.ctorInfo cv) := by
        intro n hn
        obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 ((hr.dep _ hy1).2.2.1 I rfl n hn)
        obtain ⟨c, hc⟩ := (ind_kinds hr.acc (findDecl_mem (hr.sub _ hy1)).1).2 n hn
        obtain ⟨hz1, hz2⟩ := findDecl_eq_some hz
        have e := hr.sub z hz1
        rw [hz2, hc] at e
        cases e
        exact ⟨c, hz⟩
      obtain ⟨cvs, hcvs⟩ := mapM_some_of (l := I.ctors) (f := fun c => match findDecl decls c with
        | some (.ctorInfo cv) => some cv
        | _ => none) fun n hn => by
          obtain ⟨cv, hcv⟩ := hcv n hn; exact ⟨cv, by rw [hcv]⟩
      have hvc : recViewCvs view [I] = cvs := by
        unfold recViewCvs
        rw [List.flatMap_singleton]
        exact viewCtors_of_mapM hr.vw (fun c cv h => by split at h <;> simp_all) hcvs
      obtain ⟨t, ht, hRn, -⟩ := ConLecheAccepts.rec_one hr.acc (findDecl_mem (hr.sub _ hR)).1 hRall
      refine ⟨T, I, cvs, hRn, hRall, ?_, ?_, ?_⟩
      · unfold recBlockOf?
        rw [hRall]
        simp only [List.mapM_cons, List.mapM_nil, hy, Option.bind_eq_bind, Option.bind_some,
          Option.pure_def, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        exact Option.bind_eq_some_iff.2 ⟨cvs, hcvs, rfl⟩
      · rw [← hvc, ← hI]; exact hsh
      · rw [← hvc, ← hI]; exact hsc
    | _ => simp at hI'
  next => cases hsh'

/-- A `casesOn` recognized on the closure is recognized by the view. Port of
`ML-V Core/CollectSpec.lean:1164`. -/
theorem recog_view {d : DefinitionVal} (hd : .defnInfo d ∈ decls) {iv : InductiveVal}
    (hcs : casesOnOf? decls d.name = some iv) :
    ∃ I R ctors, recognizeCasesOn view (.defnInfo d) = some (I, R, ctors) :=
  recog_of_dec_of hr.vw (fun I hI => (hr.dep _ hI).2.2.1 I rfl)
    (fun R hR => (hr.dep _ hR).2.2.2.2 R rfl) hd hcs

/-- Every declaration of the closure is inside the first-phase fragment: `declExclusion` checked a
scanned declaration (on a recursor, `rec_frag`), the sort test and `eliminatedUndecided` an
inductive's sort, `closureStep` the fields of a recognized `casesOn`'s constructors; a companion
recursor is the `T.rec` of a recognized `T.casesOn` or of an inductive with one constructor. Port
of `ML-V Core/CollectSpec.lean:1328`. -/
theorem phase (hel : eliminatedUndecided decls cases = none) {ci : ConstantInfo}
    (hci : ci ∈ decls) : PhaseIDecl view cfg decls ci := by
  rcases hr.scan ci hci with ⟨ns, ro, hcs, -, -, -⟩ | ⟨R, rfl, -, cj, hcj, ns, hcs⟩
  · obtain ⟨hdex, -, -⟩ := closureStep_extra hcs
    have dex := declExclusion_flags hdex
    cases ci with
    | recInfo r => exact .inr (.inr (hr.rec_frag hci hdex))
    | inductInfo iv =>
      obtain ⟨hu, hnn, b, hb⟩ := dex.2.1 iv rfl
      obtain ⟨n, u, hsh, hu'⟩ := sortDecided_ok hb
      -- a `casesOn` of `iv` recognized on the closure was recognized by the view
      have hrecog : (casesOnOf? decls (.str iv.name "casesOn")).isSome →
          ∃ d R, .defnInfo d ∈ decls ∧ d.name = .str iv.name "casesOn" ∧
            recognizeCasesOn view (.defnInfo d) =
              some (iv, R, iv.ctors.flatMap (viewFind view)) := by
        intro hc
        obtain ⟨iv', hiv'⟩ := Option.isSome_iff_exists.1 hc
        obtain ⟨c, hc'⟩ := casesInfo?_of hiv'
        obtain ⟨-, d, -, -, -, -, -, -, -, hd, -⟩ := casesInfo?_reads hc'
        obtain ⟨hd1, hd2⟩ := findDecl_eq_some hd
        obtain ⟨I, R, ctors, hrec⟩ :=
          hr.recog_view hd1 (by rw [show d.name = _ from hd2]; exact hiv')
        obtain ⟨T, hT, hI, -, hct, -⟩ := recognize_iff.1 hrec
        have hTT : T = iv.name := by
          have h2 : Name.str T "casesOn" = Name.str iv.name "casesOn" := hT.symm.trans hd2
          rw [Name.str.injEq] at h2; exact h2.1
        subst hTT
        obtain ⟨hIf, -⟩ := viewFind_eq hI
        have hv : view.find? iv.name = some (.inductInfo iv) := hr.vw _ hci
        rw [hv] at hIf
        cases hIf
        exact ⟨d, R, hd1, hd2, hct ▸ hrec⟩
      refine ⟨hu, hnn, ⟨n, u, hsh, ?_⟩, fun hcase cn hcn cv hcv => ?_⟩
      · rcases hu' with h | h | ⟨hm, rfl⟩
        · exact .inl h
        · exact .inr (.inl h)
        · refine .inr (.inr ⟨hm, fun hel' => ?_⟩)
          obtain ⟨hno1, hno2⟩ := eliminatedUndecided_none hel hci hb
          rcases hel' with hc | ⟨cn, cv, hcs1, hcv1, hnf⟩
          · obtain ⟨d, R, hd, hdn, hrec⟩ := hrecog hc
            obtain ⟨ns', ro', hcs', -, -, hcas'⟩ := hr.scanned hd nofun
            rcases (closureStep_spec hcs').2.2.1 d rfl with ⟨hnone, -⟩ |
              ⟨I', R', ctors', -, -, hro'⟩
            · rw [hnone] at hrec; cases hrec
            · have hmem := hcas' _ d hro' rfl
              rw [show (ConstantInfo.defnInfo d).name = d.name from rfl, hdn] at hmem
              exact hno1 (by simp [hmem])
          · exact hno2 cn cv hcs1 hcv1 hnf
      · obtain ⟨d, R, hd, -, hrec⟩ := hrecog hcase
        obtain ⟨ns', ro', hcs', -⟩ := hr.scanned hd nofun
        obtain ⟨hcvd, hcvn⟩ := findDecl_eq_some hcv
        exact (closureStep_extra hcs').2.1 d iv R _ rfl hrec cv (List.mem_flatMap.2 ⟨cn, hcn, by
          rw [viewFind_of (hcvn ▸ hr.vw _ hcvd) hcvn]; exact List.mem_singleton_self _⟩)
    | defnInfo _ | opaqueInfo _ | axiomInfo _ | thmInfo _ | quotInfo _ | ctorInfo _ =>
      exact dex.2.2 decls nofun nofun
  · obtain ⟨-, -, hkind⟩ := closureStep_extra hcs
    rcases hkind _ rfl with ⟨d, I, R', ctors, rfl, hrec, hRR⟩ | ⟨iv, rfl, hlen, hvf⟩
    · cases hRR
      obtain ⟨T, hT, -, hRv, -⟩ := recognize_spec hrec
      obtain ⟨-, hRn⟩ := viewFind_eq hRv
      obtain ⟨iv', hiv'⟩ := Option.isSome_iff_exists.1 (hr.recog_ds hcj hrec)
      have hT' : d.name = .str T "casesOn" := hT
      refine .inl ⟨T, iv', hRn, hT' ▸ hiv', ?_⟩
      rw [← hT']
      show (findDecl decls (ConstantInfo.defnInfo d).name).isSome
      rw [hr.fd hcj]; rfl
    · obtain ⟨-, hRn⟩ := viewFind_eq hvf
      exact .inr (.inl ⟨iv.name, iv, hRn, hr.fd hcj, hlen⟩)

end Run

/-! ## The pins of the program's quotient and `Nat` -/

/-- A type with a con-leche form whose `Π`-body is a sort is a syntactic arity, with as many binders
and the sort read back. -/
theorem arityShape_of_toCL : ∀ {x : Expr} {c : ConLeche.Expr} {l : ConLeche.Level},
    toCL? x = some c → (clPiBody c).2 = .sort l →
      ∃ u, arityShape x = some ((clPiBody c).1, u) ∧ Level.toCL u = some l
  | .sort u, c, l, h, hb => by
    simp only [toCL?, Functor.map, Option.map_eq_some_iff] at h
    obtain ⟨l', hl', rfl⟩ := h
    simp only [clPiBody, ConLeche.Expr.sort.injEq] at hb
    subst hb
    exact ⟨u, rfl, hl'⟩
  | .forallE _ t b _, c, l, h, hb => by
    simp only [toCL?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨_, -, cb, hcb, rfl⟩ := h
    simp only [clPiBody] at hb ⊢
    obtain ⟨u, hu, hl⟩ := arityShape_of_toCL hcb hb
    exact ⟨u, by simp [arityShape, hu], hl⟩
  | .mdata _ e, c, l, h, hb => by
    obtain ⟨u, hu, hl⟩ := arityShape_of_toCL (x := e) h hb
    exact ⟨u, by simp [arityShape, hu], hl⟩
  | .bvar _, c, l, h, hb | .lit (.natVal _), c, l, h, hb | .lit (.strVal _), c, l, h, hb => by
    simp only [toCL?, Option.some.injEq] at h; subst h; simp [clPiBody] at hb
  | .const .., c, l, h, hb | .proj .., c, l, h, hb => by
    simp only [toCL?, Functor.map, Option.map_eq_some_iff] at h
    obtain ⟨_, -, rfl⟩ := h; simp [clPiBody] at hb
  | .app .., c, l, h, hb | .lam .., c, l, h, hb => by
    simp only [toCL?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨_, -, _, -, rfl⟩ := h; simp [clPiBody] at hb
  | .letE .., c, l, h, hb => by
    simp only [toCL?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨_, -, _, -, _, -, rfl⟩ := h; simp [clPiBody] at hb
  | .fvar _, _, _, h, _ | .mvar _, _, _, h, _ => nomatch h

/-- The quotient's records are its pins (`quotPinHit`): the type of the `.type` record is an arity
(`Quot.{u} {α : Sort u} (r : α → α → Prop) : Sort u`), and the `.ind` record is ``Quot.ind``. -/
theorem _root_.EraseProof.ConLecheAccepts.quot_pins {P : List ConstantInfo} {env : ConLeche.Env}
    (hP : ConLecheAccepts P env) {c : Name} {q : QuotVal} (hq : findDecl P c = some (.quotInfo q)) :
    (q.kind = .type → (arityShape q.type).isSome) ∧ (q.kind = .ind → c = ``Quot.ind) := by
  obtain ⟨cv, hcv, hpin, -⟩ := hP.find?_quot hq
  obtain ⟨ty, hty, rfl⟩ := cvOf?_eq_some hcv
  obtain ⟨-, hn⟩ := findDecl_mem hq
  simp only [ConLeche.quotPinHit, Bool.and_eq_true] at hpin
  have heq := ConLeche.ConstantVal.eq_of_beqP hpin.2
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · rw [hk] at heq
    have h1 := congrArg ConLeche.ConstantVal.type heq
    simp only [quotKindOf, ConLeche.quotPin, ConLeche.BasisKind.decls, ConLeche.quotBasis,
      ConLeche.QuotKind.slot, ConLeche.quotA, List.getD, List.getElem?_cons_zero, Option.getD_some,
      ConLeche.ConstantInfo.toConstantVal, ConLeche.ConstantVal.atLps,
      ConLeche.Expr.instantiateLevelParams, ConLeche.BasisDSL.piI, ConLeche.BasisDSL.pi,
      ConLeche.BasisDSL.srt] at h1
    obtain ⟨u, hu, -⟩ := arityShape_of_toCL hty (by rw [h1]; rfl)
    rw [hu]; rfl
  · rw [hk] at heq
    have h1 := congrArg ConLeche.ConstantVal.name heq
    simp only [quotKindOf, ConLeche.quotPin, ConLeche.BasisKind.decls, ConLeche.quotBasis,
      ConLeche.QuotKind.slot, ConLeche.quotIndA, List.getD, ConLeche.ConstantInfo.toConstantVal,
      ConLeche.ConstantVal.atLps] at h1
    rw [← hn]
    exact Name.toCL_injective (h1.trans rfl)

/-- The kind of a con-leche constant: a former, a constructor, a recursor, or another. -/
def kindOf : ConLeche.ConstantInfo → Nat
  | .indInfo .. => 0
  | .ctorInfo .. => 1
  | .recInfo .. => 2
  | _ => 3

/-- A record that matches a pin is of the pin's kind. -/
theorem kindOf_pin {b p : ConLeche.ConstantInfo} (h : ConLeche.pinCopyOk b p = true) :
    kindOf b = kindOf p := by
  cases b <;> cases p <;>
    simp_all [ConLeche.pinCopyOk, ConLeche.pinAgrees, ConLeche.ConstantInfo.atLps,
      ConLeche.ConstantInfo.beqP, kindOf]

/-- Two lists that `listBeqBy` relates by a relation that keeps a function have one image. -/
theorem map_of_listBeqBy {α : Type} {f : α → α → Bool} {g : α → Nat}
    (hg : ∀ a b, f a b = true → g a = g b) :
    ∀ {l l' : List α}, ConLeche.listBeqBy f l l' = true → l.map g = l'.map g
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [ConLeche.listBeqBy, Bool.and_eq_true] at h
    simp [hg a b h.1, map_of_listBeqBy hg h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [ConLeche.listBeqBy] at h

/-- A list whose images are all one value has that value counted once per element. -/
theorem count_map_const {α : Type} {g : α → Nat} {k : Nat} {l : List α} (h : ∀ x ∈ l, g x = k) :
    ∀ j, (l.map g).count j = if k = j then l.length else 0 := by
  intro j
  split
  · rename_i hk; subst hk
    rw [List.count_eq_length.2 fun y hy => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy; exact (h x hx).symm, List.length_map]
  · rename_i hk
    exact List.count_eq_zero.2 fun hy => by
      obtain ⟨x, hx, he⟩ := List.mem_map.1 hy; exact hk (h x hx ▸ he)

/-- **`Nat`'s block is con-leche's pin** (`basisNamesOk`: a block that holds `Nat`, `Nat.zero` or
`Nat.succ` has the names of the pinned `Nat` block, and its records are the pins up to their
level-parameter names, `CL ConLeche/Kernel/Basis/Nat.lean:68 natBasis`): an inductive of `P` named
`Nat` or listing `Nat.zero` or `Nat.succ` is `Nat`, without parameters, of type `Type`, with the
constructors `Nat.zero`, without a field, and `Nat.succ`, with one, in that order. -/
theorem _root_.EraseProof.ConLecheAccepts.natBlock {P : List ConstantInfo} {env : ConLeche.Env}
    (hP : ConLecheAccepts P env) {t : InductiveVal} (ht : .inductInfo t ∈ P)
    (hres : t.name = ``Nat ∨ ``Nat.zero ∈ t.ctors ∨ ``Nat.succ ∈ t.ctors) :
    t.name = ``Nat ∧ t.numParams = 0 ∧ t.ctors = [``Nat.zero, ``Nat.succ] ∧
      arityShape t.type = some (0, .succ .zero) ∧
      (∃ c, findConst P ``Nat.zero = some (.ctorInfo c) ∧ c.numFields = 0) ∧
      ∃ c, findConst P ``Nat.succ = some (.ctorInfo c) ∧ c.numFields = 1 := by
  obtain ⟨ds, hds, -⟩ := id hP
  have hnd := DeclsOf?.nodup hds
  obtain ⟨Hn, H, hH, hhead, hall, hmem⟩ := hP.head ht
  obtain ⟨hHm, hHn⟩ := findDecl_mem hH
  have hHn' : H.name = Hn := hHn
  subst hHn'
  have hs := hP.ind_safe hHm
  obtain ⟨block, p, hb, -, -⟩ := hP.block hH hhead hs
  have hd : declOf? P (.inductInfo H) = some [.indDecl block H.numParams] := by
    simp [declOf?, hs, hhead, hb]
  obtain ⟨⟨e, e', hrun⟩, -⟩ := hP.stored hHm hd
  have hbn := (ConLeche.Semantics.checkDeclRun_ofEnvFactsK hrun).1
  have htt : findConst P t.name = some (.inductInfo t) := findDecl_self hnd ht
  -- a record of the block has a name of `Nat`'s block
  obtain ⟨block', hbe, -, hspec⟩ := blockOf?_spec hb
  cases hbe
  have hnamed : ∃ b ∈ block, b.name = ConLeche.natName ∨ b.name = ConLeche.natZeroName ∨
      b.name = ConLeche.natSuccName := by
    obtain ⟨t', ht', ⟨cv, hcv, hcvb⟩, hct⟩ := hspec t.name hmem
    rw [htt] at ht'
    cases ht'
    rcases hres with hn | hc | hc
    · obtain ⟨ty, -, rfl⟩ := cvOf?_eq_some hcv
      exact ⟨_, hcvb, .inl (by rw [hn]; rfl)⟩
    · obtain ⟨c, hc', cv, hcv, hcb⟩ := hct _ hc
      obtain ⟨ty, -, rfl⟩ := cvOf?_eq_some hcv
      have hcn : c.name = ``Nat.zero := (findDecl_mem hc').2
      exact ⟨_, hcb, .inr (.inl (by show Name.toCL c.name = _; rw [hcn]; rfl))⟩
    · obtain ⟨c, hc', cv, hcv, hcb⟩ := hct _ hc
      obtain ⟨ty, -, rfl⟩ := cvOf?_eq_some hcv
      have hcn : c.name = ``Nat.succ := (findDecl_mem hc').2
      exact ⟨_, hcb, .inr (.inr (by show Name.toCL c.name = _; rw [hcn]; rfl))⟩
  -- so the block is checked against `Nat`'s pin
  have hk : ConLeche.basisNameHit block = some .natK := by
    obtain ⟨b, hbm, hbn'⟩ := hnamed
    cases hh : ConLeche.basisNameHit block with
    | none =>
      simp only [ConLeche.basisNamesOk, hh] at hbn
      have := List.all_eq_true.1 hbn b hbm
      rcases hbn' with h | h | h <;> rw [h] at this <;> exact absurd this (by decide)
    | some k =>
      have hfind := List.find?_some hh
      have hkm := List.mem_of_find?_eq_some hh
      have hbm' : b.name ∈ k.decls.map (·.name) := by
        rw [beq_iff_eq.1 hfind]; exact List.mem_map_of_mem hbm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hkm
      rcases hkm with rfl | rfl | rfl | rfl <;>
        rcases hbn' with h | h | h <;> rw [h] at hbm' <;>
          first | rfl | exact absurd hbm' (by decide)
  simp only [ConLeche.basisNamesOk, hk, ConLeche.BasisKind.decls, ConLeche.pinListOk,
    Bool.and_eq_true] at hbn
  have hkinds := map_of_listBeqBy (g := kindOf) (fun _ _ h => kindOf_pin h) hbn.1
  -- the block's records: the formers, the constructors, the recursors
  have hb0 := hb
  simp only [blockOf?, Option.bind_eq_some_iff, Option.some.injEq, bind, pure] at hb
  obtain ⟨tys, htys, cvs, hcvs, _, -, types, htypes, ctors, hctors, recs, hrecs, hbe⟩ := hb
  injection hbe with hbe
  subst hbe
  have k0 : ∀ x ∈ types, kindOf x = 0 := fun x hx => by
    obtain ⟨t', -, hf⟩ := mem_of_mapM htypes hx
    cases hc : cvOf? t'.toConstantVal <;> simp [hc] at hf
    subst hf; rfl
  have k1 : ∀ x ∈ ctors.flatten, kindOf x = 1 := fun x hx => by
    obtain ⟨l, hl, hxl⟩ := List.mem_flatten.1 hx
    obtain ⟨⟨t', cs⟩, -, hf⟩ := mem_of_mapM hctors hl
    obtain ⟨c, -, hfc⟩ := mem_of_mapM hf hxl
    cases hc : cvOf? c.toConstantVal <;> simp [hc] at hfc
    subst hfc; rfl
  have k2 : ∀ x ∈ recs, kindOf x = 2 := fun x hx => by
    obtain ⟨r, -, hf⟩ := mem_of_mapM hrecs hx
    obtain ⟨_, _, -, -, rfl⟩ := recOf?_eq_some hf
    rfl
  have hcount := fun j => congrArg (List.count j) hkinds
  simp only [List.map_append, List.count_append, count_map_const k0, count_map_const k1,
    count_map_const k2, ConLeche.natBasis] at hcount
  have hl0 : types.length = 1 := by
    simpa [kindOf, ConLeche.natA, ConLeche.natZeroA, ConLeche.natSuccA, ConLeche.natRecA] using
      hcount 0
  have hl1 : ctors.flatten.length = 2 := by
    simpa [kindOf, ConLeche.natA, ConLeche.natZeroA, ConLeche.natSuccA, ConLeche.natRecA] using
      hcount 1
  -- one member, `H` itself
  have hty1 : tys.length = 1 := by
    rw [← hl0]; simpa using congrArg List.length (mapM_eq_some htypes)
  have hall1 : H.all = [t.name] := by
    have h1 : H.all.length = 1 := by
      rw [← hty1]; simpa using congrArg List.length (mapM_eq_some htys)
    match hA : H.all, h1, hmem with
    | [a], _, hm => rw [List.mem_singleton.1 hm]
  have htH : t = H := by
    have h2 := hhead
    rw [hall1] at h2
    have h3 : t.name = H.name := by simpa using h2
    rw [h3] at htt
    have := htt.symm.trans hH
    simpa using this
  subst htH
  rw [hall1] at htys
  simp only [List.mapM_cons, List.mapM_nil, htt, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def, Option.some.injEq] at htys
  subst htys
  simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at hcvs
  obtain ⟨cs, hcs, _, rfl, rfl⟩ := hcvs
  simp only [List.zip_cons_cons, List.zip_nil_right, List.mapM_cons, List.mapM_nil,
    Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hctors
  obtain ⟨l, hl, _, rfl, rfl⟩ := hctors
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at hl1 hbn
  obtain ⟨x0, rfl⟩ := List.length_eq_one_iff.1 hl0
  obtain ⟨y1, y2, rfl⟩ := eq_pair_of_length hl1
  -- the former's record
  have e0 := mapM_eq_some htypes
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at e0
  obtain ⟨cvH, hcvH, rfl⟩ : ∃ cvH, cvOf? t.toConstantVal = some cvH ∧ x0 = .indInfo cvH {} := by
    cases hc : cvOf? t.toConstantVal <;> simp [hc] at e0
    exact ⟨_, rfl, e0.symm⟩
  -- the constructors' records
  have hcl := mapM_eq_some hl
  obtain ⟨c0, c1, rfl⟩ : ∃ c0 c1, cs = [c0, c1] :=
    eq_pair_of_length (by simpa using congrArg List.length hcl)
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hcl
  obtain ⟨cv0, hcv0, rfl⟩ : ∃ cv, cvOf? c0.toConstantVal = some cv ∧
      y1 = .ctorInfo cv c0.numParams c0.numFields (Name.toCL t.name) := by
    cases hc : cvOf? c0.toConstantVal <;> simp [hc] at hcl
    exact ⟨_, rfl, hcl.1.symm⟩
  obtain ⟨cv1, hcv1, rfl⟩ : ∃ cv, cvOf? c1.toConstantVal = some cv ∧
      y2 = .ctorInfo cv c1.numParams c1.numFields (Name.toCL t.name) := by
    cases hc : cvOf? c1.toConstantVal <;> simp [hc] at hcl
    exact ⟨_, rfl, hcl.2.symm⟩
  have hcc := mapM_eq_some hcs
  obtain ⟨n0, n1, hctH⟩ : ∃ n0 n1, t.ctors = [n0, n1] :=
    eq_pair_of_length (by simpa using congrArg List.length hcc)
  rw [hctH] at hcc
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hcc
  have hn0 : findConst P n0 = some (.ctorInfo c0) := by
    have h := hcc.1; split at h <;> simp_all
  have hn1 : findConst P n1 = some (.ctorInfo c1) := by
    have h := hcc.2; split at h <;> simp_all
  -- the pins
  simp only [List.cons_append, List.nil_append, ConLeche.natBasis, ConLeche.listBeqBy,
    Bool.and_eq_true] at hbn
  obtain ⟨⟨p0, p1, p2, -⟩, -⟩ := hbn
  have pin : ∀ {b q : ConLeche.ConstantInfo}, ConLeche.pinCopyOk b q = true →
      q.toConstantVal.levelParams = [] → ConLeche.pinAgrees b (q.atLps []) = true := by
    intro b q h hq
    simp only [ConLeche.pinCopyOk, Bool.and_eq_true, beq_iff_eq, hq, List.length_nil,
      List.length_eq_zero_iff] at h
    obtain ⟨⟨-, h1⟩, h2⟩ := h
    rwa [h1] at h2
  have a0 := pin p0 rfl
  have a1 := pin p1 rfl
  have a2 := pin p2 rfl
  simp only [ConLeche.natA, ConLeche.natZeroA, ConLeche.natSuccA, ConLeche.ConstantInfo.atLps,
    ConLeche.pinAgrees, ConLeche.ConstantInfo.beqP, Bool.and_eq_true, beq_iff_eq] at a0 a1 a2
  have q0 := ConLeche.ConstantVal.eq_of_beqP a0
  have q1 := ConLeche.ConstantVal.eq_of_beqP a1.1.1.1
  have q2 := ConLeche.ConstantVal.eq_of_beqP a2.1.1.1
  obtain ⟨ty, hty, rfl⟩ := cvOf?_eq_some hcvH
  obtain ⟨ty0, -, rfl⟩ := cvOf?_eq_some hcv0
  obtain ⟨ty1, -, rfl⟩ := cvOf?_eq_some hcv1
  simp only [ConLeche.ConstantVal.atLps, ConLeche.ConstantVal.mk.injEq] at q0 q1 q2
  have hNat : Name.toCL ``Nat = ConLeche.natName := rfl
  have hZero : Name.toCL ``Nat.zero = ConLeche.natZeroName := rfl
  have hSucc : Name.toCL ``Nat.succ = ConLeche.natSuccName := rfl
  have htn : t.name = ``Nat := Name.toCL_injective (q0.1.trans hNat.symm)
  have hn0' : n0 = ``Nat.zero := by
    rw [← (findDecl_mem (c := n0) hn0).2]
    exact Name.toCL_injective (q1.1.trans hZero.symm)
  have hn1' : n1 = ``Nat.succ := by
    rw [← (findDecl_mem (c := n1) hn1).2]
    exact Name.toCL_injective (q2.1.trans hSucc.symm)
  subst hn0' hn1'
  -- the sort
  have hsort : ty = .sort (.succ .zero) := by rw [q0.2.2]; rfl
  obtain ⟨u, hu, hlu⟩ := arityShape_of_toCL hty (by rw [hsort]; rfl)
  have hu1 : u = .succ .zero := by
    cases u with
    | succ u' =>
      cases u' with
      | zero => rfl
      | _ => simp [Level.toCL, Functor.map, Option.bind_eq_some_iff] at hlu
    | _ => simp [Level.toCL, Option.bind_eq_some_iff] at hlu
  rw [hsort, hu1] at hu
  -- the parameters
  have hnp := ((blockOf?_member hb0 (n := t.name) (by rw [hall1]; exact List.mem_singleton_self _)
    htt).2.2 0 ``Nat.zero (by rw [hctH]; rfl) c0 hn0).2.2.1
  exact ⟨htn, hnp.symm.trans a1.1.1.2, hctH, hu, ⟨c0, hn0, a1.1.2⟩, c1, hn1, a2.1.2⟩

/-- The images of a successful `mapM` in `Option` under a function that reads each output off its
input. -/
theorem map_of_mapM {α β γ : Type} {f : α → Option β} {g : α → γ} {k : β → γ}
    (hf : ∀ a b, f a = some b → k b = g a) :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → l'.map k = l.map g
  | [], l', h => by simp at h; subst h; rfl
  | a :: l, l', h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    simp [hf a b hb, map_of_mapM hf hbs]

/-- The formers con-leche's split reads off a block of former records followed by other records
are those records (`CL ConLeche/Kernel/Inductives/BlockShape.lean:242 blockSplit`). -/
theorem blockSplit_prefix : ∀ {l rest : List ConLeche.ConstantInfo}, (∀ x ∈ l, kindOf x = 0) →
    (∀ x ∈ rest, kindOf x ≠ 0) → ∀ {cvTs cs rs},
      ConLeche.blockSplit (l ++ rest) = some (cvTs, cs, rs) →
      cvTs.map (·.name) = l.map (·.name)
  | [], rest, _, hr, cvTs, cs, rs, h => by
    have : cvTs = [] := by
      cases rest with
      | nil =>
        rw [List.nil_append, ConLeche.blockSplit.eq_def] at h
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨_, -, he⟩ := h; cases he; rfl
      | cons x rest =>
        rw [List.nil_append, ConLeche.blockSplit.eq_def] at h
        cases x with
        | indInfo => exact absurd rfl (hr _ List.mem_cons_self)
        | _ =>
          simp only [Option.map_eq_some_iff] at h
          obtain ⟨_, -, he⟩ := h; cases he; rfl
    subst this; rfl
  | x :: l, rest, hl, hr, cvTs, cs, rs, h => by
    cases x with
    | indInfo cv caps =>
      simp only [List.cons_append, ConLeche.blockSplit, Option.map_eq_some_iff] at h
      obtain ⟨⟨cvTs', cs', rs'⟩, h', he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      simp only [List.map_cons, blockSplit_prefix (fun y hy => hl y (List.mem_cons_of_mem _ hy))
        hr h']
      rfl
    | _ => exact absurd (hl _ List.mem_cons_self) (by simp [kindOf])

/-- **The members of an inductive block of `P` are distinct**: con-leche installs one former per
member (`CL ConLeche/Kernel/Install.lean:27 blockFormers`) under distinct names
(`blockRun_nodup`). -/
theorem _root_.EraseProof.ConLecheAccepts.all_nodup {P : List ConstantInfo} {env : ConLeche.Env}
    (hP : ConLecheAccepts P env) {t : InductiveVal} (ht : .inductInfo t ∈ P) : t.all.Nodup := by
  obtain ⟨Hn, H, hH, hhead, hall, -⟩ := hP.head ht
  obtain ⟨hHm, hHn⟩ := findDecl_mem hH
  have hHn' : H.name = Hn := hHn
  subst hHn'
  have hs := hP.ind_safe hHm
  obtain ⟨block, p, hb, hdf, -⟩ := hP.block hH hhead hs
  have hd : declOf? P (.inductInfo H) = some [.indDecl block H.numParams] := by
    simp [declOf?, hs, hhead, hb]
  obtain ⟨⟨e, e', hrun⟩, -⟩ := hP.stored hHm hd
  obtain ⟨-, hk⟩ := ConLeche.Semantics.checkDeclRun_ofEnvFactsK hrun
  have hk' : ConLeche.Semantics.DeclIndRunDispatchK _ e block H.numParams e' := hk
  unfold ConLeche.Semantics.DeclIndRunDispatchK at hk'
  rw [hdf] at hk'
  have hdecl := ConLeche.readBlock_declared hdf
  have hnd := blockRun_nodup hdecl hk'
  simp only [ConLeche.blockConstants, List.map_append] at hnd
  have hnd0 := (List.nodup_append.1 (List.nodup_append.1 hnd).1).1
  -- the formers are the members' declared formers, which the split reads off the block
  obtain ⟨-, -, -, -, -, -, -, cvTs, cs, rs, nIdxs, hsp, hkl, -, hnI, -, -, hmem, -⟩ :=
    ConLeche.readBlock_inv hdf
  have hproj := (ConLeche.blockMembers_proj (cvTs := cvTs) (nIdxs := nIdxs)
    (groups := ConLeche.blockGroups p.memberNames p.lps p.nP p.k (cs.map fun c => (c.1, c.2.2)))
    (hnI.trans hkl.symm) (by rw [ConLeche.blockGroups_length, hkl])).1
  rw [← hmem] at hproj
  have hfn : (ConLeche.blockFormers p (ConLeche.blockIsRec p)).map (·.name) =
      cvTs.map (·.name) := by
    rw [← hproj]
    simp only [ConLeche.blockFormers, List.map_map]
    have : (p.members.map (·.declared)).zipIdx.map
        ((·.name) ∘ fun (x : ConLeche.ConstantVal × Nat) =>
          ConLeche.ConstantInfo.indInfo x.1 (ConLeche.blockCapsAt p x.2 (ConLeche.blockIsRec p))) =
        ((p.members.map (·.declared)).zipIdx.map Prod.fst).map (·.name) := by
      rw [List.map_map]; rfl
    rw [this, List.zipIdx_map_fst, List.map_map]
    exact List.map_congr_left fun m hm => by simp [hdecl m hm]
  -- the block's former records are the members of `H.all`, translated
  simp only [blockOf?, Option.bind_eq_some_iff, Option.some.injEq, bind, pure] at hb
  obtain ⟨tys, htys, cvs, hcvs, _, -, types, htypes, ctors, hctors, recs, hrecs, hbe⟩ := hb
  injection hbe with hbe
  subst hbe
  have k0 : ∀ x ∈ types, kindOf x = 0 := fun x hx => by
    obtain ⟨t', -, hf⟩ := mem_of_mapM htypes hx
    cases hc : cvOf? t'.toConstantVal <;> simp [hc] at hf
    subst hf; rfl
  have krest : ∀ x ∈ ctors.flatten ++ recs, kindOf x ≠ 0 := fun x hx => by
    rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨l, hl, hxl⟩ := List.mem_flatten.1 hx
      obtain ⟨⟨t', cs'⟩, -, hf⟩ := mem_of_mapM hctors hl
      obtain ⟨c, -, hfc⟩ := mem_of_mapM hf hxl
      cases hc : cvOf? c.toConstantVal <;> simp [hc] at hfc
      subst hfc; simp [kindOf]
    · obtain ⟨r, -, hf⟩ := mem_of_mapM hrecs hx
      obtain ⟨_, _, -, -, rfl⟩ := recOf?_eq_some hf
      simp [kindOf]
  rw [List.append_assoc] at hsp
  have hsn := blockSplit_prefix k0 krest hsp
  have htn : types.map (·.name) = tys.map fun t => Name.toCL t.name :=
    map_of_mapM (fun t x hx => by
      cases hc : cvOf? t.toConstantVal <;> simp [hc] at hx
      subst hx
      obtain ⟨_, -, rfl⟩ := cvOf?_eq_some hc
      rfl) htypes
  have hyn : tys.map (·.name) = H.all.map id :=
    map_of_mapM (fun n x hx => by
      split at hx
      · rename_i t' hf; cases hx; exact (findDecl_mem hf).2
      · cases hx) htys
  rw [hfn, hsn, htn] at hnd0
  have : (H.all.map Name.toCL).Nodup := by
    rw [List.map_id] at hyn
    have h2 : tys.map (fun t => Name.toCL t.name) = (tys.map (·.name)).map Name.toCL := by
      rw [List.map_map]; rfl
    rwa [h2, hyn] at hnd0
  rw [← hall]
  exact List.Pairwise.of_map Name.toCL (fun a b h hab => h (congrArg Name.toCL hab)) this

end CoreEnvOf

open CollectSub CollectSpec CollectOk Decls CoreEnvOf in
/-- **The traversal's environment invariant holds on the fragment test's closure**: on a closure
that a successful `Erasure.collectDeps` returns and that is part of a program con-leche accepts,
whose declarations erased by their values have no compiled pre-definition, `Steps.CoreEnv` holds.
The fragment test's checks give the closure's facts (`collectDeps_spec_sub`, `Run.phase`,
`Run.read`, `Run.rec_frag`, `coreEnv_value`); `blockShapeOK` and con-leche's pins give the
program's (`blockOf?_member`, `ConLecheAccepts.all_nodup`, `ConLecheAccepts.quot_pins`,
`ConLecheAccepts.natBlock`). Adapted from `ML-V Core/StepsB.lean:367 coreEnv_of_collectDeps`.
Reference: the hypotheses of `erases_erase` (`MR E/ErasureFunction.v:1228`) on
`erase_global_deps`'s environment (`MR E/ErasureFunction.v:1602`). -/
theorem coreEnv_of {P decls : List ConstantInfo} {env : ConLeche.Env} {e : Expr} {view : EnvView}
    {cfg : ErasureConfig} (hP : ConLecheAccepts P env) (hsub : SubEnv decls P)
    (hnopre : NoPreDefs view cfg decls) (h : collectDeps view cfg e = .ok decls) :
    Steps.CoreEnv view cfg decls := by
  obtain ⟨hinj, hdep, -, hbn, har⟩ := collectDeps_spec_sub hP hsub h
  obtain ⟨cs, cases, -, hcl, hel, hirr, -, -⟩ := CollectSpec.collectDeps_ok h
  obtain ⟨hvw, -, -, -, hscan⟩ := closure_ok hcl nofun nofun
  have hr : Run P env view cfg decls cases := ⟨hP, hsub, hvw, hscan, hdep⟩
  have hph : ∀ ci ∈ decls, PhaseIDecl view cfg decls ci := fun ci hci => hr.phase hel hci
  have inP : ∀ {ci}, ci ∈ decls → ci ∈ P := fun hci => (findDecl_mem (hsub _ hci)).1
  have toP : ∀ {c ci}, findDecl decls c = some ci → findDecl P c = some ci := fun h => by
    obtain ⟨h1, h2⟩ := findDecl_eq_some h; rw [← h2]; exact hsub _ h1
  -- a declaration of `P` under a name of the closure is the closure's
  have lift : ∀ {n y}, (findDecl decls n).isSome = true → findDecl P n = some y →
      findDecl decls n = some y := by
    intro n y hn hy
    obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 hn
    have e := toP hz
    rw [hy] at e
    cases e; exact hz
  -- a covered recursor has the fragment's shape
  have covRec : ∀ n, Covered view cfg decls n →
      ∀ rv, findDecl decls n = some (.recInfo rv) → RecInFragment cfg decls rv := by
    rintro n ⟨y, hy, hyn, hyr⟩ rv hrv
    rw [← hyn, hr.fd hy] at hrv
    cases hrv
    exact hr.rec_frag hy (hyr rv rfl)
  -- the values the closure holds are closed
  have hclosed : ClosedDecls decls = true := by
    refine List.all_eq_true.2 fun ci hci => ?_
    obtain ⟨xs, hxs, -⟩ := hr.read hci (.inl rfl)
    have hval : ∀ v, ci.value? (allowOpaque := true) = some v → HasFVar v = false := by
      intro v hv
      cases ci with
      | defnInfo d =>
        simp [ConstantInfo.value?] at hv
        subst hv
        cases hc : (casesOnOf? decls d.name).isNone with
        | true =>
          obtain ⟨vs, hvs, -⟩ := hr.read hci (.inr (.inl ⟨d, rfl, rfl, hc⟩))
          exact (exprConsts_plain hvs).1
        | false =>
          obtain ⟨-, value, -, hv, -⟩ := hP.find?_defn (hsub _ hci) (hph _ hci).1
          exact toCL?_closed hv
      | thmInfo t =>
        simp [ConstantInfo.value?] at hv
        subst hv
        obtain ⟨-, -, hv, -⟩ := hP.find?_thm (hsub _ hci)
        obtain ⟨_, hv⟩ := Option.isSome_iff_exists.1 hv
        exact toCL?_closed hv
      | opaqueInfo o =>
        simp [ConstantInfo.value?] at hv
        subst hv
        obtain ⟨vs, hvs, -⟩ := hr.read hci (.inr (.inr ⟨o, rfl, rfl⟩))
        exact (exprConsts_plain hvs).1
      | _ => simp [ConstantInfo.value?] at hv
    rcases hv : ci.value? (allowOpaque := true) with _ | v <;>
      simp [hv, (exprConsts_plain hxs).1, hval]
  exact {
    closed := hclosed
    inj := hinj
    bn := hbn
    arity := har
    nopre := hnopre
    npd := fun ci hci x hx => by
      obtain ⟨xs, hxs, -⟩ := hr.read hci hx
      exact (exprConsts_plain hxs).2
    recShaped := fun ci hci x hx => by
      obtain ⟨xs, hxs, hcov⟩ := hr.read hci hx
      exact ConstsIn_mono (fun c hc => covRec c (hcov c hc)) (exprConsts_consts hxs)
    quotType := fun c q hq hk => (hP.quot_pins (toP hq)).1 hk
    quotInd := fun c q hq hk => (hP.quot_pins (toP hq)).2 hk
    value := coreEnv_value hP hsub hdep hph
    irr := fun iv ⟨ci, hci, he⟩ => hirr iv (he ▸ hci)
    phase := hph
    block := fun T iv hT => by
      obtain ⟨hivm, -⟩ := findDecl_eq_some hT
      obtain ⟨H, d, hb, hall, hmem, htf⟩ := hP.member (inP hivm)
      obtain ⟨-, hip, -⟩ := blockOf?_member hb hmem htf
      refine ⟨hP.all_nodup (inP hivm), hall ▸ hmem, fun n hn ivn hivn => ?_⟩
      obtain ⟨h1, h2, -⟩ := blockOf?_member hb (hall ▸ hn) (toP hivn)
      exact ⟨h1.trans hall, h2.trans hip.symm⟩
    ctors := fun c cv hcv => by
      have hcP := toP hcv
      obtain ⟨hcm, hcn⟩ := findDecl_mem hcP
      obtain ⟨t, ht, hmemc⟩ := ctor_kind hP hcm
      have htd := lift ((hdep _ (findDecl_eq_some hcv).1).2.2.2.1 cv rfl) ht
      obtain ⟨H, d, hb, -, hmem, htf⟩ := hP.member (findDecl_mem ht).1
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hmemc
      obtain ⟨-, hip, hcs⟩ := blockOf?_member hb hmem htf
      have hcn' : cv.name = c := hcn
      obtain ⟨-, hcidx, hnp, -⟩ := hcs j cv.name hj cv (by rw [hcn']; exact hcP)
      exact ⟨t, htd, by rw [hcidx, ← hcn']; exact hj, by rw [hip, hnp]⟩
    ctorIdx := fun T iv hT j cn hj => by
      obtain ⟨hivm, -⟩ := findDecl_eq_some hT
      obtain ⟨H, d, hb, -, hmem, htf⟩ := hP.member (inP hivm)
      obtain ⟨-, hip, hcs⟩ := blockOf?_member hb hmem htf
      have hcn : cn ∈ iv.ctors := List.mem_of_getElem? hj
      obtain ⟨c, hc⟩ := (ind_kinds hP (inP hivm)).2 cn hcn
      have hcd := lift ((hdep _ hivm).2.2.1 iv rfl cn hcn) hc
      obtain ⟨-, hcidx, hnp, -⟩ := hcs j cn hj c hc
      exact ⟨c, hcd, hcidx, hnp.trans hip.symm⟩
    ctorShape := fun T iv hT cn hcn cv hcv => by
      obtain ⟨hivm, hivn⟩ := findDecl_eq_some hT
      obtain ⟨H, d, hb, -, hmem, htf⟩ := hP.member (inP hivm)
      obtain ⟨-, hip, hcs⟩ := blockOf?_member hb hmem htf
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hcn
      obtain ⟨-, -, -, hpl, hhd⟩ := hcs j cn hj cv (toP hcv)
      have hivn' : iv.name = T := hivn
      rw [hip, ← hivn']
      exact ⟨hpl, hhd⟩
    natShaped := fun iv hiv => by
      obtain ⟨hivm, hivn⟩ := findDecl_eq_some hiv
      obtain ⟨-, hnp, hct, har', ⟨c0, hc0, hf0⟩, c1, hc1, hf1⟩ :=
        hP.natBlock (inP hivm) (.inl hivn)
      have hz := lift ((hdep _ hivm).2.2.1 iv rfl ``Nat.zero (by rw [hct]; simp)) hc0
      have hs := lift ((hdep _ hivm).2.2.1 iv rfl ``Nat.succ (by rw [hct]; simp)) hc1
      refine ⟨hnp, ?_, ``Nat.zero, ``Nat.succ, hct, ?_, ?_⟩
      · show EvalEnv.propInd ⟨decls, _, cfg⟩ ``Nat = false
        unfold EvalEnv.propInd
        rw [show findDecl decls ``Nat = _ from hiv]
        simp [har', EvidentZero]
      · show ctorFields ⟨decls, _, cfg⟩ ``Nat.zero = some 0
        unfold ctorFields
        rw [show findDecl decls ``Nat.zero = _ from hz]
        simp [hf0]
      · show ctorFields ⟨decls, _, cfg⟩ ``Nat.succ = some 1
        unfold ctorFields
        rw [show findDecl decls ``Nat.succ = _ from hs]
        simp [hf1]
    natCtors := by
      have one : ∀ {n : Name} {j : Nat} {cv : ConstructorVal},
          (n = ``Nat.zero ∧ j = 0 ∨ n = ``Nat.succ ∧ j = 1) →
          findDecl decls n = some (.ctorInfo cv) → cv.induct = ``Nat ∧ cv.cidx = j := by
        intro n j cv hnj hcv
        have hcP := toP hcv
        obtain ⟨hcm, hcn⟩ := findDecl_mem hcP
        have hcn' : cv.name = n := hcn
        obtain ⟨t, ht, hmemc⟩ := ctor_kind hP hcm
        obtain ⟨htm, htn⟩ := findDecl_mem ht
        obtain ⟨htN, -, hct, -⟩ := hP.natBlock htm
          (by rcases hnj with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rw [← hcn'] <;> simp [hmemc])
        obtain ⟨H, d, hb, -, hmem, htf⟩ := hP.member htm
        obtain ⟨-, -, hcs⟩ := blockOf?_member hb hmem htf
        have hj : t.ctors[j]? = some n := by
          rcases hnj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rw [hct] <;> rfl
        obtain ⟨hind, hcidx, -⟩ := hcs j n hj cv hcP
        have htn' : t.name = cv.induct := htn
        exact ⟨hind.trans htN, hcidx⟩
      exact ⟨fun cv hcv => one (.inl ⟨rfl, rfl⟩) hcv, fun cv hcv => one (.inr ⟨rfl, rfl⟩) hcv⟩ }

end EraseProof
