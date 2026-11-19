import EraseProof.Semantics.Decode
import EraseProof.Semantics.Frozen

/-!
# The stored records of a block member, and the decodes the ι steps read

con-leche installs the formers of a block in its order, each with the block as its `all` and its
constructor group as its `ctors`, and every constructor under the member its result type names
(`CL ConLeche/Kernel/Install.lean:27 blockFormers`, `:32 blockCtors`,
`CL ConLeche/Verify/EnvWF.lean:194 CtorWF`); its recursor stage checks that the groups, in order,
are the block's constructor records (`CL ConLeche/Kernel/Inductives/RecCheck.lean:340
targetRecPins`). Read back through `DeclsOf?`, a member's former lists the block and its own
constructors, and a constructor is stored under its own inductive (`ConLecheAccepts.blockStored`),
in a block of any size. With `RulesCanonical`, the stored rule of a constructor has the shape the ι
steps read (`rule_decode`): the decodes `CasesIotaAt`, `CasesFrozenAt` and `ProjAt`.
-/
open Lean Erasure

namespace EraseProof

namespace Decode

/-! ## Readings of the record checks -/

/-- The head constant of a spine, read. -/
theorem appHead_toCL : ∀ {e : Expr} {ce : ConLeche.Expr} {t : Name} {T : ConLeche.Name}
    {us : List ConLeche.Level}, toCL? e = some ce → appHeadConst e = some t →
    ce.getAppFn = .const T us → T = Name.toCL t
  | .app f a, ce, t, T, us, hc, hh, hg => by
    simp only [toCL?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at hc
    obtain ⟨cf, hcf, ca, -, rfl⟩ := hc
    exact appHead_toCL (e := f) hcf hh hg
  | .mdata _ e, ce, t, T, us, hc, hh, hg => appHead_toCL (e := e) hc hh hg
  | .const c us', ce, t, T, us, hc, hh, hg => by
    simp only [appHeadConst, Option.some.injEq] at hh
    subst hh
    simp only [toCL?, Option.map_eq_map, Option.map_eq_some_iff] at hc
    obtain ⟨_, -, rfl⟩ := hc
    simp only [ConLeche.Expr.getAppFn, ConLeche.Expr.const.injEq] at hg
    exact hg.1.symm
  | .bvar _, _, _, _, _, _, hh, _ | .fvar _, _, _, _, _, _, hh, _ | .mvar _, _, _, _, _, _, hh, _
  | .sort _, _, _, _, _, _, hh, _ | .lam .., _, _, _, _, _, hh, _
  | .forallE .., _, _, _, _, _, hh, _ | .letE .., _, _, _, _, _, hh, _
  | .lit _, _, _, _, _, _, hh, _ | .proj .., _, _, _, _, _, hh, _ => by simp [appHeadConst] at hh

/-- The head constant of a type's result, read: con-leche's `piResult` strips every leading `Π`
of the reading, which are the type's `piLen` leading `Π`s. -/
theorem ctorHead_toCL : ∀ {e : Expr} {ce : ConLeche.Expr} {t : Name} {T : ConLeche.Name}
    {us : List ConLeche.Level}, toCL? e = some ce → appHeadConst (piResult (piLen e) e) = some t →
    ce.piResult.getAppFn = .const T us → T = Name.toCL t
  | .forallE _ d b _, ce, t, T, us, hc, hh, hg => by
    simp only [toCL?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at hc
    obtain ⟨cd, -, cb, hcb, rfl⟩ := hc
    exact ctorHead_toCL (e := b) hcb hh hg
  | .mdata _ e, ce, t, T, us, hc, hh, hg => by
    have h' : appHeadConst (piResult (piLen e) e) = some t := by
      cases h : piLen e <;> simp only [piLen, h, piResult] at hh ⊢ <;> exact hh
    exact ctorHead_toCL (e := e) hc h' hg
  | .app f a, ce, t, T, us, hc, hh, hg => by
    simp only [toCL?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at hc
    obtain ⟨cf, hcf, ca, hca, rfl⟩ := hc
    have hg' : (ConLeche.Expr.app cf ca).getAppFn = .const T us := hg
    exact appHead_toCL (e := .app f a) (by simp [toCL?, hcf, hca]) hh hg'
  | .const c us', ce, t, T, us, hc, hh, hg => by
    simp only [toCL?, Option.map_eq_map, Option.map_eq_some_iff] at hc
    obtain ⟨us'', hus, rfl⟩ := hc
    have hg' : (ConLeche.Expr.const (Name.toCL c) us'').getAppFn = .const T us := hg
    exact appHead_toCL (e := .const c us') (by simp [toCL?, hus]) hh hg'
  | .bvar _, _, _, _, _, _, hh, _ | .fvar _, _, _, _, _, _, hh, _ | .mvar _, _, _, _, _, _, hh, _
  | .sort _, _, _, _, _, _, hh, _ | .lam .., _, _, _, _, _, hh, _
  | .letE .., _, _, _, _, _, hh, _
  | .lit _, _, _, _, _, _, hh, _ | .proj .., _, _, _, _, _, hh, _ => by
    simp [appHeadConst, piLen, piResult] at hh

/-- The constructor count `blockCtorCount` reads is the number of constructors `blockOf?` looked
up. -/
theorem blockCtorCount_of {P : List ConstantInfo} : ∀ {ns : List Name} {tys : List InductiveVal}
    {cvs : List (List ConstructorVal)},
    ns.mapM (fun n => match findConst P n with
      | some (.inductInfo t) => some t
      | _ => none) = some tys →
    tys.mapM (fun t => t.ctors.mapM fun n => match findConst P n with
      | some (.ctorInfo c) => some c
      | _ => none) = some cvs →
    blockCtorCount P ns = some (cvs.map List.length).sum
  | [], tys, cvs, h1, h2 => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h1
    subst h1
    simp only [List.mapM_nil, pure, Option.some.injEq] at h2
    subst h2; rfl
  | n :: ns, tys, cvs, h1, h2 => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at h1
    obtain ⟨t, ht, tys', htys', rfl⟩ := h1
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at h2
    obtain ⟨cs, hcs, cvs', hcvs', rfl⟩ := h2
    have hft : findConst P n = some (.inductInfo t) := by
      split at ht
      · rename_i t' hf; cases ht; exact hf
      · exact nomatch ht
    have hl : cs.length = t.ctors.length := by
      simpa using (congrArg List.length (mapM_eq_some hcs)).symm
    simp only [blockCtorCount, hft, blockCtorCount_of htys' hcvs', List.map_cons, List.sum_cons, hl]

/-- What `blockOf?` checks of the block headed by `H` (`blockShapeOK`): every recursor of the
block has the block's parameter count and `mdata`-free minor premises; every member lists the
block and has its parameter count, each of its constructors has the block's parameter count and a
result headed by the member, and the member's recursor has one motive per member, one minor
premise per constructor of the block and the member's index count. -/
theorem blockOf?_shape {P : List ConstantInfo} {H : InductiveVal} {d : ConLeche.Declaration}
    (h : blockOf? P H = some d) :
    (∀ r, .recInfo r ∈ P → r.all = H.all → r.numParams = H.numParams ∧
      ∀ i < r.numMinors, ∃ D, forallDom? (r.numParams + r.numMotives + i) r.type = some D ∧
        NoMData D = true) ∧
    ∀ n ∈ H.all, ∀ t, findConst P n = some (.inductInfo t) →
      t.all = H.all ∧ t.numParams = H.numParams ∧
      (∀ j cn, t.ctors[j]? = some cn → ∀ c, findConst P cn = some (.ctorInfo c) →
        c.induct = t.name ∧ c.cidx = j ∧ c.numParams = H.numParams ∧
        appHeadConst (piResult (piLen c.type) c.type) = some t.name) ∧
      ∃ r, .recInfo r ∈ P ∧ r.all = H.all ∧ r.name = mkRecName t.name ∧
        r.numMotives = H.all.length ∧ blockCtorCount P H.all = some r.numMinors ∧
        r.numIndices = t.numIndices := by
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
  have hlen : tys.length = H.all.length := by
    simpa using (congrArg List.length (mapM_eq_some htys)).symm
  unfold blockShapeOK at hok
  simp only [Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq,
    bne_iff_ne, ne_eq, List.mem_range] at hok
  have hrs : ∀ r, .recInfo r ∈ P → r.all = H.all → r ∈ P.reverse.filterMap (fun
      | .recInfo r => if r.all = H.all then some r else none
      | _ => none) := fun r hr hall =>
    List.mem_filterMap.mpr ⟨_, List.mem_reverse.mpr hr, by simp [hall]⟩
  obtain ⟨⟨⟨⟨⟨⟨hr, ht⟩, hz⟩, -⟩, -⟩, -⟩, hany⟩ := hok
  refine ⟨fun r hr' hall => ⟨(hr r (hrs r hr' hall)).1.1.1, fun i hi => ?_⟩, fun n hn t hnt => ?_⟩
  · have := (hr r (hrs r hr' hall)).2 i hi
    cases hd : forallDom? (r.numParams + r.numMotives + i) r.type with
    | none => simp [hd] at this
    | some D => exact ⟨D, rfl, by simpa [hd] using this⟩
  have htm := hty n hn t hnt
  obtain ⟨⟨hta, htp⟩, -⟩ := ht t htm
  refine ⟨hta, htp, fun j cn hj c hc => ?_, ?_⟩
  · obtain ⟨cs, hcs', hzm⟩ : ∃ cs, t.ctors.mapM (fun n => match findConst P n with
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
    exact ⟨hind, hcidx, hnp, by rw [hpl]; exact hhd⟩
  · obtain ⟨r, hrm, ⟨⟨⟨⟨⟨hname, -⟩, hmot⟩, hmin⟩, hidx⟩, -⟩⟩ := hany t htm
    obtain ⟨x, hx, hxr⟩ := List.mem_filterMap.mp hrm
    cases x <;> simp only [reduceCtorEq, Option.ite_none_right_eq_some, Option.some.injEq] at hxr
    obtain ⟨hrall, rfl⟩ := hxr
    exact ⟨_, List.mem_reverse.mp hx, hrall, hname, by rw [hmot, hlen],
      by rw [hmin]; exact blockCtorCount_of htys hcvs, hidx⟩

/-! ## The stored block -/

/-- The former of a former record. Reference: none. -/
def formerCv? : ConLeche.ConstantInfo → Option ConLeche.ConstantVal
  | .indInfo cv _ => some cv
  | _ => none

/-- The formers a block's split reads are its former records, in order
(`CL ConLeche/Kernel/Inductives/BlockShape.lean:242 blockSplit`). -/
theorem blockSplit_formers : ∀ {block : List ConLeche.ConstantInfo}
    {cvTs : List ConLeche.ConstantVal} {cs : List (ConLeche.ConstantVal × Nat × Nat)}
    {rs : List (ConLeche.ConstantVal × Nat × Nat × Bool × List ConLeche.RecRule)},
    ConLeche.blockSplit block = some (cvTs, cs, rs) → cvTs = block.filterMap formerCv?
  | .indInfo .. :: _, _, _, _, h => by
    simp only [ConLeche.blockSplit, Option.map_eq_some_iff] at h
    obtain ⟨⟨cvTs', cs', rs'⟩, h', he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    simp [formerCv?, blockSplit_formers h']
  | [], _, _, _, h | .recInfo .. :: _, _, _, _, h | .axiomInfo .. :: _, _, _, _, h
  | .defnInfo .. :: _, _, _, _, h | .thmInfo .. :: _, _, _, _, h | .ctorInfo .. :: _, _, _, _, h => by
    simp only [ConLeche.blockSplit] at h
    obtain ⟨⟨cs', rs'⟩, h', he⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, -, -⟩ := he
    have hno : ∀ cv caps, ConLeche.ConstantInfo.indInfo cv caps ∉ _ :=
      fun _ _ => (blockSplitCtors_mem h').2.2
    refine (List.filterMap_eq_nil_iff.mpr fun x hx => ?_).symm
    cases x <;> first | rfl | exact absurd hx (hno _ _)

/-- The former records `blockOf?` writes, in `all` order. -/
theorem formers_at {P : List ConstantInfo} {f : InductiveVal → Option ConLeche.ConstantInfo}
    (hf : ∀ t x, f t = some x → ∃ cv, cvOf? t.toConstantVal = some cv ∧ x = .indInfo cv {}) :
    ∀ {ns : List Name} {tys : List InductiveVal} {types : List ConLeche.ConstantInfo},
    ns.mapM (fun n => match findConst P n with
      | some (.inductInfo t) => some t
      | _ => none) = some tys → tys.mapM f = some types →
    (types.filterMap formerCv?).length = ns.length ∧
    ∀ {i : Nat} {n : Name}, ns[i]? = some n → ∃ t cv, findConst P n = some (.inductInfo t) ∧
      cvOf? t.toConstantVal = some cv ∧ (types.filterMap formerCv?)[i]? = some cv
  | [], tys, types, h1, h2 => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h1
    subst h1
    simp only [List.mapM_nil, pure, Option.some.injEq] at h2
    subst h2
    exact ⟨rfl, fun h => by simp at h⟩
  | n :: ns, tys, types, h1, h2 => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at h1
    obtain ⟨t, ht, tys', htys', rfl⟩ := h1
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at h2
    obtain ⟨x, hx, types', htypes', rfl⟩ := h2
    have hft : findConst P n = some (.inductInfo t) := by
      split at ht
      · rename_i t' hf; cases ht; exact hf
      · exact nomatch ht
    obtain ⟨cv, hcv, rfl⟩ := hf t x hx
    obtain ⟨hl, hi⟩ := formers_at hf htys' htypes'
    refine ⟨by simp [formerCv?, hl], fun {i n'} hi' => ?_⟩
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi'
      subst hi'
      exact ⟨t, cv, hft, hcv, by simp [formerCv?]⟩
    | succ i =>
      obtain ⟨t', cv', h1, h2, h3⟩ := hi (by simpa using hi')
      exact ⟨t', cv', h1, h2, by simpa [formerCv?] using h3⟩

/-- The constructors of the inductives `ns` of `P`, in order. Reference: none. -/
def ctorsOf (P : List ConstantInfo) (ns : List Name) : List Name :=
  ns.flatMap fun n => match findConst P n with
    | some (.inductInfo t) => t.ctors
    | _ => []

/-- The constructor records `blockOf?` writes carry the translated names of the members'
constructors, in order. -/
theorem ctors_names {P : List ConstantInfo}
    {g : InductiveVal × List ConstructorVal → Option (List ConLeche.ConstantInfo)}
    (hg : ∀ t cs L, g (t, cs) = some L → L.filterMap ctorName? = cs.map (Name.toCL ·.name)) :
    ∀ {ns : List Name} {tys : List InductiveVal} {cvs : List (List ConstructorVal)}
      {ctors : List (List ConLeche.ConstantInfo)},
    ns.mapM (fun n => match findConst P n with
      | some (.inductInfo t) => some t
      | _ => none) = some tys →
    tys.mapM (fun t => t.ctors.mapM fun n => match findConst P n with
      | some (.ctorInfo c) => some c
      | _ => none) = some cvs →
    (tys.zip cvs).mapM g = some ctors →
    ctors.flatten.filterMap ctorName? = (ctorsOf P ns).map Name.toCL
  | [], tys, cvs, ctors, h1, h2, h3 => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h1
    subst h1
    simp only [List.mapM_nil, pure, Option.some.injEq] at h2
    subst h2
    simp only [List.zip_nil_left, List.mapM_nil, pure, Option.some.injEq] at h3
    subst h3; rfl
  | n :: ns, tys, cvs, ctors, h1, h2, h3 => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at h1
    obtain ⟨t, ht, tys', htys', rfl⟩ := h1
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at h2
    obtain ⟨cs, hcs, cvs', hcvs', rfl⟩ := h2
    simp only [List.zip_cons_cons, List.mapM_cons, Option.bind_eq_bind, Option.pure_def,
      Option.bind_eq_some_iff, Option.some.injEq] at h3
    obtain ⟨L, hL, ctors', hctors', rfl⟩ := h3
    have hft : findConst P n = some (.inductInfo t) := by
      split at ht
      · rename_i t' hf; cases ht; exact hf
      · exact nomatch ht
    simp only [List.flatten_cons, List.filterMap_append, hg t cs L hL,
      ctors_names hg htys' hcvs' hctors', ctorsOf, List.flatMap_cons, hft, List.map_append,
      ← ctorLookup_names (mapM_eq_some hcs), List.map_map]
    rfl

/-- Lists of lists with the same concatenation, without repetitions, each list of the first
within the list of the second at its position, are equal. -/
theorem eq_of_flatten_eq {α : Type} : ∀ {G T : List (List α)}, G.length = T.length →
    G.flatten = T.flatten → T.flatten.Nodup →
    (∀ (i : Nat) g t, G[i]? = some g → T[i]? = some t → ∀ x ∈ g, x ∈ t) → G = T
  | [], [], _, _, _, _ => rfl
  | g :: G, t :: T, hl, he, hnd, hs => by
    simp only [List.flatten_cons] at he hnd
    have hl' : G.length = T.length := by simpa using hl
    have hsub : ∀ x ∈ G.flatten, x ∈ T.flatten := fun x hx => by
      obtain ⟨g', hg', hxg⟩ := List.mem_flatten.mp hx
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hg'
      have hiT : i < T.length := by
        have := (List.getElem?_eq_some_iff.mp hi).1; omega
      exact List.mem_flatten.mpr ⟨T[i], List.getElem_mem hiT,
        hs (i + 1) g' T[i] (by simpa using hi) (by simp [hiT]) x hxg⟩
    have hdis := (List.nodup_append.mp hnd).2.2
    have hgt : g = t := by
      rcases List.append_eq_append_iff.mp he with ⟨a', rfl, hX⟩ | ⟨c', rfl, hY⟩
      · cases a' with
        | nil => simp
        | cons y a' =>
          exact absurd rfl (hdis y (by simp) y (hsub y (by rw [hX]; simp)))
      · cases c' with
        | nil => simp
        | cons y c' =>
          have hyt := hs 0 (t ++ y :: c') t rfl rfl y (by simp)
          exact absurd rfl (hdis y hyt y (by rw [hY]; simp))
    subst hgt
    rw [eq_of_flatten_eq hl' (List.append_cancel_left he) (List.nodup_append.mp hnd).2.1
      (fun i g' t' h1 h2 => hs (i + 1) g' t' (by simpa using h1) (by simpa using h2))]
  | [], _ :: _, hl, _, _, _ | _ :: _, [], hl, _, _, _ => by simp at hl

/-! ## The stored rules -/

/-- A spine is its head applied to its arguments. -/
theorem clSpine_go : ∀ (e : ConLeche.Expr) (acc : List ConLeche.Expr),
    ConLeche.Expr.mkAppN (clSpine.go e acc).1 (clSpine.go e acc).2 = ConLeche.Expr.mkAppN e acc := by
  intro e
  induction e with
  | app f a ihf _ => intro acc; exact ihf (a :: acc)
  | _ => intro acc; rfl

/-- A spine is its head applied to its arguments. -/
theorem clSpine_mkAppN (e : ConLeche.Expr) :
    ConLeche.Expr.mkAppN (clSpine e).1 (clSpine e).2 = e := clSpine_go e []

/-- `clBvar?`, read. -/
theorem clBvar?_eq {x : ConLeche.Expr} {i : Nat} (h : clBvar? x = some i) : x = .bvar i := by
  cases x <;> simp only [clBvar?, Option.some.injEq, reduceCtorEq] at h
  rw [h]

/-- Arguments read as the bound variables `n - 1, …, 0` are the field variables. -/
theorem eq_fbv {xs : List ConLeche.Expr} {n : Nat}
    (h : xs.map clBvar? = (List.range n).map fun i => some (n - 1 - i)) : xs = SemCases.fbv n n := by
  have hl : xs.length = n := by simpa using congrArg List.length h
  refine List.ext_getElem (by simp [SemCases.fbv, hl]) fun i h1 h2 => ?_
  have := congrArg (·[i]?) h
  simp only [List.getElem?_map, List.getElem?_eq_getElem h1, List.getElem?_range (hl ▸ h1),
    Option.map_some, Option.some.injEq] at this
  simp [clBvar?_eq this, SemCases.fbv]

/-- A list of names `Name.nodup` accepts has no repetition. -/
theorem nodup_of_nodup : ∀ {l : List ConLeche.Name}, ConLeche.Name.nodup l = true → l.Nodup
  | [], _ => List.nodup_nil
  | n :: ns, h => by
    simp only [ConLeche.Name.nodup, Bool.and_eq_true, Bool.not_eq_true'] at h
    refine List.nodup_cons.mpr ⟨fun hm => ?_, nodup_of_nodup h.2⟩
    rw [List.contains_iff_mem.mpr hm] at h
    exact nomatch h.1

/-- **The stored rule of a constructor, as `RulesCanonical` checks it**: at the recursor
`T.rec` of a stored family `T` and a constructor `C` of `T`, the rule for `C` has `C`'s field
count, fires `.plain`, and its right-hand side is `rP + nF` λs over the minor premise at position
`q` (`C`'s position among the block's constructors, after the parameters and the motives) applied
to the field variables and to inductive hypotheses: as many as the minor premise's domain `A` has
leading `Π` past the fields, each of `IHShape`, recursing on the fields `A`'s binders name. Also:
the recursor's type has `mI + 1` leading `Π` and distinct level parameters. -/
theorem rule_decode {env : ConLeche.Env} (hrc : RulesCanonical env = true) {T : ConLeche.Name}
    {cvR : ConLeche.ConstantVal} {mI rP : Nat} {isK : Bool} {rules : List ConLeche.RecRule}
    (hR : env.find? (.str T "rec") = some (.recInfo cvR mI rP isK rules))
    {cvT : ConLeche.ConstantVal} {caps : ConLeche.IndCaps}
    (hT : env.find? T = some (.indInfo cvT caps)) {C : ConLeche.Name} (hC : C ∈ caps.ctors)
    {cvC : ConLeche.ConstantVal} {nP nF : Nat} {ind : ConLeche.Name}
    (hfC : env.find? C = some (.ctorInfo cvC nP nF ind)) :
    clPis cvR.type = mI + 1 ∧ cvR.levelParams.Nodup ∧
    ∃ rl A ihs, rules.find? (fun r => r.ctor == C) = some rl ∧ rl.nfields = nF ∧ rl.fire = .plain ∧
      ConLeche.Expr.binderDom (rP - (blockCtors env caps).length + (blockCtors env caps).idxOf C)
        cvR.type = some A ∧ ihs.length + nF = clPis A ∧
      clLams rl.rhs = (rP + nF, ConLeche.Expr.mkAppN
        (.bvar (nF + (rP - 1 - (rP - (blockCtors env caps).length + (blockCtors env caps).idxOf C))))
        (SemCases.fbv nF nF ++ ihs)) ∧
      (∀ ih ∈ ihs, IHShape env cvR.levelParams rP nF ih = true) ∧
      ihs.map (fun ih => clFieldOf nF (clLams ih).1 (clLams ih).2) =
        (List.range' nF (clPis A - nF)).map (minorIHField A) := by
  have hmem := ConLeche.Env.find?_mem hR
  have hname : cvR.name = .str T "rec" := ConLeche.Env.find?_name hR
  have hcan := List.all_eq_true.mp hrc _ hmem
  simp only [Bool.and_eq_true, beq_iff_eq] at hcan
  obtain ⟨⟨⟨hpis, hnd⟩, hshape⟩, hsel⟩ := hcan
  rw [hname] at hsel
  simp only [RulesSelected, hT, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hsel
  obtain ⟨⟨⟨hctors, hfire⟩, hsels⟩, -⟩ := hsel
  have hCm : C ∈ rules.map (·.ctor) := hctors ▸ hC
  obtain ⟨rl, hrl⟩ : ∃ rl, rules.find? (fun r => r.ctor == C) = some rl := by
    obtain ⟨r, hr, he⟩ := List.mem_map.mp hCm
    exact Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨r, hr, by simp [he]⟩)
  have hrlm := List.mem_of_find?_eq_some hrl
  have hrlc : rl.ctor = C := by simpa using List.find?_some hrl
  have hsh := List.all_eq_true.mp hshape rl hrlm
  have hse := hsels rl hrlm
  simp only [RuleShape, Bool.and_eq_true, beq_iff_eq] at hsh
  obtain ⟨⟨⟨hl1, -⟩, htake⟩, hihs⟩ := hsh
  simp only [RuleSelects, hrlc, hfC, Bool.and_eq_true, beq_iff_eq] at hse
  obtain ⟨⟨⟨-, hnf⟩, hhd⟩, hA⟩ := hse
  cases hAq : ConLeche.Expr.binderDom (rP - (blockCtors env caps).length + (blockCtors env caps).idxOf C)
    cvR.type with
  | none => simp [hAq] at hA
  | some A =>
  simp only [hAq, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hA
  obtain ⟨⟨hlen, hfld⟩, -⟩ := hA
  subst hnf
  refine ⟨hpis, nodup_of_nodup hnd, rl, A, _, hrl, rfl, of_decide_eq_true (by simpa using hfire rl hrlm),
    rfl, ?_, ?_, fun ih hih => List.all_eq_true.mp hihs ih hih, hfld⟩
  · have := congrArg List.length htake
    simp only [List.length_map, List.length_take, List.length_range] at this
    simp only [List.length_drop]; omega
  · have he := clSpine_mkAppN (clLams rl.rhs).2
    rw [← List.take_append_drop rl.nfields (clSpine (clLams rl.rhs).2).2] at he
    rw [eq_fbv htake, clBvar?_eq hhd] at he
    exact Prod.ext hl1 he.symm

/-- **A block of `P` stores every member's former and constructors**: the former of each member
`n` under its translated name and record, with the block as its `all` and its own constructors as
its `ctors` (`CL ConLeche/Kernel/Install.lean:27 blockFormers`,
`CL ConLeche/Kernel/Inductives/BlockInstall.lean:71 blockCapsAt`); each constructor under its
translated name and record, with its own inductive as its family (`:32 blockCtors`; the family is
its type's result head, `CL ConLeche/Verify/EnvWF.lean:194 CtorWF`, which `blockShapeOK` checks
against the inductive that lists it). con-leche groups the constructors by their result heads
(`CL ConLeche/Kernel/Inductives/BlockShape.lean:324 blockGroups`) and checks that the groups, in
order, are the block's constructor records (`blockRun_pins`), so a member's group is its
constructor list. The block's constructors have distinct names. Reference: the constructors
`MR P/PCUICWcbvEval.v:303 eval_construct` reads. -/
theorem _root_.EraseProof.ConLecheAccepts.blockStored {P : List ConstantInfo} {env : ConLeche.Env}
    (h : ConLecheAccepts P env) {Hn : Name} {H : InductiveVal}
    (hH : findDecl P Hn = some (.inductInfo H)) (hhead : H.all.head? = some Hn) :
    ((ctorsOf P H.all).map Name.toCL).Nodup ∧
    (∀ caps : ConLeche.IndCaps, caps.all = H.all.map Name.toCL →
      blockCtors env caps = (ctorsOf P H.all).map Name.toCL) ∧
    ∀ n ∈ H.all, ∀ t, findConst P n = some (.inductInfo t) →
      (∃ cvt caps, cvOf? t.toConstantVal = some cvt ∧
        env.find? (Name.toCL n) = some (.indInfo cvt caps) ∧
        caps.all = H.all.map Name.toCL ∧ caps.ctors = t.ctors.map Name.toCL) ∧
      ∀ cn ∈ t.ctors, ∀ c, findConst P cn = some (.ctorInfo c) → ∃ cv,
        cvOf? c.toConstantVal = some cv ∧
        env.find? (Name.toCL cn) = some (.ctorInfo cv c.numParams c.numFields (Name.toCL n)) := by
  obtain ⟨block, p, hb, hdf, hst, hndC, hgr, -⟩ := h.blockPins hH hhead
  obtain ⟨ds, hds, hfold, -⟩ := id h
  have hwf := ConLeche.Semantics.checkDeclsPure_envWF hfold
  obtain ⟨-, hmem⟩ := blockOf?_shape hb
  obtain ⟨block', hbe, -, hspec⟩ := blockOf?_spec hb
  simp only [ConLeche.Declaration.indDecl.injEq, and_true] at hbe
  subst hbe
  obtain ⟨hnP, -, -, -, -, -, -, cvTs, cs, rs, nIdxs, hsp, hk, -, hnI, -, -, hmems, -⟩ :=
    ConLeche.readBlock_inv hdf
  -- the constructors, under their own inductive
  have hctor : ∀ n ∈ H.all, ∀ t, findConst P n = some (.inductInfo t) → ∀ cn ∈ t.ctors, ∀ c,
      findConst P cn = some (.ctorInfo c) → ∃ cv, cvOf? c.toConstantVal = some cv ∧
        env.find? (Name.toCL cn) = some (.ctorInfo cv c.numParams c.numFields (Name.toCL n)) := by
    intro n hn t ht cn hcn c hc
    obtain ⟨t', ht', -, hcs⟩ := hspec n hn
    rw [ht, Option.some.injEq, ConstantInfo.inductInfo.injEq] at ht'
    subst ht'
    obtain ⟨c', hc', cv, hcv, hmemb⟩ := hcs cn hcn
    rw [hc, Option.some.injEq, ConstantInfo.ctorInfo.injEq] at hc'
    subst hc'
    obtain ⟨T', hT'⟩ := readBlock_ctor_mem hdf hndC hgr hmemb
    have hf := hst _ hT'
    obtain ⟨ty, hty, rfl⟩ := cvOf?_eq_some hcv
    obtain ⟨us, hus⟩ := hwf.ctors _ (ConLeche.Env.find?_mem hf) _ _ _ _ rfl
    obtain ⟨-, -, hcl, -⟩ := hmem n hn t ht
    obtain ⟨jc, hjc⟩ := List.getElem?_of_mem hcn
    obtain ⟨-, -, hnp, hhd⟩ := hcl jc cn hjc c hc
    have hTn : T' = Name.toCL t.name := ctorHead_toCL hty hhd hus
    have htn : t.name = n := (findDecl_mem ht).2
    have hcn' : c.name = cn := (findDecl_mem hc).2
    refine ⟨_, hcv, ?_⟩
    rw [hnP, ← hnp, hTn, htn] at hf
    rw [← hcn']
    exact hf
  -- the records `blockOf?` writes
  have hb' := hb
  simp only [blockOf?, Option.bind_eq_some_iff, Option.some.injEq, bind, pure] at hb'
  obtain ⟨tys, htys, cvs, hcvs, -, -, types, htypes, ctors, hctors, recs, hrecs, hbe⟩ := hb'
  simp only [ConLeche.Declaration.indDecl.injEq, and_true] at hbe
  have hrecF : recs.filterMap formerCv? = [] ∧ recs.filterMap ctorName? = [] := by
    constructor <;> refine List.filterMap_eq_nil_iff.mpr fun x hx => ?_ <;>
    · obtain ⟨r, -, he⟩ := mem_of_mapM hrecs hx
      obtain ⟨_, _, -, -, rfl⟩ := recOf?_eq_some he
      rfl
  have hctF : ctors.flatten.filterMap formerCv? = [] := List.filterMap_eq_nil_iff.mpr fun x hx => by
    obtain ⟨L, hL, hxL⟩ := List.mem_flatten.mp hx
    obtain ⟨⟨t, cs⟩, -, he⟩ := mem_of_mapM hctors hL
    obtain ⟨c, -, he'⟩ := mem_of_mapM he hxL
    cases hcv : cvOf? c.toConstantVal <;> simp [hcv] at he'
    subst he'; rfl
  have htyF : types.filterMap ctorName? = [] := List.filterMap_eq_nil_iff.mpr fun x hx => by
    obtain ⟨t, -, he⟩ := mem_of_mapM htypes hx
    cases hcv : cvOf? t.toConstantVal <;> simp [hcv] at he
    subst he; rfl
  have hcvT : cvTs = types.filterMap formerCv? := by
    rw [blockSplit_formers hsp, ← hbe]
    simp [List.filterMap_append, hrecF.1, hctF]
  obtain ⟨hlenT, hatT⟩ := formers_at (fun t x hx => by
    cases hcv : cvOf? t.toConstantVal <;> simp [hcv] at hx
    exact ⟨_, rfl, hx.symm⟩) htys htypes
  rw [← hcvT] at hlenT hatT
  have hcsn : cs.map (·.1.name) = (ctorsOf P H.all).map Name.toCL := by
    rw [blockSplit_ctors hsp, ← hbe]
    simp only [List.filterMap_append, htyF, hrecF.2, List.nil_append, List.append_nil]
    exact ctors_names (fun t cs L hL => ctorRecords_names (mapM_eq_some hL)) htys hcvs hctors
  have hcvTn : cvTs.map (·.name) = H.all.map Name.toCL := by
    refine List.ext_getElem? fun i => ?_
    rw [List.getElem?_map, List.getElem?_map]
    cases hi : H.all[i]? with
    | none => rw [List.getElem?_eq_none (by have := List.getElem?_eq_none_iff.mp hi; omega)]; rfl
    | some n =>
      obtain ⟨t, cv, ht, hcv, hcvi⟩ := hatT hi
      obtain ⟨ty, -, rfl⟩ := cvOf?_eq_some hcv
      have htn : t.name = n := (findDecl_mem ht).2
      rw [hcvi]
      simp [htn]
  -- the groups are the members' constructor lists
  have hkl : p.k = cvTs.length := hk.symm
  have hGl := ConLeche.blockGroups_length (names := p.memberNames) (lps := p.lps) (nP := p.nP)
    (k := p.k) (cs := cs.map fun c => (c.1, c.2.2))
  have hGcs : ∀ g ∈ ConLeche.blockGroups p.memberNames p.lps p.nP p.k (cs.map fun c => (c.1, c.2.2)),
      ∀ y ∈ g, y ∈ cs.map fun c => (c.1, c.2.2) := fun g hg y hy => ConLeche.mem_blockGroups hg hy
  generalize ConLeche.blockGroups p.memberNames p.lps p.nP p.k (cs.map fun c => (c.1, c.2.2)) = G
    at hmems hGl hGcs
  have hproj := ConLeche.blockMembers_proj (cvTs := cvTs) (nIdxs := nIdxs) (groups := G)
    (hnI.trans hk.symm) (by rw [hGl, hk])
  rw [← hmems] at hproj
  obtain ⟨hmT, -, hmG⟩ := hproj
  have hmn : p.memberNames = H.all.map Name.toCL := by
    show p.members.map (·.cvT.name) = _
    rw [← hcvTn, ← hmT, List.map_map]; rfl
  have hmi : ∀ {i : Nat} (hi : i < p.members.length), cvTs[i]? = some p.members[i].cvT ∧
      G[i]? = some p.members[i].ctors := fun {i} hi =>
    ⟨by rw [← hmT, List.getElem?_map, List.getElem?_eq_getElem hi]; rfl,
      by rw [← hmG, List.getElem?_map, List.getElem?_eq_getElem hi]; rfl⟩
  have hTT : (H.all.map fun n => (match findConst P n with
      | some (.inductInfo t) => t.ctors
      | _ => []).map Name.toCL).flatten = (ctorsOf P H.all).map Name.toCL := by
    simp only [ctorsOf, List.flatMap_def, List.map_flatten, List.map_map]; rfl
  have hGf : (G.map (·.map (·.1.name))).flatten = (H.all.map fun n => (match findConst P n with
      | some (.inductInfo t) => t.ctors
      | _ => []).map Name.toCL).flatten := by
    rw [hTT, ← hcsn, ← hgr hsp, ← List.map_flatten, ← hmG]; rfl
  have hGT : G.map (·.map (·.1.name)) = H.all.map fun n => (match findConst P n with
      | some (.inductInfo t) => t.ctors
      | _ => []).map Name.toCL := by
    refine eq_of_flatten_eq ?_ hGf (by rw [← hGf, ← List.map_flatten, ← hmG]; exact hndC) ?_
    · simp only [List.length_map, hGl, hkl, hlenT]
    · intro i g tt hg htt x hx
      rw [List.getElem?_map] at hg htt
      obtain ⟨gi, hgi, rfl⟩ := Option.map_eq_some_iff.mp hg
      obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.mp htt
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      have hilt : i < p.members.length := by
        have := (List.getElem?_eq_some_iff.mp hgi).1
        rw [← hmG, List.length_map] at this; exact this
      obtain ⟨hcvi, hgi'⟩ := hmi hilt
      rw [hgi, Option.some.injEq] at hgi'
      subst hgi'
      have hfy : env.find? y.1.name = some (.ctorInfo y.1 p.nP y.2 p.members[i].cvT.name) := by
        refine hst (.ctorInfo y.1 p.nP y.2 p.members[i].cvT.name)
          (List.mem_append_left _ (List.mem_append_right _ ?_))
        exact List.mem_flatMap.mpr ⟨_, List.mem_map_of_mem (f := fun ms => (ms.cvT.name, ms.ctors))
          (List.getElem_mem hilt), List.mem_map.mpr ⟨y, hy, rfl⟩⟩
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp
        (hGcs _ (hmG ▸ List.mem_map_of_mem (List.getElem_mem hilt)) _ hy)
      have hzn : z.1.name ∈ (ctorsOf P H.all).map Name.toCL :=
        hcsn ▸ List.mem_map_of_mem (f := fun c => c.1.name) hz
      obtain ⟨c0, hc0, hc0n⟩ := List.mem_map.mp hzn
      simp only [ctorsOf, List.mem_flatMap] at hc0
      obtain ⟨m, hm, hc0m⟩ := hc0
      obtain ⟨tm, htm, -, hcsm⟩ := hspec m hm
      rw [htm] at hc0m
      obtain ⟨c, hc, -⟩ := hcsm c0 hc0m
      obtain ⟨cv, -, hfc⟩ := hctor m hm tm htm c0 hc0m c hc
      simp only at hfy
      rw [← hc0n, hfc, Option.some.injEq, ConLeche.ConstantInfo.ctorInfo.injEq] at hfy
      have hn' : p.members[i].cvT.name = Name.toCL n := by
        have h1 := congrArg (·[i]?) hcvTn
        simp only [List.getElem?_map, hcvi, hn, Option.map_some, Option.some.injEq] at h1
        exact h1
      have hmn : m = n := Name.toCL_injective (hfy.2.2.2.trans hn')
      subst hmn
      simp only [htm]
      rw [← hc0n]
      exact List.mem_map_of_mem hc0m
  -- the formers, with the block and their constructor lists
  have hform : ∀ n ∈ H.all, ∀ t, findConst P n = some (.inductInfo t) → ∃ cvt caps,
      cvOf? t.toConstantVal = some cvt ∧ env.find? (Name.toCL n) = some (.indInfo cvt caps) ∧
      caps.all = H.all.map Name.toCL ∧ caps.ctors = t.ctors.map Name.toCL := by
    intro n hn t ht
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hn
    obtain ⟨t', cv, ht', hcv, hcvi⟩ := hatT hi
    rw [ht, Option.some.injEq, ConstantInfo.inductInfo.injEq] at ht'
    subst ht'
    have hilt : i < p.members.length := by
      have := (List.getElem?_eq_some_iff.mp hcvi).1
      rw [← hmT, List.length_map] at this; exact this
    obtain ⟨hcvi', hGi'⟩ := hmi hilt
    rw [hcvi, Option.some.injEq] at hcvi'
    have hdecl := ConLeche.readBlock_declared hdf _ (List.getElem_mem hilt)
    have hF : ConLeche.ConstantInfo.indInfo cv (ConLeche.blockCapsAt p i (ConLeche.blockIsRec p)) ∈
        ConLeche.blockConstants p := by
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨(cv, i), ?_, rfl⟩))
      rw [List.mem_zipIdx_iff_getElem?, List.getElem?_map, List.getElem?_eq_getElem hilt]
      simp [hdecl, hcvi']
    have hf := hst _ hF
    have hGi := congrArg (·[i]?) hGT
    simp only [List.getElem?_map, hi, hGi', Option.map_some, Option.some.injEq, ht] at hGi
    obtain ⟨ty, -, rfl⟩ := cvOf?_eq_some hcv
    refine ⟨_, ConLeche.blockCapsAt p i (ConLeche.blockIsRec p), hcv, ?_, ?_, ?_⟩
    · rw [← (findDecl_mem ht).2]; exact hf
    · unfold ConLeche.blockCapsAt; split <;> exact hmn
    · unfold ConLeche.blockCapsAt
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hilt, Option.getD_some]
      split
      · rename_i c' _ heq; rw [heq] at hGi; simpa using hGi
      · exact hGi
  refine ⟨?_, fun caps hcaps => ?_, fun n hn t ht => ⟨hform n hn t ht, hctor n hn t ht⟩⟩
  · rw [← hTT, ← hGT, ← List.map_flatten, ← hmG]; exact hndC
  · unfold blockCtors
    rw [hcaps, List.flatMap_map, ctorsOf, List.map_flatMap, List.flatMap_def, List.flatMap_def]
    congr 1
    refine List.map_congr_left fun m hm => ?_
    obtain ⟨tm, htm, -, -⟩ := hspec m hm
    obtain ⟨cvt, caps', -, hf, -, hcc⟩ := hform m hm tm htm
    simp [hf, htm, hcc]

/-! ## The minor premises, read -/

/-- The `i`-th leading `Π`-domain of a type, read. -/
theorem forallDom?_toCL : ∀ (i : Nat) {e D : Expr} {ce : ConLeche.Expr}, forallDom? i e = some D →
    toCL? e = some ce → ∃ cD, toCL? D = some cD ∧ ConLeche.Expr.binderDom i ce = some cD := by
  intro i
  induction i with
  | zero =>
    intro e D ce h hc
    cases e <;> simp only [forallDom?, reduceCtorEq, Option.some.injEq] at h
    subst h
    simp only [toCL?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at hc
    obtain ⟨ct, hct, cb, -, rfl⟩ := hc
    exact ⟨ct, hct, rfl⟩
  | succ i ih =>
    intro e D ce h hc
    cases e <;> simp only [forallDom?, reduceCtorEq] at h
    simp only [toCL?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at hc
    obtain ⟨ct, -, cb, hcb, rfl⟩ := hc
    exact ih h hcb

/-- An `mdata`-free type has as many leading `Π` as its reading. -/
theorem forallArity_toCL : ∀ {e : Expr} {ce : ConLeche.Expr}, NoMData e = true → toCL? e = some ce →
    forallArity e = clPis ce := by
  intro e
  induction e with
  | forallE _ t b _ _ ihb =>
    intro ce hn hc
    simp only [NoMData, Bool.and_eq_true] at hn
    simp only [toCL?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at hc
    obtain ⟨ct, -, cb, hcb, rfl⟩ := hc
    simp only [forallArity, clPis, ihb hn.2 hcb]
  | mdata => intro ce hn; simp [NoMData] at hn
  | app f a =>
    intro ce _ hc
    simp only [toCL?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at hc
    obtain ⟨_, -, _, -, rfl⟩ := hc; rfl
  | lam _ t b _ =>
    intro ce _ hc
    simp only [toCL?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at hc
    obtain ⟨_, -, _, -, rfl⟩ := hc; rfl
  | letE _ t v b _ =>
    intro ce _ hc
    simp only [toCL?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at hc
    obtain ⟨_, -, _, -, _, -, rfl⟩ := hc; rfl
  | bvar => intro ce _ hc; simp only [toCL?, Option.some.injEq] at hc; subst hc; rfl
  | sort =>
    intro ce _ hc; simp only [toCL?, Option.map_eq_map, Option.map_eq_some_iff] at hc
    obtain ⟨_, -, rfl⟩ := hc; rfl
  | const =>
    intro ce _ hc; simp only [toCL?, Option.map_eq_map, Option.map_eq_some_iff] at hc
    obtain ⟨_, -, rfl⟩ := hc; rfl
  | proj =>
    intro ce _ hc; simp only [toCL?, Option.map_eq_map, Option.map_eq_some_iff] at hc
    obtain ⟨_, -, rfl⟩ := hc; rfl
  | lit l =>
    intro ce _ hc; cases l <;> simp only [toCL?, Option.some.injEq] at hc <;> subst hc <;> rfl
  | fvar | mvar => intro ce _ hc; simp [toCL?] at hc

/-- The minor premise at position `pos` of a recursor of `P` whose minor premises `DeclsOf?`
checks: its stored domain `A` has `minorArity` leading `Π`. -/
theorem minorArity_eq {R : RecursorVal} {cvR : ConLeche.ConstantVal} (hcv : cvOf? R.toConstantVal = some cvR)
    {pos : Nat} {D : Expr} (hD : forallDom? pos R.type = some D) (hnm : NoMData D = true)
    {A : ConLeche.Expr} (hA : ConLeche.Expr.binderDom pos cvR.type = some A) :
    minorArity R.type pos = clPis A := by
  obtain ⟨ty, hty, rfl⟩ := cvOf?_eq_some hcv
  obtain ⟨cD, hcD, hb⟩ := forallDom?_toCL pos hD hty
  rw [hA, Option.some.injEq] at hb
  subst hb
  simp [minorArity, hD, forallArity_toCL hnm hcD]

/-- The constructor count of the members `ns` is the length of their constructor list. -/
theorem blockCtorCount_length {P : List ConstantInfo} : ∀ {ns : List Name} {k : Nat},
    blockCtorCount P ns = some k → (ctorsOf P ns).length = k
  | [], k, h => by simp only [blockCtorCount, Option.some.injEq] at h; subst h; rfl
  | n :: ns, k, h => by
    unfold blockCtorCount at h
    split at h
    · rename_i it m hf hm
      simp only [Option.some.injEq] at h
      subst h
      have := blockCtorCount_length hm
      simp only [ctorsOf] at this
      simp [ctorsOf, List.flatMap_cons, hf, this]
    · exact nomatch h

/-- The position of a constructor among the constructors of the members `ns`: the members before
its inductive's (`blockCtorCount`), then its index. -/
theorem ctorsOf_idxOf {P : List ConstantInfo} {ns : List Name} {j : Nat} {T : Name}
    {t : InductiveVal} {C : Name} {i before : Nat} (hnd : ((ctorsOf P ns).map Name.toCL).Nodup)
    (hj : ns[j]? = some T) (ht : findConst P T = some (.inductInfo t)) (hi : t.ctors[i]? = some C)
    (hb : blockCtorCount P (ns.take j) = some before) :
    before + i < (ctorsOf P ns).length ∧
      ((ctorsOf P ns).map Name.toCL).idxOf (Name.toCL C) = before + i := by
  have hjl : j < ns.length := (List.getElem?_eq_some_iff.mp hj).1
  have hsplit : ctorsOf P ns = ctorsOf P (ns.take j) ++ (t.ctors ++ ctorsOf P (ns.drop (j + 1))) := by
    have hns : ns.take j ++ T :: ns.drop (j + 1) = ns := by
      rw [← (List.getElem?_eq_some_iff.mp hj).2, ← List.drop_eq_getElem_cons hjl,
        List.take_append_drop]
    have := (show ctorsOf P (ns.take j ++ T :: ns.drop (j + 1)) =
        ctorsOf P (ns.take j) ++ (t.ctors ++ ctorsOf P (ns.drop (j + 1))) by
      simp [ctorsOf, List.flatMap_append, ht])
    rwa [hns] at this
  have hlb := blockCtorCount_length hb
  have hil : i < t.ctors.length := (List.getElem?_eq_some_iff.mp hi).1
  have hget : (ctorsOf P ns)[before + i]? = some C := by
    rw [hsplit, List.getElem?_append_right (by omega), List.getElem?_append_left (by omega)]
    simpa [hlb] using hi
  have hlt : before + i < (ctorsOf P ns).length := (List.getElem?_eq_some_iff.mp hget).1
  refine ⟨hlt, ?_⟩
  have := hnd.idxOf_getElem (before + i) (by simpa using hlt)
  obtain ⟨hlt', hget'⟩ := List.getElem?_eq_some_iff.mp hget
  simp only [List.getElem_map, hget'] at this
  exact this

/-- A stored definition has distinct level parameters (`RulesCanonical`). -/
theorem defn_nodup {env : ConLeche.Env} (hrc : RulesCanonical env = true) {n : ConLeche.Name}
    {cv : ConLeche.ConstantVal} {v : ConLeche.Expr} {hint : ConLeche.ReducibilityHint}
    (h : env.find? n = some (.defnInfo cv v hint)) : cv.levelParams.Nodup :=
  nodup_of_nodup (List.all_eq_true.mp hrc _ (ConLeche.Env.find?_mem h))

/-! ## The decode of a recognized `casesOn` -/

/-- **The stored records of a recognized `casesOn`**, at a constructor `C` of its inductive `iv`,
a member of a block of any size: the shipping recognizer `casesInfo?`
(`LeanToLambdaBox/Erasure/Pure.lean:107`) accepts `c = T.casesOn` with the value
`fun ps motive is t ms => T.rec ps motives' minors' is t`, the own minor of `C` (at the position
`off + cidx` of the recursor's arguments, `off` the parameters, the motives and the constructors
of the members before `T`) the wrapper `fun fs ihs => m_C fs` over the recursor's minor premise;
con-leche's fold stores that value at `c` (`ConLecheAccepts.find?_defn`, closed by
`CL ConLeche/Verify/EnvWF.lean:102 ConstWF`), the recursor `T.rec` (`ConLecheAccepts.find?_rec`)
and `C` under `T` (`ConLecheAccepts.blockStored`); `RulesCanonical` gives the rule for `C`
(`rule_decode`), whose minor premise is at `off + cidx` (the block's constructors in order,
`blockCtors`), and `DeclsOf?` (`blockShapeOK`) gives the recursor the block's counts and
`mdata`-free minor premises, so the wrapper binds as many hypotheses as the rule passes. `hsafe`:
the definition is safe, as `find?_defn` asks. Reference: `casesInfo?` on the stored records, the
rule shape of `CL ConLeche/Kernel/Inductives/GenRec.lean:189 classGenRule`. -/
theorem casesDecode {P : List ConstantInfo} {env : ConLeche.Env} (h : ConLecheAccepts P env)
    {c : Name} {iv : InductiveVal} (hc : casesOnOf? P c = some iv)
    (hsafe : ∀ d, findDecl P c = some (.defnInfo d) → d.safety = .safe)
    {C : Name} {cv : ConstructorVal} (hCm : C ∈ iv.ctors) (hC : findDecl P C = some (.ctorInfo cv)) :
    cv.induct = iv.name ∧ cv.numParams = iv.numParams ∧ iv.ctors[cv.cidx]? = some C ∧
    ∃ (cvD : ConLeche.ConstantVal) (val : ConLeche.Expr) (hint : ConLeche.ReducibilityHint)
      (rargs : List ConLeche.Expr) (cvR : ConLeche.ConstantVal) (mI rP : Nat)
      (isK : Bool) (rules : List ConLeche.RecRule) (cvj : ConLeche.ConstantVal)
      (rl : ConLeche.RecRule) (pos : Nat) (w : ConLeche.Expr) (ihs : List ConLeche.Expr),
      env.find? (Name.toCL c) = some (.defnInfo cvD val hint) ∧ val.looseBVarsBounded 0 = true ∧
      clLams val = (casesArity iv, ConLeche.Expr.mkAppN
        (.const (Name.toCL (mkRecName iv.name)) (cvD.levelParams.map .param)) rargs) ∧
      env.find? (Name.toCL (mkRecName iv.name)) = some (.recInfo cvR mI rP isK rules) ∧
      cvR.levelParams.length = cvD.levelParams.length ∧ clPis cvR.type = mI + 1 ∧ rP ≤ mI ∧
      rargs.length = mI + 1 ∧ rargs[mI]? = some (.bvar (casesArity iv - 1 - casesMajor iv)) ∧
      pos < rP ∧ rargs[pos]? = some w ∧
      clLams w = (cv.numFields + ihs.length, ConLeche.Expr.mkAppN
        (.bvar (cv.numFields + ihs.length + (casesArity iv - 1 - (casesMajor iv + 1 + cv.cidx))))
        (SemCases.fbv cv.numFields (cv.numFields + ihs.length))) ∧
      env.find? (Name.toCL C) =
        some (.ctorInfo cvj cv.numParams cv.numFields (Name.toCL iv.name)) ∧
      rules.find? (fun r => r.ctor == Name.toCL C) = some rl ∧ rl.nfields = cv.numFields ∧
      (∃ ihs' : List ConLeche.Expr, ihs'.length = ihs.length ∧
        clLams rl.rhs = (rP + cv.numFields, ConLeche.Expr.mkAppN
          (.bvar (cv.numFields + (rP - 1 - pos))) (SemCases.fbv cv.numFields cv.numFields ++ ihs'))) ∧
      mI = rP + iv.numIndices ∧ cvD.levelParams.Nodup ∧ rl.fire = .plain ∧
      ∀ i < iv.numParams, rargs[i]? = some (.bvar (casesArity iv - 1 - i)) := by
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
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, hlps⟩, -⟩, hmot⟩, hhd⟩, hlen⟩, hpar⟩, -⟩, hmin⟩, -⟩, hmaj⟩ := hok
  -- the block of `iv`
  obtain ⟨Hn, H, hH, hhead, hHall, hivm⟩ := h.head (findDecl_mem hiv).1
  have hHs := h.ind_safe (findDecl_mem hH).1
  obtain ⟨blk, p, hbH, -, -⟩ := h.block hH hhead hHs
  obtain ⟨hrsh, hmem⟩ := blockOf?_shape hbH
  have hiv' : findConst P iv.name = some (.inductInfo iv) := hiv
  obtain ⟨hivall, hivpar, hivc, r, hrm, hrall, hrname, hrmot, hrmin, hridx⟩ :=
    hmem iv.name hivm iv hiv'
  have hRmem := (findDecl_mem (P := P) hR).1
  have hRname : R.name = mkRecName iv.name := (findDecl_mem (P := P) hR).2
  have hRr : R = r := by
    have h1 : findDecl P r.name = some (.recInfo r) := findDecl_self hnd hrm
    have h2 : findDecl P (mkRecName iv.name) = some (.recInfo R) := hR
    rw [hrname, h2] at h1; simpa using h1
  subst r
  obtain ⟨hRpar, hRnm⟩ := hrsh R hRmem hrall
  -- the constructor
  obtain ⟨jC, hjC⟩ := List.getElem?_of_mem hCm
  obtain ⟨hCind, hCidx, hCpar, -⟩ := hivc jC C hjC cv hC
  subst hCidx
  refine ⟨hCind, by rw [hCpar, hivpar], hjC, ?_⟩
  -- the stored records
  obtain ⟨hbnd, hbc, hst⟩ := h.blockStored hH hhead
  obtain ⟨⟨cvT, caps, -, hfT, hcall, hcctors⟩, hctor⟩ := hst iv.name hivm iv hiv'
  obtain ⟨cvj, -, hfC⟩ := hctor C hCm cv hC
  have hd' : findDecl P (iv.name.str "casesOn") = some (.defnInfo d) := hd
  obtain ⟨cvD, val, hcvD, hval, hfD⟩ := h.find?_defn hd' (hsafe d hd')
  obtain ⟨cvR, rules, f, hcvR, -, hfR⟩ := h.find?_rec hH hhead hHs hRmem hrall
  rw [hRname] at hfR
  have hvcl := (((ConLeche.Semantics.checkDeclsPure_envWF hfold).consts _
    (ConLeche.Env.find?_mem hfD)).2.2.2.2.1 cvD val _ rfl).2.2.2
  obtain ⟨hpis, -, rl, A, ihs', hrl, hnf, hfire, hA, hlA, hrhs, -, -⟩ :=
    rule_decode hrc hfR hfT (by rw [hcctors]; exact List.mem_map_of_mem hCm) hfC
  -- the minor premise's position
  rw [hrall] at hbe
  have hjlt : H.all.idxOf iv.name < H.all.length := List.idxOf_lt_length_of_mem hivm
  have hjH : H.all[H.all.idxOf iv.name]? = some iv.name := by
    rw [List.getElem?_eq_getElem hjlt, List.getElem_idxOf hjlt]
  obtain ⟨hposlt, hidxC⟩ := ctorsOf_idxOf hbnd hjH hiv' hjC hbe
  have hminl := blockCtorCount_length hrmin
  have hq : R.numParams + R.numMotives + R.numMinors - (blockCtors env caps).length +
      (blockCtors env caps).idxOf (Name.toCL C) = R.numParams + R.numMotives + (before + cv.cidx) := by
    rw [hbc caps hcall, List.length_map, hminl, hidxC]; omega
  rw [hq] at hA hrhs
  obtain ⟨D, hD, hDnm⟩ := hRnm (before + cv.cidx) (by omega)
  have hLA := minorArity_eq hcvR hD hDnm hA
  have hpos : iv.numParams + R.numMotives + before + cv.cidx =
      R.numParams + R.numMotives + (before + cv.cidx) := by omega
  have hL : minorArity R.type (iv.numParams + R.numMotives + before + cv.cidx) =
      cv.numFields + ihs'.length := by rw [hpos, hLA, ← hlA]; omega
  obtain ⟨tyD, -, rfl⟩ := cvOf?_eq_some hcvD
  obtain ⟨tyR, -, rfl⟩ := cvOf?_eq_some hcvR
  -- the value's reading
  obtain ⟨cb, hcb, hlv⟩ := toCL?_peelLams _ hb hval
  rcases hsp : spine body with ⟨hd0, args⟩
  rw [hsp] at hhd hlen hmin hmaj hpar
  dsimp only at hhd hlen hmin hmaj hpar
  rw [spine_foldl hsp] at hcb
  obtain ⟨chd, rargs, hchd, hall, rfl⟩ := toCL?_foldl args hd0 hcb
  rw [isConstAt_eq hhd] at hchd
  simp only [toCL?, mapM_param, Option.map_eq_map, Option.map_some, Option.some.injEq] at hchd
  subst hchd
  rw [clLams_mkAppN rargs rfl] at hlv
  have hlen' := SemCases.forall₂_length hall
  -- the own minor of `C`
  have hjlt' : cv.cidx < iv.ctors.length := (List.getElem?_eq_some_iff.mp hjC).1
  obtain ⟨hal, haf⟩ := ctorAlts_spec ha
  have hmj := hmin cv.cidx (by omega)
  split at hmj
  rotate_left; · exact nomatch hmj
  rename_i w0 m hw0 hm
  rw [hw0, Option.getD_some] at hm
  rw [haf hjC hC] at hmj
  obtain ⟨as, rfl, hasl, hasb⟩ := isMinorBody_eq hmj
  obtain ⟨w, hw, hrw⟩ := SemCases.forall₂_getElem? hall hw0
  obtain ⟨cm, hcm, hlw⟩ := toCL?_peelLams _ hm hrw
  obtain ⟨cbv, cas, hcbv, hcas, rfl⟩ := toCL?_foldl as _ hcm
  simp only [toCL?, Option.some.injEq] at hcbv
  subst hcbv
  rw [forall₂_fbv hcas hasl hasb, clLams_mkAppN _ rfl, hL] at hlw
  rw [hpos] at hw
  -- the major
  obtain ⟨cmj, hcmj, hrmj⟩ := SemCases.forall₂_getElem? hall (isBVarAt_eq hmaj)
  simp only [toCL?, Option.some.injEq] at hrmj
  subst hrmj
  refine ⟨_, val, _, rargs, _, _, _, _, _, cvj, rl, _, w, ihs', hfD, hvcl, ?_, hfR, by simp [hlps],
    hpis, by omega, by omega, ?_, by omega, hw, ?_, hfC, hrl, hnf, ⟨ihs', rfl, hrhs⟩, by omega,
    defn_nodup hrc hfD, hfire, fun i hi => ?_⟩
  · rw [hlv, hlps, hRname]; simp [casesArity, casesMajor]
  · rw [hridx, hRpar, ← hivpar]; simpa [casesArity, casesMajor] using hcmj
  · rw [hlw]; simp [casesArity, casesMajor, Nat.add_assoc]
  · obtain ⟨ca, hca, hra⟩ := SemCases.forall₂_getElem? hall (isBVarAt_eq (hpar i hi))
    simp only [toCL?, Option.some.injEq] at hra
    rw [hca, ← hra]; simp [casesArity, casesMajor]

/-- The inductive of a recognized `casesOn` is the program's. -/
theorem casesOnOf?_ind {P : List ConstantInfo} {c : Name} {iv : InductiveVal}
    (hc : casesOnOf? P c = some iv) : findDecl P iv.name = some (.inductInfo iv) := by
  unfold casesOnOf? at hc
  split at hc
  · split at hc
    · rename_i iv' hiv'; cases hc; rw [← (findDecl_mem hiv').2] at hiv'; exact hiv'
    · exact nomatch hc
  · exact nomatch hc

/-- The ι case split's stored facts at a constructor application whose head is `C`, read at the
records the decode names. -/
theorem iotaNoCert_of {env : ConLeche.Env} {T C : Name} {m : Expr} {us : List Level}
    (hm : m.getAppFn = .const C us) (h : IotaNoCertAt env T m) {cvR : ConLeche.ConstantVal}
    {mI rP : Nat} {isK : Bool} {rules : List ConLeche.RecRule} {rl : ConLeche.RecRule}
    {cvC : ConLeche.ConstantVal} {nP nF : Nat} {ind : ConLeche.Name}
    (hR : env.find? (Name.toCL (mkRecName T)) = some (.recInfo cvR mI rP isK rules))
    (hrl : rules.find? (·.ctor == Name.toCL C) = some rl)
    (hC : env.find? (Name.toCL C) = some (.ctorInfo cvC nP nF ind)) :
    ConLeche.iotaNoCert env.find? isK ind (ConLeche.recFireLevelCount rl cvC.levelParams) = true := by
  obtain ⟨C', us', cvR', mI', rP', isK', rules', rl', cvC', nP', nF', ind', hg, hR', hrl', hC', hno⟩ := h
  rw [hm, Expr.const.injEq] at hg
  obtain ⟨rfl, rfl⟩ := hg
  rw [hR, Option.some.injEq, ConLeche.ConstantInfo.recInfo.injEq] at hR'
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hR'
  rw [hrl, Option.some.injEq] at hrl'
  subst hrl'
  rw [hC, Option.some.injEq, ConLeche.ConstantInfo.ctorInfo.injEq] at hC'
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hC'
  exact hno

/-- **The stored records of the ι step of a recognized `casesOn`** (`CasesIotaAt`), at the
constructor `C` of the major's value `mv` (`hmv`), its inductive `iv` a member of a block of any
size: the decode `casesDecode`, and the ι case split's case 2 by the stored facts, which the rule
premise `IotaNoCertAt` states at those records. `hcl` (`CtorsListed`): `C` is the constructor at
its index; `hsafe`: the definition is safe, as `find?_defn` asks. Reference: `casesInfo?`
(`LeanToLambdaBox/Erasure/Pure.lean:107`) on the stored records. -/
theorem _root_.EraseProof.ConLecheAccepts.casesIotaAt {P : List ConstantInfo} {env : ConLeche.Env}
    (h : ConLecheAccepts P env) (hcl : CtorsListed P) {c : Name} {iv : InductiveVal}
    (hc : casesOnOf? P c = some iv)
    (hsafe : ∀ d, findDecl P c = some (.defnInfo d) → d.safety = .safe)
    {C : Name} {cv : ConstructorVal} (hC : findDecl P C = some (.ctorInfo cv))
    (hCT : cv.induct = iv.name) {mv : Expr} {usC : List Level} (hmv : mv.getAppFn = .const C usC)
    (hnc : IotaNoCertAt env iv.name mv) :
    SemCases.CasesIotaAt env (Name.toCL c) (Name.toCL C) (casesArity iv) (casesMajor iv) cv.cidx
      cv.numParams cv.numFields := by
  obtain ⟨iv', hiv', hCidx, -⟩ := hcl C cv hC
  rw [hCT, casesOnOf?_ind hc, Option.some.injEq, ConstantInfo.inductInfo.injEq] at hiv'
  subst iv'
  obtain ⟨-, -, -, cvD, val, hint, rargs, cvR, mI, rP, isK, rules, cvj, rl, pos, w, ihs, h1, h2, h3,
    h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, -⟩ :=
    casesDecode h hc hsafe (List.mem_of_getElem? hCidx) hC
  exact ⟨cvD, val, hint, _, rargs, cvR, mI, rP, isK, rules, cvj, _, rl, pos, w, ihs, h1, h2, h3, h4,
    h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, iotaNoCert_of hmv hnc h4 h14 h13⟩

/-- **The stored records of the ι step of a recognized `casesOn` on a frozen discriminant**
(`CasesFrozenAt`), at the one constructor `cn` of its inductive `iv`: the decode `casesDecode`
at the alternative `0`, the ι case split's case 2 by the stored facts for a constructor without
fields (the rule premise `IotaNoCertAt`); for one with fields, no indices (the rule premise),
distinct level parameters of the `casesOn` constant and a plain rule (`RulesCanonical`), the
parameters passed on (`casesInfo?`). `hsafe`: the definition is safe, as `find?_defn` asks.
Reference: `casesInfo?` (`LeanToLambdaBox/Erasure/Pure.lean:107`) on the stored records. -/
theorem _root_.EraseProof.ConLecheAccepts.casesFrozenAt {P : List ConstantInfo}
    {env : ConLeche.Env} (h : ConLecheAccepts P env) {c : Name} {iv : InductiveVal}
    (hc : casesOnOf? P c = some iv)
    (hsafe : ∀ d, findDecl P c = some (.defnInfo d) → d.safety = .safe)
    {cn : Name} (hcn : iv.ctors = [cn]) {cv : ConstructorVal}
    (hC : findDecl P cn = some (.ctorInfo cv)) {us : List Level}
    (hz : cv.numFields = 0 → IotaNoCertAt env iv.name (.const cn us))
    (hidx : 0 < cv.numFields → iv.numIndices = 0) :
    SemCases.CasesFrozenAt env (Name.toCL c) (Name.toCL (mkRecName iv.name)) (Name.toCL cn)
      (casesArity iv) (casesMajor iv) iv.numParams cv.numFields := by
  obtain ⟨-, hpar, hcidx, cvD, val, hint, rargs, cvR, mI, rP, isK, rules, cvj, rl, pos, w, ihs, h1,
    h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, hmI, hnd, hfire, hps⟩ :=
    casesDecode h hc hsafe (by rw [hcn]; exact List.mem_singleton_self _) hC
  have hc0 : cv.cidx = 0 := by
    rw [hcn] at hcidx
    match h' : cv.cidx, hcidx with
    | 0, _ => rfl
    | _ + 1, hx => simp at hx
  rw [hc0, Nat.add_zero] at h12
  rw [hpar] at h13
  refine ⟨cvD, val, hint, rargs, cvR, mI, rP, isK, rules, cvj, _, rl, pos, w, ihs, h1, h2, h3, h4,
    h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, fun hz0 =>
      iotaNoCert_of (us := us) rfl (hz hz0) h4 h14 h13, fun hpos => ⟨by have := hidx hpos; omega,
      hnd, by unfold casesMajor; omega, hps, hfire⟩⟩

/-- **The stored projection table of a structure-like member** (`ProjAt`): con-leche's table of
`S` at field `i`, wherever it has one (`CL ConLeche/Kernel/Env.lean:482 findProj?`), names the
constructor `C` at index `0` of `S` with its parameter and field counts (`TablesCanonical`, the
former's constructor list `ConLecheAccepts.blockStored`). Reference: the table of
`CL ConLeche/Kernel/Env.lean:255 ProjTable`, the constructor `MR P/PCUICWcbvEval.v:264 eval_proj`
reads. -/
theorem _root_.EraseProof.ConLecheAccepts.projAt {P : List ConstantInfo} {env : ConLeche.Env}
    (h : ConLecheAccepts P env) (hcl : CtorsListed P) {S C : Name} {cv : ConstructorVal}
    (hC : findDecl P C = some (.ctorInfo cv)) (hCT : cv.induct = S) (hc0 : cv.cidx = 0) {i : Nat}
    {entry : ConLeche.ProjEntry} (hfp : env.findProj? (Name.toCL S) i = some entry) :
    SemCases.ProjAt env (Name.toCL S) i (Name.toCL C) cv.numParams cv.numFields := by
  obtain ⟨-, -, -, -, htc⟩ := id h
  obtain ⟨sv, hsv, hCidx, -⟩ := hcl C cv hC
  rw [hCT] at hsv
  obtain ⟨Hn, H, hH, hhead, -, hsm⟩ := h.head (findDecl_mem hsv).1
  obtain ⟨-, -, hst⟩ := h.blockStored hH hhead
  have hsv' : findConst P S = some (.inductInfo sv) := hsv
  have hSn : sv.name = S := (findDecl_mem hsv).2
  obtain ⟨⟨cvT, caps, -, hfT, -, hcc⟩, hctor⟩ := hst S (hSn ▸ hsm) sv hsv'
  rw [hc0] at hCidx
  obtain ⟨cvj, -, hfC⟩ := hctor C (List.mem_of_getElem? hCidx) cv hC
  have hfp0 := hfp
  unfold ConLeche.Env.findProj? at hfp
  split at hfp
  rotate_left; · exact nomatch hfp
  rename_i tbl htbl
  split at hfp
  rotate_left; · exact nomatch hfp
  simp only [Option.some.injEq] at hfp
  subst hfp
  have htm := ConLeche.Env.findTable?_mem htbl
  have htc' := List.all_eq_true.mp htc tbl htm.1
  rw [htm.2.1, hfT] at htc'
  simp only [Bool.and_eq_true, beq_iff_eq] at htc'
  obtain ⟨hcaps, htcC⟩ := htc'
  have htC : tbl.ctor = Name.toCL C := by
    rw [hcc] at hcaps
    have h0 := congrArg (·[0]?) hcaps
    simp only [List.getElem?_map, hCidx, Option.map_some] at h0
    simpa using h0.symm
  rw [htC, hfC] at htcC
  simp only [Bool.and_eq_true, beq_iff_eq] at htcC
  obtain ⟨⟨⟨hnP, hnF⟩, hlp⟩, hpp⟩ := htcC
  refine ⟨_, cvj, _, _, _, hfp0, htC, hnP.symm, hnF.symm, hlp.symm, hfC, hpp⟩

end Decode

end EraseProof
