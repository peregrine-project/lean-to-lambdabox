import LeanToLambdaBox.VisitExprRefines.Motives
-- `runClosedW_concl`: the three run facts as one `RunClosedW` instance, which F-ACC's
-- `Erasure.firstNonProofField` walk is stepped against here as the term walk is there.
import LeanToLambdaBox.VisitExprRefines.Step.Env

/-!
# The pass-facing steps of the bridge induction

Eight of the eighteen members: the literal tower that rebuilds a `Nat` through the
constructor member, the constructor block, the projection, the two η entry points, the two η
loops, and the `case` node itself. Each step concludes its motive through an introduction
lemma of `ErasesLB`/`ErasesLBFix` read at the reader's fixvar mode, never by re-proving a
`Lower` fact inline.

Each concludes the induction's own `Stepᵢ`. The emitted `.construct`, `.proj` and `.case`
nodes read their `InductiveId` and their argument masks out of the inductive registry, and
`BridgeInv.indcanon` is what says the registry is the model's; the entry a registration
leaves behind is `pass_register_inductive_entry`.

No step carries a named `Prop` premise: the primitives' generator bounds are
`ErasureSpec.prim_monotone` and the constructor and block readings of a declaration are
`ErasureSpec.block_adequate`. Steps 3 and 17 take the wave's `UpstreamAsks` binder, and each
takes one unnamed clause its bundle is short of — `iv.name ∈ iv.all` for step 3, and the two
`Lean.CasesInfo` agreements `CasesInfoAgrees` does not record for step 17. Both belong in
`BlockAdequate` and `CasesInfoAgrees` respectively; each theorem's docstring says so.
-/
namespace LeanToLambdaBox

open Lean Lean4Lean Erasure Witness Lean.Order

set_option synthInstance.maxSize 4000

/-! ## Spine plumbing -/

/-- Spine reconstruction, at the list the composite's introduction lemmas fold over. -/
theorem pass_getAppArgs_foldl (e : Expr) :
    e.getAppArgs.toList.foldl Expr.app e.getAppFn = e := by
  rw [Lean.Expr.getAppArgs_toList, ← Lean.Expr.mkAppList_eq_foldl,
    Lean.Expr.mkAppList_getAppArgsList]

/-- Spine reconstruction at `srcSpine`, which is what the motives are stated at. -/
theorem pass_srcSpine_self {e : Expr} {cn : Name} {us : List Level}
    (h : e.getAppFn = .const cn us) : srcSpine (.const cn us) e.getAppArgs = e := by
  rw [srcSpine, ← h]; exact pass_getAppArgs_foldl e

/-- The retained-field index of a projection: with pruning off, the mask is all-`keep`, so the
count of retained fields below `i` is `i`. -/
theorem pass_count_keep_prefix {nf i : Nat} (h : i ≤ nf) :
    Array.count ConstructorArgRelevance.keep
      (Std.Slice.toArray (Array.toSubarray (Array.replicate nf ConstructorArgRelevance.keep) 0 i))
      = i := by
  have key : Std.Slice.toArray
      (Array.toSubarray (Array.replicate nf ConstructorArgRelevance.keep) 0 i)
      = Array.replicate i ConstructorArgRelevance.keep := by
    apply Array.ext'
    rw [← Subarray.toArray_eq_sliceToArray, ← Subarray.toArray_toList, Subarray.toList_eq]
    simp
    omega
  rw [key, Array.count, ← Array.countP_toList]
  simp only [Array.toList_replicate, List.countP_eq_length_filter, List.filter_replicate,
    if_pos (by decide : (ConstructorArgRelevance.keep == ConstructorArgRelevance.keep) = true),
    List.length_replicate]


/-! ## Array slices, at the shapes the constructor branch builds -/

/-- The clamped window a `Subarray` records is the window `Array.extract` takes. -/
theorem pass_take_drop_min {α : Type} (L : List α) (lo hi : Nat) :
    List.take (min hi L.length - min lo (min hi L.length))
        (List.drop (min lo (min hi L.length)) L)
      = List.take (hi - lo) (List.drop lo L) := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop]; omega
  · intro i h1 h2
    simp only [List.length_take, List.length_drop] at h1
    simp only [List.getElem_take, List.getElem_drop]
    congr 1
    omega

/-- A materialised array slice is the extract of its window. -/
theorem pass_slice_toArray {α : Type} (a : Array α) (lo hi : Nat) :
    Std.Slice.toArray (a.toSubarray lo hi) = a.extract lo hi := by
  rw [← Subarray.toArray_eq_sliceToArray]
  apply Array.ext'
  rw [← Subarray.toArray_toList, Subarray.toList_eq]
  simp only [Array.start_toSubarray, Array.stop_toSubarray, Array.array_toSubarray,
    Array.toList_extract, List.extract_eq_take_drop]
  exact pass_take_drop_min _ _ _

/-- An all-`keep` mask retains every argument it covers: the configuration pins constructor
argument pruning off, so `Erasure.filter` is the identity on the field window. -/
theorem pass_filter_replicate_keep {α : Type} (n : Nat) (arr : Array α) (h : arr.size ≤ n) :
    Erasure.filter (Array.replicate n ConstructorArgRelevance.keep) arr = arr := by
  apply Array.ext'
  simp only [Erasure.filter, Array.toList_filterMap, Array.toList_zip, Array.toList_replicate]
  have key : ∀ (l : List α) (m : Nat), l.length ≤ m →
      List.filterMap (fun p => match p.1 with
        | ConstructorArgRelevance.erase => none
        | ConstructorArgRelevance.keep => some p.2)
        ((List.replicate m ConstructorArgRelevance.keep).zip l) = l := by
    intro l
    induction l with
    | nil => intro m _; simp
    | cons a as ih =>
      intro m hm
      cases m with
      | zero => simp at hm
      | succ k =>
        simp only [List.replicate_succ, List.zip_cons_cons, List.filterMap_cons]
        rw [ih k (by simpa using hm)]
  exact key _ _ (by simpa using h)


/-! ## The alternatives loop's plumbing

`Erasure.visitCases` fills the alternatives with a *parallel* `for` over three collections: the
index range, the elaborator's per-alternative metadata and the registered argument masks. The
accumulator therefore threads two `Std.Stream` states beside the output array, and these are
the four facts a prefix-indexed invariant needs about them.
-/

/-- A total array read is the total read of its list. -/
theorem pass_getElem!_toList {α : Type} [Inhabited α] (a : Array α) (k : Nat) (h : k < a.size) :
    a[k]! = a.toList[k]! := by
  rw [getElem!_pos a k h, getElem!_pos a.toList k (by simpa using h)]
  simp

/-- One step of the `Subarray` stream `Erasure.visitCases`' parallel `for` threads for the
alternative metadata: at a position inside the window it yields that element and advances the
start. Stated componentwise, since the record carries its own bounds proofs. -/
theorem pass_subarray_next {α : Type} [Inhabited α] {st : Subarray α} {a : Array α} {k n : Nat}
    (harr : st.array = a) (hst : st.start = k) (hsp : st.stop = n) (h : k < n) :
    ∃ st', Std.Stream.next? st = some (a[k]!, st') ∧
      st'.array = a ∧ st'.start = k + 1 ∧ st'.stop = n := by
  subst harr; subst hst; subst hsp
  have hlt2 : st.start < st.array.size := by
    have h1 := st.internalRepresentation.stop_le_array_size
    have h' : st.internalRepresentation.start < st.internalRepresentation.stop := h
    show st.internalRepresentation.start < st.internalRepresentation.array.size
    omega
  unfold Std.Stream.next?
  simp only [Std.instStreamSubarray]
  rw [dif_pos h, getElem!_pos st.array st.start hlt2]
  exact ⟨_, rfl, rfl, rfl, rfl⟩

/-- One step of the `List` stream the same `for` threads for the argument masks. -/
theorem pass_list_next {α : Type} [Inhabited α] {l : List α} {k : Nat} (h : k < l.length) :
    Std.Stream.next? (l.drop k) = some (l[k]!, l.drop (k + 1)) := by
  rw [List.drop_eq_getElem_cons h]
  show some _ = _
  rw [getElem!_pos l k h]

/-- The alternatives' index range, materialised: one index per alternative. -/
theorem pass_rco_size (r : Std.Rco Nat) : r.toArray.size = r.upper - r.lower := by
  show (r.lower...r.upper).toArray.size = _
  simp

/-- The index the parallel `for` is at, read off the processed prefix: the loop's `i` at the
`k`-th iteration is `lower + k`, and `k` is below the range's width. -/
theorem pass_rco_split {r : Std.Rco Nat} {pre post : List Nat} {x : Nat}
    (h : r.toArray.toList = pre ++ x :: post) :
    x = r.lower + pre.length ∧ pre.length < r.upper - r.lower := by
  have hlen : r.toArray.toList.length = r.upper - r.lower := by
    rw [Array.length_toList, pass_rco_size]
  have hlt : pre.length < r.upper - r.lower := by rw [← hlen, h]; simp
  refine ⟨?_, hlt⟩
  have h0 : r.toArray.toList[pre.length]? = some x := by
    rw [h, List.getElem?_append_right (Nat.le_refl _)]
    simp
  rw [Array.getElem?_toList] at h0
  have h1 : r.toArray[pre.length]? = some (r.lower + pre.length) := by
    show (r.lower...r.upper).toArray[pre.length]? = _
    rw [Std.Rco.getElem?_toArray_eq]
    simp
    omega
  rw [h1] at h0
  exact (Option.some.inj h0).symm


/-! ## The model reading of the table's inductive column

`ErasureSpec.decl_adequate` reads a declared constant into `env.constants`; the three
`Expr.const` readings `Erases` distinguishes — a constructor, a type former, a plain constant —
are not among what it gives. `ErasureSpec.block_adequate` does, and the table pin names the
kernel declaration each reading is about.
-/

/-- Every constructor of a tabled inductive type is the model's constructor of it, at the
index the table records: the pin names the kernel `ConstructorVal` and
`BlockAdequate.ctor` reads it into the model. -/
theorem pass_ctorOf_of_tabled {lenv : Environment} {env : VEnv} {Us : List Name}
    {gw : Void IO.RealWorld → NameGenerator} {tbl : SourceTable}
    (P : ErasureSpec lenv env Us gw) (htbl : SourceTableAdequate lenv tbl)
    {I : Name} {Ir : ReifiedInduct} {c : ReifiedCtor}
    (hind : tbl.ind? I = some Ir) (hc : c ∈ Ir.ctors) : CtorOf env c.name I c.cidx := by
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hcs⟩ := htbl.inds _ Ir (mem_of_lookup hind)
  obtain ⟨cv, hcvf, _, hcidx, _, _, _, _, hcind⟩ := hcs j c hj
  have h := P.block_adequate.ctor c.name cv hcvf
  rwa [hcind, hcidx] at h

variable {env : VEnv} {Us : List Name} {Γ : GlobalDeclarations} {Δ : VLCtx}
variable {kns : List Kername} {ids : List FVarId}

/-! ## The two introduction lemmas, at either fixvar mode -/

/-- `ErasesLB.lit` read through the reader's fixvar mode. -/
theorem ErasesLBMode.lit {tbl : SourceTable} {ctx : ErasureContext}
    {Γspec : GlobalDeclarations} {l : Literal} {t : LBTerm} (hcl : env.ContainsLits l)
    (h : ErasesLBMode tbl ctx env Us Γspec Δ l.toConstructor t) :
    ErasesLBMode tbl ctx env Us Γspec Δ (.lit l) t :=
  ⟨fun hfx => .lit hcl (h.1 hfx), fun nms is hfx => .lit hcl (h.2 nms is hfx)⟩

/-- `ErasesLB.proj` read through the reader's fixvar mode. -/
theorem ErasesLBMode.proj {tbl : SourceTable} {ctx : ErasureContext}
    {Γspec : GlobalDeclarations} {S : Name} {i : Nat} {e : Expr} {t : LBTerm}
    {iid : InductiveId} {np nf : Nat}
    (hs : IndInfo env S iid np [nf]) (hinf : InformativeInd env S) (hi : i < nf)
    (h : ErasesLBMode tbl ctx env Us Γspec Δ e t) :
    ErasesLBMode tbl ctx env Us Γspec Δ (.proj S i e) (.proj ⟨iid, np, i⟩ t) :=
  ⟨fun hfx => .proj hs hinf hi (h.1 hfx), fun nms is hfx => .proj hs hinf hi (h.2 nms is hfx)⟩


/-- `ErasesLB.cases` read through the reader's fixvar mode. -/
theorem ErasesLBMode.cases {tbl : SourceTable} {ctx : ErasureContext}
    {Γspec : GlobalDeclarations} {con : Name} {us : List Level} {vc : VConstant}
    {iid : InductiveId} {np dp : Nat} {nfs : List Nat} {argsL : List Expr}
    {disc : LBTerm} {alts : List (List BinderName × LBTerm)}
    (hE : ElimDecl Γspec (toKername con) iid np dp nfs)
    (hcst : env.constants con = some vc) (hco : ConstOrigin env con) (henv : env.WF)
    (hclass : ∀ c vc', env.constants c = some vc' → (∃ J k, CtorOf env c J k) ∨
      (∃ iid' np' nfs', IndInfo env c iid' np' nfs') ∨ ConstOrigin env c)
    (hΔ : VLCtx.WF env Us.length Δ)
    (hpre : ∀ a ∈ argsL.take dp, ∃ ve, TrExprS env Us Δ a ve)
    (hppi : ∀ a ∈ argsL.take dp, ProjInfo env a)
    (hlen : argsL.length = dp + 1 + nfs.length)
    (hd : ErasesLBMode tbl ctx env Us Γspec Δ argsL[dp]! disc)
    (hmlen : (argsL.drop (dp + 1)).length = nfs.length) (halen : alts.length = nfs.length)
    (hm : ∀ i, i < nfs.length →
      ErasesLBAltMode tbl ctx env Us Γspec Δ nfs[i]! (argsL.drop (dp + 1))[i]! alts[i]!) :
    ErasesLBMode tbl ctx env Us Γspec Δ (argsL.foldl Expr.app (.const con us))
      (.case (iid, np) disc alts) :=
  ⟨fun hfx => ErasesLB.cases hE hcst hco henv hclass hΔ hpre hppi hlen (hd.1 hfx)
      ⟨hmlen, halen, fun i hi => (hm i hi).1 hfx⟩,
    fun nms ids hfx => ErasesLBFix.cases hE hcst hco henv hclass hΔ hpre hppi hlen
      (hd.2 nms ids hfx) ⟨hmlen, halen, fun i hi => (hm i hi).2 nms ids hfx⟩⟩

/-! ## Threading the generator through a prefix step -/

/-- A refinement established after a generator-advancing prefix is one at the entry point. -/
theorem pass_runRefines_le {env : VEnv} {Us : List Name} {tbl : SourceTable}
    {ctx : ErasureContext} {Δ : VLCtx} {s s' : ErasureState} {g g₁ g' : NameGenerator}
    {e : Expr} {t : LBTerm} (hle : g ≤ g₁)
    (h : RunRefines env Us tbl ctx Δ s s' g₁ g' e t) :
    RunRefines env Us tbl ctx Δ s s' g g' e t :=
  ⟨h.1, h.2.1, NameGenerator.LE.trans hle h.2.2.1, h.2.2.2⟩

/-! ## Step 2 — `Erasure.visitLiteral` -/

/-- Nothing is δ-reachable from a literal: it names no constant, so the fragment's body clause
is vacuous there. -/
theorem pass_lit_not_reaches {tbl : SourceTable} {l : Literal} {c : Name}
    (h : Reaches tbl (.lit l) c) : False := by
  induction h with
  | root hc => simp [constNames] at hc
  | body _ _ _ ih => exact ih

/-- A `Nat` literal is inside the fragment whenever the peano tower is available and the table
separates its own kernames — the latter being a condition on the table, which the step reads
off the fragment premise its own subject carries. -/
theorem pass_supported_lit {env : VEnv} {tbl : SourceTable} {n : Nat} (hpe : PeanoReady env)
    (hpb : peanoReadyB tbl = true)
    (hkn : ∀ m m' : Name, Tabled tbl m → Tabled tbl m' →
      toKername m = toKername m' → m = m') : Supported env tbl (.lit (.natVal n)) where
  term := .natLit hpe hpb
  bodies _ _ hr _ := absurd hr pass_lit_not_reaches
  kernames := hkn

/-- The two kernel constructor indices `Erasure.visitLiteral`'s peano arm rebuilds, read off
the table's own peano verdict. -/
theorem pass_peano_ctors {tbl : SourceTable} (h : peanoReadyB tbl = true) :
    ∃ I : ReifiedInduct, tbl.ind? ``Nat = some I ∧
      (∃ c ∈ I.ctors, c.name = ``Nat.zero ∧ c.cidx = 0) ∧
      (∃ c ∈ I.ctors, c.name = ``Nat.succ ∧ c.cidx = 1) := by
  simp only [peanoReadyB] at h
  split at h
  · rename_i I hI
    simp only [Bool.and_eq_true, List.any_eq_true] at h
    obtain ⟨⟨cz, hzm, hz⟩, ⟨cs, hsm, hs⟩⟩ := h
    simp only [beq_iff_eq] at hz hs
    exact ⟨I, hI, ⟨cz, hzm, hz.1, hz.2⟩, ⟨cs, hsm, hs.1, hs.2⟩⟩
  · exact Bool.noConfusion h

/-- The peano arm rebuilds the literal as its kernel unfolding, one `Erasure.visitConstructor`
call per `succ`: the case is `ErasesLB.lit` over the constructor motive, and the recursion is
carried by the fixpoint induction rather than by a measure on the literal. -/
theorem step_visitLiteral {lenv : Environment} {env : VEnv} {tbl : SourceTable}
    {cfg : ErasureConfig} {gw : Void IO.RealWorld → NameGenerator} :
    Step2 lenv env tbl cfg gw := by
  intro P₀ htbl hcfg _hcb vCtor h3
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
      have hgo := h3 _ _ _ _ _ _ _ _ _ _ hrun _ Δ ([] : List Level) hinv ⟨_, _, hcz⟩
        (fun i hi => absurd hi (by simp))
      refine ⟨hgo.1, hgo.2.1, hgo.2.2.1, fun Γspec hspec => ?_⟩
      refine ErasesLBMode.lit hcl ?_
      have := hgo.2.2.2 Γspec hspec
      simpa [srcSpine, Literal.toConstructor, Expr.natLitToConstructor, Expr.natZero] using this
    | succ m =>
      simp only [hpe] at hrun
      have hinner : ∃ ve', TrExprS env Us Δ (.lit (.natVal m)) ve' := by
        cases htrC with | app _ _ _ htra => exact ⟨_, htra⟩
      have hargs : ArgsOk env Us tbl Δ #[Expr.lit (.natVal m)] := by
        intro i hi
        have hi0 : i = 0 := by simpa using hi
        subst hi0
        exact ⟨pass_supported_lit hpeano hpeanoB hsup.kernames, hinner⟩
      have hgo := h3 _ _ _ _ _ _ _ _ _ _ hrun _ Δ ([] : List Level) hinv ⟨_, _, hcs⟩ hargs
      refine ⟨hgo.1, hgo.2.1, hgo.2.2.1, fun Γspec hspec => ?_⟩
      refine ErasesLBMode.lit hcl ?_
      have := hgo.2.2.2 Γspec hspec
      simpa [srcSpine, Literal.toConstructor, Expr.natLitToConstructor, Expr.natSucc] using this


/-! ## The registration a `.construct`, `.proj` or `.case` node reads

`Erasure.register_inductive` answers out of the *inductive registry*: at a hit the identifier
the run reports is whatever the state holds, and at a miss it is the entry the cold branch
mints for `indinfo.name`. `BridgeInv.indcanon` says the registry is the model's;
`pass_register_inductive_entry` says the answer is the entry the state ends up holding, which
is what puts the two together.
-/

/-- The block position of a constructor, and the constructor at a block position. The block
`CtorOf` exhibits and the one `IndArity` exhibits are the same block (ask 2) and the same type
former inside it, so the index is in range and the name at it is determined. -/
theorem pass_ctorOf_index {env : VEnv} (A : UpstreamAsks env) {c I : Name} {k np : Nat}
    {nfs : List Nat} (h : CtorOf env c I k) (ha : IndArity env I np nfs) :
    k < nfs.length ∧ ∀ c', CtorOf env c' I k → c' = c := by
  obtain ⟨ds, env₀, decl, t, ctor, hds, hd, hle, hmem, hname, hk, hcn⟩ := h
  obtain ⟨decl', hblk', t', ht', hname', hnp', hnfs⟩ := ha.indBlockBelow
  have hblk : IndBlockBelow env decl := ⟨ds, env₀, hds, hle, hd⟩
  obtain rfl : decl = decl' := indBlock_uniq A hblk hblk' ⟨t, hmem, hname⟩ ⟨t', ht', hname'⟩
  obtain rfl : t = t' := indBlockBelow_type_uniq hblk hmem ht' (hname.trans hname'.symm)
  subst hnfs
  refine ⟨?_, ?_⟩
  · rcases List.getElem?_eq_some_iff.mp hk with ⟨hlt, -⟩
    simpa [ctorFieldCounts] using hlt
  · rintro c' ⟨ds₂, env₂, decl₂, t₂, ctor₂, hds₂, hd₂, hle₂, hmem₂, hname₂, hk₂, hcn₂⟩
    have hblk₂ : IndBlockBelow env decl₂ := ⟨ds₂, env₂, hds₂, hle₂, hd₂⟩
    obtain rfl : decl₂ = decl :=
      indBlock_uniq A hblk₂ hblk ⟨t₂, hmem₂, hname₂⟩ ⟨t, hmem, hname⟩
    obtain rfl : t₂ = t := indBlockBelow_type_uniq hblk hmem₂ hmem (hname₂.trans hname.symm)
    rw [hk] at hk₂
    cases hk₂
    rw [← hcn, ← hcn₂]

/-- **The field count the registry indexes by is the constructor's own.** The model list `nfs`
and the kernel block `iv` agree position by position (`KernelFields`), and the position of `c`
is determined by `pass_ctorOf_index`. -/
theorem pass_kernelFields_at {lenv : Environment} {env : VEnv} {Us : List Name}
    {gw : Void IO.RealWorld → NameGenerator} (P : ErasureSpec lenv env Us gw)
    (A : UpstreamAsks env) {c : Name} {cv : ConstructorVal} {iv : InductiveVal} {np : Nat}
    {nfs : List Nat} (hcvf : lenv.find? c = some (.ctorInfo cv)) (hivn : iv.name = cv.induct)
    (ha : IndArity env cv.induct np nfs) (hkf : KernelFields lenv iv nfs) :
    nfs[cv.cidx]? = some cv.numFields := by
  have hct : CtorOf env c cv.induct cv.cidx := P.block_adequate.ctor c cv hcvf
  obtain ⟨hlt, hnm⟩ := pass_ctorOf_index A hct ha
  obtain ⟨hlen, hfields⟩ := hkf
  obtain ⟨c', hc'⟩ : ∃ c', iv.ctors[cv.cidx]? = some c' := by
    cases hc : iv.ctors[cv.cidx]? with
    | none => exact absurd (List.getElem?_eq_none_iff.mp hc) (by omega)
    | some c' => exact ⟨c', rfl⟩
  obtain ⟨cv', hcvf', hnfj, hind', hcidx', -⟩ := hfields cv.cidx c' hc'
  have hct' : CtorOf env c' cv.induct cv.cidx := by
    have h := P.block_adequate.ctor c' cv' hcvf'
    rw [hind', hivn, hcidx'] at h
    exact h
  have hc'c : c' = c := hnm c' hct'
  subst hc'c
  have : cv' = cv := by
    rw [hcvf] at hcvf'
    injection hcvf' with h1
    injection h1 with h2
    exact h2.symm
  subst this
  exact hnfj

/-- **The entry a registration leaves behind is the value it answers.** At a hit that is the
entry already there; at a miss the cold branch inserts one entry per member of `indinfo.all`
and answers at `indinfo.name`, which is a member of its own block. Under `ConfigPinned` the
`@[extern]` and pruning arms of the constructor loop are dead, so that loop leaves the
registry alone and only the per-member `modify` writes to it. -/
theorem pass_register_inductive_entry {lenv : Environment} {env : VEnv} {Us : List Name}
    {gw : Void IO.RealWorld → NameGenerator} (P : ErasureSpec lenv env Us gw)
    {indinfo : InductiveVal}
    (hdecl : lenv.find? indinfo.name = some (.inductInfo indinfo))
    (hself : indinfo.name ∈ indinfo.all)
    {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
    {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
    {r : InductiveId × InductiveArgMasks} {s' : ErasureState} {w' : Void IO.RealWorld}
    (hcfg : ConfigPinned ctx.config)
    (hrun : Erasure.register_inductive indinfo s ctx cctx ref w = .ok (r, s') w') :
    s'.inductives.get? indinfo.name = some r := by
  have hext : ctx.config.extern = Config.Extern.preferLogical := hcfg.2.1
  have hpr : ctx.config.remove_irrel_constr_args = false := hcfg.2.2.2.1
  cases hhit : s.inductives.get? indinfo.name with
  | some rc0 =>
    obtain ⟨hr, hs, -⟩ := run_register_inductive_hit_ok hhit hrun
    subst hr
    subst hs
    exact hhit
  | none =>
    unfold Erasure.register_inductive at hrun
    simp only [] at hrun
    rw [run_bind_ok] at hrun
    obtain ⟨s0, sA, wA, hget, hk⟩ := hrun
    rw [run_get] at hget
    cases hget
    rw [hhit] at hk
    simp only [] at hk
    rw [run_bind_ok] at hk
    obtain ⟨ug, sG, wG, hguard, hk⟩ := hk
    obtain ⟨hsG, hwG, -⟩ := run_checkIndKernameFresh_ok hguard
    rw [hsG, hwG] at hk
    rw [run_bind_ok] at hk
    obtain ⟨bodies, sM, wM, hmap, htail⟩ := hk
    rw [run_bind_ok] at htail
    obtain ⟨u, sN, wN, hmod, htail2⟩ := htail
    rw [run_modify] at hmod
    cases hmod
    rw [run_bind_ok] at htail2
    obtain ⟨sX, sY, wY, hget2, hp⟩ := htail2
    rw [run_get] at hget2
    cases hget2
    rw [run_pure] at hp
    cases hp
    have key := run_list_mapM_ok ctx cctx ref
      (P := fun pre _outs s₁ _ =>
        ∀ p ∈ pre, p.1 = indinfo.name → (s₁.inductives.get? indinfo.name).isSome)
      (by simp) ?step hmap
    · obtain ⟨p, hp, hp1⟩ : ∃ p ∈ indinfo.all.zipIdx, p.1 = indinfo.name :=
        List.mem_map.mp (by rw [List.zipIdx_map_fst]; exact hself)
      have hsome := key p hp hp1
      show sM.inductives.get? indinfo.name = some sM.inductives[indinfo.name]!
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
      have hv' : sM.inductives[indinfo.name]? = some v := hv
      rw [hv, Std.HashMap.getElem!_eq_get!_getElem?, hv']
      rfl
    case step =>
      intro pre x post outs sP wP b sQ wQ hL hP hbody
      rw [run_bind_ok] at hbody
      obtain ⟨ci, sa, wa, hci, hrest⟩ := hbody
      have hsa : sa = sP := run_getConstInfo_state sP ctx cctx ref wP hci
      subst hsa
      have key : (∀ n : Name, (sa.inductives.get? n).isSome → (sQ.inductives.get? n).isSome) ∧
          ((∃ iv0 : InductiveVal, ci = .inductInfo iv0) →
            (sQ.inductives.get? x.1).isSome) := by
        split at hrest
        case _ ivv =>
          rw [run_bind_ok] at hrest
          obtain ⟨res, sb, wb, hctors, hrest2⟩ := hrest
          have hinds : sb.inductives = sa.inductives := by
            refine run_list_mapM_ok ctx cctx ref
              (P := fun _ _ s₁ _ => s₁.inductives = sa.inductives) rfl ?inner hctors
            case inner =>
              intro pre' cn post' outs' sA' wA' bres sB' wB' hL' hP' hb
              rw [run_bind_ok] at hb
              obtain ⟨envv, se, we, henv, h2⟩ := hb
              have hse : se = sA' := run_getEnv_state sA' ctx cctx ref wA' henv
              subst hse
              rw [run_bind_ok] at h2
              obtain ⟨c1, sr, wr, hread, h3⟩ := h2
              rw [run_read] at hread
              cases hread
              have hcond : (isExtern envv cn && (ctx.config.extern == Config.Extern.preferAxiom))
                  = false := by
                rw [hext]; simp only [Bool.and_eq_false_iff]; exact Or.inr (by decide)
              rw [hcond] at h3
              simp only [Bool.false_eq_true, if_false] at h3
              rw [run_bind_ok] at h3
              obtain ⟨ci2, s6, w6, hci2, h4⟩ := h3
              have h6s := run_getConstInfo_state _ ctx cctx ref _ hci2
              subst h6s
              split at h4
              case _ cvv =>
                rw [run_bind_ok] at h4
                obtain ⟨c2, sr2, wr2, hread2, h5⟩ := h4
                rw [run_read] at hread2
                cases hread2
                rw [hpr] at h5
                simp only [Bool.false_eq_true, if_false] at h5
                rw [run_bind_ok] at h5
                obtain ⟨am, s7, w7, ham, h6⟩ := h5
                rw [run_pure] at ham
                cases ham
                rw [run_pure] at h6
                cases h6
                exact hP'
              case _ hne2 =>
                rw [run_panicWithPosWithDecl] at h4
                cases h4
                exact hP'
          split at hrest2
          all_goals
            rw [run_bind_ok] at hrest2
            obtain ⟨projs, sc, wc, hpj, hrest3⟩ := hrest2
            rw [run_pure] at hpj
            have hsc : sc = sb := by cases hpj; rfl
            have hwc : wc = wb := by cases hpj; rfl
            subst hsc
            subst hwc
            rw [run_bind_ok] at hrest3
            obtain ⟨uu, sd, wd, hmod2, hfin⟩ := hrest3
            rw [run_modify] at hmod2
            cases hmod2
            rw [run_pure] at hfin
            cases hfin
            refine ⟨?_, ?_⟩
            · intro n hn
              show (Std.HashMap.get? (Std.HashMap.insert _ _ _) n).isSome = true
              rw [Std.HashMap.get?_insert]
              split
              · simp
              · rw [hinds]; exact hn
            · intro _
              show (Std.HashMap.get? (Std.HashMap.insert _ _ _) x.1).isSome = true
              rw [Std.HashMap.get?_insert]
              simp
        case _ hne =>
          rw [run_panicWithPosWithDecl] at hrest
          cases hrest
          exact ⟨fun _ h => h, fun ⟨iv0, hinf⟩ => (hne iv0 hinf).elim⟩
      intro p hp hp1
      rcases List.mem_append.mp hp with h1 | h1
      · exact key.1 _ (hP p h1 hp1)
      · simp only [List.mem_singleton] at h1
        subst h1
        obtain ⟨-, hfind⟩ :=
          P.lookup_adequate.constInfo _ cctx ref wP ci wa (pass_getConstInfo_core hci)
        rw [hp1] at hfind
        rw [hdecl] at hfind
        rw [← hp1]
        exact key.2 ⟨indinfo, (Option.some.inj hfind).symm⟩

/-! ## Step 10 — `Erasure.visitProj` -/

/-- **Step 10.** The declaration fetch is the table's, the emitted field index is `i` because
pruning is off, the parameter count is the model block's, the registry the emitted identifier
comes from is the model's by `BridgeInv.indcanon`, and the discriminant is motive 1's. -/
theorem step_visitProj {lenv : Environment} {env : VEnv} {tbl : SourceTable}
    {cfg : ErasureConfig} {gw : Void IO.RealWorld → NameGenerator} :
    Step10 lenv env tbl cfg gw := by
  intro P₀ htbl hcfg _hcb vExpr h1
  refine ⟨?_, bodyLe10 h1.2⟩
  intro tn i e s ctx cctx ref w t s' w' hrun Us Δ I np nf hinv hind hinf harity hi hsup hex
  have P := P₀ Us
  have hregm := hinv.indcanon
  replace h1 := h1.1
  obtain ⟨iv, hfind, hname, hnp, -⟩ := P.block_adequate.bwd tn np [nf] harity
  have hself : iv.name ∈ iv.all := by
    obtain ⟨iv', hfind', hivn', -, -, -, -, hall', hmem', -, -⟩ :=
      htbl.inds _ I (mem_of_lookup hind)
    obtain rfl : iv' = iv := by
      rw [hfind] at hfind'
      injection hfind' with h1'
      injection h1' with h2'
      exact h2'.symm
    rw [hname, hall']
    exact hmem'
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
  have hget := pass_register_inductive_entry P (by rw [hname]; exact hfind) hself hcfgc hregrun
  have hmod := hregm₂ iv.name r np [nf] hget (by rw [hname]; exact harity)
  have hmask : r.2[0]! = Array.replicate nf ConstructorArgRelevance.keep := by
    have h0 := hmod.2 0 nf rfl
    have hlt : 0 < r.2.length := by
      rcases List.getElem?_eq_some_iff.mp h0 with ⟨hlt, -⟩; exact hlt
    rw [getElem!_pos r.2 0 hlt]
    exact Option.some.inj ((List.getElem?_eq_getElem hlt).symm.trans h0)
  rw [hmask, pass_count_keep_prefix (Nat.le_of_lt hi), hnp] at hk
  rw [run_bind_ok] at hk
  obtain ⟨t₀, s₃, w₃, hve, hp⟩ := hk
  rw [run_pure] at hp
  cases hp
  have hgo := h1 e s₂ ctx cctx ref w₂ t₀ _ _ hve _ Δ
    ((hinv.mono_state hrc hregm₂).mono (NameGenerator.LE.trans hle₁ hle₂)) hsup hex
  refine ⟨hrc.trans hgo.1, hgo.2.1,
    NameGenerator.LE.trans hle₁ (NameGenerator.LE.trans hle₂ hgo.2.2.1),
    fun Γspec hspec => ?_⟩
  exact ErasesLBMode.proj (hname ▸ hmod.1) hinf hi (hgo.2.2.2 Γspec hspec)

/-! ## Step 3 — `Erasure.visitConstructor`

The emitted `.construct` node's identifier and the argument mask that decides which fields
survive both come out of the inductive registry, which `BridgeInv.indcanon` pins to the
model's.
-/

/-- The head of a constructor spine, read through the reader's fixvar mode. -/
theorem ErasesLBMode.ctor_head {env : VEnv} {Us : List Name} {Δ : VLCtx}
    {tbl : SourceTable} {ctx : ErasureContext} {Γspec : GlobalDeclarations} {cn I : Name}
    {us : List Level} {iid : InductiveId} {k np : Nat} {nfs : List Nat}
    (hc : CtorOf env cn I k) (hi : IndInfo env I iid np nfs) :
    ErasesLBMode tbl ctx env Us Γspec Δ (.const cn us) (.construct iid k []) :=
  ⟨fun _ => ErasesLB.ctor_head hc hi, fun _ _ _ => ErasesLBFix.ctor_head hc hi⟩

/-- **Step 3.** With the configuration pinned, the `@[extern]` arm and both machine-`Nat` arms
are dead, the argument mask retains every field so the emitted spine is the source spine, and
the head is `ErasesLB.ctor_head` at the registered block. The block self-membership the
registration loop is indexed by is `BlockAdequate.selfMem`: the motive gives no table entry for
the constructor's type, so it cannot come from `Witness.ReifiedInduct.Pinned` as it does at
steps 10 and 17. -/
theorem step_visitConstructor {lenv : Environment} {env : VEnv}
    {tbl : SourceTable} {cfg : ErasureConfig} {gw : Void IO.RealWorld → NameGenerator}
    (A : UpstreamAsks env) :
    Step3 lenv env tbl cfg gw := by
  intro P₀ _htbl hcfg _hcb vLit vConst vArgs _h2 _h4 h7
  refine ⟨?_, bodyLe3 _h2.2 _h4.2 h7.2⟩
  intro cn args s ctx cctx ref w t s' w' hrun Us Δ us hinv hctor hargs
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
    pass_kernelFields_at P A hcvf hivn harity hkf
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
  have hhead : HeadRefines env Us tbl ctx Δ s₄ (.const cn us) (.construct r.1 cv.cidx []) :=
    fun _ _ => ErasesLBMode.ctor_head hck' (hivn ▸ hmod.1)
  have hgo := h7 _ _ _ _ _ _ _ _ _ _ hk _ Δ (Expr.const cn us)
    ((hinv.mono_state hrc hregm₃).mono hle) hhead hargs
  exact ⟨hrc.trans hgo.1, hgo.2.1, NameGenerator.LE.trans hle hgo.2.2.1, hgo.2.2.2⟩

/-- **F-SPARSE's per-constructor slot lookup is the identity.** `CasesInfoAgrees.altCtor`
names slot `j` after constructor `j` and `numAlts` makes the array exactly as long as the
block, while a pinned block's constructor names are distinct — each reified constructor pins
its own `cidx` and `lenv` answers one `ConstructorVal` per name. So `Erasure.visitCases`'
`findIdx?` over the alternatives (`Erasure.lean:1143-1145`), which returns the *first* match,
returns the constructor's own index. -/
theorem pass_altIdx_self {lenv : Environment} {ci : Lean.CasesInfo} {con : Name}
    {I : ReifiedInduct} {iv : InductiveVal}
    (hpin : ReifiedInduct.Pinned lenv con.getPrefix I)
    (hfind : lenv.find? con.getPrefix = some (.inductInfo iv))
    (hagr : CasesInfoAgrees ci con I) {k : Nat} (hk : k < iv.ctors.length) :
    (ci.altNumParams.findIdx? fun altInfo =>
        match altInfo with
        | .ctor c _ => c == iv.ctors[k]!
        | .default _ => false) = some k := by
  obtain ⟨iv', hfind', -, -, -, -, -, -, -, hctors', hcs⟩ := hpin
  have hiveq : iv' = iv := by injection Option.some.inj (hfind'.symm.trans hfind)
  rw [hiveq] at hctors'
  have hctors := hctors'
  have hlen : iv.ctors.length = I.ctors.length := by rw [hctors]; simp
  have hcbget : ∀ j, j < I.ctors.length → iv.ctors[j]! = I.ctors[j]!.name := by
    intro j hj
    have h1 : iv.ctors[j]? = some I.ctors[j]!.name := by
      rw [hctors, List.getElem?_map, getElem!_pos I.ctors j hj,
        List.getElem?_eq_getElem hj]
      rfl
    rw [List.getElem!_eq_getElem?_getD, h1]
    rfl
  have hslot : ∀ j (hj : j < ci.altNumParams.size),
      ci.altNumParams[j] = .ctor I.ctors[j]!.name (altNumFields ci.altNumParams[j]) := by
    intro j hj
    have hjc : j < I.ctors.length := by rw [← hagr.numAlts]; exact hj
    obtain ⟨nf, hnf⟩ := hagr.altCtor j ci.altNumParams[j] I.ctors[j]!
      (Array.getElem?_eq_getElem hj) (by rw [getElem!_pos I.ctors j hjc]; simp)
    rw [hnf]; rfl
  have hinj : ∀ j, j < I.ctors.length → I.ctors[j]!.name = I.ctors[k]!.name → j = k := by
    intro j hj hname
    have hkc : k < I.ctors.length := by omega
    obtain ⟨cvj, hfj, -, hcij, hcijj, -, -, -, -⟩ :=
      hcs j I.ctors[j]! (by rw [getElem!_pos I.ctors j hj]; simp)
    obtain ⟨cvk, hfk, -, hcik, hcikk, -, -, -, -⟩ :=
      hcs k I.ctors[k]! (by rw [getElem!_pos I.ctors k hkc]; simp)
    rw [hname] at hfj
    obtain rfl : cvj = cvk := by injection Option.some.inj (hfj.symm.trans hfk)
    omega
  have hksz : k < ci.altNumParams.size := by rw [hagr.numAlts]; omega
  rw [Array.findIdx?_eq_some_iff_getElem]
  refine ⟨hksz, ?_, ?_⟩
  · rw [hslot k hksz]
    simp [hcbget k (by omega)]
  · intro j hj
    have hjsz : j < ci.altNumParams.size := Nat.lt_trans hj hksz
    have hjc : j < I.ctors.length := by rw [← hagr.numAlts]; exact hjsz
    rw [hslot j hjsz]
    simp only [beq_iff_eq, hcbget k (by omega)]
    intro hname
    exact absurd (hinj j hjc hname) (by omega)

/-- The loop `Erasure.visitCases` walks, at an index array that is the identity: the element
the `k`-th iteration sees is the `k`-th constructor's own slot, at the `k`-th position.
`pass_altIdx_self` is what makes the array self-indexing. -/
theorem pass_selfIdx_zipIdx_split {a : Array (Option Nat)} {pre post : List (Option Nat × Nat)}
    {x : Option Nat × Nat}
    (hself : ∀ (k : Nat) (hk : k < a.size), a[k] = some k)
    (h : a.zipIdx.toList = pre ++ x :: post) :
    x = (some pre.length, pre.length) ∧ pre.length < a.size := by
  have hlen : a.zipIdx.toList.length = a.size := by simp
  have hplt : pre.length < a.size := by
    rw [← hlen, h]; simp
  refine ⟨?_, hplt⟩
  have h0 : a.zipIdx.toList[pre.length]? = some x := by
    rw [h, List.getElem?_append_right (Nat.le_refl _)]
    simp
  rw [show a.zipIdx.toList = a.toList.zipIdx by simp, List.getElem?_zipIdx,
    List.getElem?_eq_getElem (show pre.length < a.toList.length by simpa using hplt)] at h0
  simp only [Option.map_some] at h0
  have := Option.some.inj h0
  rw [show a.toList[pre.length] = a[pre.length]'hplt from rfl, hself pre.length hplt] at this
  simpa using this.symm

/-- **A refusal whose test throws, stepped.** The throwing side cannot have produced `.ok`, so
the continuation ran where the test left it. `Erasure.visitCases`' machine-numeral refusal
(F-SPARSE, `Erasure.lean:1123-1124`) has this shape. -/
theorem pass_throw_guard_then {c : Bool} {msg : MessageData} {k : EraseM LBTerm}
    {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
    {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
    {t : LBTerm} {s' : ErasureState} {w' : Void IO.RealWorld}
    (hrun : (if c = true then (do throwError msg; k) else k) s ctx cctx ref w
      = .ok (t, s') w') :
    k s ctx cctx ref w = .ok (t, s') w' := by
  split at hrun
  · rw [run_bind_ok] at hrun
    obtain ⟨a0, sa0, wa0, hthr, -⟩ := hrun
    exact absurd hthr (run_throwError_ne_ok _ ctx cctx ref _ _ _ _ _)
  · exact hrun

/-- `pass_throw_guard_then` at an `unless`, whose throwing side is the other one. The
side-condition and one-to-one refusals of `Erasure.visitCases` (F-SPARSE, `Erasure.lean:1125`,
`:1148`) have this shape. -/
theorem pass_throw_guard_else {c : Bool} {msg : MessageData} {k : EraseM LBTerm}
    {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
    {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
    {t : LBTerm} {s' : ErasureState} {w' : Void IO.RealWorld}
    (hrun : (if c = true then k else (do throwError msg; k)) s ctx cctx ref w
      = .ok (t, s') w') :
    k s ctx cctx ref w = .ok (t, s') w' := by
  split at hrun
  · exact hrun
  · rw [run_bind_ok] at hrun
    obtain ⟨a0, sa0, wa0, hthr, -⟩ := hrun
    exact absurd hthr (run_throwError_ne_ok _ ctx cctx ref _ _ _ _ _)

/-- **`Erasure.firstNonProofField` writes nothing.** `run_firstNonProofField_okW`'s state
column, read on its own: the walk's only state-touching calls are `Lean.getConstInfo` and one
lifted `Lean.MetaM` computation per constructor, and both are state-transparent. The
world-indexed form cannot report this — `RunClosedW` is not inhabited at `(· = s)`, its
registration clauses being false there — so the equation is stepped directly. -/
theorem run_firstNonProofField_state {ind : InductiveVal} {r : Option (Name × Nat)}
    {s s₁ : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
    {ref : ST.Ref IO.RealWorld Core.State} {w w₁ : Void IO.RealWorld}
    (hrun : firstNonProofField ind s ctx cctx ref w = .ok (r, s₁) w₁) : s₁ = s := by
  unfold firstNonProofField at hrun
  simp only [] at hrun
  rw [run_bind_ok] at hrun
  obtain ⟨acc, s₂, w₂, hloop, htail⟩ := hrun
  have hP₂ : s₂ = s := by
    refine run_list_forIn_ok ctx cctx ref (P := fun _ s' _ => s' = s) _ _ _ _ _ rfl ?_ _ _ _ hloop
    intro c _ a sa wa st sb wb hPa hb
    rw [run_bind_ok] at hb
    obtain ⟨ci, sc, wc, hci, hb⟩ := hb
    obtain rfl := run_getConstInfo_state _ _ cctx ref _ hci
    cases ci
    case ctorInfo cv =>
      simp only [] at hb
      rw [run_bind_ok] at hb
      obtain ⟨found, sd, wd, hmeta, hb⟩ := hb
      obtain rfl := run_liftMetaM_state _ _ _ _ _ hmeta
      cases found <;>
        (simp only [] at hb; rw [run_pure] at hb; cases hb; exact hPa)
    all_goals
      (simp only [] at hb
       rw [run_bind_ok] at hb
       obtain ⟨a0, s0, w0, hthr, -⟩ := hb
       exact absurd hthr (run_throwError_ne_ok _ ctx cctx ref _ _ _ _ _))
  obtain ⟨found, u⟩ := acc
  cases found <;>
    (simp only [] at htail; rw [run_pure] at htail; cases htail; exact hP₂)

/-- **F-ACC's refusal, stepped.** `Erasure.visitCases` tests the eliminated inductive's declared
arity and, when it ends in `Prop`, walks the constructors for a field that is not a proof and
refuses if it finds one (`Erasure.lean:1134-1136`). On a successful run the walk found nothing —
or did not run — so the continuation runs at *the same state* and a generator the walk only
advanced. The continuation and the message are abstract, so the branch is stepped rather than
assumed away; the walk's generator bound is `run_firstNonProofField_okW` and its state equation
`run_firstNonProofField_state`. The state equation, rather than a `RunConcl`, is what the
accumulator bundle needs at this guard: `AccGrows` crosses an equation and not a growth. -/
theorem pass_propArity_guard {lenv : Environment} {env : VEnv} {Us : List Name}
    {gw : Void IO.RealWorld → NameGenerator} (P : ErasureSpec lenv env Us gw)
    (E : EraserAsks lenv env gw) {b : Bool} {iv : InductiveVal}
    {msg : Name → Nat → MessageData} {k : EraseM LBTerm}
    {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
    {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
    {t : LBTerm} {s' : ErasureState} {w' : Void IO.RealWorld}
    (hrun : (if b = true then
        (do
          let r ← firstNonProofField iv
          match r with
          | some (cn, fi) => do throwError (msg cn fi); k
          | _ => k)
      else k) s ctx cctx ref w = .ok (t, s') w') :
    ∃ wG : Void IO.RealWorld, gw w ≤ gw wG ∧ k s ctx cctx ref wG = .ok (t, s') w' := by
  split at hrun
  · rw [run_bind_ok] at hrun
    obtain ⟨fr, sf, wf, hfn, hrun⟩ := hrun
    obtain ⟨⟨-, hlef⟩, -⟩ :=
      run_firstNonProofField_okW (runClosedW_concl P E s w) hfn
        ⟨⟨RunConcl.rfl' _, NameGenerator.LE.rfl⟩, id⟩
    obtain rfl := run_firstNonProofField_state hfn
    cases fr with
    | some pr =>
      obtain ⟨cn0, fi0⟩ := pr
      simp only [] at hrun
      rw [run_bind_ok] at hrun
      obtain ⟨a0, sa0, wa0, hthr, -⟩ := hrun
      exact absurd hthr (run_throwError_ne_ok _ ctx cctx ref _ _ _ _ _)
    | none => exact ⟨wf, hlef, hrun⟩
  · exact ⟨w, NameGenerator.LE.rfl, hrun⟩

/-! ## Step 13 — `Erasure.visitCtorEta` -/

/-- The saturated constructor spine's entry point: `Meta.inferType` leaves the state alone and
only advances the generator, and `Expr.withApp` hands the spine to the loop. -/
theorem step_visitCtorEta {lenv : Environment} {env : VEnv} {tbl : SourceTable}
    {cfg : ErasureConfig} {gw : Void IO.RealWorld → NameGenerator} :
    Step13 lenv env tbl cfg gw := by
  intro P₀ _htbl _hcfg _hcb vGo h14
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
  have hgo := h14 _ _ _ _ _ _ _ _ _ _ _ _ _ hk _ Δ us (hinv.mono hle₁) hctor har hargs
  rw [pass_srcSpine_self hfn] at hgo
  exact pass_runRefines_le hle₁ hgo


/-! ## Steps 15 and 16 — the `casesOn` η loop -/

/-- The saturated `casesOn` spine's entry point. Mirrors `step_visitCtorEta`: the inferred type
is discarded on the saturated path, and the spine goes to the loop. -/
theorem step_visitCasesEta {lenv : Environment} {env : VEnv}
    {tbl : SourceTable} {cfg : ErasureConfig} {gw : Void IO.RealWorld → NameGenerator} :
    Step15 lenv env tbl cfg gw := by
  intro P₀ _htbl _hcfg _hcb vGo h16
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
  have hgo := h16 _ _ _ _ _ _ _ _ _ _ _ _ hk _ Δ con us I (hinv.mono hle₁) hhead har
    (by rw [hsp]; exact hsup) hargs (by rw [hsp]; exact hex)
  rw [hsp] at hgo
  exact pass_runRefines_le hle₁ hgo

/-- The `casesOn` η loop, at a saturated spine: the elaborator's arity is the fragment's own
(`CasesInfoAgrees.arity`), so the η-expansion branch is dead and the run is `Erasure.visitCases`
on the nose. F-ETA2's `let` prefix — `Erasure.etaArgIsValue` and `Erasure.withEtaPrefixLets` —
sits in that dead branch, which is why the step is still one rewrite. -/
theorem step_visitCasesEtaGo {lenv : Environment} {env : VEnv}
    {tbl : SourceTable} {cfg : ErasureConfig} {gw : Void IO.RealWorld → NameGenerator} :
    Step16 lenv env tbl cfg gw := by
  intro _P _htbl _hcfg _hcb vExpr vGo vCases h1 _h16 h17
  refine ⟨?_, bodyLe16 h1.2 _h16.2 h17.2⟩
  intro ci ty fe args s ctx cctx ref w t s' w' hrun Us Δ con us I hinv hhead har hsup hargs hex
  replace h17 := h17.1
  simp only [visitCasesEtaGoBody] at hrun
  rw [if_pos har] at hrun
  exact h17 _ _ _ _ _ _ _ _ _ _ hrun _ Δ con us I hinv hhead har hsup hargs hex

/-! ## Step 14 — the constructor η loop -/

/-- The constructor η loop, at a saturated spine: the arity is met, so the run is
`Erasure.visitConstructor` on the nose and the η-expansion branch is dead — F-ETA2's `let`
prefix included. -/
theorem step_visitCtorEtaGo {lenv : Environment} {env : VEnv}
    {tbl : SourceTable} {cfg : ErasureConfig} {gw : Void IO.RealWorld → NameGenerator} :
    Step14 lenv env tbl cfg gw := by
  intro _P _htbl _hcfg _hcb vExpr vCtor vGo h1 h3 _h14
  refine ⟨?_, bodyLe14 h1.2 h3.2 _h14.2⟩
  intro cn ar ty fe args s ctx cctx ref w t s' w' hrun Us Δ us hinv hctor har hargs
  replace h3 := h3.1
  simp only [visitCtorEtaGoBody] at hrun
  rw [if_pos har] at hrun
  exact h3 _ _ _ _ _ _ _ _ _ _ hrun _ Δ us hinv hctor hargs


/-! ## Step 17 — `Erasure.visitCases`

The `case` node itself. `ConfigPinned.nat = .peano` kills the two machine arms, so the run is
the generic one: the discriminant by motive 1, the alternatives by the parallel `for` and
motive 18, and the over-application tail by motive 1 again.
-/

/-- **Step 17.** The discriminant is motive 1's, the alternatives are motive 18's through the
parallel `for`, and the over-application tail is motive 1's again. Two numeric facts frame the
loop: `CasesInfoAgrees.numAlts` gives one alternative slot per constructor, which refutes the
loop's two early exits, and `BlockAdequate.casesOnDecl` reports the model's segmentation at the
block's own arithmetic, which is `CasesInfoAgrees.discrPos` through the pin and is what makes
`ErasesLB.cases`' length equation hold. -/
theorem step_visitCases {lenv : Environment} {env : VEnv}
    {tbl : SourceTable} {cfg : ErasureConfig} {gw : Void IO.RealWorld → NameGenerator}
    (A : UpstreamAsks env) (E : EraserAsks lenv env gw) :
    Step17 lenv env tbl cfg gw := by
  intro P₀ htbl hcfg _hcb vExpr vAlt ih1 ih18
  refine ⟨?_, bodyLe17 ih1.2 ih18.2⟩
  replace ih1 := ih1.1
  replace ih18 := ih18.1
  intro ci args s ctx cctx ref w t s' w' hrun Us Δ con us I hinv hhead har hsup hargs hex
  have P := P₀ Us
  have hcfgc : ConfigPinned ctx.config := by rw [hinv.cfg]; exact hcfg
  have hpe : ctx.config.nat = Config.Nat.peano := hcfgc.2.2.1
  -- the elaborator's segmentation, in the table's numbers
  have hdiscrP := hhead.agrees.discrPos
  have harityE := hhead.agrees.arity
  obtain ⟨hlo, hhi⟩ := hhead.agrees.altsRange
  have hdplt : ci.discrPos < args.size := by omega
  obtain ⟨hsupd, hexd⟩ := hargs ci.discrPos hdplt
  rw [← getElem!_pos args ci.discrPos hdplt] at hsupd hexd
  simp only [visitCasesBody] at hrun
  rw [hhead.agrees.decl] at hrun
  -- F-SPARSE reads the eliminated block off `CasesInfo.indName`, not off the head's prefix
  rw [hhead.agrees.indName] at hrun
  -- the block the head names, in the table and in the model
  have hpin := htbl.inds _ I (mem_of_lookup hhead.ind)
  obtain ⟨iv, hfind, hivn, -, -, hivnp, hivni, hivall, hivmem, hivctors, -⟩ := id hpin
  have hself : iv.name ∈ iv.all := by rw [hivn, hivall]; exact hivmem
  obtain ⟨iid₀, hII⟩ := indInfo_of_tabled P htbl hhead.ind
  have harity : IndArity env con.getPrefix I.numParams (I.ctors.map (·.numFields)) := hII.arity
  -- the discriminant sub-run
  rw [run_bind_ok] at hrun
  obtain ⟨disc, s₁, w₁, hdrun, hk⟩ := hrun
  obtain ⟨hrc₁, hreg₁, hle₁, hdmode⟩ := ih1 _ _ _ _ _ _ _ _ _ hdrun _ Δ hinv hsupd hexd
  rw [run_bind_ok] at hk
  obtain ⟨rctx, s₂, w₂, hrd, hk⟩ := hk
  rw [run_read] at hrd
  cases hrd
  -- `.peano` kills the two machine arms
  rw [hpe] at hk
  split at hk
  case h_1 => exact absurd ‹Config.Nat.peano = Config.Nat.machine› (by simp)
  case h_2 => exact absurd ‹Config.Nat.peano = Config.Nat.machine› (by simp)
  case h_3 =>
  rw [run_bind_ok] at hk
  obtain ⟨ret, s₃, w₃, hmatch, hk⟩ := hk
  rw [run_bind_ok] at hmatch
  obtain ⟨cinf, s₄, w₄, hcinf, hm2⟩ := hmatch
  have hs₄ : s₄ = s₁ := run_getConstInfo_state _ _ _ _ _ hcinf
  subst hs₄
  obtain ⟨hle₄, hfindc⟩ :=
    P.lookup_adequate.constInfo _ cctx ref w₁ cinf w₄ (pass_getConstInfo_core hcinf)
  have hceq : cinf = .inductInfo iv := by
    rw [hfind] at hfindc; exact (Option.some.inj hfindc).symm
  subst hceq
  simp only [] at hm2
  -- F-SPARSE's three refusals and F-ACC's, each stepped to its test and its throwing side
  -- killed; the surviving sides leave the state where they found it or grow it canonically
  rw [run_bind_ok] at hm2
  obtain ⟨rctx2, s₄', w₄', hrd2, hm2⟩ := hm2
  rw [run_read] at hrd2
  cases hrd2
  replace hm2 := pass_throw_guard_then hm2
  replace hm2 := pass_throw_guard_else hm2
  obtain ⟨wG, hleG, hm2⟩ := pass_propArity_guard P E hm2
  rw [run_bind_ok] at hm2
  obtain ⟨rr, s₅, w₅, hregrun, hm3⟩ := hm2
  -- the registration's answer, and the model behind it
  have hrc₅ := run_register_inductive_runConcl hregrun
  have hreg₅ := run_register_inductive_models P hfind hcfgc hreg₁ hregrun
  have hle₅ := run_register_inductive_gen P hcfgc hregrun
  have hget := pass_register_inductive_entry P (by rw [hivn]; exact hfind) hself hcfgc hregrun
  have hmodel := hreg₅ iv.name rr I.numParams (I.ctors.map (·.numFields)) hget
    (by rw [hivn]; exact harity)
  -- the fragment's own `casesApp` data for this spine
  have hspineinv : ∀ (l : List Expr) (f : Expr) (sp : List Expr),
      SupportedTm env tbl (l.foldl Expr.app f) sp → SupportedTm env tbl f (l ++ sp) := by
    intro l
    induction l with
    | nil => intro f sp h; simpa using h
    | cons a as ih =>
      intro f sp h
      cases ih (f.app a) sp h with
      | app _ hf => simpa using hf
  have hhd : SupportedTm env tbl (.const con us) args.toList := by
    have h := hspineinv args.toList (.const con us) [] hsup.term
    simpa using h
  cases hhd with
  | @const _ _ _ _ hcases0 _ _ _ => exact absurd hhead.cases (by rw [hcases0]; simp)
  | @casesApp _ _ _ minors0 I0 hplain0 hcases0 hind0 hinf0 harity0 hmin0 hlen0 htel0 =>
  obtain rfl : I = I0 := by
    have hii := hhead.ind
    rw [hind0] at hii
    exact (Option.some.inj hii).symm
  -- the loop's numeric frame
  have hlo' : ci.altsRange.lower = I.numParams + 1 + I.numIndices + 1 := by omega
  have hnalts : ci.altsRange.upper - ci.altsRange.lower = I.ctors.length := by omega
  have hnfsget : ∀ j, j < I.ctors.length →
      (I.ctors.map (·.numFields))[j]? = some I.ctors[j]!.numFields := by
    intro j hj
    rw [List.getElem?_map, List.getElem?_eq_getElem hj, getElem!_pos I.ctors j hj]
    rfl
  have hmasklen : I.ctors.length ≤ rr.2.length := by
    by_contra hcon
    have hcon' : rr.2.length < I.ctors.length := by omega
    have hj := hmodel.2 rr.2.length _ (hnfsget rr.2.length hcon')
    rcases List.getElem?_eq_some_iff.mp hj with ⟨hlt, -⟩
    omega
  have haltslen : I.ctors.length ≤ ci.altNumParams.size :=
    Nat.le_of_eq hhead.agrees.numAlts.symm
  have hinv₅ : BridgeInv env Us tbl cfg (gw w₅) ctx s₅ Δ :=
    (((hinv.mono_state hrc₁ hreg₁).mono hle₁).mono_state hrc₅ hreg₅).mono
      (NameGenerator.LE.trans hle₄ (NameGenerator.LE.trans hleG hle₅))
  -- F-SPARSE: every constructor's slot is its own, so the index array is total, the
  -- catch-all is never built and the loop walks the block in constructor order
  have hctorsl : iv.ctors.length = I.ctors.length := by rw [hivctors]; simp
  have hself : ∀ (k : Nat)
      (hk : k < (iv.ctors.toArray.map fun ctorName =>
        ci.altNumParams.findIdx? fun altInfo =>
          match altInfo with
          | .ctor c _ => c == ctorName
          | .default _ => false).size),
      (iv.ctors.toArray.map fun ctorName =>
        ci.altNumParams.findIdx? fun altInfo =>
          match altInfo with
          | .ctor c _ => c == ctorName
          | .default _ => false)[k] = some k := by
    intro k hk
    simp only [Array.size_map, List.size_toArray] at hk
    rw [Array.getElem_map, List.getElem_toArray,
      show iv.ctors[k] = iv.ctors[k]! by rw [getElem!_pos iv.ctors k hk]]
    exact pass_altIdx_self hpin hfind hhead.agrees hk
  have haltall : (iv.ctors.toArray.map fun ctorName =>
      ci.altNumParams.findIdx? fun altInfo =>
        match altInfo with
        | .ctor c _ => c == ctorName
        | .default _ => false).all (·.isSome) = true := by
    rw [Array.all_eq_true]
    intro k hk
    rw [hself k hk]
    rfl
  replace hm3 := pass_throw_guard_else hm3
  split at hm3
  case isFalse hc => exact absurd haltall hc
  case isTrue =>
  rw [run_bind_ok] at hm3
  obtain ⟨dflt, sD, wD, hdflt, hm3⟩ := hm3
  rw [run_pure] at hdflt
  cases hdflt
  rw [run_bind_ok] at hm3
  obtain ⟨accF, s₆, w₆, hloop, hfin⟩ := hm3
  rw [run_pure] at hfin
  cases hfin
  -- the alternatives' `for`, one slot per constructor
  have hloopP := run_array_forIn_ok' ctx cctx ref
    (P := fun pre acc s₇ w₇ =>
      RunConcl s₅ s₇ ∧ IndRegistryModelled env s₇ ∧ gw w₅ ≤ gw w₇ ∧
      acc.size = pre.length ∧
      ∀ Γspec, SpecEnv env tbl.body? tbl.levels? s₇ Γspec →
        ∀ j, j < pre.length →
          ErasesLBAltMode tbl ctx env Us Γspec Δ (I.ctors.map (·.numFields))[j]!
            args[ci.altsRange.lower + j]! acc[j]!)
    ⟨RunConcl.rfl' _, hreg₅, NameGenerator.LE.rfl, by simp, by simp⟩
    (by
      intro pre x post acc s₇ w₇ acc' s₈ w₈ hL hPacc hf
      obtain ⟨hrcA, hregA, hleA, hsizeA, haltA⟩ := hPacc
      obtain ⟨hxv, hplt⟩ := pass_selfIdx_zipIdx_split hself hL
      subst hxv
      simp only [Array.size_map, List.size_toArray] at hplt
      have hjlt : pre.length < I.ctors.length := by omega
      simp only [] at hf
      have haltlt : pre.length < ci.altNumParams.size := by
        rw [hhead.agrees.numAlts]; exact hjlt
      have hai : ci.altNumParams[pre.length]? = some ci.altNumParams[pre.length]! := by
        rw [getElem!_pos ci.altNumParams pre.length haltlt, Array.getElem?_eq_getElem haltlt]
      have hcb : I.ctors[pre.length]? = some I.ctors[pre.length]! := by
        rw [getElem!_pos I.ctors pre.length hjlt, List.getElem?_eq_getElem hjlt]
      have hnfeq := hhead.agrees.numFields pre.length _ _ hai hcb
      have hnfval : (I.ctors.map (·.numFields))[pre.length]! = I.ctors[pre.length]!.numFields := by
        rw [List.getElem!_eq_getElem?_getD, hnfsget pre.length hjlt]
        rfl
      have hmaskv : rr.2[pre.length]! = Array.replicate I.ctors[pre.length]!.numFields .keep := by
        rw [List.getElem!_eq_getElem?_getD, hmodel.2 pre.length _ (hnfsget pre.length hjlt)]
        rfl
      replace hf : ((vAlt I.ctors[pre.length]!.numFields
            (Array.replicate I.ctors[pre.length]!.numFields .keep)
            args[ci.altsRange.lower + pre.length]!) >>= fun alt =>
              pure (ForInStep.yield (acc.push alt)))
          s₇ ctx cctx ref w₇ = .ok (.yield acc', s₈) w₈ := by
        rw [← hmaskv, ← hnfeq]; exact hf
      have hxlt : ci.altsRange.lower + pre.length < args.size := by omega
      obtain ⟨hsupx0, hexx0⟩ := hargs _ hxlt
      rw [← getElem!_pos args _ hxlt] at hsupx0 hexx0
      have hminj : minors0[pre.length]? = some args[ci.altsRange.lower + pre.length]! := by
        rw [hmin0, List.getElem?_take, if_pos hjlt, List.getElem?_drop,
          show I.numParams + 1 + I.numIndices + 1 + pre.length
            = ci.altsRange.lower + pre.length by omega,
          List.getElem?_eq_getElem (show ci.altsRange.lower + pre.length < args.toList.length by
            simpa using hxlt),
          getElem!_pos args _ hxlt]
        simp
      have htelx : IsLamTelescope I.ctors[pre.length]!.numFields
          args[ci.altsRange.lower + pre.length]! := htel0 pre.length _ _ hminj hcb
      have hinv₇ : BridgeInv env Us tbl cfg (gw w₇) ctx s₇ Δ :=
        (hinv₅.mono_state hrcA hregA).mono hleA
      rw [run_bind_ok] at hf
      obtain ⟨alt, s₉, w₉, halt, hp⟩ := hf
      rw [run_pure] at hp
      cases hp
      obtain ⟨hrcB, hregB, hleB, haltmode⟩ :=
        ih18 _ _ _ _ _ _ _ _ _ _ _ halt _ Δ hinv₇ rfl htelx hsupx0 hexx0
      refine ⟨hrcA.trans hrcB, hregB, NameGenerator.LE.trans hleA hleB, by simp [hsizeA], ?_⟩
      intro Γspec hspec j hj
      simp only [List.length_append, List.length_cons, List.length_nil] at hj
      rcases Nat.lt_or_ge j pre.length with hjp | hjp
      · have hprev := haltA Γspec (SpecEnv.mono hrcB.le hspec) j hjp
        have hpush : (acc.push alt)[j]! = acc[j]! := by
          rw [getElem!_pos (acc.push alt) j (by simp; omega),
            getElem!_pos acc j (by omega), Array.getElem_push_lt]
        rw [hpush]
        exact hprev
      · have hjeq : j = pre.length := by omega
        subst hjeq
        have hpush : (acc.push alt)[pre.length]! = alt := by
          rw [getElem!_pos (acc.push alt) pre.length (by simp; omega)]
          rw [Array.getElem_push, dif_neg (by omega)]
        rw [hpush, hnfval]
        exact haltmode Γspec hspec)
    (by
      intro pre x post acc s₇ w₇ acc' s₈ w₈ hL hPacc hf
      obtain ⟨hxv, -⟩ := pass_selfIdx_zipIdx_split hself hL
      subst hxv
      simp only [] at hf
      rw [run_bind_ok] at hf
      obtain ⟨alt, s₉, w₉, halt, hp⟩ := hf
      rw [run_pure] at hp
      simp at hp)
    hloop
  -- the saturated prefix, and the `.case` node it erases to
  have hAL : ∀ k, k < args.size → args[k]! = args.toList[k]! :=
    fun k hk => pass_getElem!_toList args k hk
  have hmemargs : ∀ a ∈ args.toList, Supported env tbl a ∧ ∃ ve, TrExprS env Us Δ a ve := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    have hi' : i < args.size := by simpa using hi
    simpa using hargs i hi'
  have hrcT := hrc₅.trans hloopP.1
  have hindsome : (s₃.inductives.get? con.getPrefix).isSome := by
    refine hloopP.1.le.inds ?_
    rw [← hivn, hget]
    simp
  obtain ⟨nm0, vc0, hcst0, hco0, hshape0⟩ :=
    P.block_adequate.casesOnDecl con con.getPrefix iv hhead.cases rfl hfind
  rw [show iv.numParams + 1 + iv.numIndices = ci.discrPos by rw [hdiscrP, hivnp, hivni]]
    at hshape0
  have hnalen : accF.size = I.ctors.length := by
    rw [hloopP.2.2.2.1]
    simp [← hctorsl]
  have htakeidx : ∀ k, k < ci.arity → (args.toList.take ci.arity)[k]! = args[k]! := by
    intro k hk
    have hks : k < args.size := by omega
    rw [getElem!_pos (args.toList.take ci.arity) k (by simp; omega), hAL k hks,
      getElem!_pos args.toList k (by simpa using hks), List.getElem_take]
  have hcase : ∀ Γspec, SpecEnv env tbl.body? tbl.levels? s₃ Γspec →
      ErasesLBMode tbl ctx env Us Γspec Δ
        ((args.toList.take ci.arity).foldl Expr.app (.const con us))
        (.case (rr.1, iv.numParams) disc accF.toList) := by
    intro Γspec hspec
    obtain ⟨iid', np', nfs', hE, hII', hnmlen⟩ :=
      (hspec.inds _ hindsome).elims con ci.discrPos nm0 hshape0 hhead.informative hco0
    obtain ⟨hiid, hnp, hnfs⟩ := IndInfo.inj A hII' (hivn ▸ hmodel.1)
    subst hiid
    subst hnp
    subst hnfs
    rw [hivnp]
    refine ErasesLBMode.cases hE hcst0 hco0 P.envWF (consts_classified A P.envWF)
      hinv.vlctx_wf ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro a ha
      rw [List.take_take, Nat.min_eq_left (by omega)] at ha
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
      simp only [List.length_take] at hi
      have hi' : i < args.size := by omega
      rw [List.getElem_take]
      exact (hmemargs _ (List.getElem_mem (by simpa using hi'))).2
    · intro a ha
      rw [List.take_take, Nat.min_eq_left (by omega)] at ha
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
      simp only [List.length_take] at hi
      have hi' : i < args.size := by omega
      rw [List.getElem_take]
      exact Supported.projInfo (hmemargs _ (List.getElem_mem (by simpa using hi'))).1.term
    · simp only [List.length_take, List.length_map]
      omega
    · rw [htakeidx ci.discrPos (by omega)]
      exact hdmode Γspec (SpecEnv.mono hrcT.le hspec)
    · simp only [List.length_drop, List.length_take, List.length_map]
      omega
    · rw [Array.length_toList, hnalen, List.length_map]
    · intro i hi
      simp only [List.length_map] at hi
      have hkey := hloopP.2.2.2.2 Γspec hspec i (by simp; omega)
      rw [← pass_getElem!_toList accF i (by omega)]
      rw [show ((args.toList.take ci.arity).drop (ci.discrPos + 1))[i]!
          = args[ci.altsRange.lower + i]! from ?_]
      · exact hkey
      · have hidx : ci.altsRange.lower + i < args.size := by omega
        rw [hAL _ hidx, getElem!_pos args.toList _ (by simpa using hidx),
          getElem!_pos ((args.toList.take ci.arity).drop (ci.discrPos + 1)) i
            (by simp; omega),
          List.getElem_drop, List.getElem_take]
        congr 1
        omega
  -- the over-application tail
  have hslice : (Std.Slice.toArray (args.toSubarray ci.arity)).toList
      = args.toList.drop ci.arity := by
    rw [pass_slice_toArray]
    simp only [Array.toList_extract, List.extract_eq_take_drop]
    rw [List.take_of_length_le (by simp)]
  rw [run_bind_ok] at hk
  obtain ⟨tf, sT, wT, htail, hp⟩ := hk
  rw [run_pure] at hp
  cases hp
  have htailP := run_array_forIn_ok' ctx cctx ref
    (P := fun pre acc s₉ w₉ =>
      RunConcl s₃ s₉ ∧ IndRegistryModelled env s₉ ∧ gw w₃ ≤ gw w₉ ∧
      ∀ Γspec, SpecEnv env tbl.body? tbl.levels? s₉ Γspec →
        ErasesLBMode tbl ctx env Us Γspec Δ
          (pre.foldl Expr.app ((args.toList.take ci.arity).foldl Expr.app (.const con us))) acc)
    ⟨RunConcl.rfl' _, hloopP.2.1, NameGenerator.LE.rfl, hcase⟩
    (by
      intro pre x post acc s₉ w₉ acc' s₁₀ w₁₀ hL hQ hg
      obtain ⟨hrcC, hregC, hleC, hmodeC⟩ := hQ
      rw [run_bind_ok] at hg
      obtain ⟨tx, s₁₁, w₁₁, hvx, hpx⟩ := hg
      rw [run_pure] at hpx
      cases hpx
      have hxmem : x ∈ args.toList := by
        have hxm : x ∈ (Std.Slice.toArray (args.toSubarray ci.arity)).toList := by
          rw [hL]; exact List.mem_append_right _ List.mem_cons_self
        rw [hslice] at hxm
        exact List.mem_of_mem_drop hxm
      obtain ⟨hsx, hex⟩ := hmemargs x hxmem
      obtain ⟨hrcD, hregD, hleD, hmx⟩ :=
        ih1 _ _ _ _ _ _ _ _ _ hvx _ Δ
          ((((hinv₅.mono_state hloopP.1 hloopP.2.1).mono hloopP.2.2.1).mono_state hrcC
            hregC).mono hleC) hsx hex
      refine ⟨hrcC.trans hrcD, hregD, NameGenerator.LE.trans hleC hleD, fun Γspec hspec => ?_⟩
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact ⟨fun hfx => ErasesLB.app ((hmodeC Γspec (SpecEnv.mono hrcD.le hspec)).1 hfx)
          ((hmx Γspec hspec).1 hfx),
        fun nms ids hfx => ErasesLBFix.app
          ((hmodeC Γspec (SpecEnv.mono hrcD.le hspec)).2 nms ids hfx)
          ((hmx Γspec hspec).2 nms ids hfx)⟩)
    (by
      intro pre x post acc s₉ w₉ acc' s₁₀ w₁₀ hL hQ hg
      rw [run_bind_ok] at hg
      obtain ⟨tx, s₁₁, w₁₁, hvx, hpx⟩ := hg
      rw [run_pure] at hpx
      simp at hpx)
    htail
  obtain ⟨hrcF, hregF, hleF, hmodeF⟩ := htailP
  refine ⟨hrc₁.trans (hrc₅.trans (hloopP.1.trans hrcF)), hregF, ?_,
    fun Γspec hspec => ?_⟩
  · exact NameGenerator.LE.trans hle₁ (NameGenerator.LE.trans hle₄ (NameGenerator.LE.trans hleG
      (NameGenerator.LE.trans hle₅ (NameGenerator.LE.trans hloopP.2.2.1 hleF))))
  · have h := hmodeF Γspec hspec
    rw [hslice, ← List.foldl_append, List.take_append_drop] at h
    exact h

/-! ## `RegKeyed` at a run

Every emitted key is a registered constant's kername or a registered inductive's block key,
read off the entry's own shape (`ColdStartShape.RegKeyed`). It is a fact about the state
alone, hence a `RunClosedW` motive and not a refinement conclusion: each registration
primitive writes a statically known `GlobalDecl` constructor at a statically known key, so
every `consts` clause is that writer's own and the only clause with content is the block
registration's.

That clause takes its model content from `ErasureSpec.BlockAdequate.fwd` at the
`Lean.InductiveVal` the call was made at, whose provenance `RunClosedW.reg` carries — the
`Lean.getConstInfo` run, read through `ErasureSpec.LookupAdequate.constInfo`, the
machine-numeral arm refuted by `ConfigPinned` — and not from `Bridge.IndRegistryModelled`,
whose `IndArity` premise the step has no reason to hold. `fwd`'s fourth premise and the
member loop's `.inductInfo` match are `BlockAdequate.fields` and `BlockAdequate.selfName`.
-/

/-- **The block registration maintains `RegKeyed`.** The cold branch conses one body-less
constant entry per `@[extern]` constructor — none, at a pinned configuration — and one block
entry, at `mutualBlockKn ii`; `BlockAdequate.selfName` and `selfMem` put `ii.name` in the
registry (`pass_register_inductive_entry`), and `BlockAdequate.fwd` at the index the member
loop minted reads its model block. The hit branch leaves the state alone. -/
theorem regKeyed_register_inductive {lenv : Environment} {env : VEnv} {Us : List Name}
    {gw : Void IO.RealWorld → NameGenerator} {ii : InductiveVal} {hd : Name}
    {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
    {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
    {r : InductiveId × InductiveArgMasks} {s₁ : ErasureState} {w₁ : Void IO.RealWorld}
    (P : ErasureSpec lenv env Us gw) (hfind : lenv.find? hd = some (.inductInfo ii))
    (hcfg : ConfigPinned ctx.config)
    (hrun : Erasure.register_inductive ii s ctx cctx ref w = .ok (r, s₁) w₁)
    (H : RegKeyed env s) : RegKeyed env s₁ := by
  have hdecl : lenv.find? ii.name = some (.inductInfo ii) := by
    rw [P.block_adequate.selfName hd ii hfind]; exact hfind
  have hget : s₁.inductives.get? ii.name = some r :=
    pass_register_inductive_entry P hdecl (P.block_adequate.selfMem hd ii hfind) hcfg hrun
  have hcl := (run_register_inductive_entries (Ci := fun nm ci => lenv.find? nm = some ci)
    (fun nm ci s₀ s₂ w₀ w₂ h =>
      let k := P.lookup_adequate.constInfo nm cctx ref w₀ ci w₂ (pass_getConstInfo_core h)
      ⟨k.2, k.1⟩)
    (fun le s₀ s₂ w₀ w₂ h => P.prim_monotone.getEnv s₀ ctx cctx ref w₀ le s₂ w₂ h)
    (fun msg u s₀ s₂ w₀ w₂ h => P.prim_monotone.logInfo msg s₀ ctx cctx ref w₀ u s₂ w₂ h)
    hcfg.2.2.2.1 hrun).2
  cases hi : s.inductives.get? ii.name with
  | some rc0 => rw [(run_register_inductive_hit_ok hi hrun).2.1]; exact H
  | none =>
    obtain ⟨-, bodies, sM, hs1, -, -, hce, hgrow, -⟩ :=
      run_register_inductive_cold_ok (Ci := fun _ _ => True)
        (fun _ _ _ _ _ _ _ => trivial) hi hrun
    refine hs1 ▸ (ConstExt.regKeyed hce.toConstExt (fun _ hn => hgrow hn) H).indCons
      (kn := mutualBlockKn ii) rfl (fun _ hn => hn) (fun _ hn => hn) ?_
    rcases hcl ii.name r hget with hold | ⟨idx, inf, hidx, hCin, -, -, -⟩
    · rw [hold] at hi; exact absurd hi (by simp)
    · obtain ⟨nfs, hkfs⟩ := P.block_adequate.fields ii.name inf hCin
      exact ⟨ii.name, ⟨indBlockKername ii.all, idx⟩, ii.numParams, nfs,
        by rw [hs1] at hget; rw [hget]; simp,
        P.block_adequate.fwd hd ii.name ii inf idx nfs hfind hidx hCin hkfs, rfl⟩

/-- **`RegKeyed` as a `RunClosedW` motive.** The eleven ambient primitives and
`Erasure.prepare_erasure` leave the state alone; `Erasure.addAxiom`,
`Erasure.visitMutual`'s two term exits and `Erasure.addRealizer` are constant extensions;
the block registration is `regKeyed_register_inductive`. -/
theorem runClosedW_regKeyed {lenv : Environment} {env : VEnv}
    {gw : Void IO.RealWorld → NameGenerator} (P : ∀ Us, ErasureSpec lenv env Us gw) :
    RunClosedW ConfigPinned (fun s _ => RegKeyed env s) where
  oracle h hq := by rw [run_liftMetaM_state _ _ _ _ _ h]; exact hq
  inferType h hq := by rw [run_liftMetaM_state _ _ _ _ _ h]; exact hq
  metaM _ h hq := by rw [run_liftMetaM_state _ _ _ _ _ h]; exact hq
  constInfo h hq := by rw [run_getConstInfo_state _ _ _ _ _ h]; exact hq
  getEnv h hq := by rw [run_getEnv_state _ _ _ _ _ h]; exact hq
  logInfo h hq := by rw [run_logInfo_state _ _ _ _ _ h]; exact hq
  isInstance h hq := by rw [run_liftCoreM_state _ _ _ _ _ h]; exact hq
  fresh h hq := by rw [run_mkFreshFVarId_state _ _ _ _ _ h]; exact hq
  declInfo h hq := by rw [run_liftCoreM_state _ _ _ _ _ h]; exact hq
  ctorArity h hq := by rw [run_liftCoreM_state _ _ _ _ _ h]; exact hq
  casesInfo h hq := by rw [run_liftCoreM_state _ _ _ _ _ h]; exact hq
  inl := by
    intro s w kn hq
    exact ConstExt.regKeyed (s := s) (s' := { s with inlinings := kn :: s.inlinings })
      (ConstExt.of_same rfl rfl) (fun _ hn => hn) hq
  ax h hq := by
    rw [(run_addAxiom_ok h).1]
    exact ConstExt.regKeyed (BodylessExt.addAxiom _ _).toConstExt (fun _ hn => hn) hq
  reg := by
    intro ii s ctx cctx ref w r s' w' hprov hc h hq
    rcases hprov with ⟨hd, sa, sb, wa, wb, hci⟩ | hmach
    · exact regKeyed_register_inductive (P [])
        (((P []).lookup_adequate.constInfo hd cctx ref wa _ wb
          (pass_getConstInfo_core hci)).2) hc h hq
    · exact absurd (hc.2.2.1.symm.trans hmach) (by simp)
  prep hc h hq := by rw [(run_prepare_erasure_ok hc.1 h).1]; exact hq
  nrc hq _ _ _ := ConstExt.regKeyed (ConstExt.addRealizer _ _ _) (fun _ hn => hn) hq
  rlz hq _ _ _ := ConstExt.regKeyed (ConstExt.addRealizer _ _ _) (fun _ hn => hn) hq
  rc hq _ _ := regKeyed_recConstState hq

/-- **`RegKeyed` at a run of the term walk.** `regSaturated_of_regKeyed`'s first antecedent,
at the final state of `Erasure.visitExpr`; `regKeyed_empty` starts it at a cold entry. -/
theorem regKeyed_of_run {lenv : Environment} {env : VEnv}
    {gw : Void IO.RealWorld → NameGenerator} {e : Expr} {t : LBTerm} {s s' : ErasureState}
    {ctx : ErasureContext} {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
    {w w' : Void IO.RealWorld} (P : ∀ Us, ErasureSpec lenv env Us gw)
    (hcfg : ConfigPinned ctx.config)
    (hvis : Erasure.visitExpr e s ctx cctx ref w = .ok (t, s') w') (hk : RegKeyed env s) :
    RegKeyed env s' :=
  ((visitExpr_shapeW (runClosedW_regKeyed P)).1 _ _ _ _ _ _ _ _ _ hvis hk hcfg).1

/-! ## `IndBlocksCover` at a run

The mirror between the two fields `Erasure.register_inductive` writes in one `modify`
(`ErasureRun.lean`), carried along a run of the term walk. Like `RegKeyed` it is a fact about
the state alone, so it is a `RunClosedW` motive: every other writer is a constant extension
that leaves `ErasureState.indBlocks` alone, and the one clause with content is the block
registration's, where the new row's declared members come from
`run_register_inductive_members` and the older rows survive because the key the run mints is
fresh in the emitted environment (`blockKey_fresh_of_cover`). -/

/-- **The block registration maintains `IndBlocksCover`.** The cold branch's member loop is a
constant extension of the entry state that leaves the block table alone
(`run_register_inductive_cold_blocks`), and the closing `modify` conses the entry and its row
together; the new row's declared members are registered by `run_register_inductive_members`,
whose `.inductInfo` guard `ErasureSpec.lookup_adequate` pays at a declared member, and the
key it is filed under is fresh in `gdecls` by `blockKey_fresh_of_cover`. The hit branch
leaves the state alone. -/
theorem indBlocksCover_register_inductive {lenv : Environment} {env : VEnv} {Us : List Name}
    {gw : Void IO.RealWorld → NameGenerator} {ii : InductiveVal} {hd : Name}
    {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
    {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
    {r : InductiveId × InductiveArgMasks} {s₁ : ErasureState} {w₁ : Void IO.RealWorld}
    (P : ErasureSpec lenv env Us gw) (hfind : lenv.find? hd = some (.inductInfo ii))
    (hrun : Erasure.register_inductive ii s ctx cctx ref w = .ok (r, s₁) w₁)
    (H : IndBlocksCover lenv s) : IndBlocksCover lenv s₁ := by
  have hdecl : lenv.find? ii.name = some (.inductInfo ii) := by
    rw [P.block_adequate.selfName hd ii hfind]; exact hfind
  have hself : ii.name ∈ ii.all := P.block_adequate.selfMem hd ii hfind
  cases hi : s.inductives.get? ii.name with
  | some rc0 => rw [(run_register_inductive_hit_ok hi hrun).2.1]; exact H
  | none =>
    obtain ⟨hfresh, bodies, sM, hs1, -, -, hce, hgrow, -⟩ :=
      run_register_inductive_cold_ok (Ci := fun _ _ => True)
        (fun _ _ _ _ _ _ _ => trivial) hi hrun
    have hnew : ∀ n ∈ ii.all, (∃ iv : InductiveVal, lenv.find? n = some (.inductInfo iv)) →
        (s₁.inductives.get? n).isSome :=
      run_register_inductive_members
        (fun nm ci _s' _s'' w' w'' hci _hnm hiv =>
          let ⟨iv, hlen⟩ := hiv
          ⟨iv, Option.some.inj (((P.lookup_adequate.constInfo nm cctx ref w' ci w''
            (pass_getConstInfo_core hci)).2).symm.trans hlen)⟩)
        hi hrun
    have hbl : s₁.indBlocks = (mutualBlockKn ii, ii.all) :: s.indBlocks :=
      run_register_inductive_cold_blocks hi hrun
    have hblM : sM.indBlocks = s.indBlocks := by
      rw [hs1] at hbl
      injection hbl with _hrow h2
    rw [hs1] at hnew ⊢
    refine (ConstExt.indBlocksCover hce.toConstExt hblM (fun _ hn => hgrow hn) H).indCons
      rfl rfl (fun _ hn => hn) ?_ hnew
    intro mib hmem
    obtain ⟨pre, hpre, hshape⟩ := hce.toConstExt.gdecls
    rw [hpre] at hmem
    rcases List.mem_append.mp hmem with h1 | h1
    · exact absurd (hshape _ h1).1 (by simp)
    · exact blockKey_fresh_of_cover H hfresh hdecl hself hi mib h1

/-- **`IndBlocksCover` as a `RunClosedW` motive.** The eleven ambient primitives and
`Erasure.prepare_erasure` leave the state alone; `Erasure.addAxiom`, `Erasure.visitMutual`'s
two term exits and `Erasure.addRealizer` are constant extensions that write no block row; the
block registration is `indBlocksCover_register_inductive`. -/
theorem runClosedW_indBlocksCover {lenv : Environment} {env : VEnv}
    {gw : Void IO.RealWorld → NameGenerator} (P : ∀ Us, ErasureSpec lenv env Us gw) :
    RunClosedW ConfigPinned (fun s _ => IndBlocksCover lenv s) where
  oracle h hq := by rw [run_liftMetaM_state _ _ _ _ _ h]; exact hq
  inferType h hq := by rw [run_liftMetaM_state _ _ _ _ _ h]; exact hq
  metaM _ h hq := by rw [run_liftMetaM_state _ _ _ _ _ h]; exact hq
  constInfo h hq := by rw [run_getConstInfo_state _ _ _ _ _ h]; exact hq
  getEnv h hq := by rw [run_getEnv_state _ _ _ _ _ h]; exact hq
  logInfo h hq := by rw [run_logInfo_state _ _ _ _ _ h]; exact hq
  isInstance h hq := by rw [run_liftCoreM_state _ _ _ _ _ h]; exact hq
  fresh h hq := by rw [run_mkFreshFVarId_state _ _ _ _ _ h]; exact hq
  declInfo h hq := by rw [run_liftCoreM_state _ _ _ _ _ h]; exact hq
  ctorArity h hq := by rw [run_liftCoreM_state _ _ _ _ _ h]; exact hq
  casesInfo h hq := by rw [run_liftCoreM_state _ _ _ _ _ h]; exact hq
  inl := by
    intro s w kn hq
    exact ConstExt.indBlocksCover (s := s) (s' := { s with inlinings := kn :: s.inlinings })
      (ConstExt.of_same rfl rfl) rfl (fun _ hn => hn) hq
  ax h hq := by
    rw [(run_addAxiom_ok h).1]
    exact ConstExt.indBlocksCover (BodylessExt.addAxiom _ _).toConstExt rfl (fun _ hn => hn) hq
  reg := by
    intro ii s ctx cctx ref w r s' w' hprov hc h hq
    rcases hprov with ⟨hd, sa, sb, wa, wb, hci⟩ | hmach
    · exact indBlocksCover_register_inductive (P [])
        (((P []).lookup_adequate.constInfo hd cctx ref wa _ wb
          (pass_getConstInfo_core hci)).2) h hq
    · exact absurd (hc.2.2.1.symm.trans hmach) (by simp)
  prep hc h hq := by rw [(run_prepare_erasure_ok hc.1 h).1]; exact hq
  nrc hq _ _ _ := ConstExt.indBlocksCover (ConstExt.addRealizer _ _ _) rfl (fun _ hn => hn) hq
  rlz hq _ _ _ := ConstExt.indBlocksCover (ConstExt.addRealizer _ _ _) rfl (fun _ hn => hn) hq
  rc hq _ _ := indBlocksCover_recConstState hq

/-- **`IndBlocksCover` at a run of the term walk**, at the final state of
`Erasure.visitExpr`; `indBlocksCover_empty` starts it at a cold entry. -/
theorem indBlocksCover_of_run {lenv : Environment} {env : VEnv}
    {gw : Void IO.RealWorld → NameGenerator} {e : Expr} {t : LBTerm} {s s' : ErasureState}
    {ctx : ErasureContext} {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
    {w w' : Void IO.RealWorld} (P : ∀ Us, ErasureSpec lenv env Us gw)
    (hcfg : ConfigPinned ctx.config)
    (hvis : Erasure.visitExpr e s ctx cctx ref w = .ok (t, s') w')
    (hk : IndBlocksCover lenv s) : IndBlocksCover lenv s' :=
  ((visitExpr_shapeW (runClosedW_indBlocksCover P)).1 _ _ _ _ _ _ _ _ _ hvis hk hcfg).1

/-! ## The specification prefix of a block registration, produced from a run

`regInv_registerInd_step` takes its prefix as a parameter; `indPrefixOf_of_run` produces it
from the run, at the definitions of `ColdStartShape.lean`. Three ingredients beyond the run
lemmas: `ErasureSpec.BlockAdequate` reads the emitted block against the model, `UpstreamAsks`
pins each member's block coordinates and each eliminator's segmentation, and
`blockKey_fresh_of_cover` refutes the escape disjunct of the two registry reports — a member
already registered at the entry state would put the block key in `Γ` through
`RegInvShape'.inds`, hence in `s.gdecls` through `SpecKeysEmitted.inds`, where the guard's own
verdict says it is not.
-/

set_option maxHeartbeats 2000000 in
/-- **The specification prefix, produced from a run.** The block entry the cold branch conses
together with one eliminator entry per member whose emitted body is not propositional, with
the four obligations of `IndPrefixOf` discharged and the block entry exposed in the shape
`regInv_registerInd_step`'s `hblk` asks for. `hsafe` is the safety column
`ErasureSpec.propositionalInd_of_arity` spends at each member. -/
theorem indPrefixOf_of_run {lenv : Environment} {env : VEnv} {Us : List Name}
    {gw : Void IO.RealWorld → NameGenerator} {bo : Name → Option Expr}
    {lp : Name → List Name} {Γ : GlobalDeclarations} {indinfo : InductiveVal}
    {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
    {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
    {r : InductiveId × InductiveArgMasks} {s₁ : ErasureState} {w₁ : Void IO.RealWorld}
    (P : ErasureSpec lenv env Us gw) (A : UpstreamAsks env)
    (Acc : RegAcc env bo lp Γ s) (hcovs : IndBlocksCover lenv s)
    (K : BodiedKeysFresh env bo indinfo)
    (hsafe : ∀ (I : Name) (iv : InductiveVal), lenv.find? I = some (.inductInfo iv) →
      DefinitionSafety.safe ≤ (ConstantInfo.inductInfo iv).safety)
    (hcfg : ConfigPinned ctx.config)
    (hfind : lenv.find? indinfo.name = some (.inductInfo indinfo))
    (hmiss : s.inductives.get? indinfo.name = none)
    (hrun : Erasure.register_inductive indinfo s ctx cctx ref w = .ok (r, s₁) w₁) :
    ∃ pre : GlobalDeclarations, IndPrefixOf env bo lp indinfo pre ∧
      ∀ mib, LBTerm.envLookup s₁.gdecls (mutualBlockKn indinfo) = some (.inductiveDecl mib) →
        LBTerm.envLookup pre (mutualBlockKn indinfo) = some (.inductiveDecl mib) := by
  have hself : indinfo.name ∈ indinfo.all := P.block_adequate.selfMem _ indinfo hfind
  have hCi : ∀ (nm : Name) (ci : ConstantInfo) (s' s'' : ErasureState)
      (w' w'' : Void IO.RealWorld),
      (getConstInfo nm : EraseM ConstantInfo) s' ctx cctx ref w' = .ok (ci, s'') w'' →
      lenv.find? nm = some ci ∧ gw w' ≤ gw w'' := fun nm ci _ _ w' w'' h =>
    let k := P.lookup_adequate.constInfo nm cctx ref w' ci w'' (pass_getConstInfo_core h)
    ⟨k.2, k.1⟩
  obtain ⟨hfresh, bodies, sM, hs1, -, -, hce, hgrow, hreport⟩ :=
    run_register_inductive_cold_ok (Ci := fun nm ci => lenv.find? nm = some ci)
      (fun nm ci s' s'' w' w'' h => (hCi nm ci s' s'' w' w'' h).1) hmiss hrun
  have hents := (run_register_inductive_cold_entries (Ci := fun nm ci => lenv.find? nm = some ci)
    (gw := gw) hCi
    (fun le s₀ s₂ w₀ w₂ h => P.prim_monotone.getEnv s₀ ctx cctx ref w₀ le s₂ w₂ h)
    (fun msg u s₀ s₂ w₀ w₂ h => P.prim_monotone.logInfo msg s₀ ctx cctx ref w₀ u s₂ w₂ h)
    hcfg.2.2.2.1 hmiss hrun).2
  have hmembers : ∀ n ∈ indinfo.all,
      (∃ iv : InductiveVal, lenv.find? n = some (.inductInfo iv)) →
      (s₁.inductives.get? n).isSome :=
    run_register_inductive_members
      (fun nm ci _s' _s'' w' w'' hci _hnm hiv =>
        let ⟨iv, hlen⟩ := hiv
        ⟨iv, Option.some.inj (((hCi nm ci _s' _s'' w' w'' hci).1).symm.trans hlen)⟩)
      hmiss hrun
  have hinds : s₁.inductives = sM.inductives := by rw [hs1]; rfl
  -- the escape disjunct of the two registry reports, refuted
  have hnotreg : ∀ (n : Name) (iid : InductiveId) (np : Nat) (nfs : List Nat),
      IndInfo env n iid np nfs → iid.mutualBlockName = mutualBlockKn indinfo →
      ¬ (s.inductives.get? n).isSome := by
    intro n iid np nfs hi hkn hsome
    obtain ⟨-, mib, hlook, -, -⟩ := (Acc.shape.inds n hsome).block iid np nfs hi
    rw [hkn] at hlook
    obtain ⟨mib', hmem⟩ := Acc.keysEmitted.inds _ mib hlook
    exact blockKey_fresh_of_cover hcovs hfresh hfind hself hmiss mib' hmem
  -- what one declared member of the block leaves behind
  have hdata : ∀ (I : Name) (iid : InductiveId) (np : Nat) (nfs : List Nat),
      I ∈ indinfo.all → IndInfo env I iid np nfs →
      ∃ (ivm : InductiveVal) (oib : OneInductiveBody),
        lenv.find? I = some (.inductInfo ivm) ∧
        indinfo.all[iid.idx]? = some I ∧
        iid = ⟨mutualBlockKn indinfo, iid.idx⟩ ∧ np = indinfo.numParams ∧
        ivm.numParams = np ∧ nfs = kernelFieldsOf lenv ivm ∧
        bodies[iid.idx]? = some oib ∧ oib.ctors.map (·.nargs) = nfs ∧
        (oib.propositional = true → PropositionalInd env I) := by
    intro I iid np nfs hImem hi
    obtain ⟨ivm, hfindI, hnameI, hnpI, hkfI⟩ := P.block_adequate.bwd I np nfs hi.arity
    obtain ⟨i, hidx⟩ := List.getElem?_of_mem hImem
    have hfwd := P.block_adequate.fwd indinfo.name I indinfo ivm i nfs hfind hidx hfindI hkfI
    obtain ⟨rfl, rfl, -⟩ := IndInfo.inj A hi hfwd
    have hkn : (⟨indBlockKername indinfo.all, i⟩ : InductiveId).mutualBlockName
        = mutualBlockKn indinfo := rfl
    obtain ⟨rc, hrc⟩ := Option.isSome_iff_exists.mp (hmembers I hImem ⟨ivm, hfindI⟩)
    rcases hents I rc hrc with hold | ⟨idx, inf, hidx2, hCinf, hlen2, hrc1, hmask⟩
    · exact absurd (by rw [hold]; rfl) (hnotreg I _ _ _ hfwd hkn)
    · obtain rfl : inf = ivm := by
        have h := Option.some.inj (hCinf.symm.trans hfindI)
        injection h
      have hidxeq : i = idx := by
        have h2 := P.block_adequate.fwd indinfo.name I indinfo inf idx nfs hfind hidx2 hfindI hkfI
        exact congrArg InductiveId.idx (IndInfo.inj A hfwd h2).1
      subst hidxeq
      rcases hreport (by rw [← hinds]; exact hrc) with hold
        | ⟨oib, hkn2, hbod, -, ⟨inf2, hCinf2, hflag⟩, hctors⟩
      · exact absurd (by rw [hold]; rfl) (hnotreg I _ _ _ hfwd hkn)
      · have hinf2 : inf2 = inf := by
          have h := Option.some.inj (hCinf2.symm.trans hfindI)
          injection h
        rw [hinf2] at hflag
        refine ⟨inf, oib, hfindI, hidx2, rfl, rfl, hnpI, kernelFieldsOf_eq hkfI, ?_, ?_, ?_⟩
        · rw [hrc1] at hbod; exact hbod
        · rw [hctors]
          refine List.ext_getElem? (fun j => ?_)
          rw [List.getElem?_map]
          cases hj : inf.ctors[j]? with
          | none =>
            rw [List.getElem?_eq_none (by rw [hlen2]; exact List.getElem?_eq_none_iff.mp hj),
              List.getElem?_eq_none (by rw [hkfI.1]; exact List.getElem?_eq_none_iff.mp hj)]
            rfl
          | some cn =>
            obtain ⟨cv, hcvf, hnfj, -, -, -⟩ := hkfI.2 j cn hj
            obtain ⟨ci, hci, hmk⟩ := hmask j cn hj
            obtain rfl : ci = .ctorInfo cv := Option.some.inj (hci.symm.trans hcvf)
            rw [hmk cv rfl, hnfj]
            simp only [Option.map_some]
            congr 1
            rw [Array.count, ← Array.countP_toList]
            simp only [Array.toList_replicate, List.countP_eq_length_filter,
              List.filter_replicate,
              if_pos (by decide : (Erasure.ConstructorArgRelevance.keep
                == Erasure.ConstructorArgRelevance.keep) = true),
              List.length_replicate]
        · intro hp
          exact P.propositionalInd_of_arity hfindI (hsafe I inf hfindI) (hflag ▸ hp)
  -- the slots, read back
  have hslot : ∀ e ∈ elimSlots lenv indinfo bodies,
      ∃ (inf : InductiveVal) (oib : OneInductiveBody) (nm : Nat),
        lenv.find? e.name = some (.inductInfo inf) ∧ e.name ∈ indinfo.all ∧
        IndInfo env e.name ⟨mutualBlockKn indinfo, e.idx⟩ indinfo.numParams e.fields ∧
        bodies[e.idx]? = some oib ∧ oib.propositional = false ∧
        oib.ctors.map (·.nargs) = e.fields ∧
        CasesOnShape env (Name.str e.name "casesOn") e.name e.dropped nm := by
    intro e he
    obtain ⟨hidx, ⟨inf, hfindI, hdrop, hfld⟩, oib, hbod, hprop⟩ := elimSlots_spec he
    have hmem : e.name ∈ indinfo.all := List.mem_of_getElem? hidx
    obtain ⟨nfs, hkf⟩ := P.block_adequate.fields e.name inf hfindI
    have hfeq : nfs = e.fields := by rw [hfld, kernelFieldsOf_eq hkf]
    have hii := P.block_adequate.fwd indinfo.name e.name indinfo inf e.idx nfs hfind hidx
      hfindI hkf
    rw [hfeq] at hii
    obtain ⟨-, oib', -, -, -, -, -, -, hbod', hctors, -⟩ := hdata e.name _ _ _ hmem hii
    have hoo : oib' = oib := Option.some.inj (hbod'.symm.trans hbod)
    rw [hoo] at hctors
    obtain ⟨nm, vc, -, -, hsh⟩ := P.block_adequate.casesOnDecl (Name.str e.name "casesOn")
      e.name inf rfl rfl hfindI
    exact ⟨inf, oib, nm, hfindI, hmem, hii, hbod, hprop, hctors, hdrop ▸ hsh⟩
  -- the prefix's keys are distinct
  have hfreshKey : ∀ e ∈ elimSlots lenv indinfo bodies,
      toKername (Name.str e.name "casesOn") ≠ mutualBlockKn indinfo := by
    intro e he
    obtain ⟨_inf, _oib, _nm, -, -, -, -, -, -, hsh⟩ := hslot e he
    exact K.elims _ _ _ _ indinfo.all hsh
  have hinj : ∀ e ∈ elimSlots lenv indinfo bodies, ∀ f ∈ elimSlots lenv indinfo bodies,
      toKername (Name.str e.name "casesOn") = toKername (Name.str f.name "casesOn") → e = f := by
    intro e he f hf hk
    obtain ⟨_inf1, _oib1, _nm1, hfindE, hmemE, hiiE, -, -, -, -⟩ := hslot e he
    obtain ⟨_inf2, _oib2, _nm2, hfindF, hmemF, hiiF, -, -, -, -⟩ := hslot f hf
    have hname : e.name = f.name := by
      refine K.memberNames f.name hmemF e.name ?_
      have := congrArg Kername.mp hk
      simpa [toKername] using this
    obtain ⟨hidxE, ⟨infE, hfE, hdE, hfldE⟩, -⟩ := elimSlots_spec he
    obtain ⟨hidxF, ⟨infF, hfF, hdF, hfldF⟩, -⟩ := elimSlots_spec hf
    rw [hname] at hfE hiiE
    obtain rfl : infE = infF := by
      have h := Option.some.inj (hfE.symm.trans hfF)
      injection h
    have hidx : e.idx = f.idx := by
      rw [hname] at hidxE
      have hkfE : KernelFields lenv infE (kernelFieldsOf lenv infE) := by
        obtain ⟨nfs, hkf⟩ := P.block_adequate.fields f.name infE hfF
        exact (kernelFieldsOf_eq hkf) ▸ hkf
      have h1 := P.block_adequate.fwd indinfo.name f.name indinfo infE e.idx
        (kernelFieldsOf lenv infE) hfind hidxE hfF hkfE
      have h2 := P.block_adequate.fwd indinfo.name f.name indinfo infE f.idx
        (kernelFieldsOf lenv infE) hfind hidxF hfF hkfE
      exact congrArg InductiveId.idx (IndInfo.inj A h1 h2).1
    obtain ⟨n1, i1, d1, f1⟩ := e
    obtain ⟨n2, i2, d2, f2⟩ := f
    simp only [ElimSlot.mk.injEq]
    exact ⟨hname, hidx, hdE.trans hdF.symm, hfldE.trans hfldF.symm⟩
  have hnodup : ((indPrefix indinfo bodies (elimSlots lenv indinfo bodies)).map Prod.fst).Nodup := by
    rw [indPrefix, List.map_cons, List.map_map, List.nodup_cons]
    refine ⟨?_, ?_⟩
    · intro hmem
      obtain ⟨e, he, hk⟩ := List.mem_map.mp hmem
      exact hfreshKey e he hk
    · rw [List.Nodup, List.pairwise_map]
      refine List.Pairwise.imp_of_mem ?_ (List.Pairwise.filterMap
        (l := indinfo.all.zipIdx)
        (R := fun p q => p.2 ≠ q.2)
        (S := fun e f => e.idx ≠ f.idx) _ ?_ ?_)
      · intro e f he hf hne hk
        exact hne (congrArg ElimSlot.idx (hinj e he f hf hk))
      · intro a a' hne b hb b' hb'
        have hbi : b.idx = a.2 := by
          split at hb
          · split at hb
            · exact absurd hb (by simp)
            · cases hb; rfl
          · exact absurd hb (by simp)
        have hbi' : b'.idx = a'.2 := by
          split at hb'
          · split at hb'
            · exact absurd hb' (by simp)
            · cases hb'; rfl
          · exact absurd hb' (by simp)
        rw [hbi, hbi']; exact hne
      · rw [← List.pairwise_map (f := Prod.snd) (R := (· ≠ ·)), List.zipIdx_map_snd]
        exact List.nodup_range'
  have hlookElim : ∀ e ∈ elimSlots lenv indinfo bodies,
      LBTerm.envLookup (indPrefix indinfo bodies (elimSlots lenv indinfo bodies))
          (toKername (Name.str e.name "casesOn"))
        = some (.constantDecl ⟨some (mkElimBody ⟨mutualBlockKn indinfo, e.idx⟩
            indinfo.numParams e.dropped e.fields)⟩) := by
    intro e he
    exact envLookup_of_mem_nodup
      (p := elimEntry (mutualBlockKn indinfo) indinfo.numParams e)
      (by rw [indPrefix]; exact List.mem_cons_of_mem _ (List.mem_map_of_mem he)) hnodup
  have hcov : ∀ I ∈ indinfo.all,
      IndCovered env (indPrefix indinfo bodies (elimSlots lenv indinfo bodies)) I := by
    intro I hI
    refine ⟨?_, ?_⟩
    · intro iid np nfs hi
      obtain ⟨inf, oib, hfindI, hidxI, hiid, hnp, -, -, hbod, hctors, hflag⟩ :=
        hdata I iid np nfs hI hi
      refine ⟨IndInfo.indDeclOf A hi, { npars := indinfo.numParams, bodies := bodies }, ?_,
        ⟨hnp.symm, oib, hbod, hctors⟩, fun oib' hoib' hp => ?_⟩
      · rw [hiid]; exact indPrefix_block
      · obtain rfl : oib' = oib := Option.some.inj (hoib'.symm.trans hbod)
        exact hflag hp
    · intro c dp nm hsh hinf hco
      obtain ⟨ds, env₀, decl, t, hds, hd, hle, ht, hnameI, hdp, hnm⟩ := hsh.2.2.2
      obtain ⟨iid0, hi0⟩ :=
        IndArity.indInfo (env := env) (I := I) (np := decl.nparams)
          (nfs := ctorFieldCounts decl.nparams t)
          ⟨ds, env₀, decl, t, hds, hd, hle, ht, hnameI, rfl, rfl⟩
      obtain ⟨inf, oib, hfindI, hidxI, hiid, hnp, -, hnfs, hbod, hctors, hflag⟩ :=
        hdata I iid0 _ _ hI hi0
      obtain ⟨nm', vc, -, -, hsh'⟩ := P.block_adequate.casesOnDecl c I inf hsh.1 hsh.2.1 hfindI
      obtain ⟨hdpeq, hnmeq⟩ := CasesOnShape.inj A hsh hsh'
      have hpf : oib.propositional = false := propositional_false_of_informative hflag hinf
      have hmemslot := elimSlots_mem (indinfo := indinfo) hidxI hfindI hbod hpf
      have hckey : toKername c = toKername (Name.str I "casesOn") := by
        rw [eq_str_casesOn hsh.1, hsh.2.1]
      refine ⟨iid0, decl.nparams, ctorFieldCounts decl.nparams t, ⟨⟨_, ?_, .cases⟩, ?_⟩, hi0, ?_⟩
      · rw [hckey]
        have hl := hlookElim _ hmemslot
        simp only [] at hl
        rw [hl, hnp, ← hnfs, ← hdpeq, ← hiid, hnp]
      · exact ⟨{ npars := indinfo.numParams, bodies := bodies },
          by rw [hiid]; exact indPrefix_block,
          ⟨hnp.symm, oib, hbod, hctors⟩, oib, hbod, hpf⟩
      · rw [ctorFieldCounts, List.length_map]
        exact hnm.symm
  refine ⟨indPrefix indinfo bodies (elimSlots lenv indinfo bodies), ⟨hcov, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- content
    refine ⟨hnodup, ?_, ?_, ?_, ?_⟩
    · intro c b hbo hs
      obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hs
      rcases indPrefix_key_cases hd with ⟨hk, -⟩ | ⟨e, he, hk, -⟩
      · exact absurd hk (K.bodied c b hbo)
      · exact absurd (toKername_of_cleanIdent_casesOn hk) (by rw [K.notCasesOn c b hbo]; simp)
    · intro c hbo hco hnc hs
      obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hs
      rcases indPrefix_key_cases hd with ⟨hk, -⟩ | ⟨e, he, hk, -⟩
      · obtain ⟨iid, np, nfs, hi⟩ := K.consts c hco hk
        exact absurd hi (constOrigin_not_indInfo A hco iid np nfs)
      · exact absurd (toKername_of_cleanIdent_casesOn hk) (by rw [hnc]; simp)
    · intro I iid np nfs hi hs
      obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hs
      rcases indPrefix_key_cases hd with ⟨hk, -⟩ | ⟨e, he, hk, -⟩
      · exact hcov I (K.blocks I iid np nfs hi hk)
      · obtain ⟨ds, env₀, decl, t, -, -, -, -, -, hkn, -, -⟩ := hi.block
        obtain ⟨_i, _o, _n, -, -, -, -, -, -, hsh⟩ := hslot e he
        exact absurd (hk ▸ hkn) (K.elims _ _ _ _ (decl.types.map (·.name)) hsh)
    · intro c I dp nm hsh hs
      obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hs
      rcases indPrefix_key_cases hd with ⟨hk, -⟩ | ⟨e, he, hk, -⟩
      · exact absurd hk (K.elims c I dp nm indinfo.all hsh)
      · obtain ⟨_i, _o, _n, -, hmemE, -, -, -, -, -⟩ := hslot e he
        have hckey : toKername c = toKername (Name.str I "casesOn") := by
          rw [eq_str_casesOn hsh.1, hsh.2.1]
        have hIe : I = e.name := by
          refine K.memberNames e.name hmemE I ?_
          have h := congrArg Kername.mp (hckey.symm.trans hk)
          simpa [toKername] using h
        rw [hIe]
        exact hcov e.name hmemE
  · exact ⟨_, indPrefix_block⟩
  · -- entries
    intro p hp
    rw [indPrefix, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact Or.inl ⟨rfl, _, rfl⟩
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp
      obtain ⟨_i, oib, _n, -, -, -, hbod, hpf, hctors, -⟩ := hslot e he
      refine Or.inr ⟨⟨⟨mutualBlockKn indinfo, e.idx⟩, indinfo.numParams, e.dropped, e.fields,
        ⟨_, ?_, .cases⟩, { npars := indinfo.numParams, bodies := bodies }, indPrefix_block,
        ⟨rfl, oib, hbod, hctors⟩, oib, hbod, hpf⟩, _, _, _, _, _, rfl, .cases⟩
      exact hlookElim e he
  · -- elimKeys
    intro p hp
    rw [indPrefix, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact Or.inl rfl
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp
      obtain ⟨-, -, nm, -, -, hii, -, -, -, hsh⟩ := hslot e he
      exact Or.inr ⟨Name.str e.name "casesOn", e.name, e.dropped, nm,
        ⟨mutualBlockKn indinfo, e.idx⟩, indinfo.numParams, e.fields, rfl, hsh, hii, rfl⟩
  · intro mib hmib
    rw [hs1, registerIndState] at hmib
    simp only [] at hmib
    rw [envLookup_cons_self] at hmib
    have h := Option.some.inj hmib
    injection h with h'
    rw [← h']
    exact indPrefix_block

/-! ## The accumulator across a block registration, produced from a run

`regInv_registerInd_step` takes thirteen premises; `regInv_registerInd_run` produces them.
The prefix and its block entry come from `indPrefixOf_of_run`; the key discipline from
`blockKey_fresh_of_cover` and `constKey_fresh`, which is why `RegKeyed`, `CanonicalConstants`
and `IndBlocksCover` are premises; `hnewc` and `hkeys` from the two pinned-config run
lemmas, `hnewi` from `run_register_inductive_cold_registry` beside the prefix's coverage.

Two premises are not about this call at all but about the pair the accumulator does not
constrain. `RuntimeKeysModelled` refutes an eliminator entry of `Γspec` at the key the run
mints — `SpecKeysEmitted.consts` exempts a runtime key, so without it `Γspec` may declare one
at a key no source name prints as, and the prefix would not be fresh. `EmittedNotRuntime`
refutes an emitted entry at a runtime key, which is what lets `RegInvShape'.defsTotal` read a
body-less emitted entry back as a body-less specification entry and pay `haxpre`. Both are
re-established at the grown pair, so the induction that spends them can carry them.
-/

set_option maxHeartbeats 1000000 in
/-- **The registration step, at a run.** `regInv_registerInd_step`'s thirteen premises
produced rather than assumed, with the prefix existential and the two clauses
`SpecKeysEmitted` exempts carried across. -/
theorem regInv_registerInd_run {lenv : Environment} {env : VEnv} {Us : List Name}
    {gw : Void IO.RealWorld → NameGenerator} {bo : Name → Option Expr}
    {lp : Name → List Name} {Γ : GlobalDeclarations} {indinfo : InductiveVal}
    {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
    {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
    {r : InductiveId × InductiveArgMasks} {s₁ : ErasureState} {w₁ : Void IO.RealWorld}
    (P : ErasureSpec lenv env Us gw) (A : UpstreamAsks env)
    (Acc : RegAcc env bo lp Γ s)
    (hkeyed : RegKeyed env s) (hcanon : CanonicalConstants s)
    (hcovs : IndBlocksCover lenv s)
    (hrkm : RuntimeKeysModelled env Γ) (henr : EmittedNotRuntime Γ s)
    (K : BodiedKeysFresh env bo indinfo)
    (hsafe : ∀ (I : Name) (iv : InductiveVal), lenv.find? I = some (.inductInfo iv) →
      DefinitionSafety.safe ≤ (ConstantInfo.inductInfo iv).safety)
    (hcfg : ConfigPinned ctx.config)
    (hfind : lenv.find? indinfo.name = some (.inductInfo indinfo))
    (hmiss : s.inductives.get? indinfo.name = none)
    (hrun : Erasure.register_inductive indinfo s ctx cctx ref w = .ok (r, s₁) w₁) :
    ∃ pre : GlobalDeclarations, IndPrefixOf env bo lp indinfo pre ∧
      SpecGrow Γ (pre ++ Γ) ∧ RegAcc env bo lp (pre ++ Γ) s₁ ∧
      RuntimeKeysModelled env (pre ++ Γ) ∧ EmittedNotRuntime (pre ++ Γ) s₁ := by
  obtain ⟨pre, HP, hblkpre⟩ :=
    indPrefixOf_of_run P A Acc hcovs K hsafe hcfg hfind hmiss hrun
  refine ⟨pre, HP, ?_⟩
  have hself : indinfo.name ∈ indinfo.all := P.block_adequate.selfMem _ indinfo hfind
  have hfreshG : IndKernameFresh indinfo.all (mutualBlockKn indinfo) s :=
    (run_register_inductive_cold_ok (Ci := fun _ _ => True)
      (fun _ _ _ _ _ _ _ => trivial) hmiss hrun).1
  have hbfresh := blockKey_fresh_of_cover hcovs hfreshG hfind hself hmiss
  have hcfresh := constKey_fresh hkeyed hcanon hfreshG
  obtain ⟨mib₁, hgd⟩ := run_register_inductive_cold_gdecls hcfg.2.1 hmiss hrun
  obtain ⟨mib₀, hpreblk⟩ := HP.block
  have hblockNotIn : mutualBlockKn indinfo ∉ s.gdecls.map Prod.fst := by
    intro hk
    obtain ⟨q, hq, hqk⟩ := List.mem_map.mp hk
    obtain ⟨k, d⟩ := q
    simp only [] at hqk
    subst hqk
    cases d with
    | constantDecl cb => exact hcfresh cb hq
    | inductiveDecl mib => exact hbfresh mib hq
  have hblockNot : ∀ mib, LBTerm.envLookup Γ (mutualBlockKn indinfo)
      ≠ some (.inductiveDecl mib) := by
    intro mib hlook
    obtain ⟨mib', hmem⟩ := Acc.keysEmitted.inds _ mib hlook
    exact hbfresh mib' hmem
  -- the prefix is fresh against the specification environment
  have hfresh : ∀ p ∈ pre, ∀ q ∈ Γ, p.1 ≠ q.1 := by
    intro p hp q hq hpq
    have hqlook : LBTerm.envLookup Γ q.1 = some q.2 :=
      envLookup_of_mem_nodup hq Acc.shape.spec.keys
    rcases HP.elimKeys p hp with hk | ⟨c, I, dp, nm, iid, np, nfs, hk, hsh, hi, hiid⟩
    · rw [hk] at hpq
      obtain ⟨k, d⟩ := q
      simp only [] at hpq hqlook
      subst hpq
      cases d with
      | inductiveDecl mib => exact hblockNot mib hqlook
      | constantDecl cb =>
        by_cases hrk : RuntimeKey Γ (mutualBlockKn indinfo)
        · obtain ⟨c', I', dp', nm', hsh', hkc⟩ := hrkm _ hrk
          exact K.elims c' I' dp' nm' indinfo.all hsh' hkc.symm
        · obtain ⟨cb', hmem⟩ := Acc.keysEmitted.consts _ cb hqlook hrk
          exact hcfresh cb' hmem
    · have hs : (LBTerm.envLookup Γ (toKername c)).isSome := by
        rw [← hk, hpq, hqlook]; rfl
      obtain ⟨-, mib, hlook, -, -⟩ :=
        (Acc.shape.spec.elims c I dp nm hsh hs).block iid np nfs hi
      rw [hiid] at hlook
      exact hblockNot mib hlook
  have hg : SpecGrow Γ (pre ++ Γ) :=
    SpecGrow.of_fresh hfresh (elimBlocksDeclared_of_constsDeclaredEnv Acc.content.declEnv)
  -- the prefix's bodies are eliminators'
  have hpreBody : ∀ (kn : Kername) (b : LBTerm), DefnDecl pre kn b →
      ∃ (iid : InductiveId) (np dp : Nat) (nfs : List Nat), ElimBody iid np dp nfs b ∧
        RuntimeKey pre kn := by
    intro kn b hd
    have hmem := envLookup_mem hd
    rcases HP.entries _ hmem with ⟨-, mib, hshape⟩ | ⟨hrk, body, iid, np, dp, nfs, hshape, he⟩
    · exact absurd hshape (by simp)
    · simp only [GlobalDecl.constantDecl.injEq, ConstantBody.mk.injEq,
        Option.some.injEq] at hshape
      exact ⟨iid, np, dp, nfs, hshape ▸ he, hrk⟩
  have hcl : ClosedBodies pre := by
    intro kn b hd
    obtain ⟨iid, np, dp, nfs, he, -⟩ := hpreBody kn b hd
    exact he.closed
  have hfv : FVarFreeBodies pre := by
    intro kn b x hd
    obtain ⟨iid, np, dp, nfs, he, -⟩ := hpreBody kn b hd
    exact he.noFVar
  -- the δ column at the grown environment
  have hdenv : ConstsDeclaredEnv (pre ++ Γ) := by
    intro kn b hd kn' hkn'
    rcases envLookup_append_cases hd with h1 | ⟨-, h2⟩
    · obtain ⟨iid, np, dp, nfs, -, hrk⟩ := hpreBody kn b h1
      obtain ⟨iid', np', dp', nfs', ⟨body', hlook', he'⟩, mib, hmib, -, -⟩ := hrk
      have hbe : body' = b := by
        rw [h1] at hlook'
        injection Option.some.inj hlook' with h'
        injection h' with h''
        exact (Option.some.inj h'').symm
      subst hbe
      rw [constRefs_elimBody he'] at hkn'
      simp only [List.mem_singleton] at hkn'
      subst hkn'
      rw [envLookup_append_left hmib]
      rfl
    · exact envLookup_append_isSome (Acc.content.declEnv kn b h2 kn' hkn')
  -- saturation at the prefix
  have hkpre : SpecKeysEmitted pre s₁ := by
    refine ⟨?_, ?_⟩
    · intro kn cb hlook hrk
      have hmem := envLookup_mem hlook
      rcases HP.entries _ hmem with ⟨-, mib, hshape⟩ | ⟨hrk', -⟩
      · exact absurd hshape (by simp)
      · exact absurd hrk' hrk
    · intro kn mib hlook
      have hmem := envLookup_mem hlook
      rcases HP.entries _ hmem with ⟨hk, -⟩ | ⟨-, body, iid, np, dp, nfs, hshape, -⟩
      · refine ⟨mib₁, ?_⟩
        rw [hgd, show kn = mutualBlockKn indinfo from hk]
        exact List.mem_cons_self
      · exact absurd hshape (by simp)
  -- the state-facing side conditions
  have hkeys : (s₁.gdecls.map Prod.fst).Nodup := by
    rw [hgd, List.map_cons, List.nodup_cons]
    exact ⟨hblockNotIn, Acc.shape.keys⟩
  have haxpre : ∀ p ∈ s₁.gdecls, p.2 = GlobalDecl.constantDecl ⟨none⟩ →
      LBTerm.envLookup (pre ++ Γ) p.1 = some (.constantDecl ⟨none⟩) := by
    intro p hp hax
    rw [hgd, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact absurd hax (by simp)
    · obtain ⟨k, d⟩ := p
      simp only [] at hax ⊢
      subst hax
      have hemit : LBTerm.envLookup s.gdecls k = some (.constantDecl ⟨none⟩) :=
        envLookup_of_mem_nodup (p := (k, GlobalDecl.constantDecl ⟨none⟩)) hp Acc.shape.keys
      have hnrk : ¬ RuntimeKey Γ k := henr k (by rw [hemit]; rfl)
      obtain ⟨n, hkn, hns⟩ := hkeyed.consts k ⟨none⟩ hp
      have hdecl : (LBTerm.envLookup Γ k).isSome := by rw [hkn]; exact Acc.shape.consts n hns
      obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hdecl
      have hfin : d = GlobalDecl.constantDecl ⟨none⟩ := by
        cases d with
        | inductiveDecl mib =>
          obtain ⟨mib', hmem⟩ := Acc.keysEmitted.inds _ mib hd
          have hcl' := envLookup_of_mem_nodup (p := (k, GlobalDecl.inductiveDecl mib')) hmem
            Acc.shape.keys
          rw [hemit] at hcl'
          exact absurd hcl' (by simp)
        | constantDecl cb =>
          obtain ⟨body⟩ := cb
          cases body with
          | none => rfl
          | some b =>
            have hdd : DefnDecl Γ (toKername n) b := by rw [DefnDecl, ← hkn]; exact hd
            obtain ⟨b', hb'⟩ := Acc.shape.defsTotal n b hns hdd (by rw [← hkn]; exact hnrk)
            rw [DefnDecl, ← hkn, hemit] at hb'
            exact absurd hb' (by simp)
      rw [← hfin]
      exact envLookup_append_of_fresh
        (fun q hq => hfresh q hq (k, d) (envLookup_mem hd)) hd
  have hblk : ∀ mib, LBTerm.envLookup s₁.gdecls (mutualBlockKn indinfo)
      = some (.inductiveDecl mib) →
      LBTerm.envLookup (pre ++ Γ) (mutualBlockKn indinfo) = some (.inductiveDecl mib) :=
    fun mib h => envLookup_append_left (hblkpre mib h)
  have hnewc : ∀ n : Name, (s₁.constants.get? n).isSome → (s.constants.get? n).isSome ∨
      LBTerm.envLookup (pre ++ Γ) (toKername n) = some (.constantDecl ⟨none⟩) := by
    intro n hn
    exact .inl (by rwa [run_register_inductive_cold_constants hcfg.2.1 hmiss hrun] at hn)
  have hnewi : ∀ n : Name, (s₁.inductives.get? n).isSome → (s.inductives.get? n).isSome ∨
      (IndCovered env (pre ++ Γ) n ∧ IndEmitted env (pre ++ Γ) s₁.gdecls n) := by
    intro n hn
    rcases run_register_inductive_cold_registry hmiss hrun n hn with hold | hmem
    · exact .inl hold
    · refine .inr ⟨(HP.covered n hmem).appendLeft, ?_⟩
      intro iid np nfs hi d hd
      obtain ⟨-, mib, hlook, -, -⟩ := (HP.covered n hmem).block iid np nfs hi
      have hblockKey : iid.mutualBlockName = mutualBlockKn indinfo := by
        rcases HP.entries _ (envLookup_mem hlook) with ⟨hk, -⟩ | ⟨-, _, _, _, _, _, hshape, -⟩
        · exact hk
        · exact absurd hshape (by simp)
      rw [envLookup_append_left hlook] at hd
      have hmd : mib = d := by injection Option.some.inj hd
      subst hmd
      rw [hblockKey] at hlook ⊢
      have hs₁ : LBTerm.envLookup s₁.gdecls (mutualBlockKn indinfo)
          = some (.inductiveDecl mib₁) := by rw [hgd]; exact envLookup_cons_self
      have hme : mib₁ = mib := by
        have h := hblkpre mib₁ hs₁
        rw [hlook] at h
        injection Option.some.inj h with hh
        exact hh.symm
      rw [hs₁, hme]
  -- the two carried clauses, re-established
  have hrkm' : RuntimeKeysModelled env (pre ++ Γ) := by
    intro kn hrk
    obtain ⟨iid, np, dp, nfs, hed⟩ := hrk
    obtain ⟨body, hlook, he⟩ := hed.1
    rcases envLookup_append_cases hlook with h1 | ⟨-, h2⟩
    · rcases HP.elimKeys _ (envLookup_mem h1) with
        hk | ⟨c, I, dp', nm, iid', np', nfs', hk, hsh, -, -⟩
      · have hk' : kn = mutualBlockKn indinfo := hk
        rw [hk', hpreblk] at h1
        exact absurd h1 (by simp)
      · exact ⟨c, I, dp', nm, hsh, hk⟩
    · exact hrkm kn (hg.runtimeKey (by rw [h2]; rfl) ⟨iid, np, dp, nfs, hed⟩)
  have henr' : EmittedNotRuntime (pre ++ Γ) s₁ := by
    intro kn hkn hrk
    rw [hgd] at hkn
    by_cases hk : mutualBlockKn indinfo = kn
    · subst hk
      obtain ⟨iid, np, dp, nfs, ⟨body, hlook, -⟩, -⟩ := hrk
      rw [envLookup_append_left hpreblk] at hlook
      exact absurd hlook (by simp)
    · rw [envLookup_cons_ne hk] at hkn
      obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hkn
      have hsub : (LBTerm.envLookup Γ kn).isSome := by
        cases hc : LBTerm.envLookup Γ kn with
        | none => exact absurd hc (Acc.shape.sub kn (by rw [hd]; simp))
        | some d' => rfl
      exact henr kn hkn (hg.runtimeKey hsub hrk)
  exact ⟨hg, (regInv_registerInd_step Acc HP.content hfresh hcl hfv hkpre hdenv hmiss hrun
    hkeys haxpre hblk hnewc hnewi).2, hrkm', henr'⟩

end LeanToLambdaBox
