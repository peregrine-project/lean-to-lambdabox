import LeanToLambdaBox.VisitExprRefines.Motives

/-!
# The pass-facing steps of the bridge induction

Seven of the eight members whose emitted node is a λ□ *pass* node — the constructor block, the
projection, the two η entry points, the two η loops — together with the literal tower that
rebuilds a `Nat` through the constructor member. Each step concludes its motive through a
derived introduction lemma of `ErasesLB`/`ErasesLBFix`, never by re-proving a `Lower` fact
inline; `ErasesLB.lit` and `ErasesLB.proj` are the two such lemmas the composite's own module
leaves out, and they are proved here.

Steps 2, 13, 14, 15 and 16 conclude the induction's own `Stepᵢ`. Steps 3 and 10 conclude
`Step3Reg` and `Step10Reg`, motive 3 and motive 10 carrying one extra premise —
`IndRegistryModelled`, the inductive-registry twin of `BridgeInv.canon`. The emitted
`.construct` and `.proj` nodes read their `InductiveId` and their argument masks out of that
registry, and nothing in `BridgeInv` says what it holds, so at a registry hit the node's
identifier is unconstrained. Once `BridgeInv` records it, `Motive3Reg → Motive3` and
`Motive10Reg → Motive10` are one `obtain` each.

The facts these steps need that `ErasureSpec` does not carry are named premises of the step
lemmas that need them, one clause each: `InferTypeMonotone` and `GetEnvMonotone` (two
primitives that only advance the generator), `CtorAdequate`, `CtorDeclModelled` and
`IndDeclModelled` (the constructor and block readings of a declaration, which
`ErasureSpec.decl_adequate` does not give), and `RegisterModels` (what a registration reports,
guarded by the registry invariant). Every one is class **D**, and each docstring says what it
would be as an `ErasureSpec` field.
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

/-! ## `CoreM` runs under an `EraseM` run

`ErasureSpec.LookupAdequate` is stated at `CoreM`, and the erasure calls `Lean.getConstInfo`
elaborated at `EraseM`; the two are not definitionally equal, so the bridge is proved.
-/

/-- Running a `CoreM` bind, the `EraseM` `run_bind`'s twin one layer down. -/
theorem pass_core_bind {α β : Type} (x : CoreM α) (f : α → CoreM β) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) :
    (x >>= f) cctx ref w =
      match x cctx ref w with
      | .ok a w₁ => f a cctx ref w₁
      | .error e w₁ => .error e w₁ := by
  cases hx : x cctx ref w with
  | ok a w₁ => show EST.bind (x cctx ref) _ w = _; unfold EST.bind; rw [hx]
  | error e w₁ => show EST.bind (x cctx ref) _ w = _; unfold EST.bind; rw [hx]

set_option maxHeartbeats 1000000 in
/-- **A successful `EraseM` lookup is a successful `CoreM` lookup**, at the same world tokens.
This is what makes `ErasureSpec.LookupAdequate.constInfo` applicable to the erasure's own
calls. -/
theorem pass_getConstInfo_core {nm : Name} {ci : ConstantInfo} {s s₁ : ErasureState}
    {ctx : ErasureContext} {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
    {w w₁ : Void IO.RealWorld}
    (h : (Lean.getConstInfo nm : EraseM ConstantInfo) s ctx cctx ref w = .ok (ci, s₁) w₁) :
    (Lean.getConstInfo nm : CoreM ConstantInfo) cctx ref w = .ok ci w₁ := by
  unfold Lean.getConstInfo at h ⊢
  rw [run_bind_ok] at h
  obtain ⟨e, s₂, w₂, henv, hk⟩ := h
  have hs2 : s₂ = s := run_getEnv_state _ _ _ _ _ henv
  subst hs2
  have henvC : (getEnv : CoreM Environment) cctx ref w = .ok e w₂ :=
    ((run_liftCoreM_ok _ _ _ _ _).mp henv).1
  rw [pass_core_bind, henvC]
  cases hfind : e.find? nm with
  | some info =>
    rw [hfind] at hk
    simp only [] at hk
    rw [run_pure] at hk
    cases hk
    simp only [hfind]
    rfl
  | none =>
    rw [hfind] at hk
    simp only [] at hk
    unfold Lean.throwUnknownConstant at hk
    refine absurd hk (run_bind_ne_ok _ ctx cctx ref w₂ ?_ _ _ _)
    intro a s₃ w₃ b s₄ w₄
    unfold Lean.throwUnknownConstantAt Lean.throwUnknownIdentifierAt
    refine run_bind_ne_ok _ ctx cctx ref w₃ ?_ _ _ _
    intro a' s₅ w₅ b' s₆ w₆
    unfold Lean.throwErrorAt Lean.withRef
    refine run_bind_ne_ok _ ctx cctx ref w₅ ?_ _ _ _
    intro a'' s₇ w₇ b'' s₈ w₈
    rw [run_monadRefWithRef]
    exact run_throwError_ne_ok s₇ ctx _ ref w₇ _ _ _ _

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


/-! ## The generator's advance across `Meta.inferType` -/

/-- `Erasure.visitCtorEta` and `Erasure.visitCasesEta` each call `Meta.inferType` before
dispatching; the type is discarded on the saturated path, but the run's generator conclusion
still needs the call not to rewind it. Class **D**: no term denotes a `MetaM` run, so this is
the `ErasureSpec` field the pass steps are missing — a `lookup_adequate`-shaped clause for
`Lean.Meta.inferType`. -/
def InferTypeMonotone (gw : Void IO.RealWorld → NameGenerator) : Prop :=
  ∀ (e : Expr) (s : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) (ty : Expr)
    (s₁ : ErasureState) (w₁ : Void IO.RealWorld),
    Erasure.liftMetaM (Lean.Meta.inferType e) s ctx cctx ref w = .ok (ty, s₁) w₁ →
    gw w ≤ gw w₁

/-! ## The model reading of the table's inductive column

`ErasureSpec.decl_adequate` reads a declared constant into `env.constants`; the three
`Expr.const` readings `Erases` distinguishes — a constructor, a type former, a plain constant —
are not among what it gives. These are the two the pass steps need, stated at the reified table
so that no `Lean.Environment` lookup and no safety side condition enters. Class **D**, for the
same reason `decl_adequate` is; their home is `ErasureSpec.lean`.
-/

/-- Every constructor of a tabled inductive type is the model's constructor of it, at the
index the table records. -/
def CtorAdequate (env : VEnv) (tbl : SourceTable) : Prop :=
  ∀ (I : Name) (Ir : ReifiedInduct) (c : ReifiedCtor), tbl.ind? I = some Ir → c ∈ Ir.ctors →
    CtorOf env c.name I c.cidx

/-! ## Two derived introduction lemmas

`ErasesLB.lit` and `ErasesLB.proj`, the two arms of `Erases` the composite's own module leaves
without an introduction lemma. Their home is `ErasesLB.lean` beside the other six.
-/

variable {env : VEnv} {Us : List Name} {Γ : GlobalDeclarations} {Δ : VLCtx}

/-- A literal composes to whatever its kernel unfolding composes to: the pass is the identity
at the source step, so the composite inherits `Erases.lit`. -/
theorem ErasesLB.lit {l : Literal} {t : LBTerm} (hcl : env.ContainsLits l)
    (h : ErasesLB env Us Γ Δ l.toConstructor t) : ErasesLB env Us Γ Δ (.lit l) t :=
  let ⟨t₀, h₀, h₁⟩ := h
  ⟨t₀, .lit hcl h₀, h₁⟩

/-- A projection composes to the projection node: `Erases.proj` reads the block data and the
relevance of the type former, and the pass is the `proj` congruence. -/
theorem ErasesLB.proj {S : Name} {i : Nat} {e : Expr} {t : LBTerm} {iid : InductiveId}
    {np nf : Nat} (hs : IndInfo env S iid np [nf]) (hinf : InformativeInd env S) (hi : i < nf)
    (hd : ErasesLB env Us Γ Δ e t) :
    ErasesLB env Us Γ Δ (.proj S i e) (.proj ⟨iid, np, i⟩ t) :=
  let ⟨t₀, h₀, h₁⟩ := hd
  ⟨.proj ⟨iid, np, i⟩ t₀, .proj hs hinf hi h₀, .proj h₁⟩

variable {kns : List Kername} {ids : List FVarId}

/-- `ErasesLB.lit` inside a block. -/
theorem ErasesLBFix.lit {l : Literal} {t : LBTerm} (hcl : env.ContainsLits l)
    (h : ErasesLBFix env Us Γ kns ids Δ l.toConstructor t) :
    ErasesLBFix env Us Γ kns ids Δ (.lit l) t :=
  let ⟨_, h₁, hc⟩ := h.exists_erasesLB
  .of_erasesLB (ErasesLB.lit hcl h₁) hc

/-- `ErasesLB.proj` inside a block. -/
theorem ErasesLBFix.proj {S : Name} {i : Nat} {e : Expr} {t : LBTerm} {iid : InductiveId}
    {np nf : Nat} (hs : IndInfo env S iid np [nf]) (hinf : InformativeInd env S) (hi : i < nf)
    (hd : ErasesLBFix env Us Γ kns ids Δ e t) :
    ErasesLBFix env Us Γ kns ids Δ (.proj S i e) (.proj ⟨iid, np, i⟩ t) :=
  let ⟨_, h₁, hc⟩ := hd.exists_erasesLB
  .of_erasesLB (ErasesLB.proj hs hinf hi h₁) (.proj hc)

/-! ## The two introduction lemmas, at either fixvar mode -/

/-- `ErasesLB.lit` read through the reader's fixvar mode. -/
theorem ErasesLBMode.lit {ctx : ErasureContext} {Γspec : GlobalDeclarations} {l : Literal}
    {t : LBTerm} (hcl : env.ContainsLits l)
    (h : ErasesLBMode ctx env Us Γspec Δ l.toConstructor t) :
    ErasesLBMode ctx env Us Γspec Δ (.lit l) t :=
  ⟨fun hfx => .lit hcl (h.1 hfx), fun nms is hfx => .lit hcl (h.2 nms is hfx)⟩

/-- `ErasesLB.proj` read through the reader's fixvar mode. -/
theorem ErasesLBMode.proj {ctx : ErasureContext} {Γspec : GlobalDeclarations} {S : Name}
    {i : Nat} {e : Expr} {t : LBTerm} {iid : InductiveId} {np nf : Nat}
    (hs : IndInfo env S iid np [nf]) (hinf : InformativeInd env S) (hi : i < nf)
    (h : ErasesLBMode ctx env Us Γspec Δ e t) :
    ErasesLBMode ctx env Us Γspec Δ (.proj S i e) (.proj ⟨iid, np, i⟩ t) :=
  ⟨fun hfx => .proj hs hinf hi (h.1 hfx), fun nms is hfx => .proj hs hinf hi (h.2 nms is hfx)⟩


/-! ## Threading the generator through a prefix step -/

/-- A refinement established after a generator-advancing prefix is one at the entry point. -/
theorem pass_runRefines_le {env : VEnv} {Us : List Name} {tbl : SourceTable}
    {ctx : ErasureContext} {Δ : VLCtx} {s s' : ErasureState} {g g₁ g' : NameGenerator}
    {e : Expr} {t : LBTerm} (hle : g ≤ g₁)
    (h : RunRefines env Us tbl ctx Δ s s' g₁ g' e t) :
    RunRefines env Us tbl ctx Δ s s' g g' e t :=
  ⟨h.1, NameGenerator.LE.trans hle h.2.1, h.2.2⟩

/-! ## Step 2 — `Erasure.visitLiteral` -/

/-- Nothing is δ-reachable from a literal: it names no constant, so the fragment's body clause
is vacuous there. -/
theorem pass_lit_not_reaches {tbl : SourceTable} {l : Literal} {c : Name}
    (h : Reaches tbl (.lit l) c) : False := by
  induction h with
  | root hc => simp [constNames] at hc
  | body _ _ _ ih => exact ih

/-- A `Nat` literal is inside the fragment whenever the peano tower is available. -/
theorem pass_supported_lit {env : VEnv} {tbl : SourceTable} {n : Nat} (hpe : PeanoReady env)
    (hpb : peanoReadyB tbl = true) : Supported env tbl (.lit (.natVal n)) where
  term := .natLit hpe hpb
  bodies _ _ hr _ := absurd hr pass_lit_not_reaches

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
theorem step_visitLiteral {lenv : Environment} {env : VEnv} {Us : List Name} {tbl : SourceTable}
    {cfg : ErasureConfig} {gw : Void IO.RealWorld → NameGenerator}
    (hca : CtorAdequate env tbl) : Step2 lenv env Us tbl cfg gw := by
  intro _P _htbl hcfg _hcb vCtor h3
  refine ⟨?_, bodyLe2 h3.2⟩
  intro l s ctx cctx ref w t s' w' hrun Δ n hinv hl hpeano hpeanoB hex
  subst hl
  replace h3 := h3.1
  have hpe : ctx.config.nat = .peano := by rw [hinv.cfg]; exact hcfg.2.2.1
  obtain ⟨I, hI, ⟨cz, hzm, hzn, hzi⟩, ⟨cs, hsm, hsn, hsi⟩⟩ := pass_peano_ctors hpeanoB
  have hcz : CtorOf env ``Nat.zero ``Nat 0 := by
    have := hca ``Nat I cz hI hzm; rwa [hzn, hzi] at this
  have hcs : CtorOf env ``Nat.succ ``Nat 1 := by
    have := hca ``Nat I cs hI hsm; rwa [hsn, hsi] at this
  obtain ⟨ve, hve⟩ := hex
  simp only [visitLiteralBody] at hrun
  rw [run_read_bind] at hrun
  cases hve with
  | lit hcl htrC =>
    cases n with
    | zero =>
      simp only [hpe] at hrun
      have hgo := h3 _ _ _ _ _ _ _ _ _ _ hrun Δ ([] : List Level) hinv ⟨_, _, hcz⟩
        (fun i hi => absurd hi (by simp))
      refine ⟨hgo.1, hgo.2.1, fun Γspec hspec => ?_⟩
      refine ErasesLBMode.lit hcl ?_
      have := hgo.2.2 Γspec hspec
      simpa [srcSpine, Literal.toConstructor, Expr.natLitToConstructor, Expr.natZero] using this
    | succ m =>
      simp only [hpe] at hrun
      have hinner : ∃ ve', TrExprS env Us Δ (.lit (.natVal m)) ve' := by
        cases htrC with | app _ _ _ htra => exact ⟨_, htra⟩
      have hargs : ArgsOk env Us tbl Δ #[Expr.lit (.natVal m)] := by
        intro i hi
        have hi0 : i = 0 := by simpa using hi
        subst hi0
        exact ⟨pass_supported_lit hpeano hpeanoB, hinner⟩
      have hgo := h3 _ _ _ _ _ _ _ _ _ _ hrun Δ ([] : List Level) hinv ⟨_, _, hcs⟩ hargs
      refine ⟨hgo.1, hgo.2.1, fun Γspec hspec => ?_⟩
      refine ErasesLBMode.lit hcl ?_
      have := hgo.2.2 Γspec hspec
      simpa [srcSpine, Literal.toConstructor, Expr.natLitToConstructor, Expr.natSucc] using this


/-! ## Step 10 — `Erasure.visitProj`

`Erasure.visitProj` reads the emitted node's `InductiveId` out of the *inductive registry*,
and `BridgeInv` records nothing about that registry — its `canon` field is about the constant
registry only. So the identifier the run reports is, at a registry hit
(`Erasure.run_register_inductive_hit_ok`), whatever the state holds, and `Erases.proj` needs it
to be the model's. The two facts below are that gap, named: `IndRegistryModelled` is the
`BridgeInv` field, `RegisterModels` the run clause guarded by it. `Motive10Reg` is motive 10
carrying the field as a premise; once `BridgeInv` records it, `Motive10Reg → Motive10` is one
`obtain`.
-/

/-- **The inductive registry is the model's.** Every entry names the block identifier the model
declares for that name, and — the configuration pinning constructor-argument pruning off — its
masks retain every field. True of the initial state, whose registry is empty. -/
def IndRegistryModelled (env : VEnv) (s : ErasureState) : Prop :=
  ∀ (n : Name) (r : InductiveId × InductiveArgMasks) (np : Nat) (nfs : List Nat),
    s.inductives.get? n = some r → IndArity env n np nfs →
    IndInfo env n r.1 np nfs ∧
      ∀ (j nf : Nat), nfs[j]? = some nf → r.2[j]? = some (Array.replicate nf .keep)

/-- The empty registry is modelled. -/
theorem indRegistryModelled_empty {env : VEnv} : IndRegistryModelled env {} := by
  intro n r np nfs h _
  exact absurd h (by simp)

/-- **A registration reports the entry it leaves behind, and leaves the registry modelled.**
Guarded by the invariant, which is what keeps it off `Erasure.run_register_inductive_hit_mk`'s
hand-made states: at a registry holding a junk identifier the guard fails rather than the
conclusion. Class **D** at the cold branch, whose masks are computed inside a `MetaM`
telescope. -/
def RegisterModels (env : VEnv) (gw : Void IO.RealWorld → NameGenerator) : Prop :=
  ∀ (indinfo : InductiveVal) (s : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld)
    (r : InductiveId × InductiveArgMasks) (s₁ : ErasureState) (w₁ : Void IO.RealWorld),
    ctx.config.remove_irrel_constr_args = false → IndRegistryModelled env s →
    register_inductive indinfo s ctx cctx ref w = .ok (r, s₁) w₁ →
    IndRegistryModelled env s₁ ∧ s₁.inductives.get? indinfo.name = some r ∧ gw w ≤ gw w₁

/-- **The kernel's inductive declaration, in the model.** A block the model declares is
declared in `lenv` too, under its own name and at the same parameter count. Class **D**,
`ErasureSpec.decl_adequate`'s block-level sibling. -/
def IndDeclModelled (lenv : Environment) (env : VEnv) : Prop :=
  ∀ (n : Name) (np : Nat) (nfs : List Nat), IndArity env n np nfs →
    ∃ iv : InductiveVal, lenv.find? n = some (.inductInfo iv) ∧ iv.name = n ∧ iv.numParams = np

/-- **The kernel's constructor declarations and the model's constructor reading agree.** The
forward half names the kernel declaration behind a `CtorOf`; the backward half reads a kernel
constructor into the model and pins its field count against the block's. Class **D**, the
constructor-level sibling of `ErasureSpec.decl_adequate`. -/
def CtorDeclModelled (lenv : Environment) (env : VEnv) : Prop :=
  (∀ (c I : Name) (k : Nat), CtorOf env c I k →
      ∃ cv : ConstructorVal, lenv.find? c = some (.ctorInfo cv) ∧ cv.induct = I ∧ cv.cidx = k) ∧
  (∀ (c : Name) (cv : ConstructorVal), lenv.find? c = some (.ctorInfo cv) →
      CtorOf env c cv.induct cv.cidx ∧
        ∀ np nfs, IndArity env cv.induct np nfs → nfs[cv.cidx]? = some cv.numFields)

/-- `Lean.getEnv` only advances the ambient generator. Class **D**, and the
`ErasureSpec.LookupAdequate` clause the constructor branch's `@[extern]` test is missing. -/
def GetEnvMonotone (gw : Void IO.RealWorld → NameGenerator) : Prop :=
  ∀ (s : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) (le : Environment)
    (s₁ : ErasureState) (w₁ : Void IO.RealWorld),
    (getEnv : EraseM Environment) s ctx cctx ref w = .ok (le, s₁) w₁ → gw w ≤ gw w₁

/-- Motive 10, carrying the registry invariant `BridgeInv` does not record. -/
def Motive10Reg (env : VEnv) (Us : List Name) (tbl : SourceTable) (cfg : ErasureConfig)
    (gw : Void IO.RealWorld → NameGenerator) (f : Name → Nat → Expr → EraseM LBTerm) : Prop :=
  (∀ tn i e s ctx cctx ref w t s' w', f tn i e s ctx cctx ref w = .ok (t, s') w' →
    ∀ Δ (I : ReifiedInduct) (np nf : Nat), BridgeInv env Us cfg (gw w) ctx s Δ →
      IndRegistryModelled env s →
      tbl.ind? tn = some I → InformativeInd env tn → IndArity env tn np [nf] → i < nf →
      Supported env tbl e → (∃ ve, TrExprS env Us Δ e ve) →
      RunRefines env Us tbl ctx Δ s s' (gw w) (gw w') (.proj tn i e) t) ∧
  f ⊑ Erasure.visitProj

/-- `Motive10Reg` is motive 10 weakened by one premise and nothing else: what is proved here
is strictly less than motive 10, and the converse is exactly the missing `BridgeInv` field. -/
theorem Motive10Reg.of_motive10 {env : VEnv} {Us : List Name} {tbl : SourceTable}
    {cfg : ErasureConfig} {gw : Void IO.RealWorld → NameGenerator}
    {f : Name → Nat → Expr → EraseM LBTerm} (h : Motive10 env Us tbl cfg gw f) :
    Motive10Reg env Us tbl cfg gw f :=
  ⟨fun tn i e s ctx cctx ref w t s' w' hrun Δ I np nf hinv _ =>
    h.1 tn i e s ctx cctx ref w t s' w' hrun Δ I np nf hinv, h.2⟩

/-- Step 10, at `Motive10Reg`. -/
abbrev Step10Reg (lenv : Environment) (env : VEnv) (Us : List Name) (tbl : SourceTable)
    (cfg : ErasureConfig) (gw : Void IO.RealWorld → NameGenerator) : Prop :=
  ErasureSpec lenv env Us gw → SourceTableAdequate lenv tbl → ConfigPinned cfg →
  CompilerBodies lenv env tbl.body? →
  ∀ (vExpr : Expr → EraseM LBTerm),
    Motive1 env Us tbl cfg gw vExpr →
    Motive10Reg env Us tbl cfg gw (visitProjBody vExpr)


/-- **Step 10's content, at `Motive10Reg`.** Everything but the registry fact is proved: the
declaration fetch is the table's, the emitted field index is `i` because pruning is off, the
parameter count is the model block's, and the discriminant is motive 1's. -/
theorem step_visitProj {lenv : Environment} {env : VEnv} {Us : List Name} {tbl : SourceTable}
    {cfg : ErasureConfig} {gw : Void IO.RealWorld → NameGenerator}
    (hdm : IndDeclModelled lenv env) (hrm : RegisterModels env gw) :
    Step10Reg lenv env Us tbl cfg gw := by
  intro P _htbl hcfg _hcb vExpr h1
  refine ⟨?_, bodyLe10 h1.2⟩
  intro tn i e s ctx cctx ref w t s' w' hrun Δ I np nf hinv hregm _hind hinf harity hi hsup hex
  replace h1 := h1.1
  obtain ⟨iv, hfind, hname, hnp⟩ := hdm tn np [nf] harity
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
  have hcfgr : ctx.config.remove_irrel_constr_args = false := by
    rw [hinv.cfg]; exact hcfg.2.2.2.1
  obtain ⟨hregm₂, hget, hle₂⟩ := hrm iv _ ctx cctx ref w₁ r s₂ w₂ hcfgr hregm hregrun
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
  have hgo := h1 e s₂ ctx cctx ref w₂ t₀ _ _ hve Δ
    ((hinv.mono_state hrc).mono (NameGenerator.LE.trans hle₁ hle₂)) hsup hex
  refine ⟨hrc.trans hgo.1, NameGenerator.LE.trans hle₁ (NameGenerator.LE.trans hle₂ hgo.2.1),
    fun Γspec hspec => ?_⟩
  exact ErasesLBMode.proj (hname ▸ hmod.1) hinf hi (hgo.2.2 Γspec hspec)

/-! ## Step 3 — `Erasure.visitConstructor`

Same registry gap as step 10: the emitted `.construct` node's identifier and the argument mask
that decides which fields survive both come out of the inductive registry, so the step is
proved at `Motive3Reg`, motive 3 carrying `IndRegistryModelled`.
-/

/-- Motive 3, carrying the registry invariant `BridgeInv` does not record. -/
def Motive3Reg (env : VEnv) (Us : List Name) (tbl : SourceTable) (cfg : ErasureConfig)
    (gw : Void IO.RealWorld → NameGenerator) (f : Name → Array Expr → EraseM LBTerm) : Prop :=
  (∀ cn args s ctx cctx ref w t s' w', f cn args s ctx cctx ref w = .ok (t, s') w' →
    ∀ Δ (us : List Level), BridgeInv env Us cfg (gw w) ctx s Δ →
      IndRegistryModelled env s →
      (∃ I k, CtorOf env cn I k) → ArgsOk env Us tbl Δ args →
      RunRefines env Us tbl ctx Δ s s' (gw w) (gw w') (srcSpine (.const cn us) args) t) ∧
  f ⊑ Erasure.visitConstructor

/-- `Motive3Reg` is motive 3 weakened by one premise and nothing else. -/
theorem Motive3Reg.of_motive3 {env : VEnv} {Us : List Name} {tbl : SourceTable}
    {cfg : ErasureConfig} {gw : Void IO.RealWorld → NameGenerator}
    {f : Name → Array Expr → EraseM LBTerm} (h : Motive3 env Us tbl cfg gw f) :
    Motive3Reg env Us tbl cfg gw f :=
  ⟨fun cn args s ctx cctx ref w t s' w' hrun Δ us hinv _ =>
    h.1 cn args s ctx cctx ref w t s' w' hrun Δ us hinv, h.2⟩

/-- Step 3, at `Motive3Reg`. -/
abbrev Step3Reg (lenv : Environment) (env : VEnv) (Us : List Name) (tbl : SourceTable)
    (cfg : ErasureConfig) (gw : Void IO.RealWorld → NameGenerator) : Prop :=
  ErasureSpec lenv env Us gw → SourceTableAdequate lenv tbl → ConfigPinned cfg →
  CompilerBodies lenv env tbl.body? →
  ∀ (vLit : Literal → EraseM LBTerm) (vConst : Expr → EraseM LBTerm)
    (vArgs : LBTerm → Array Expr → EraseM LBTerm),
    Motive2 env Us tbl cfg gw vLit →
    Motive4 env Us tbl cfg gw vConst →
    Motive7 env Us tbl cfg gw vArgs →
    Motive3Reg env Us tbl cfg gw (visitConstructorBody vLit vConst vArgs)

/-- The head of a constructor spine, read through the reader's fixvar mode. -/
theorem ErasesLBMode.ctor_head {env : VEnv} {Us : List Name} {Δ : VLCtx}
    {ctx : ErasureContext} {Γspec : GlobalDeclarations} {cn I : Name} {us : List Level}
    {iid : InductiveId} {k np : Nat} {nfs : List Nat}
    (hc : CtorOf env cn I k) (hi : IndInfo env I iid np nfs) :
    ErasesLBMode ctx env Us Γspec Δ (.const cn us) (.construct iid k []) :=
  ⟨fun _ => ErasesLB.ctor_head hc hi, fun _ _ _ => ErasesLBFix.ctor_head hc hi⟩

/-- **Step 3's content, at `Motive3Reg`.** With the configuration pinned, the `@[extern]` arm
and both machine-`Nat` arms are dead, the argument mask retains every field so the emitted
spine is the source spine, and the head is `ErasesLB.ctor_head` at the registered block. -/
theorem step_visitConstructor {lenv : Environment} {env : VEnv} {Us : List Name}
    {tbl : SourceTable} {cfg : ErasureConfig} {gw : Void IO.RealWorld → NameGenerator}
    (hcd : CtorDeclModelled lenv env) (hdm : IndDeclModelled lenv env)
    (hge : GetEnvMonotone gw) (hrm : RegisterModels env gw) :
    Step3Reg lenv env Us tbl cfg gw := by
  intro P _htbl hcfg _hcb vLit vConst vArgs _h2 _h4 h7
  refine ⟨?_, bodyLe3 _h2.2 _h4.2 h7.2⟩
  intro cn args s ctx cctx ref w t s' w' hrun Δ us hinv hregm hctor hargs
  replace h7 := h7.1
  obtain ⟨I, k, hck⟩ := hctor
  obtain ⟨cv, hcvf, hcvI, hcvk⟩ := hcd.1 cn I k hck
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
  obtain ⟨hck', hnf⟩ := hcd.2 cn cv hcvf
  obtain ⟨iid0, np, nfs, hII⟩ := hck'.indInfo
  have harity : IndArity env cv.induct np nfs := hII.arity
  obtain ⟨iv, hivf, hivn, hivp⟩ := hdm cv.induct np nfs harity
  have hci2eq : ci2 = .inductInfo iv := by rw [hivf] at hfind2; exact (Option.some.inj hfind2).symm
  subst hci2eq
  simp only [] at hk
  rw [run_bind_ok] at hk
  obtain ⟨r, s₃, w₃, hregrun, hk⟩ := hk
  have hrc := run_register_inductive_runConcl hregrun
  have hcfgr : ctx.config.remove_irrel_constr_args = false := by
    rw [hinv.cfg]; exact hcfg.2.2.2.1
  obtain ⟨hregm₃, hget, hle₃⟩ := hrm iv _ ctx cctx ref w₂ r s₃ w₃ hcfgr hregm hregrun
  have hmod := hregm₃ iv.name r np nfs hget (by rw [hivn]; exact harity)
  have hmask : r.2[cv.cidx]! = Array.replicate cv.numFields ConstructorArgRelevance.keep := by
    have h0 := hmod.2 cv.cidx cv.numFields (hnf np nfs harity)
    have hlt : cv.cidx < r.2.length := by
      rcases List.getElem?_eq_some_iff.mp h0 with ⟨hlt, -⟩; exact hlt
    rw [getElem!_pos r.2 cv.cidx hlt]
    exact Option.some.inj ((List.getElem?_eq_getElem hlt).symm.trans h0)
  rw [run_bind_ok] at hk
  obtain ⟨le, s₄, w₄, hgenv, hk⟩ := hk
  have hs₄ : s₄ = s₃ := run_getEnv_state _ _ _ _ _ hgenv
  subst hs₄
  have hle₄ := hge _ ctx cctx ref w₃ le _ w₄ hgenv
  rw [run_bind_ok] at hk
  obtain ⟨ctx', s₅, w₅, hrd, hk⟩ := hk
  rw [run_read] at hrd
  cases hrd
  have hext : ctx.config.extern = Config.Extern.preferLogical := by
    rw [hinv.cfg]; exact hcfg.2.1
  have hpe : ctx.config.nat = Config.Nat.peano := by rw [hinv.cfg]; exact hcfg.2.2.1
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
  have hgo := h7 _ _ _ _ _ _ _ _ _ _ hk Δ (Expr.const cn us)
    ((hinv.mono_state hrc).mono hle) hhead hargs
  exact ⟨hrc.trans hgo.1, NameGenerator.LE.trans hle hgo.2.1, hgo.2.2⟩

/-! ## Step 13 — `Erasure.visitCtorEta` -/

/-- The saturated constructor spine's entry point: `Meta.inferType` leaves the state alone and
only advances the generator, and `Expr.withApp` hands the spine to the loop. -/
theorem step_visitCtorEta {lenv : Environment} {env : VEnv} {Us : List Name} {tbl : SourceTable}
    {cfg : ErasureConfig} {gw : Void IO.RealWorld → NameGenerator}
    (hit : InferTypeMonotone gw) : Step13 lenv env Us tbl cfg gw := by
  intro _P _htbl _hcfg _hcb vGo h14
  refine ⟨?_, bodyLe13 h14.2⟩
  intro cn ar e s ctx cctx ref w t s' w' hrun Δ us hinv hfn hctor har hargs
  replace h14 := h14.1
  simp only [visitCtorEtaBody] at hrun
  rw [run_bind_ok] at hrun
  obtain ⟨ty, s₁, w₁, hinfer, hk⟩ := hrun
  have hs₁ : s₁ = s := run_liftMetaM_state _ _ _ _ _ hinfer
  subst hs₁
  have hle₁ := hit _ _ _ _ _ _ _ _ _ hinfer
  rw [expr_withApp_eq] at hk
  have hgo := h14 _ _ _ _ _ _ _ _ _ _ _ _ _ hk Δ us (hinv.mono hle₁) hctor har hargs
  rw [pass_srcSpine_self hfn] at hgo
  exact pass_runRefines_le hle₁ hgo


/-! ## Steps 15 and 16 — the `casesOn` η loop -/

/-- The saturated `casesOn` spine's entry point. Mirrors `step_visitCtorEta`: the inferred type
is discarded on the saturated path, and the spine goes to the loop. -/
theorem step_visitCasesEta {lenv : Environment} {env : VEnv} {Us : List Name}
    {tbl : SourceTable} {cfg : ErasureConfig} {gw : Void IO.RealWorld → NameGenerator}
    (hit : InferTypeMonotone gw) : Step15 lenv env Us tbl cfg gw := by
  intro _P _htbl _hcfg _hcb vGo h16
  refine ⟨?_, bodyLe15 h16.2⟩
  intro ci e s ctx cctx ref w t s' w' hrun Δ con us I hinv hfn hhead har hsup hargs hex
  replace h16 := h16.1
  simp only [visitCasesEtaBody] at hrun
  rw [run_bind_ok] at hrun
  obtain ⟨ty, s₁, w₁, hinfer, hk⟩ := hrun
  have hs₁ : s₁ = s := run_liftMetaM_state _ _ _ _ _ hinfer
  subst hs₁
  have hle₁ := hit _ _ _ _ _ _ _ _ _ hinfer
  rw [expr_withApp_eq] at hk
  have hsp := pass_srcSpine_self (e := e) hfn
  have hgo := h16 _ _ _ _ _ _ _ _ _ _ _ _ hk Δ con us I (hinv.mono hle₁) hhead har
    (by rw [hsp]; exact hsup) hargs (by rw [hsp]; exact hex)
  rw [hsp] at hgo
  exact pass_runRefines_le hle₁ hgo

/-- The `casesOn` η loop, at a saturated spine: the elaborator's arity is the fragment's own
(`CasesInfoAgrees.arity`), so the η-expansion branch is dead and the run is `Erasure.visitCases`
on the nose. -/
theorem step_visitCasesEtaGo {lenv : Environment} {env : VEnv} {Us : List Name}
    {tbl : SourceTable} {cfg : ErasureConfig} {gw : Void IO.RealWorld → NameGenerator} :
    Step16 lenv env Us tbl cfg gw := by
  intro _P _htbl _hcfg _hcb vGo vCases _h16 h17
  refine ⟨?_, bodyLe16 _h16.2 h17.2⟩
  intro ci ty fe args s ctx cctx ref w t s' w' hrun Δ con us I hinv hhead har hsup hargs hex
  replace h17 := h17.1
  simp only [visitCasesEtaGoBody] at hrun
  rw [if_pos har] at hrun
  exact h17 _ _ _ _ _ _ _ _ _ _ hrun Δ con us I hinv hhead har hsup hargs hex

/-! ## Step 14 — the constructor η loop -/

/-- The constructor η loop, at a saturated spine: the arity is met, so the run is
`Erasure.visitConstructor` on the nose and the η-expansion branch is dead. -/
theorem step_visitCtorEtaGo {lenv : Environment} {env : VEnv} {Us : List Name}
    {tbl : SourceTable} {cfg : ErasureConfig} {gw : Void IO.RealWorld → NameGenerator} :
    Step14 lenv env Us tbl cfg gw := by
  intro _P _htbl _hcfg _hcb vCtor vGo h3 _h14
  refine ⟨?_, bodyLe14 h3.2 _h14.2⟩
  intro cn ar ty fe args s ctx cctx ref w t s' w' hrun Δ us hinv hctor har hargs
  replace h3 := h3.1
  simp only [visitCtorEtaGoBody] at hrun
  rw [if_pos har] at hrun
  exact h3 _ _ _ _ _ _ _ _ _ _ hrun Δ us hinv hctor hargs


end LeanToLambdaBox
