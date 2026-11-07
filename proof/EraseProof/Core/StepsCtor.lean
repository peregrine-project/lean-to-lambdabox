import EraseProof.Core.StepsB
import EraseProof.Simulation.Ind

/-!
# The steps of the constructor and projection cases

The steps, in the shape of `Core/Steps.lean`, of two special cases of `Erasure.visitExpr` that
`Steps.StepsB` collects: a constructor spine (`stepsB_ctor`: `visitConstApp`'s `ctorArity?`
branch, `withAppEtaToMinArity` and `visitConstructor`) and a projection (`stepsB_proj`:
`visitProj`).

A constructor spine `c.{us} as` that the oracle keeps is not of a `Prop` inductive
(`Pure.isErasable_ctorProp`, `SrcProof.ctor_evidentProp`, `RegisterInd.propInductive_iff`). With
fewer arguments than its arity it is η-expanded over the remaining `Π`s of its type, which the
oracle computes as the declared type with the arguments substituted (`spine_piInst`), a syntactic
telescope (`IndBlock.ctorType`); each new binder is opened with a fresh variable, and the saturated
spine is erased by `visitConstructor` (`visitConstructor_spec`, every field kept) and closed again
(`etaGo_spec`), which is `Erases.eta` of `EvalEnv.etaSpine?`. A saturated spine is `Erases.ctor`.

A projection that the oracle keeps is typed by it, so its structure eliminates into every sort
(`OracleSound.infer_projProof_ne` rules out the proof projections); it is a structure of the
program, a subsingleton (`subsingleton_of_structure`), in `Prop` or of a sort that is never zero
(`PhaseIDecl`), and its field index is unchanged by the mask that keeps every field
(`Erases.proj`).

Reference: the `tConstruct` and `tProj` cases of `erases_erase` (`MR E/ErasureFunction.v:1228`),
rules `erases_tConstruct`, `erases_tProj` (`MR E/Extract.v:106,118`); η-expansion: DV-23.
-/

open Lean Erasure
open Metalean (Defeq TypeEq EnvWF)

namespace EraseProof

namespace Steps

section
open TravFrame
variable {pc : PureCtx}

/-- A run of `getConst` at the pure backend: the declaration of the closure, states unchanged. -/
theorem getConst_eq {n : Name} {tc : TravCtx} {st : ErasureState} {ps : PureState} :
    (getConst (m := PureM) n).runPure st tc pc ps =
      match findConst pc.decls n with
      | some ci => .ok ((ci, st), ps)
      | none => .error (.outOfFragment s!"unknown constant {n}") := by
  unfold Erasure.getConst
  rw [runPure_bind, runPure_liftM]
  have : ((Backend.findConst? (m := PureM) n).run pc).run ps = .ok (findConst pc.decls n, ps) := rfl
  rw [this]
  cases findConst pc.decls n <;> rfl

/-- A successful run of `getConst` found the declaration and kept both states. -/
theorem getConst_run {n : Name} {tc : TravCtx} {st st' : ErasureState} {ps ps' : PureState}
    {ci : ConstantInfo}
    (h : (getConst (m := PureM) n).runPure st tc pc ps = .ok ((ci, st'), ps')) :
    findConst pc.decls n = some ci ∧ st' = st ∧ ps' = ps := by
  rw [getConst_eq] at h
  split at h
  · cases h; exact ⟨‹_›, rfl, rfl⟩
  · cases h

/-- A run of `x` at the pure backend that keeps the counter. -/
def KeepsPS (pc : PureCtx) {α : Type} (x : EraseT PureM α) : Prop :=
  ∀ st tc ps r st' ps', x.runPure st tc pc ps = .ok ((r, st'), ps') → ps' = ps

theorem KeepsPS.pure {α : Type} (a : α) : KeepsPS pc (Pure.pure a : EraseT PureM α) := by
  intro st tc ps r st' ps' h; cases h; rfl

theorem KeepsPS.bind {α β : Type} {x : EraseT PureM α} {k : α → EraseT PureM β}
    (hx : KeepsPS pc x) (hk : ∀ a, KeepsPS pc (k a)) : KeepsPS pc (x >>= k) := by
  intro st tc ps r st' ps' h
  rw [runPure_bind] at h
  obtain ⟨⟨⟨a, st₁⟩, ps₁⟩, h1, h2⟩ := OracleWhnf.ok_of_bind h
  exact (hk a _ _ _ _ _ _ h2).trans (hx _ _ _ _ _ _ h1)

theorem KeepsPS.get : KeepsPS pc (MonadState.get : EraseT PureM ErasureState) := by
  intro st tc ps r st' ps' h; cases h; rfl

theorem KeepsPS.modify (f : ErasureState → ErasureState) :
    KeepsPS pc (_root_.modify f : EraseT PureM PUnit) := by
  intro st tc ps r st' ps' h; cases h; rfl

theorem KeepsPS.read_bind {α : Type} {k : TravCtx → EraseT PureM α}
    (hk : ∀ c, KeepsPS pc (k c)) : KeepsPS pc (read >>= k) := by
  intro st tc ps r st' ps' h
  rw [runPure_read_bind] at h
  exact hk tc _ _ _ _ _ _ h

theorem KeepsPS.ite {α : Type} {c : Prop} [Decidable c] {a b : EraseT PureM α}
    (ha : KeepsPS pc a) (hb : KeepsPS pc b) : KeepsPS pc (if c then a else b) := by
  split
  · exact ha
  · exact hb

theorem KeepsPS.liftM {α : Type} (x : PureM α)
    (hx : ∀ a ps ps', (x.run pc).run ps = .ok (a, ps') → ps' = ps) :
    KeepsPS pc (_root_.liftM x : EraseT PureM α) := by
  intro st tc ps r st' ps' h
  rw [runPure_liftM] at h
  obtain ⟨⟨a, ps₁⟩, h1, h2⟩ := OracleWhnf.ok_of_bind h
  cases h2
  exact hx _ _ _ h1

theorem KeepsPS.throwM {α : Type} (err : EraseError) :
    KeepsPS pc (_root_.liftM (throw err : PureM α) : EraseT PureM α) :=
  fun _ _ _ _ _ _ h => nomatch h

theorem KeepsPS.mapM {α β : Type} {f : α → EraseT PureM β} (hf : ∀ a, KeepsPS pc (f a)) :
    ∀ l : List α, KeepsPS pc (l.mapM f)
  | [] => by rw [List.mapM_nil]; exact KeepsPS.pure _
  | a :: l => by
    rw [List.mapM_cons]
    exact KeepsPS.bind (hf a) fun _ => KeepsPS.bind (KeepsPS.mapM hf l) fun _ => KeepsPS.pure _

theorem KeepsPS.getConst (n : Name) : KeepsPS pc (getConst (m := PureM) n) :=
  fun _ _ _ _ _ _ h => (getConst_run h).2.2

theorem KeepsPS.getOrFail {γ : Type} [Inhabited γ] (o : Option γ) (msg : String) :
    KeepsPS pc (getOrFail (m := PureM) o msg) := by
  cases o with
  | some a => exact KeepsPS.pure a
  | none => exact KeepsPS.throwM _

theorem KeepsPS.addAxiom (n : Name) : KeepsPS pc (addAxiom (m := PureM) n) := by
  unfold Erasure.addAxiom
  refine KeepsPS.bind KeepsPS.get fun s => ?_
  dsimp only
  split
  · exact KeepsPS.bind (KeepsPS.liftM _ fun _ _ _ h => nomatch h) fun _ => KeepsPS.modify _
  · exact KeepsPS.modify _

/-- `liftM` of a pure-backend call that answers without touching the counter. -/
macro (name := _keepsLift) "keeps_lift" : tactic => `(tactic| (
  refine KeepsPS.liftM _ fun _ _ _ h => ?_
  first
    | (cases h; rfl)
    | (rw [RegisterInd.isPropFormerType_run] at h
       rcases hq : Pure.isPropFormerType _ _ _ _ with _ | _ <;> rw [hq] at h <;> cases h; rfl)))

/-- The constructor step of `register_inductive`. -/
macro (name := _keepsCtorTail) "keeps_ctor_tail" : tactic => `(tactic| (
  refine KeepsPS.bind (KeepsPS.getConst _) fun _ => ?_
  split
  · refine KeepsPS.read_bind fun _ => KeepsPS.ite ?_ ?_
    · exact KeepsPS.read_bind fun _ => KeepsPS.bind (by keeps_lift) fun _ => KeepsPS.pure _
    · exact KeepsPS.bind (KeepsPS.pure _) fun _ => KeepsPS.pure _
  · exact KeepsPS.throwM _))

/-- `register_inductive` allocates no free variable. -/
theorem KeepsPS.register_inductive (iv : InductiveVal) :
    KeepsPS pc (register_inductive (m := PureM) iv) := by
  rw [Erasure.register_inductive]
  refine KeepsPS.bind KeepsPS.get fun s => ?_
  split
  · exact KeepsPS.pure _
  · refine KeepsPS.bind (KeepsPS.mapM (fun p => ?_) _) fun _ => ?_
    · obtain ⟨ind_name, idx⟩ := p
      dsimp only
      refine KeepsPS.bind (KeepsPS.getConst _) fun ci => ?_
      split
      · refine KeepsPS.bind (KeepsPS.mapM (fun c => ?_) _) fun r => ?_
        · refine KeepsPS.bind (by keeps_lift) fun _ => KeepsPS.read_bind fun _ => ?_
          refine KeepsPS.ite ?_ ?_
          · refine KeepsPS.bind (by keeps_lift) fun _ =>
              KeepsPS.bind (KeepsPS.addAxiom _) fun _ => ?_
            keeps_ctor_tail
          · keeps_ctor_tail
        · refine KeepsPS.ite ?_ ?_
          · exact KeepsPS.bind (KeepsPS.getOrFail _ _) fun _ => KeepsPS.bind (KeepsPS.pure _)
              fun _ => KeepsPS.bind (KeepsPS.modify _) fun _ => KeepsPS.bind (by keeps_lift)
                fun _ => KeepsPS.pure _
          · exact KeepsPS.bind (KeepsPS.pure _) fun _ => KeepsPS.bind (KeepsPS.modify _) fun _ =>
              KeepsPS.bind (by keeps_lift) fun _ => KeepsPS.pure _
      · exact KeepsPS.throwM _
    · exact KeepsPS.bind (KeepsPS.modify _) fun _ => KeepsPS.bind KeepsPS.get fun _ =>
        KeepsPS.getOrFail _ _

/-- The pure backend's `inferType` is the oracle's, at `oracleFuel`. -/
theorem inferType_runPure {tc : TravCtx} {st : ErasureState} {ps : PureState}
    {lctx : LocalContext} {ls : List Local} {e : Expr} :
    (liftM (Backend.inferType (m := PureM) lctx ls e) : EraseT PureM Expr).runPure st tc pc ps =
      (Pure.inferType ⟨pc.decls⟩ oracleFuel ls [] e).map fun T => ((T, st), ps) := by
  rw [runPure_liftM]
  rcases h : Pure.inferType ⟨pc.decls⟩ oracleFuel ls [] e with err | T
  · change ((match Pure.inferType ⟨pc.decls⟩ oracleFuel ls [] e with
      | .ok t => (Pure.pure t : PureM Expr) | .error err => throw err).run pc).run ps >>= _ = _
    rw [h]; rfl
  · change ((match Pure.inferType ⟨pc.decls⟩ oracleFuel ls [] e with
      | .ok t => (Pure.pure t : PureM Expr) | .error err => throw err).run pc).run ps >>= _ = _
    rw [h]; rfl

/-- The pure backend's `isExtern` reads the view. -/
theorem isExtern_runPure {n : Name} {tc : TravCtx} {st : ErasureState} {ps : PureState} :
    (liftM (Backend.isExtern (m := PureM) n) : EraseT PureM Bool).runPure st tc pc ps =
      .ok ((pc.view.isExtern n, st), ps) := rfl

/-- A successful `getOrFail` returns the option's value and keeps both states. -/
theorem getOrFail_run {γ : Type} [Inhabited γ] {o : Option γ} {msg : String} {tc : TravCtx}
    {st st' : ErasureState} {ps ps' : PureState} {a : γ}
    (h : (getOrFail (m := PureM) o msg).runPure st tc pc ps = .ok ((a, st'), ps')) :
    o = some a ∧ st' = st ∧ ps' = ps := by
  cases o with
  | some b => cases h; exact ⟨rfl, rfl, rfl⟩
  | none => cases h

end

theorem count_keep_replicate :
    ∀ n, List.count ConstructorArgRelevance.keep (List.replicate n .keep) = n
  | 0 => rfl
  | n + 1 => by rw [List.replicate_succ, List.count_cons, count_keep_replicate n]; rfl

/-- The kept fields among the first `i` of a mask that keeps all `N ≥ i` fields: `i`. -/
theorem count_keep_slice {N i : Nat} (h : i ≤ N) :
    Array.count ConstructorArgRelevance.keep
      (Std.Slice.toArray ((Array.replicate N ConstructorArgRelevance.keep).toSubarray 0 i)) = i := by
  rw [← Subarray.toArray_eq_sliceToArray, ← Subarray.toArray_toList, ← Array.count_toList,
    Subarray.toList_eq, Array.array_toSubarray]
  simp
  rw [count_keep_replicate]
  omega

/-! ## Closed λ□ terms under the traversal's abstraction -/

theorem length_toBvarDefs (x : FVarId) (k : Nat) :
    ∀ ds : List (@FixDef LBTerm), (toBvarDefs x k ds).length = ds.length
  | [] => rfl
  | _ :: ds => by simp only [toBvarDefs, List.length_cons, length_toBvarDefs x k ds]

mutual
/-- Turning a free variable into the bound variable `k` keeps a term closed one level up. -/
theorem closedn_toBvar (x : FVarId) : ∀ (t : LBTerm) (k : Nat), closedn k t = true →
    closedn (k + 1) (toBvar x k t) = true
  | .box, _, _ => rfl
  | .bvar i, k, h => by simp only [toBvar, closedn, decide_eq_true_eq] at h ⊢; omega
  | .fvar y, k, _ => by
    simp only [toBvar]
    split
    · simp [closedn]
    · rfl
  | .lambda _ b, k, h => closedn_toBvar x b (k + 1) h
  | .letIn _ v b, k, h => by
    simp only [toBvar, closedn, Bool.and_eq_true] at h ⊢
    exact ⟨closedn_toBvar x v k h.1, closedn_toBvar x b (k + 1) h.2⟩
  | .app a b, k, h => by
    simp only [toBvar, closedn, Bool.and_eq_true] at h ⊢
    exact ⟨closedn_toBvar x a k h.1, closedn_toBvar x b k h.2⟩
  | .const _, _, _ => rfl
  | .construct _ _ args, k, h => closednL_toBvarList x args k h
  | .case (_, _) d alts, k, h => by
    simp only [toBvar, closedn, Bool.and_eq_true] at h ⊢
    exact ⟨closedn_toBvar x d k h.1, closednB_toBvarAlts x alts k h.2⟩
  | .proj _ e, k, h => closedn_toBvar x e k h
  | .fix defs _, k, h => by
    simp only [toBvar, closedn] at h ⊢
    rw [length_toBvarDefs, show k + 1 + defs.length = k + defs.length + 1 by omega]
    exact closednD_toBvarDefs x defs (k + defs.length) h
  | .prim _, _, _ => rfl

theorem closednL_toBvarList (x : FVarId) : ∀ (as : List LBTerm) (k : Nat),
    closednL k as = true → closednL (k + 1) (toBvarList x k as) = true
  | [], _, _ => rfl
  | a :: as, k, h => by
    simp only [toBvarList, closednL, Bool.and_eq_true] at h ⊢
    exact ⟨closedn_toBvar x a k h.1, closednL_toBvarList x as k h.2⟩

theorem closednB_toBvarAlts (x : FVarId) : ∀ (bs : List (List BinderName × LBTerm)) (k : Nat),
    closednB k bs = true → closednB (k + 1) (toBvarAlts x k bs) = true
  | [], _, _ => rfl
  | (ns, b) :: bs, k, h => by
    simp only [toBvarAlts, closednB, Bool.and_eq_true] at h ⊢
    refine ⟨?_, closednB_toBvarAlts x bs k h.2⟩
    rw [show k + 1 + ns.length = k + ns.length + 1 by omega]
    exact closedn_toBvar x b (k + ns.length) h.1

theorem closednD_toBvarDefs (x : FVarId) : ∀ (ds : List (@FixDef LBTerm)) (k : Nat),
    closednD k ds = true → closednD (k + 1) (toBvarDefs x k ds) = true
  | [], _, _ => rfl
  | ⟨_, b, _⟩ :: ds, k, h => by
    simp only [toBvarDefs, closednD, Bool.and_eq_true] at h ⊢
    exact ⟨closedn_toBvar x b k h.1, closednD_toBvarDefs x ds k h.2⟩
end

/-! ## Constructor arguments -/

theorem filterMap_keep {α : Type} : ∀ (l : List α) (n : Nat), l.length ≤ n →
    ((List.replicate n ConstructorArgRelevance.keep).zip l).filterMap
      (fun (x : ConstructorArgRelevance × α) => match x with
        | (r, a) => match r with | .erase => none | .keep => some a) = l
  | [], _, _ => by simp
  | a :: l, n + 1, h => by
    simp only [List.replicate_succ, List.zip_cons_cons, List.filterMap_cons]
    rw [filterMap_keep l n (by simp at h; omega)]
  | _ :: _, 0, h => by simp at h

/-- A mask that keeps every field leaves the fields unchanged. -/
theorem filter_keep {α : Type} (arr : Array α) (n : Nat) (h : arr.size ≤ n) :
    filter (Array.replicate n .keep) arr = arr := by
  apply Array.ext'
  unfold filter
  rw [Array.toList_filterMap, Array.toList_zip, Array.toList_replicate]
  exact filterMap_keep arr.toList n (by simpa using h)

/-- The arguments of a constructor spine reassembled by `visitConstructor` around the kept fields
are the arguments. -/
theorem slices_keep {α : Type} (l : List α) (p f : Nat) (h : p + f ≤ l.length) :
    Std.Slice.toArray (l.toArray.toSubarray 0 p) ++
      filter (Array.replicate f .keep) ↑(l.toArray.toSubarray p (p + f)) ++
      Std.Slice.toArray (l.toArray.toSubarray (p + f)) = l.toArray := by
  simp only [Subarray.copy_eq_toArray]
  rw [filter_keep _ _ (by
    simp only [Subarray.size_toArray, Subarray.size_eq, Array.start_toSubarray,
      Array.stop_toSubarray, List.size_toArray]
    omega)]
  apply Array.ext'
  rw [Array.toList_append, Array.toList_append, ← Subarray.toArray_toList, ← Subarray.toArray_toList,
    ← Subarray.toArray_toList]
  simp only [List.toList_toArray, Subarray.toList_eq_drop_take, Array.array_toSubarray,
    Array.start_toSubarray, Array.stop_toSubarray, List.size_toArray]
  rw [show min 0 (min p l.length) = 0 by omega, show min p l.length = p by omega,
    show min (p + f) l.length = p + f by omega, show min p (p + f) = p by omega,
    show min l.length l.length = l.length by omega, show min (p + f) l.length = p + f by omega,
    List.take_length, List.drop_zero]
  conv => rhs; rw [← List.take_append_drop (p + f) l]
  congr 1
  conv => rhs; rw [← List.take_append_drop p (List.take (p + f) l)]
  rw [List.take_take, show min p (p + f) = p by omega]

/-! ## η-expansion of a constructor spine -/

/-- The body of the η-expansion of `c.{us} as` by `m` binders: the arguments lifted over the new
binders, then the new bound variables, outermost first (`EvalEnv.etaSpine?`). -/
def etaBody (c : Name) (us : List Level) (as : List Expr) (m : Nat) : Expr :=
  mkAppN (.const c us)
    (as.map (·.liftLooseBVars' 0 m) ++ (List.range m).reverse.map Expr.bvar).toArray

theorem inst_foldl (a : Expr) (d : Nat) : ∀ (xs : List Expr) (h : Expr),
    (xs.foldl .app h).instantiate1' a d = (xs.map (·.instantiate1' a d)).foldl .app (h.instantiate1' a d)
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.foldl_cons, inst_foldl a d xs, List.map_cons, List.foldl_cons]
    rfl

/-- Opening the outermost new binder of the η-body with a free variable adds it to the
arguments. -/
theorem etaBody_inst (c : Name) (us : List Level) (as : List Expr) (m : Nat) (x : FVarId) :
    (etaBody c us as (m + 1)).instantiate1' (.fvar x) m = etaBody c us (as ++ [.fvar x]) m := by
  unfold etaBody
  rw [mkAppN_toArray, mkAppN_toArray, inst_foldl]
  congr 1
  have hA : ∀ e : Expr, (e.liftLooseBVars' 0 (m + 1)).instantiate1' (.fvar x) m =
      e.liftLooseBVars' 0 m := fun e => by
    have := OracleInfer.inst_lift (.fvar x) e 0 m
    rwa [Nat.zero_add] at this
  have hB : ∀ i ∈ (List.range m).reverse, (Expr.bvar i).instantiate1' (.fvar x) m = .bvar i := by
    intro i hi
    simp only [List.mem_reverse, List.mem_range] at hi
    simp [Expr.instantiate1', hi]
  have hm : (Expr.bvar m).instantiate1' (.fvar x) m = .fvar x := by
    simp [Expr.instantiate1', Expr.liftLooseBVars']
  rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
    List.map_cons, List.map_append, List.map_append, List.map_map, List.map_cons, hm]
  have hA' : List.map ((fun y => y.instantiate1' (Expr.fvar x) m) ∘ fun y => y.liftLooseBVars' 0 (m + 1)) as =
      List.map (fun y => y.liftLooseBVars' 0 m) as := List.map_congr_left fun e _ => hA e
  have hB' : List.map (fun y => y.instantiate1' (Expr.fvar x) m) (List.map Expr.bvar (List.range m).reverse) =
      List.map Expr.bvar (List.range m).reverse := by
    rw [List.map_map]
    exact List.map_congr_left fun i hi => hB i hi
  rw [hA', hB']
  simp [Expr.liftLooseBVars']

/-- Instantiating a bound variable commutes with `lamsOf`, the body one binder level deeper per
binder. -/
theorem lamsOf_inst (a : Expr) : ∀ (m : Nat) (ty body w : Expr) (d : Nat),
    lamsOf m ty body = some w →
      lamsOf m (ty.instantiate1' a d) (body.instantiate1' a (d + m)) = some (w.instantiate1' a d)
  | 0, _, _, w, d, h => by cases h; rfl
  | m + 1, ty, body, w, d, h => by
    cases ty with
    | forallE n dom b bi =>
      simp only [lamsOf, Option.map_eq_some_iff] at h
      obtain ⟨w₁, h₁, rfl⟩ := h
      have ih := lamsOf_inst a m b body w₁ (d + 1) h₁
      rw [show d + 1 + m = d + (m + 1) by omega] at ih
      simp only [Expr.instantiate1', lamsOf, ih, Option.map_some]
    | _ => simp [lamsOf] at h

/-- `lamsOf` succeeds on a type with enough leading `Π`s. -/
theorem lamsOf_some : ∀ (m : Nat) (ty body : Expr) {r : Expr}, peelForalls m ty = some r →
    ∃ w, lamsOf m ty body = some w
  | 0, _, body, _, _ => ⟨body, rfl⟩
  | m + 1, ty, body, r, h => by
    obtain ⟨x, A, b, bi, rfl, hb⟩ := OracleInfer.peelForalls_succ h
    obtain ⟨w, hw⟩ := lamsOf_some m b body hb
    exact ⟨.lam x A w bi, by simp only [lamsOf, hw, Option.map_some]⟩

theorem fvarsIn_lamsOf {p : FVarId → Prop} : ∀ {m : Nat} {ty body w : Expr},
    lamsOf m ty body = some w → FVarsIn p ty → FVarsIn p body → FVarsIn p w
  | 0, _, _, _, h, _, hb => by cases h; exact hb
  | m + 1, ty, body, w, h, ht, hb => by
    cases ty with
    | forallE n dom b bi =>
      simp only [lamsOf, Option.map_eq_some_iff] at h
      obtain ⟨w₁, h₁, rfl⟩ := h
      exact ⟨ht.1, fvarsIn_lamsOf h₁ ht.2 hb⟩
    | _ => simp [lamsOf] at h

theorem fvarsIn_etaBody {p : FVarId → Prop} {c : Name} {us : List Level} {as : List Expr}
    {m : Nat} (h : ∀ a ∈ as, FVarsIn p a) : FVarsIn p (etaBody c us as m) := by
  unfold etaBody
  rw [mkAppN_toArray, FVarsIn_foldl]
  refine ⟨trivial, fun a ha => ?_⟩
  rcases List.mem_append.1 ha with ha | ha
  · obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.1 ha
    exact OracleAgree.fvarsIn_lift (h a₀ ha₀)
  · obtain ⟨j, -, rfl⟩ := List.mem_map.1 ha
    trivial

theorem piInst_append (a : Expr) : ∀ (as : List Expr) (ty : Expr),
    piInst (as ++ [a]) ty = (piInst as ty).bind (piInst [a])
  | [], ty => rfl
  | x :: as, ty => by
    cases ty with
    | forallE n d b bi => exact piInst_append a as _
    | _ => rfl

/-- The oracle's type of `c.{us} as`, when `c`'s declared type has at least `as.length` leading
`Π`s, is the declared type with the arguments substituted for the leading binders (`piInst`).
Reference: `type_of_typing` on `tApp` (`MR S/PCUICSafeRetyping.v:806`). -/
theorem spine_piInst {cx : Pure.Ctx} {ls : List Local} {Γo : List Expr} {c : Name}
    {us : List Level} {ci : ConstantInfo} {k : Nat} {body : Expr}
    (hci : findConst cx.decls c = some ci)
    (hpk : peelForalls k (Pure.instLevels ci.levelParams us ci.type) = some body) :
    ∀ (as : List Expr) {f : Nat} {T : Expr}, as.length ≤ k →
      Pure.inferType cx f ls Γo (mkAppN (.const c us) as.toArray) = .ok T →
      piInst as (Pure.instLevels ci.levelParams us ci.type) = some T := by
  have hc : ∀ ci', findConst cx.decls c = some ci' → us.length = ci'.levelParams.length →
      peelForalls k (Pure.instLevels ci'.levelParams us ci'.type) = some body := by
    intro ci' hci' _
    rw [hci] at hci'
    cases hci'
    exact hpk
  intro as
  induction as using List.reverseRecOn with
  | nil =>
    intro f T _ h
    cases f with
    | zero => simp [Pure.inferType, throw, throwThe, MonadExceptOf.throw] at h
    | succ f =>
      simp only [mkAppN_eq_foldl, List.foldl_nil, Pure.inferType, hci] at h
      split at h
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        rfl
      · simp [throw, throwThe, MonadExceptOf.throw] at h
  | append_singleton as a ih =>
    intro f T hk h
    simp only [List.length_append, List.length_singleton] at hk
    have happ : mkAppN (.const c us) (as ++ [a]).toArray =
        .app (mkAppN (.const c us) as.toArray) a := by
      simp only [mkAppN_eq_foldl, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [happ] at h
    cases f with
    | zero => simp [Pure.inferType, throw, throwThe, MonadExceptOf.throw] at h
    | succ f =>
      simp only [Pure.inferType] at h
      obtain ⟨Tg, h1, h⟩ := OracleWhnf.ok_of_bind h
      obtain ⟨W, h2, h⟩ := OracleWhnf.ok_of_bind h
      have hp := OracleInfer.spine_type hc as (by omega) h1
      rw [show k - as.length = (k - (as.length + 1)) + 1 by omega] at hp
      obtain ⟨x, A, b, bi, rfl, -⟩ := OracleInfer.peelForalls_succ hp
      have hW := OracleInfer.whnf_forallE h2
      subst hW
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      rw [piInst_append, ih (by omega) h1]
      rfl


section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P : List ConstantInfo}

/-- After a run of `register_inductive iv`, the type `iv` is registered with the returned λ□
inductive and masks. -/
theorem register_inductive_mem {σ : EvalEnv} {iv : InductiveVal} {tc : TravCtx} {pc : PureCtx}
    {st st' : ErasureState} {ps ps' : PureState} {r : InductiveId × InductiveArgMasks}
    (henv : ProgEnv P ζ E B) (hsub : SubEnv σ.decls P) (hdecls : pc.decls = σ.decls)
    (hirr : tc.config.remove_irrel_constr_args = false)
    (hph : ∀ ci ∈ σ.decls, PhaseIDecl pc.view tc.config σ.decls ci)
    (hiv : findDecl σ.decls iv.name = some (.inductInfo iv))
    (h : (register_inductive (m := PureM) iv).runPure st tc pc ps = .ok ((r, st'), ps')) :
    st'.inductives[iv.name]? = some r := by
  obtain ⟨hnd, -, -⟩ := RegisterInd.ProgEnv.ind_all henv (SrcDefeq.findDecl_sub hsub hiv)
  have hext : ∀ cn cv, findDecl σ.decls cn = some (.ctorInfo cv) →
      tc.config.1 = .preferAxiom → pc.view.isExtern cn = false := by
    intro cn cv hc hx
    obtain ⟨hm, hn⟩ := findDecl_eq_some hc
    have := (hph _ hm).2 hx
    rwa [show cv.name = cn from hn] at this
  rcases RegisterInd.register_inductive_run hdecls hirr hext hnd st st ps r st' ps' rfl h with
    ⟨hr, rfl⟩ | ⟨-, s₁, bodies, -, -, hr, rfl⟩
  · exact hr
  · exact hr

/-- Every argument of a constructor spine whose image is typed has a typed image. -/
theorem ctor_args_typed {lps : List Name} {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
    {ι : Metalean.IndSig} {η : Metalean.Head ζ (.inductive ι)} {s : Fin ι.nsorts}
    {k : Fin (ι.nctors s)} {o : List Nat} {us : List Level}
    {as : List (Metalean.Expr ζ lps.length n)} {t : Metalean.Expr ζ lps.length n}
    (hord : MetaOrderOK o (ι.ctors s k).nfields (ι.ctors s k).nrecFields)
    (h : SatTr E lps (.ctor η s k o) us as t) (ht : ∃ T, E[Γ] ⊢ t : T) :
    ∀ a ∈ as, ∃ A, E[Γ] ⊢ a : A := by
  obtain ⟨T, ht⟩ := ht
  cases h with
  | ctorEta =>
    intro a ha
    exact (InstPre.appList_inv ht).2 a ha
  | ctorSat ps fs rest fds recFds hls hfs hord' hperm =>
    obtain ⟨⟨_, hc⟩, hrest⟩ := InstPre.appList_inv ht
    obtain ⟨_, _, _, hps, hfds, hrf, -, -⟩ := hc.ctor_inv
    obtain ⟨-, -, -, -, -, -, -, hpm⟩ := hord
    intro a ha
    simp only [List.mem_append, List.mem_ofFn] at ha
    rcases ha with (⟨p, rfl⟩ | ha) | ha
    · exact ⟨_, (hps p).right⟩
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
      have hjr : j ∈ o := hpm.symm.subset (List.mem_range.mpr (hfs ▸ hj))
      obtain ⟨q, hq, hqj⟩ := List.getElem_of_mem hjr
      obtain ⟨j', x, hj', hx, hfx⟩ := hperm ⟨q, hord' ▸ hq⟩
      rw [List.getElem?_eq_getElem hq, hqj, Option.some.injEq] at hj'
      subst hj'
      rw [List.getElem?_eq_getElem hj, Option.some.injEq] at hx
      subst hx
      rw [← hfx]
      refine Fin.addCases (fun f => ?_) (fun r => ?_) (⟨q, hord' ▸ hq⟩ :
        Fin ((ι.ctors s k).nfields + (ι.ctors s k).nrecFields))
      · rw [Fin.append_left]; exact ⟨_, (hfds f).right⟩
      · rw [Fin.append_right]; exact ⟨_, (hrf r).right⟩
    · exact hrest a ha

/-- A structure is a subsingleton in the sense of `Subsingleton`: a proof built with its
constructor has proofs as fields. Reference: `Subsingleton` (`MR P/PCUICElimination.v:45`);
`IsStructure.ordinaryLevel_eq_zero_of_eval_zero` (`ML Syntax/Structure.lean`). -/
theorem subsingleton_of_structure (hE : EnvWF E) {S : Name} {ι : Metalean.IndSig}
    {η : Metalean.Head ζ (.inductive ι)} {s : Fin ι.nsorts} {c : Fin (ι.nctors s)}
    (hBS : B S = some (.ind η s)) (hst : (E.get η).block.IsStructure s c) :
    Subsingleton E B S := by
  intro ι' η' s' hB' ℓ n Γ c' ls ps fds recFds _ hΓ hpf
  rw [hBS] at hB'
  cases hB'
  have herase : IsErasable E Γ (.ctor η s c' ls ps fds recFds) := by
    obtain ⟨T, hT, hTp⟩ := hpf
    exact ⟨T, hT, .inr hTp⟩
  obtain ⟨-, hl⟩ := SimInd.ctor_isProof hE hΓ herase
  have hzero : ((E.get η).block.level{ls}).eval (fun _ => 0) = 0 := by
    rw [hl]; rfl
  obtain ⟨h1, -⟩ := hst.sortLargeElim.singleton_of_eval_zero ls hzero c'
  obtain rfl := hst.ctor_unique c'
  obtain ⟨T, hT, -⟩ := hpf
  obtain ⟨ps₁, fds₁, recFds₁, hps, hfds, -, -, -⟩ := Metalean.Defeq.ctor_inv hT
  refine ⟨by omega, fun f => ?_, fun f => hst.no_recursive.elim f⟩
  have hlz := hst.ordinaryLevel_eq_zero_of_eval_zero ls hzero f
  have hctor := ((hE.entryWF η).block).ctors s c'
  have hty := hctor.ordinaryFieldExpr f (fun p => (hps p).left) (fun f => (hfds f).left)
  rw [hlz] at hty
  exact ⟨_, (hfds f).right, hty⟩

end

section
open TravFrame
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P decls : List ConstantInfo}
  {view : EnvView} {cfg : ErasureConfig}

/-- `visitAppArgs (j + 1) tf args`, from `visitExpr` at `j` (`ih`): the head applied to erasures of
the arguments, one by one. Reference: the `tApp` case of `erases_erase`
(`MR E/ErasureFunction.v:1228`). -/
theorem visitAppArgs_list {j : Nat} (ih : ∀ e, ExprSpec E B view cfg decls j e)
    {lps : List Name} {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    {S : Name → Prop} {st st' : ErasureState} {tc : TravCtx} {ps ps' : PureState}
    {r tf : LBTerm} {args : List Expr}
    (hctx : CtxOK E B lps Γ Δ cfg tc ps) (hsc : ScopeOK decls S)
    (hargs : ∀ a ∈ args, (∀ d, nameOccurs d a = true → S d) ∧ MachineFree cfg a ∧
      NatPlain cfg a ∧ RecShaped cfg decls a ∧ ∃ a', TrM E B lps Γ Δ a a' ∧ ∃ A, E[Γ] ⊢ a' : A)
    (hok : StateOK E B (evalEnvOf view cfg decls) st)
    (hrun : (visitAppArgs (m := PureM) (j + 1) tf args.toArray).runPure st tc ⟨decls, view⟩ ps =
      .ok ((r, st'), ps')) :
    ∃ as' : List LBTerm, r = mkApps tf as' ∧ args.length = as'.length ∧
      (∀ (i : Nat) a a', args[i]? = some a → as'[i]? = some a' →
        Erases E B lps (evalEnvOf view cfg decls) Γ Δ a a') ∧
      (∀ a' ∈ as', ErasesDeps E B (evalEnvOf view cfg decls) st'.gdecls a') ∧
      Grows E B (evalEnvOf view cfg decls) S st st' ps ps' := by
  rw [visitAppArgs, ← Array.foldlM_toList, List.toList_toArray] at hrun
  induction args generalizing tf st ps with
  | nil =>
    cases hrun
    exact ⟨[], rfl, rfl, by simp, by simp, .refl hok⟩
  | cons a l ihl =>
    rw [List.foldlM_cons, runPure_bind] at hrun
    obtain ⟨⟨⟨x, st₁⟩, ps₁⟩, hx, hrun⟩ := OracleWhnf.ok_of_bind hrun
    rw [runPure_bind] at hx
    obtain ⟨⟨⟨ta, st₂⟩, ps₂⟩, ha, hx⟩ := OracleWhnf.ok_of_bind hx
    cases hx
    obtain ⟨hoa, hma, hna, hra, a', hta, A, hA⟩ := hargs a (.head _)
    have ⟨hera, hdepsa, hgra⟩ := ih a hctx hsc hoa hma hna hra hok hta ⟨A, hA⟩ ha
    obtain ⟨as', rfl, hlen, hers, hdeps, hgr⟩ := ihl (tf := .app tf ta) (hctx.mono hgra.next)
      (fun b hb => hargs b (.tail _ hb)) hgra.inv hrun
    refine ⟨ta :: as', rfl, by simp [hlen], fun i b b' h1 h2 => ?_, fun b hb => ?_,
      hgra.trans hgr⟩
    · cases i with
      | zero => simp at h1 h2; subst h1 h2; exact hera
      | succ i => exact hers i b b' (by simpa using h1) (by simpa using h2)
    · rcases List.mem_cons.1 hb with rfl | hb
      · exact ErasesDeps.ext hgr.ext hdepsa
      · exact hdeps b hb

/-- A λ□ spine whose head and arguments have erased dependencies has erased dependencies. -/
theorem deps_mkApps_intro {lenv : GlobalDeclarations} :
    ∀ {f : LBTerm} {as : List LBTerm}, ErasesDeps E B (evalEnvOf view cfg decls) lenv f →
      (∀ a ∈ as, ErasesDeps E B (evalEnvOf view cfg decls) lenv a) →
      ErasesDeps E B (evalEnvOf view cfg decls) lenv (mkApps f as)
  | _, [], hf, _ => hf
  | _, a :: as, hf, ha => deps_mkApps_intro (as := as) (.app hf (ha a (.head _)))
      fun b hb => ha b (.tail _ hb)

/-- `visitConstructor (j + 1) c args` at the pure backend on a constructor `c` with at least its
arity of arguments, each translated and typed: every field is kept (`KeepMasks`), so the result is
the λ□ constructor of `c`'s inductive applied to erasures of the arguments, closed, with the
inductive's block erased. Reference: the `tConstruct` case of `erases_erase`
(`MR E/ErasureFunction.v:1228`). -/
theorem visitConstructor_core (hG : CoreEnv E B P decls view cfg) {j : Nat}
    (ih : StepIH E B view cfg decls j)
    {lps : List Name} {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    {S : Name → Prop} {st st' : ErasureState} {tc : TravCtx} {ps ps' : PureState} {r : LBTerm}
    {c : Name} {cv : ConstructorVal} {args : List Expr}
    (hctx : CtxOK E B lps Γ Δ cfg tc ps) (hsc : ScopeOK decls S)
    (hargs : ∀ a ∈ args, (∀ d, nameOccurs d a = true → S d) ∧ MachineFree cfg a ∧
      NatPlain cfg a ∧ RecShaped cfg decls a ∧ ∃ a', TrM E B lps Γ Δ a a' ∧ ∃ A, E[Γ] ⊢ a' : A)
    (hc : findDecl decls c = some (.ctorInfo cv))
    (hlen : cv.numParams + cv.numFields ≤ args.length)
    (hnat : cfg.nat = .machine → c ≠ ``Nat.zero ∧ c ≠ ``Nat.succ)
    (hok : StateOK E B (evalEnvOf view cfg decls) st)
    (hrun : (visitConstructor (m := PureM) (j + 1) c args.toArray).runPure st tc ⟨decls, view⟩ ps =
      .ok ((r, st'), ps')) :
    ∃ iid as', r = mkApps (.construct iid cv.cidx []) as' ∧
      IndIdOf (evalEnvOf view cfg decls) cv.induct = some iid ∧ args.length = as'.length ∧
      (∀ (i : Nat) a a', args[i]? = some a → as'[i]? = some a' →
        Erases E B lps (evalEnvOf view cfg decls) Γ Δ a a') ∧
      ErasesDeps E B (evalEnvOf view cfg decls) st'.gdecls r ∧
      Grows E B (evalEnvOf view cfg decls) S st st' ps ps' ∧ closedn 0 r = true := by
  rw [visitConstructor, runPure_bind] at hrun
  obtain ⟨⟨⟨ci, st₁⟩, ps₁⟩, hci, hrun⟩ := OracleWhnf.ok_of_bind hrun
  obtain ⟨hfc, h1, h2⟩ := getConst_run hci
  subst st₁ ps₁
  rw [show findConst decls c = findDecl decls c from rfl, hc] at hfc
  cases hfc
  dsimp only at hrun
  rw [runPure_bind] at hrun
  obtain ⟨⟨⟨ci, st₁⟩, ps₁⟩, hci, hrun⟩ := OracleWhnf.ok_of_bind hrun
  obtain ⟨hfi, h1, h2⟩ := getConst_run hci
  subst st₁ ps₁
  cases ci with
  | inductInfo iv =>
    dsimp only at hrun
    rw [runPure_bind] at hrun
    obtain ⟨⟨⟨rr, st₁⟩, ps₁⟩, hreg, hrun⟩ := OracleWhnf.ok_of_bind hrun
    have h1 : ps₁ = ps := KeepsPS.register_inductive iv _ _ _ _ _ _ hreg
    subst ps₁
    dsimp only at hrun
    rw [runPure_bind] at hrun
    obtain ⟨⟨⟨mask, st₂⟩, ps₂⟩, hmask, hrun⟩ := OracleWhnf.ok_of_bind hrun
    obtain ⟨hmk, h1, h2⟩ := getOrFail_run hmask
    subst st₂ ps₂
    dsimp only at hrun
    rw [runPure_bind, isExtern_runPure, ok_bind'] at hrun
    dsimp only at hrun
    rw [runPure_read_bind] at hrun
    have hmem : ConstantInfo.ctorInfo cv ∈ decls := (findDecl_eq_some hc).1
    have hcn : cv.name = c := (findDecl_eq_some hc).2
    have hph := hG.phase _ hmem
    have hne : (view.isExtern c && tc.config.1 == .preferAxiom) = false := by
      rw [hctx.config]
      cases hcfg : cfg.1 with
      | preferAxiom =>
        have := hph.2 hcfg
        rw [hcn] at this
        simp [this]
      | _ => cases view.isExtern c <;> rfl
    rw [hne, if_neg Bool.false_ne_true, runPure_read_bind, hctx.config] at hrun
    have hiv : findDecl (evalEnvOf view cfg decls).decls cv.induct = some (.inductInfo iv) := hfi
    have hname : iv.name = cv.induct := (findDecl_eq_some hiv).2
    have hirr : tc.config.remove_irrel_constr_args = false := by
      rw [hctx.config]; exact hG.irr iv ⟨_, (findDecl_eq_some hiv).1, rfl⟩
    have hph' : ∀ ci ∈ (evalEnvOf view cfg decls).decls,
        PhaseIDecl (⟨decls, view⟩ : PureCtx).view tc.config (evalEnvOf view cfg decls).decls ci := by
      rw [hctx.config]; exact hG.phase
    have hiv' : findDecl (evalEnvOf view cfg decls).decls iv.name = some (.inductInfo iv) := by
      rw [hname]; exact hiv
    obtain ⟨hok₁, hext₁, hcst₁, hiid, hkm⟩ :=
      register_inductive_ok hG.prog hG.wf hG.sub hok rfl hirr hph' hG.bn hiv' hreg
    have hreg₁ := register_inductive_mem hG.prog hG.sub rfl hirr hph' hiv' hreg
    rw [hname] at hiid hreg₁
    obtain ⟨hcpos, -⟩ := SimInd.ctor_block hG.prog hG.sub hc hiv
    have hmask' : mask = Array.replicate cv.numFields .keep := by
      have := hkm.2 cv.cidx _ cv hcpos hc
      rw [hmk] at this
      cases this; rfl
    split at hrun
    · exact absurd rfl (hnat ‹cfg.nat = .machine›).1
    · exact absurd rfl (hnat ‹cfg.nat = .machine›).2
    all_goals
      rw [hmask', slices_keep args cv.numParams cv.numFields hlen] at hrun
      cases j with
      | zero => rw [visitAppArgs] at hrun; cases hrun
      | succ i =>
        obtain ⟨as', rfl, hlen', hers, hdeps, hgr⟩ :=
          visitAppArgs_list (fun e => ih.expr i (by omega) e) hctx hsc hargs hok₁ hrun
        have hind : ErasesInd E B (evalEnvOf view cfg decls) st'.gdecls cv.induct :=
          StateLemmas.ErasesInd.ext hgr.ext (hok₁.inductives _ rr hreg₁).2.1
        refine ⟨_, as', rfl, hiid, hlen', hers,
          deps_mkApps_intro (.construct hiid hind (by simp)) hdeps,
          Grows.trans ⟨hok₁, hext₁, Nat.le_refl _, ?_⟩ hgr, ?_⟩
        · intro c' kn h1 h2
          rw [hcst₁, h1] at h2
          cases h2
        · refine AbsFV.closedn_mkApps.2 ⟨rfl, fun a' ha' => ?_⟩
          obtain ⟨i', ha'i⟩ := List.mem_iff_getElem?.1 ha'
          have hi : i' < args.length := by rw [hlen']; exact (List.getElem?_eq_some_iff.1 ha'i).1
          have hai : args[i']? = some args[i'] := List.getElem?_eq_getElem hi
          obtain ⟨-, -, -, -, a₀, hta, -⟩ := hargs _ (List.mem_of_getElem? hai)
          have := Erases.closed hta (hers i' _ a' hai ha'i)
          rwa [countP_none hctx.nobv] at this
  | _ => dsimp only at hrun; cases hrun

/-- `visitConstructor_core` on a constructor of an inductive that is not in `Prop`: an erasure
(`Erases.ctor`). Reference: rule `erases_tConstruct` (`MR E/Extract.v:106`). -/
theorem visitConstructor_spec (hG : CoreEnv E B P decls view cfg) {j : Nat}
    (ih : StepIH E B view cfg decls j)
    {lps : List Name} {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    {S : Name → Prop} {st st' : ErasureState} {tc : TravCtx} {ps ps' : PureState} {r : LBTerm}
    {c : Name} {us : List Level} {cv : ConstructorVal} {args : List Expr}
    (hctx : CtxOK E B lps Γ Δ cfg tc ps) (hsc : ScopeOK decls S)
    (hargs : ∀ a ∈ args, (∀ d, nameOccurs d a = true → S d) ∧ MachineFree cfg a ∧
      NatPlain cfg a ∧ RecShaped cfg decls a ∧ ∃ a', TrM E B lps Γ Δ a a' ∧ ∃ A, E[Γ] ⊢ a' : A)
    (hc : findDecl decls c = some (.ctorInfo cv))
    (hlen : cv.numParams + cv.numFields ≤ args.length)
    (hnprop : ¬ PropInductive E B cv.induct)
    (hnat : cfg.nat = .machine → c ≠ ``Nat.zero ∧ c ≠ ``Nat.succ)
    (hok : StateOK E B (evalEnvOf view cfg decls) st)
    (hrun : (visitConstructor (m := PureM) (j + 1) c args.toArray).runPure st tc ⟨decls, view⟩ ps =
      .ok ((r, st'), ps')) :
    Erases E B lps (evalEnvOf view cfg decls) Γ Δ (mkAppN (.const c us) args.toArray) r ∧
      ErasesDeps E B (evalEnvOf view cfg decls) st'.gdecls r ∧
      Grows E B (evalEnvOf view cfg decls) S st st' ps ps' ∧ closedn 0 r = true := by
  obtain ⟨iid, as', rfl, hiid, hlen', hers, hdeps, hgr, hcl⟩ :=
    visitConstructor_core hG ih hctx hsc hargs hc hlen hnat hok hrun
  exact ⟨.ctor hc hnprop hiid hlen hlen' hers, hdeps, hgr, hcl⟩

/-- What the continuation `kont` of `withAppEtaToMinArity` at the arity `ar` does on the head
`c.{us}` and at least `ar` translated, typed arguments, from a state with `StateOK` and the
property `I` (which `withAppEtaToMinArity` does not change), on a spine that translates to a typed
term: a successful run erases the spine, with erased dependencies, `Grows` within the scope, and
returns a closed term. -/
def SatSpec (E : Metalean.Env ζ) (B : Binds ζ) (view : EnvView) (cfg : ErasureConfig)
    (decls : List ConstantInfo) (ar : Nat) (c : Name) (us : List Level)
    (I : ErasureState → Prop) (kont : Expr → Array Expr → EraseT PureM LBTerm) : Prop :=
  ∀ ⦃lps : List Name⦄ ⦃n : Nat⦄ ⦃Γ : Metalean.Ctx ζ lps.length 0 n⦄ ⦃Δ : MLCtx ζ lps.length n⦄
    ⦃S : Name → Prop⦄ ⦃st st' : ErasureState⦄ ⦃tc : TravCtx⦄ ⦃ps ps' : PureState⦄ ⦃r : LBTerm⦄
    ⦃as : List Expr⦄,
    CtxOK E B lps Γ Δ cfg tc ps → ScopeOK decls S →
    (∀ a ∈ as, (∀ d, nameOccurs d a = true → S d) ∧ MachineFree cfg a ∧
      NatPlain cfg a ∧ RecShaped cfg decls a ∧ ∃ a', TrM E B lps Γ Δ a a' ∧ ∃ A, E[Γ] ⊢ a' : A) →
    ar ≤ as.length → StateOK E B (evalEnvOf view cfg decls) st → I st →
    (∃ t U, TrM E B lps Γ Δ (mkAppN (.const c us) as.toArray) t ∧ E[Γ] ⊢ t : U) →
    (kont (.const c us) as.toArray).runPure st tc ⟨decls, view⟩ ps = .ok ((r, st'), ps') →
    Erases E B lps (evalEnvOf view cfg decls) Γ Δ (mkAppN (.const c us) as.toArray) r ∧
      ErasesDeps E B (evalEnvOf view cfg decls) st'.gdecls r ∧
      Grows E B (evalEnvOf view cfg decls) S st st' ps ps' ∧ closedn 0 r = true

/-- The η-expansion loop of `withAppEtaToMinArity` at the arity `ar` on a spine `c.{us} as` whose
type `T` has `m` leading `Π`s left before the arity, given what the continuation does on a
saturated spine (`SatSpec`): the result erases the η-expansion `lamsOf m T (etaBody c us as m)`,
under binders named as `T`'s (`EvalEnv.etaSpine?`), and is closed. Reference: none (MetaRocq
η-expands in λ□, `MR E/EEtaExpanded.v`; DV-23). -/
theorem etaGo_spec (hG : CoreEnv E B P decls view cfg) {ar : Nat} {c : Name} {us : List Level}
    {I : ErasureState → Prop} {kont : Expr → Array Expr → EraseT PureM LBTerm}
    (hk : SatSpec E B view cfg decls ar c us I kont) :
    ∀ (m fuel : Nat) {lps : List Name} {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
      {Δ : MLCtx ζ lps.length n} {S : Name → Prop} {st st' : ErasureState} {tc : TravCtx}
      {ps ps' : PureState} {r : LBTerm} {T : Expr} {T' : Metalean.Expr ζ lps.length n}
      {as : List Expr},
      CtxOK E B lps Γ Δ cfg tc ps → ScopeOK decls S →
      (∀ a ∈ as, (∀ d, nameOccurs d a = true → S d) ∧ MachineFree cfg a ∧
        NatPlain cfg a ∧ RecShaped cfg decls a ∧ ∃ a', TrM E B lps Γ Δ a a' ∧ ∃ A, E[Γ] ⊢ a' : A) →
      (ar = as.length + m ∨ (m = 0 ∧ ar ≤ as.length)) →
      (∃ body, peelForalls m T = some body) → TrM E B lps Γ Δ T T' → E[Γ] ⊢ T' typ →
      StateOK E B (evalEnvOf view cfg decls) st → I st →
      (∃ t, TrM E B lps Γ Δ (mkAppN (.const c us) as.toArray) t ∧ E[Γ] ⊢ t : T') →
      (withAppEtaToMinArity.go (m := PureM) ar kont fuel T (.const c us) as.toArray).runPure
        st tc ⟨decls, view⟩ ps = .ok ((r, st'), ps') →
      ∀ w, lamsOf m T (etaBody c us as m) = some w →
        Erases E B lps (evalEnvOf view cfg decls) Γ Δ w r ∧
          ErasesDeps E B (evalEnvOf view cfg decls) st'.gdecls r ∧
          Grows E B (evalEnvOf view cfg decls) S st st' ps ps' ∧ closedn 0 r = true := by
  intro m
  induction m with
  | zero =>
    intro fuel lps n Γ Δ S st st' tc ps ps' r T T' as hctx hsc hargs hlen _ _ _ hok hI hsp hrun w hw
    cases fuel with
    | zero => rw [withAppEtaToMinArity.go] at hrun; cases hrun
    | succ fuel =>
    rw [withAppEtaToMinArity.go, if_pos (show as.toArray.size ≥ ar by simp; omega)] at hrun
    cases hw
    have hw : etaBody c us as 0 = mkAppN (.const c us) as.toArray := by
      simp [etaBody, liftLooseBVars'_zero]
    rw [hw]
    obtain ⟨t, ht, htT⟩ := hsp
    exact hk hctx hsc hargs (by omega) hok hI ⟨t, T', ht, htT⟩ hrun
  | succ m ihm =>
    intro fuel lps n Γ Δ S st st' tc ps ps' r T T' as hctx hsc hargs hlen hpk hT hT' hok hI hsp hrun
      w hw
    cases fuel with
    | zero => rw [withAppEtaToMinArity.go] at hrun; cases hrun
    | succ fuel =>
    rw [withAppEtaToMinArity.go, if_neg (by simp; omega)] at hrun
    obtain ⟨body, hpk⟩ := hpk
    obtain ⟨nm, d, b, bi, rfl, hpb⟩ := OracleInfer.peelForalls_succ hpk
    obtain ⟨d', b', rfl, hd, hb⟩ := SrcDefeq.trM_forallE_inv hT
    obtain ⟨lT, hlT⟩ := hT'
    obtain ⟨hd', hb'⟩ := Metalean.Defeq.forallE_inv hlT
    simp only [forallMonocular, Expr.isForall, ite_true, withLocalDecl] at hrun
    rw [runPure_bind, show (pure (Expr.forallE nm d b bi) : EraseT PureM Expr).runPure st tc
      ⟨decls, view⟩ ps = .ok ((.forallE nm d b bi, st), ps) from rfl, ok_bind'] at hrun
    dsimp only at hrun
    rw [runPure_bind, fresh_run, ok_bind'] at hrun
    dsimp only at hrun
    rw [runPure_withReader, runPure_bind] at hrun
    obtain ⟨⟨⟨r₀, st₁⟩, ps₁⟩, hgo, hrun⟩ := OracleWhnf.ok_of_bind hrun
    dsimp only at hrun
    rw [mkLambda_run (l := ⟨pureFVar ps.next, nm, d, none⟩) rfl rfl] at hrun
    cases hrun
    have hxΔ : Δ.findF (pureFVar ps.next) = none := hctx.freshNext
    have hctx' := hctx.pushFVar (nm := nm) hd hd' (tc.lctx.mkLocalDecl (pureFVar ps.next) nm d bi)
    have hΓ' : E[Γ.snoc d'] ⊢ ok := hctx'.wf
    have hargs' : ∀ a ∈ as ++ [.fvar (pureFVar ps.next)], (∀ e, nameOccurs e a = true → S e) ∧
        MachineFree cfg a ∧ NatPlain cfg a ∧ RecShaped cfg decls a ∧
        ∃ a', TrM E B lps (Γ.snoc d') (Δ.pushLam (some (pureFVar ps.next))) a a' ∧
          ∃ A, E[Γ.snoc d'] ⊢ a' : A := by
      intro a ha
      rcases List.mem_append.1 ha with ha | ha
      · obtain ⟨h1, h2, h3, h4, a', hta, A, hA⟩ := hargs a ha
        exact ⟨h1, h2, h3, h4, a'.wk, TrM.weakFV hxΔ hta, A.wk, hA.wk d'⟩
      · rw [List.mem_singleton] at ha
        subst ha
        refine ⟨fun _ h => by simp [nameOccurs] at h, trivial, trivial, trivial, .var (Fin.last n),
          .fvar ?_, _, hΓ'.var (Fin.last n)⟩
        simp [MLCtx.pushLam, MLCtx.findF, (fvarId_beq_iff _ _).mpr rfl, MLDecl.denote]
    simp only [lamsOf, Option.map_eq_some_iff] at hw
    obtain ⟨w₁, hw₁, rfl⟩ := hw
    have hw' := lamsOf_inst (.fvar (pureFVar ps.next)) m b _ w₁ 0 hw₁
    rw [Nat.zero_add, etaBody_inst] at hw'
    rw [show Backend.instantiate1 PureM b (.fvar (pureFVar ps.next)) =
      b.instantiate1' (.fvar (pureFVar ps.next)) from rfl, List.push_toArray] at hgo
    -- the spine applied to the new variable translates to a term typed at the codomain
    have hsp' : ∃ t₁, TrM E B lps (Γ.snoc d') (Δ.pushLam (some (pureFVar ps.next)))
        (mkAppN (.const c us) (as ++ [Expr.fvar (pureFVar ps.next)]).toArray) t₁ ∧
        E[Γ.snoc d'] ⊢ t₁ : b' := by
      obtain ⟨t, ht, htT⟩ := hsp
      have hvar : TrM E B lps (Γ.snoc d') (Δ.pushLam (some (pureFVar ps.next)))
          (.fvar (pureFVar ps.next)) (.var (Fin.last n)) :=
        .fvar (by simp [MLCtx.pushLam, MLCtx.findF, (fvarId_beq_iff _ _).mpr rfl, MLDecl.denote])
      obtain ⟨t₁, ht₁, hred⟩ := TrM.apps (TrM.weakFV hxΔ ht) (.cons hvar .nil)
      have happ := app_var_typed htT hΓ'
      have hd₁ := Metalean.WHRedS.defeq hG.wf hΓ' hred (by simpa using happ)
      refine ⟨t₁, ?_, hd₁.right⟩
      rw [SrcDefeq.mkAppN_snoc]
      exact ht₁
    obtain ⟨her, hdeps, hgr, hcl⟩ := ihm fuel hctx' hsc hargs' (by
        rcases hlen with h | ⟨h, -⟩
        · left; simp only [List.length_append, List.length_singleton]; omega
        · omega)
      ⟨_, OracleInfer.peelForalls_inst _ m b body 0 hpb⟩ (TrM.inst_fvar hxΔ hb) hb' hok hI hsp' hgo _
      hw'
    have hfvΔ : ∀ {e : Expr}, FVarsIn (fun y => (Δ.findF y).isSome) e →
        FVarsIn (· ≠ pureFVar ps.next) e :=
      fun h => fvarsIn_mono (fun y hy hyx => by subst hyx; simp [hxΔ] at hy) h
    have hfv : FVarsIn (· ≠ pureFVar ps.next) w₁ :=
      fvarsIn_lamsOf hw₁ (hfvΔ (TrM.fvarsIn hT).2) (fvarsIn_etaBody fun a ha => by
        obtain ⟨-, -, -, -, a', hta, -⟩ := hargs a ha
        exact hfvΔ (TrM.fvarsIn hta))
    exact ⟨.lam hd hd' (Erases.abstract hG.prog hG.sub hxΔ hfv hcl her),
      .lambda (ErasesDeps.toBvar hdeps 0),
      ⟨hgr.inv, hgr.ext, Nat.le_trans (Nat.le_succ _) hgr.next, hgr.scope⟩,
      closedn_toBvar _ r₀ 0 hcl⟩

/-- `withAppEtaToMinArity f e ar kont` at the pure backend, on a translated, typed spine `e` of
`c.{us}` whose arity (`specialArity`) is `ar` and whose declared type is a `Π`-telescope of `ar`
binders, given what `kont` does on a saturated spine (`SatSpec`): with fewer than `ar` arguments
the result erases the η-expansion (`Erases.eta`, `EvalEnv.etaSpine?`), otherwise `kont`'s result
erases `e`. Reference: none (MetaRocq η-expands in λ□, `MR E/EEtaExpanded.v`; DV-23). -/
theorem withAppEta_spec (hG : CoreEnv E B P decls view cfg) {ar f : Nat} {c : Name}
    {us : List Level} {ci : ConstantInfo} {body : Expr}
    {kont : Expr → Array Expr → EraseT PureM LBTerm}
    (hci : findDecl decls c = some ci) (hsa : specialArity (evalEnvOf view cfg decls) c = some ar)
    {I : ErasureState → Prop}
    (hpk : peelForalls ar ci.type = some body) (hk : SatSpec E B view cfg decls ar c us I kont)
    {lps : List Name} {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    {S : Name → Prop} {t : Metalean.Expr ζ lps.length n} {st st' : ErasureState} {tc : TravCtx}
    {ps ps' : PureState} {r : LBTerm} {e : Expr} (hfn : e.getAppFn = .const c us)
    (hctx : CtxOK E B lps Γ Δ cfg tc ps) (hsc : ScopeOK decls S)
    (hargs : ∀ a ∈ spineArgs e, (∀ d, nameOccurs d a = true → S d) ∧ MachineFree cfg a ∧
      NatPlain cfg a ∧ RecShaped cfg decls a ∧ ∃ a', TrM E B lps Γ Δ a a' ∧ ∃ A, E[Γ] ⊢ a' : A)
    (hok : StateOK E B (evalEnvOf view cfg decls) st) (hI : I st)
    (he : TrM E B lps Γ Δ e t) (ht : ∃ T, E[Γ] ⊢ t : T)
    (hrun : (withAppEtaToMinArity (m := PureM) f e ar kont).runPure st tc ⟨decls, view⟩ ps =
      .ok ((r, st'), ps')) :
    Erases E B lps (evalEnvOf view cfg decls) Γ Δ e r ∧
      ErasesDeps E B (evalEnvOf view cfg decls) st'.gdecls r ∧
      Grows E B (evalEnvOf view cfg decls) S st st' ps ps' := by
  have hA : (e.withApp fun _ as => as) = (spineArgs e).toArray := by
    rw [← withApp_toList e, Array.toArray_toList]
  have hsp : mkAppN (.const c us) (spineArgs e).toArray = e := by rw [← hfn]; exact mkAppN_spine e
  rw [withAppEtaToMinArity, runPure_read_bind, runPure_read_bind, runPure_bind,
    inferType_runPure] at hrun
  rcases hinf : Pure.inferType ⟨decls⟩ oracleFuel tc.locals [] e with err | T
  · rw [hinf] at hrun; cases hrun
  rw [hinf, show Except.map (fun T => ((T, st), ps)) (Except.ok T : Except EraseError Expr) =
    Except.ok ((T, st), ps) from rfl, ok_bind'] at hrun
  dsimp only at hrun
  rw [withApp_eq, hfn, hA] at hrun
  obtain ⟨T', hTT', htT'⟩ :=
    Pure.inferType_sound hG.prog hG.wf hG.sub hctx.wf hctx.locals hctx.nobv he ht hinf
  have hT'typ : E[Γ] ⊢ T' typ := htT'.regular
  have hpkI := OracleInfer.peelForalls_instLevels ci.levelParams us _ _ _ hpk
  have hfc : findConst decls c = some ci := hci
  have hinf' := hinf
  rw [← hsp] at hinf'
  by_cases hlt : (spineArgs e).length < ar
  · have hc'' : ∀ ci', findConst decls c = some ci' → us.length = ci'.levelParams.length →
        peelForalls ar (Pure.instLevels ci'.levelParams us ci'.type) =
          some (Pure.instLevels ci.levelParams us body) := by
      intro ci' hci' _
      rw [hfc] at hci'
      cases hci'
      exact hpkI
    have hpT := OracleInfer.spine_type hc'' (spineArgs e) (by omega) hinf'
    have hpiT := spine_piInst hfc hpkI (spineArgs e) (by omega) hinf'
    obtain ⟨w, hw⟩ := lamsOf_some _ T (etaBody c us (spineArgs e) (ar - (spineArgs e).length)) hpT
    obtain ⟨her, hdeps, hgr, -⟩ := etaGo_spec hG hk _ f hctx hsc hargs
      (.inl (by omega)) ⟨_, hpT⟩ hTT' hT'typ hok hI ⟨t, by rw [hsp]; exact he, htT'⟩ hrun w hw
    refine ⟨?_, hdeps, hgr⟩
    have hη : (evalEnvOf view cfg decls).etaSpine? c us (spineArgs e) = some w := by
      unfold EvalEnv.etaSpine?
      rw [show findDecl (evalEnvOf view cfg decls).decls c = some ci from hci, hsa]
      simp only [if_pos hlt]
      rw [hpiT]
      exact hw
    rw [← hsp]
    exact .eta hη her
  · obtain ⟨her, hdeps, hgr, -⟩ := etaGo_spec hG hk 0 f hctx hsc hargs
      (.inr ⟨rfl, by omega⟩) ⟨T, rfl⟩ hTT' hT'typ hok hI ⟨t, by rw [hsp]; exact he, htT'⟩ hrun _ rfl
    refine ⟨?_, hdeps, hgr⟩
    have hw : etaBody c us (spineArgs e) 0 = e := by
      simp only [etaBody, liftLooseBVars'_zero, List.map_id', List.range_zero, List.reverse_nil,
        List.map_nil, List.append_nil]
      exact hsp
    rw [hw] at her
    exact her

/-- The `proj` step (`StepsB.proj`): a projection the oracle keeps is a projection of a structure
(the oracle types it only for a large-eliminating inductive, `OracleSound.infer_projProof_ne`),
erased by `visitProj` to the λ□ projection of the erased major at the same field
(`Erases.proj`). Reference: the `tProj` case of `erases_erase` (`MR E/ErasureFunction.v:1228`),
rule `erases_tProj` (`MR E/Extract.v:118`). -/
theorem stepsB_proj {fuel : Nat} {s : Name} {i : Nat} {b : Expr}
    (hG : CoreEnv E B P decls view cfg) (ih : StepIH E B view cfg decls fuel) :
    ExprSpec E B view cfg decls (fuel + 1) (.proj s i b) := by
  intro lps n Γ Δ S t st₀ tc ps₀ r st' ps' hctx hsc hocc hmf hnp hrf hok he ht hrun
  rw [visitExpr] at hrun
  rcases oracle_run hrun with ⟨hor, rfl, rfl, rfl⟩ | ⟨hor, hrun⟩
  · exact visitExpr_box hG hctx hok he ht hor
  cases fuel with
  | zero => rw [visitProj] at hrun; cases hrun
  | succ k =>
  rw [visitProj, runPure_bind] at hrun
  obtain ⟨⟨⟨ci, st₁⟩, ps₁⟩, hci, hrun⟩ := OracleWhnf.ok_of_bind hrun
  obtain ⟨hfc, h1, h2⟩ := getConst_run hci
  subst st₁ ps₁
  cases ci with
  | inductInfo iv =>
    dsimp only at hrun
    rw [runPure_bind] at hrun
    obtain ⟨⟨⟨rr, st₁⟩, ps₁⟩, hreg, hrun⟩ := OracleWhnf.ok_of_bind hrun
    dsimp only at hrun
    have h1 : ps₁ = ps₀ := KeepsPS.register_inductive iv _ _ _ _ _ _ hreg
    subst ps₁
    rw [runPure_bind] at hrun
    obtain ⟨⟨⟨mask, st₂⟩, ps₂⟩, hmask, hrun⟩ := OracleWhnf.ok_of_bind hrun
    obtain ⟨hmk, h1, h2⟩ := getOrFail_run hmask
    subst st₂ ps₂
    dsimp only at hrun
    rw [runPure_bind] at hrun
    obtain ⟨⟨⟨rb, st₃⟩, ps₃⟩, hb, hrun⟩ := OracleWhnf.ok_of_bind hrun
    cases hrun
    have hfd : findDecl decls s = some (.inductInfo iv) := hfc
    have hname : iv.name = s := (findDecl_eq_some hfd).2
    have hmem : ConstantInfo.inductInfo iv ∈ decls := (findDecl_eq_some hfd).1
    have hirr : tc.config.remove_irrel_constr_args = false := by
      rw [hctx.config]; exact hG.irr iv ⟨_, hmem, rfl⟩
    have hph : ∀ ci ∈ (evalEnvOf view cfg decls).decls,
        PhaseIDecl (⟨decls, view⟩ : PureCtx).view tc.config (evalEnvOf view cfg decls).decls ci := by
      rw [hctx.config]; exact hG.phase
    have hiv : findDecl (evalEnvOf view cfg decls).decls iv.name = some (.inductInfo iv) := by
      rw [hname]; exact hfd
    obtain ⟨hok₁, hext₁, hcst₁, hiid, hkm⟩ :=
      register_inductive_ok hG.prog hG.wf hG.sub hok rfl hirr hph hG.bn hiv hreg
    have hreg₁ := register_inductive_mem hG.prog hG.sub rfl hirr hph hiv hreg
    have hfdP : findDecl P s = some (.inductInfo iv) := OracleWhnf.findConst_sub hG.sub hfc
    generalize hx : Expr.proj s i b = x at he
    cases he with
    | projProof hi0 hBS hs hc hnr _ hnst =>
      cases hx
      exfalso
      rcases OracleSound.isErasable_cases hor with ⟨c, us, v, hsp, -⟩ | ⟨T, ba, hT, -⟩
      · cases hsp
      · rw [show oracleFuel = 1048575 + 1 from rfl] at hT
        exact OracleSound.infer_projProof_ne hG.prog hG.wf hG.sub hBS hs hc hi0 hnr hnst hT
    | special => exact absurd hx (CasesWhred.ne_mkAppN_const fun _ _ h => by cases h)
    | projStruct hst hi hBS hb' hty =>
      cases hx
      rename_i ι η s' c ls₀ ps₀' is₀ e'
      obtain ⟨T, hT⟩ := ht
      have hmaj := recr_major (by rw [← hst.projTerm_eq_recr]; exact hT)
      obtain ⟨her, hdeps, hgr⟩ := ih.expr k (Nat.le_succ k) b hctx hsc (fun d hd => hocc d hd)
        hmf hnp hrf.2 hok₁ hb' ⟨_, hmaj⟩ hb
      -- the block of `s`: its only constructor and that constructor's fields
      obtain ⟨lps', Is, Cs, Rs, orders, ⟨_, _, _, _, hIB⟩, -, hfind, -, hindB, -⟩ :=
        CasesWhred.ProgEnv.block hG.prog η
      have hsI : s = (Is s').name := hindB s s' hBS
      have hivI : iv = Is s' := by
        have h1 : findDecl P (Is s').name = some (.inductInfo (Is s')) :=
          hfind (.inductInfo (Is s')) (by simp [IndBlock.decls, List.mem_ofFn])
        rw [← hsI, hfdP] at h1
        cases h1; rfl
      have hctorsI : iv.ctors = List.ofFn (fun d => (Cs s' d).name) := by
        rw [hivI]; exact (hIB.ind s').2.2.2.2.2.1
      have hn1 : ι.nctors s' = 1 := by
        have h0 := c.isLt
        by_contra hne
        have ha := hst.ctor_unique ⟨0, by omega⟩
        have hb := hst.ctor_unique ⟨1, by omega⟩
        rw [Fin.ext_iff] at ha hb
        simp at ha hb
        omega
      have hc0 : (⟨0, by omega⟩ : Fin (ι.nctors s')) = c := hst.ctor_unique _
      have hget0 : iv.ctors[0]? = some (Cs s' c).name := by
        rw [hctorsI, List.getElem?_ofFn]
        simp only [show 0 < ι.nctors s' by omega, dite_true]
        rw [hc0]
      have hlen1 : iv.ctors.length = 1 := by rw [hctorsI, List.length_ofFn, hn1]
      have hctors1 : iv.ctors = [(Cs s' c).name] := by
        obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hlen1
        rw [ha] at hget0 ⊢
        simp at hget0
        rw [hget0]
      have hcP : findDecl P (Cs s' c).name = some (.ctorInfo (Cs s' c)) :=
        hfind (.ctorInfo (Cs s' c)) (by
          simp only [IndBlock.decls, List.mem_append, List.mem_flatten, List.mem_ofFn]
          exact .inl (.inr ⟨_, ⟨s', rfl⟩, List.mem_ofFn.mpr ⟨c, rfl⟩⟩))
      have hcd : findDecl decls (Cs s' c).name = some (.ctorInfo (Cs s' c)) := by
        obtain ⟨-, -, hcl, -⟩ := hG.deps _ hmem
        obtain ⟨ci', hci'⟩ := Option.isSome_iff_exists.mp
          (hcl iv rfl _ (by rw [hctors1]; exact List.mem_singleton_self _))
        have h1 := OracleWhnf.findConst_sub hG.sub hci'
        rw [hcP] at h1
        cases h1
        exact hci'
      have hnf : (Cs s' c).numFields = (ι.ctors s' c).nfields + (ι.ctors s' c).nrecFields :=
        (hIB.ctor s' c).2.2.2.2.2.1
      have hmask' : mask = Array.replicate (Cs s' c).numFields .keep := by
        have := hkm.2 0 _ _ hget0 hcd
        rw [hmk] at this
        cases this; rfl
      have hcount : Array.count ConstructorArgRelevance.keep
          (Std.Slice.toArray (mask.toSubarray 0 i)) = i := by
        rw [hmask']; exact count_keep_slice (by omega)
      -- the sort of `s`
      have hdisj : PropInductive E B s ∨
          ∃ n u, arityShape iv.type = some (n, u) ∧ u.isNeverZero = true := by
        obtain ⟨-, -, ⟨nn, u, har, hu⟩, -⟩ := hG.phase _ hmem
        rcases hu with rfl | hnz | ⟨-, hnel⟩
        · exact .inl ((RegisterInd.propInductive_iff hG.prog hG.wf hfdP har (.inl rfl)).2 rfl)
        · exact .inr ⟨nn, u, har, hnz⟩
        · exact absurd (.inr ⟨_, _, hctors1, hcd, by omega⟩) hnel
      have hind : ErasesInd E B (evalEnvOf view cfg decls) st₃.gdecls s :=
        StateLemmas.ErasesInd.ext hgr.ext (hok₁.inductives s rr (hname ▸ hreg₁)).2.1
      dsimp only
      rw [hcount]
      refine ⟨.proj (subsingleton_of_structure hG.wf hBS hst) (hname ▸ hiid) hfd hdisj her,
        .proj (hname ▸ hiid) hind hdeps, Grows.trans ⟨hok₁, hext₁, Nat.le_refl _, ?_⟩ hgr⟩
      intro c' kn h1 h2
      rw [hcst₁, h1] at h2
      cases h2
    | _ => cases hx
  | _ =>
    dsimp only at hrun
    cases hrun

/-- `visitApp` on a constructor spine that the oracle keeps: `visitConstApp`'s constructor branch,
η-expanded by `withAppEtaToMinArity` (`etaGo_spec`). -/
theorem visitApp_ctor (hG : CoreEnv E B P decls view cfg) {fuel : Nat}
    (ih : StepIH E B view cfg decls fuel) {e : Expr} {c : Name} {us : List Level} {k : Nat}
    (hfn : e.getAppFn = .const c us) (hci : casesInfo? decls c = none)
    (hca : ctorArity? decls c = some k)
    {lps : List Name} {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    {S : Name → Prop} {t : Metalean.Expr ζ lps.length n} {st st' : ErasureState} {tc : TravCtx}
    {ps ps' : PureState} {r : LBTerm}
    (hctx : CtxOK E B lps Γ Δ cfg tc ps) (hsc : ScopeOK decls S)
    (hocc : ∀ d, nameOccurs d e = true → S d) (hmf : MachineFree cfg e) (hnp : NatPlain cfg e)
    (hrf : RecShaped cfg decls e) (hok : StateOK E B (evalEnvOf view cfg decls) st)
    (he : TrM E B lps Γ Δ e t) (ht : ∃ T, E[Γ] ⊢ t : T)
    (hor : Pure.isErasable ⟨decls⟩ oracleFuel tc.locals e = .ok false)
    (hrun : (visitApp (m := PureM) fuel e).runPure st tc ⟨decls, view⟩ ps =
      .ok ((r, st'), ps')) :
    Erases E B lps (evalEnvOf view cfg decls) Γ Δ e r ∧
      ErasesDeps E B (evalEnvOf view cfg decls) st'.gdecls r ∧
      Grows E B (evalEnvOf view cfg decls) S st st' ps ps' := by
  obtain ⟨cv, hc, rfl⟩ : ∃ cv, findDecl decls c = some (.ctorInfo cv) ∧
      k = cv.numParams + cv.numFields := by
    unfold ctorArity? at hca
    split at hca
    · rename_i cv hcv
      cases hca
      exact ⟨cv, hcv, rfl⟩
    · cases hca
  -- the spine
  have hA : (e.withApp fun _ as => as) = (spineArgs e).toArray := by
    rw [← withApp_toList e, Array.toArray_toList]
  have hsp : mkAppN (.const c us) (spineArgs e).toArray = e := by rw [← hfn]; exact mkAppN_spine e
  have hQ : ∀ {Q : Expr → Prop}, (∀ f a, Q (.app f a) → Q f ∧ Q a) → Q e →
      Q e.getAppFn ∧ ∀ a ∈ spineArgs e, Q a := fun hQ' h =>
    foldl_pred hQ' (by rw [← mkAppN_toArray, mkAppN_spine]; exact h)
  obtain ⟨-, hoccA⟩ := hQ (Q := fun x => ∀ d, nameOccurs d x = true → S d)
    (fun f a h => ⟨fun d hd => h d (by simp [nameOccurs, hd]),
      fun d hd => h d (by simp [nameOccurs, hd])⟩) hocc
  obtain ⟨hmfF, hmfA⟩ := hQ (Q := MachineFree cfg) (fun _ _ h => h) hmf
  obtain ⟨hnpF, hnpA⟩ := hQ (Q := NatPlain cfg) (fun _ _ h => h) hnp
  obtain ⟨-, hrfA⟩ := hQ (Q := RecShaped cfg decls) (fun _ _ h => h) hrf
  rw [hfn] at hmfF hnpF
  have hnat : cfg.nat = .machine → c ≠ ``Nat.zero ∧ c ≠ ``Nat.succ := fun h =>
    ⟨(hnpF h).1, (hmfF h).1⟩
  -- the constructor's block
  have hcP := SrcDefeq.findDecl_sub (σ := evalEnvOf view cfg decls) hG.sub hc
  obtain ⟨ι, η, s, k', o, hB, -, -, -, hord, -⟩ := hG.prog.lookup_ctor hcP
  have he' := he
  rw [← hsp] at he'
  obtain ⟨bs', hlenb, htr, hsat⟩ := TrM.special_inv hB rfl he'
  have htyped := ctor_args_typed hord hsat ht
  have hargs : ∀ a ∈ spineArgs e, (∀ d, nameOccurs d a = true → S d) ∧ MachineFree cfg a ∧
      NatPlain cfg a ∧ RecShaped cfg decls a ∧ ∃ a', TrM E B lps Γ Δ a a' ∧ ∃ A, E[Γ] ⊢ a' : A := by
    intro a ha
    refine ⟨hoccA a ha, hmfA a ha, hnpA a ha, hrfA a ha, ?_⟩
    obtain ⟨i, hai⟩ := List.mem_iff_getElem?.1 ha
    have hi : i < bs'.length := by rw [← hlenb]; exact (List.getElem?_eq_some_iff.1 hai).1
    have hbi : bs'[i]? = some bs'[i] := List.getElem?_eq_getElem hi
    exact ⟨_, htr i a _ hai hbi, htyped _ (List.mem_of_getElem? hbi)⟩
  -- the inductive is not in `Prop`: the oracle would have erased the spine
  have hnprop : ¬ PropInductive E B cv.induct := by
    intro hprop
    obtain ⟨ι₀, ζ₀, E₀, B₀, η₀, lps₀, Is, Cs, Rs, orders, s₀, k₀, hblk, hcv, hI⟩ :=
      SrcProof.ctor_mem_block hG.prog (findDecl_eq_some hcP).1
    have hfI := CasesWhred.findDecl_of_nodup hG.prog.fresh hI
    obtain ⟨-, -, hind, -⟩ := hblk.ctor s₀ k₀
    rw [CasesWhred.name_inductInfo, ← hind, ← hcv] at hfI
    obtain ⟨-, -, -, hcl, -⟩ := hG.deps _ (findDecl_eq_some hc).1
    obtain ⟨ci₁, hci₁⟩ := Option.isSome_iff_exists.mp (hcl cv rfl)
    have h1 := SrcDefeq.findDecl_sub (σ := evalEnvOf view cfg decls) hG.sub hci₁
    rw [hfI] at h1
    cases h1
    obtain ⟨-, -, ⟨nn, u, har, hu⟩, -⟩ := hG.phase _ (findDecl_eq_some hci₁).1
    have hu0 : u = .zero := (RegisterInd.propInductive_iff hG.prog hG.wf hfI har
      (hu.imp_right (Or.imp_right fun h => h.1))).1 hprop
    have hpi : (evalEnvOf view cfg decls).propInd cv.induct = true := by
      simp [EvalEnv.propInd, evalEnvOf, hci₁, har, hu0, EvidentZero]
    have hev := SrcProof.ctor_evidentProp hG.prog hG.wf hG.sub hc hpi
    have := Pure.isErasable_ctorProp (σ := evalEnvOf view cfg decls) rfl hc hev
      (by rw [hsp]; exact hor)
    cases this
  have hca' : ctorArity? decls c = some (cv.numParams + cv.numFields) := by
    unfold ctorArity?
    rw [show findConst decls c = findDecl decls c from rfl, hc]
  cases fuel with
  | zero => rw [visitApp] at hrun; cases hrun
  | succ f1 =>
  rw [visitApp] at hrun
  split at hrun
  swap
  · rename_i hne; exact absurd hfn (hne c us)
  cases f1 with
  | zero => rw [visitConstApp] at hrun; cases hrun
  | succ f2 =>
  rw [visitConstApp, withApp_eq] at hrun
  split at hrun
  swap
  · rename_i hne; exact absurd hfn (hne c us)
  rename_i c' us' hc'
  rw [hfn] at hc'
  cases hc'
  rw [runPure_bind, show (liftM (Backend.casesInfo? (m := PureM) c) :
      EraseT PureM (Option CasesInfo)).runPure st tc ⟨decls, view⟩ ps = .ok ((none, st), ps) by
    show Except.ok ((casesInfo? decls c, st), ps) = _; rw [hci], ok_bind'] at hrun
  dsimp only at hrun
  rw [runPure_bind, show (liftM (Backend.ctorArity? (m := PureM) c) :
      EraseT PureM (Option Nat)).runPure st tc ⟨decls, view⟩ ps =
        .ok ((some (cv.numParams + cv.numFields), st), ps) by
    show Except.ok ((ctorArity? decls c, st), ps) = _; rw [hca'], ok_bind'] at hrun
  dsimp only at hrun
  -- the declared type of the constructor has its arity of leading `Π`s
  obtain ⟨ι₀, ζ₀, E₀, B₀, η₀, lps₀, Is, Cs, Rs, orders, s₀, k₀, hblk, hcv, -⟩ :=
    SrcProof.ctor_mem_block hG.prog (findDecl_eq_some hcP).1
  subst hcv
  obtain ⟨body, -, hpk, -⟩ := hblk.ctorType s₀ k₀
  obtain ⟨-, -, -, -, hnpar, -⟩ := hblk.ctor s₀ k₀
  rw [← hnpar] at hpk
  refine withAppEta_spec (I := fun _ => True) hG hc (by simp [specialArity, evalEnvOf, hc]) hpk ?_
    hfn hctx hsc hargs hok trivial he ht hrun
  intro lps' n' Γ' Δ' S' st₁ st₁' tc' ps₁ ps₁' r' as' hctx' hsc' hargs' hlen' hok' _ _ hrun'

  beta_reduce at hrun'
  cases f2 with
  | zero => rw [visitConstructor] at hrun'; cases hrun'
  | succ g =>
  exact visitConstructor_spec hG ⟨fun m hm => ih.expr m (by omega), fun m hm => ih.mutDecl m (by omega)⟩
    hctx' hsc' hargs' hc hlen' hnprop hnat hok' hrun'

/-- The `ctor` step (`StepsB.ctor`): an application or a constant whose head is a constructor and not
a recognized `casesOn` constant, through `visitApp_ctor`. Reference: the `tConstruct` case of
`erases_erase` (`MR E/ErasureFunction.v:1228`), rule `erases_tConstruct`
(`MR E/Extract.v:106`); DV-23. -/
theorem stepsB_ctor {fuel : Nat} {e : Expr} {c : Name} {us : List Level} {k : Nat}
    (hG : CoreEnv E B P decls view cfg) (ih : StepIH E B view cfg decls fuel)
    (hfn : e.getAppFn = .const c us) (hci : casesInfo? decls c = none)
    (hca : ctorArity? decls c = some k) :
    ExprSpec E B view cfg decls (fuel + 1) e := by
  intro lps n Γ Δ S t st tc ps r st' ps' hctx hsc hocc hmf hnp hrf hok he ht hrun
  cases e with
  | app f a =>
    rw [visitExpr] at hrun
    rcases oracle_run hrun with ⟨hor, rfl, rfl, rfl⟩ | ⟨hor, hrun⟩
    · exact visitExpr_box hG hctx hok he ht hor
    exact visitApp_ctor hG ih hfn hci hca hctx hsc hocc hmf hnp hrf hok he ht hor hrun
  | const c' us' =>
    rw [visitExpr] at hrun
    rcases oracle_run hrun with ⟨hor, rfl, rfl, rfl⟩ | ⟨hor, hrun⟩
    · exact visitExpr_box hG hctx hok he ht hor
    exact visitApp_ctor hG ih hfn hci hca hctx hsc hocc hmf hnp hrf hok he ht hor hrun
  | _ => simp [Expr.getAppFn] at hfn

/-- The constructors that the closure declares under the names ``Nat.zero`` and ``Nat.succ``, if
any, are the constructors `0` and `1` of `Nat`, with no parameter and with `0` and `1` fields: the
names through which `visitLiteral` erases a Nat literal (`LeanToLambdaBox/Erasure.lean:708`), as
Lean's kernel reads a literal. -/
def NatCtorNames (decls : List ConstantInfo) : Prop :=
  (∀ cv, findDecl decls ``Nat.zero = some (.ctorInfo cv) →
    cv.induct = ``Nat ∧ cv.cidx = 0 ∧ cv.numParams = 0 ∧ cv.numFields = 0) ∧
  (∀ cv, findDecl decls ``Nat.succ = some (.ctorInfo cv) →
    cv.induct = ``Nat ∧ cv.cidx = 1 ∧ cv.numParams = 0 ∧ cv.numFields = 1)

/-- A successful run of `visitConstructor` is on a constructor of the closure. -/
theorem visitConstructor_ctor {j : Nat} {c : Name} {args : Array Expr} {tc : TravCtx}
    {st st' : ErasureState} {ps ps' : PureState} {r : LBTerm}
    (h : (visitConstructor (m := PureM) (j + 1) c args).runPure st tc ⟨decls, view⟩ ps =
      .ok ((r, st'), ps')) : ∃ cv, findDecl decls c = some (.ctorInfo cv) := by
  rw [visitConstructor, runPure_bind] at h
  obtain ⟨⟨⟨ci, st₁⟩, ps₁⟩, hci, h⟩ := OracleWhnf.ok_of_bind h
  obtain ⟨hfc, -, -⟩ := getConst_run hci
  cases ci with
  | ctorInfo cv => exact ⟨cv, hfc⟩
  | _ => dsimp only at h; cases h

/-- The `lit` step (`StepsB.lit`), when the closure's ``Nat.zero`` and ``Nat.succ`` are `Nat`'s
constructors (`NatCtorNames`): under `nat := .peano` (`NatPlain`) a literal `k + 1` is erased as
``Nat.succ`` applied to the erasure of `k`, and `0` as ``Nat.zero`` (`Erases.litSucc`,
`Erases.litZero`); a literal above `peanoMaxLiteral` has no successful run, and a string literal
has no translation. Reference: none (PCUIC has no literals; `visitLiteral`,
`LeanToLambdaBox/Erasure.lean:704`). -/
theorem stepsB_lit_of (hnn : NatCtorNames decls) {fuel : Nat} {l : Literal}
    (hG : CoreEnv E B P decls view cfg) (ih : StepIH E B view cfg decls fuel) :
    ExprSpec E B view cfg decls (fuel + 1) (.lit l) := by
  intro lps n Γ Δ S t st tc ps r st' ps' hctx hsc hocc hmf hnp hrf hok he ht hrun
  rw [visitExpr] at hrun
  rcases oracle_run hrun with ⟨hor, rfl, rfl, rfl⟩ | ⟨-, hrun⟩
  · exact visitExpr_box hG hctx hok he ht hor
  obtain ⟨k, rfl⟩ : ∃ k, l = .natVal k := by
    cases l with
    | natVal k => exact ⟨k, rfl⟩
    | strVal s =>
      exfalso
      generalize hx : Expr.lit (.strVal s) = x at he
      cases he with
      | special => exact absurd hx (CasesWhred.ne_mkAppN_const fun _ _ h => by cases h)
      | _ => cases hx
  have hpeano : cfg.nat = .peano := hnp
  obtain ⟨ηNat, hB, rfl⟩ := CasesWhred.trM_lit_inv he
  obtain ⟨η', o₀, o₁, hB', h₀, h₁⟩ := CasesWhred.trM_lit_ctors he
  obtain rfl : η' = ηNat := by rw [hB] at hB'; cases hB'; rfl
  have hnat : cfg.nat = .machine → ∀ c : Name, c ≠ ``Nat.zero ∧ c ≠ ``Nat.succ := fun h => by
    rw [hpeano] at h; cases h
  cases fuel with
  | zero => rw [visitLiteral] at hrun; cases hrun
  | succ f =>
  cases f with
  | zero =>
    rw [visitLiteral, runPure_read_bind, hctx.config, hpeano] at hrun
    dsimp only at hrun
    by_cases hb : k > peanoMaxLiteral
    · rw [if_pos hb, runPure_read_bind] at hrun; cases hrun
    rw [if_neg hb] at hrun
    cases k with
    | zero => rw [if_pos rfl, visitConstructor] at hrun; cases hrun
    | succ k => rw [if_neg (Nat.succ_ne_zero k), visitConstructor] at hrun; cases hrun
  | succ g =>
  have ihg : StepIH E B view cfg decls g :=
    ⟨fun m hm => ih.expr m (by omega), fun m hm => ih.mutDecl m (by omega)⟩
  rw [visitLiteral, runPure_read_bind, hctx.config, hpeano] at hrun
  dsimp only at hrun
  by_cases hb : k > peanoMaxLiteral
  · rw [if_pos hb, runPure_read_bind] at hrun; cases hrun
  rw [if_neg hb] at hrun
  cases k with
  | zero =>
    rw [if_pos rfl] at hrun
    obtain ⟨cv, hcv⟩ := visitConstructor_ctor hrun
    obtain ⟨hind, hcidx, hnp0, hnf0⟩ := hnn.1 cv hcv
    obtain ⟨iid, as', rfl, hiid, hlen', -, hdeps, hgr, -⟩ :=
      visitConstructor_core (args := []) hG ihg hctx hsc (by simp) hcv (by simp; omega)
        (hnat · _) hok hrun
    obtain rfl : as' = [] := List.eq_nil_of_length_eq_zero hlen'.symm
    rw [hind] at hiid
    rw [hcidx] at hdeps ⊢
    exact ⟨.litZero hiid, hdeps, hgr⟩
  | succ k =>
    rw [if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel] at hrun
    obtain ⟨cv, hcv⟩ := visitConstructor_ctor hrun
    obtain ⟨hind, hcidx, hnp0, hnf0⟩ := hnn.2 cv hcv
    obtain ⟨A', -, hA'⟩ := OracleInfer.lit_type (Γ := Γ) (Δ := Δ) (lps := lps) hB k
    have hargs : ∀ a ∈ [Expr.lit (.natVal k)], (∀ d, nameOccurs d a = true → S d) ∧
        MachineFree cfg a ∧ NatPlain cfg a ∧ RecShaped cfg decls a ∧
        ∃ a', TrM E B lps Γ Δ a a' ∧ ∃ A, E[Γ] ⊢ a' : A := by
      intro a ha
      rw [List.mem_singleton] at ha
      subst ha
      exact ⟨fun _ h => by simp [nameOccurs] at h, trivial, hpeano, trivial, _, .lit hB h₀ h₁, _, hA'⟩
    obtain ⟨iid, as', rfl, hiid, hlen', hers, hdeps, hgr, -⟩ :=
      visitConstructor_core (args := [.lit (.natVal k)]) hG ihg hctx hsc hargs hcv
        (by simp; omega) (hnat · _) hok hrun
    obtain ⟨t', rfl⟩ : ∃ t', as' = [t'] := List.length_eq_one_iff.mp hlen'.symm
    rw [hind] at hiid
    rw [hcidx] at hdeps ⊢
    exact ⟨.litSucc hiid (hers 0 _ _ rfl rfl), hdeps, hgr⟩

end
end Steps
end EraseProof
