import EraseProof.Core.State

/-!
# Registering an inductive block

`register_inductive` (`LeanToLambdaBox/Erasure.lean:509`) registers the whole block of an
inductive type at once, each type at its position with masks that keep every field, and conses
one λ□ block to the environment (`register_inductive_run`, over a Hoare-style reading `HT` of the
pure backend's runs). It sets a λ□ body's `propositional` flag to `Pure.isPropFormerType` of the
Lean inductive's declared type, a syntactic test: the sort reached through Π-binders and metadata
is `Sort 0` as written (`isPropFormerType_arity`). `ErasesInd` asks the flag to be
`EvalEnv.propInd`, that the sort is zero under every assignment, structurally (`EvidentZero`).
The two agree on the sorts the fragment test admits (`PhaseIDecl`, checked by
`Erasure.sortDecided`): written `Prop`, never zero, or not zero under some assignment
(`isPropFormerType_iff`). Lean's kernel accepts an inductive at `Sort (max 0 0)`, which is
`EvidentZero` while the test answers `false`; the fragment test excludes it.

`register_inductive_ok` keeps `StateOK`. The block facts that the run does not check (the block's
names are distinct and contain the type, and every member lists the same block and parameter
count) are its premises. Port of `ML-V Core/RegisterInd.lean` without its Metalean part (the
level of a Metalean block), and with `EvidentZero` for Metalean's level of a block.
-/

open Lean Erasure

namespace EraseProof

namespace RegisterInd

open StateLemmas Restrict

/-- A successful bind is a successful first step followed by a successful continuation. Port of
`ML-V Oracle/Whnf.lean:71`. -/
theorem ok_of_bind {α β ε : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  rcases x with e | a
  · cases h
  · exact ⟨a, rfl, h⟩

/-! ## The propositional flag -/

/-- On a syntactic arity, `whnf` only strips metadata. -/
theorem whnf_arity {cx : Pure.Ctx} {ls : List Local} :
    ∀ {f : Nat} {T W : Expr} {k : Nat} {u : Level}, arityShape T = some (k, u) →
      Pure.whnf cx f ls T = .ok W → arityShape W = some (k, u) ∧ ∀ d e, W ≠ .mdata d e
  | 0, _, _, _, _, _, h => by simp [Pure.whnf, throw, throwThe, MonadExceptOf.throw] at h
  | f + 1, .sort v, W, k, u, ha, h => by
    simp only [Pure.whnf, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨ha, fun _ _ h => by cases h⟩
  | f + 1, .forallE x A C bi, W, k, u, ha, h => by
    simp only [Pure.whnf, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨ha, fun _ _ h => by cases h⟩
  | f + 1, .mdata d e, W, k, u, ha, h => by
    simp only [Pure.whnf] at h
    simp only [arityShape] at ha
    exact whnf_arity ha h
  | _ + 1, .bvar _, _, _, _, ha, _ | _ + 1, .fvar _, _, _, _, ha, _
  | _ + 1, .mvar _, _, _, _, ha, _ | _ + 1, .const .., _, _, _, ha, _
  | _ + 1, .app .., _, _, _, ha, _ | _ + 1, .lam .., _, _, _, ha, _
  | _ + 1, .letE .., _, _, _, ha, _ | _ + 1, .lit _, _, _, _, ha, _
  | _ + 1, .proj .., _, _, _, ha, _ => by simp [arityShape] at ha

/-- On a syntactic arity `Π x̄, Sort u`, `isPropFormerType` answers whether `u` is written
`Prop`. -/
theorem isPropFormerType_arity {cx : Pure.Ctx} {ls : List Local} :
    ∀ {f : Nat} {T : Expr} {k : Nat} {u : Level} {b : Bool}, arityShape T = some (k, u) →
      Pure.isPropFormerType cx f ls T = .ok b → (b = true ↔ u = .zero)
  | 0, _, _, _, _, _, h => by
    simp [Pure.isPropFormerType, throw, throwThe, MonadExceptOf.throw] at h
  | f + 1, T, k, u, b, ha, h => by
    simp only [Pure.isPropFormerType] at h
    obtain ⟨W, hW, h⟩ := ok_of_bind h
    obtain ⟨haW, hnm⟩ := whnf_arity ha hW
    cases W with
    | sort v =>
      simp only [arityShape, Option.some.injEq, Prod.mk.injEq] at haW
      obtain ⟨-, rfl⟩ := haW
      cases v <;> simp_all [pure, Except.pure]
    | forallE x A C bi =>
      simp only [arityShape, Option.map_eq_some_iff] at haW
      obtain ⟨⟨k', u'⟩, hC, he⟩ := haW
      simp only [Prod.mk.injEq] at he
      obtain ⟨-, rfl⟩ := he
      exact isPropFormerType_arity hC h
    | mdata d e => exact absurd rfl (hnm d e)
    | _ => simp [arityShape] at haW

/-- A level that is zero under every assignment, structurally, is not never zero. Reference:
none. -/
theorem evidentZero_isNeverZero : ∀ {u : Level}, EvidentZero u = true → u.isNeverZero = false
  | .zero, _ => rfl
  | .max a b, h => by
    simp only [EvidentZero, Bool.and_eq_true] at h
    simp only [Level.isNeverZero, evidentZero_isNeverZero h.1, evidentZero_isNeverZero h.2,
      Bool.or_self]
  | .imax _ b, h => by
    simp only [EvidentZero] at h
    simp only [Level.isNeverZero, evidentZero_isNeverZero h]
  | .succ _, h | .param _, h | .mvar _, h => by simp [EvidentZero] at h

/-- A level that is zero under every assignment, structurally, stays so under a substitution of
its parameters. Reference: none. -/
theorem evidentZero_instLevel (ps : List Name) (us : List Level) :
    ∀ {u : Level}, EvidentZero u = true → EvidentZero (Pure.instLevel ps us u) = true
  | .zero, _ => rfl
  | .max a b, h => by
    simp only [EvidentZero, Bool.and_eq_true] at h
    simp only [Pure.instLevel, EvidentZero, evidentZero_instLevel ps us h.1,
      evidentZero_instLevel ps us h.2, Bool.and_self]
  | .imax a b, h => by
    simp only [EvidentZero] at h
    simp only [Pure.instLevel, EvidentZero, evidentZero_instLevel ps us h]
  | .succ _, h | .param _, h | .mvar _, h => by simp [EvidentZero] at h

/-- On a sort written `Prop`, never zero, or not zero under some assignment of the parameters
`lps` (the sorts `Erasure.sortDecided` admits), `EvidentZero` is `Prop` as written. Reference:
none. -/
theorem evidentZero_iff {lps : List Name} {u : Level}
    (hu : u = .zero ∨ u.isNeverZero = true ∨ mayBeNonZero lps u = true) :
    EvidentZero u = true ↔ u = .zero := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  rcases hu with hu | hu | hu
  · exact hu
  · rw [evidentZero_isNeverZero h] at hu
    cases hu
  · unfold mayBeNonZero at hu
    rw [evidentZero_isNeverZero (evidentZero_instLevel _ _ h)] at hu
    cases hu

/-- The propositional flag that `register_inductive` computes is `EvalEnv.propInd`, on every
inductive that passes the fragment test (`PhaseIDecl`, `Erasure.sortDecided`): the test reads
`Sort 0` as written, `propInd` a sort that is zero under every assignment, and the fragment admits
only sorts written `Prop`, never zero, or not zero under some assignment, on which the two agree.
Adapted from `ML-V Core/RegisterInd.lean:326`. Reference: `Sort.is_propositional` of the
inductive's sort in `MR E/ErasureFunction.v:1325 erase_one_inductive_body`, `isPropositional`
(`MR P/PCUICFirstorder.v:109`). -/
theorem isPropFormerType_iff {σ : EvalEnv} {view : EnvView} {cfg : ErasureConfig}
    {cx : Pure.Ctx} {fuel : Nat} {ls : List Local} {c : Name} {iv : InductiveVal} {b : Bool}
    (hc : findDecl σ.decls c = some (.inductInfo iv))
    (hph : PhaseIDecl view cfg σ.decls (.inductInfo iv))
    (h : Pure.isPropFormerType cx fuel ls iv.type = .ok b) : b = true ↔ σ.propInd c = true := by
  obtain ⟨-, -, ⟨k, u, ha, hu⟩, -⟩ := hph
  rw [isPropFormerType_arity ha h]
  have hp : σ.propInd c = EvidentZero u := by
    unfold EvalEnv.propInd
    rw [hc]
    simp only [ha]
  rw [hp]
  exact (evidentZero_iff (lps := iv.levelParams) (hu.imp_right (Or.imp_right And.left))).symm

/-! ## Runs of the pure traversal -/

section
variable {α β : Type} {tc : TravCtx} {pc : PureCtx}

/-- A run of a bind runs the continuation from the state the first action leaves. Port of
`ML-V Core/Frame.lean:85`. -/
theorem runPure_bind {st : ErasureState} {ps : PureState} {tc : TravCtx} (x : EraseT PureM α)
    (k : α → EraseT PureM β) :
    (x >>= k).runPure st tc pc ps =
      x.runPure st tc pc ps >>= fun r => (k r.1.1).runPure r.1.2 tc pc r.2 := rfl

/-- A run of `read >>= k` runs `k` on the reader context. Port of `ML-V Core/Frame.lean:90`. -/
theorem runPure_read_bind {st : ErasureState} {ps : PureState} {tc : TravCtx}
    (k : TravCtx → EraseT PureM α) :
    (read >>= k).runPure st tc pc ps = (k tc).runPure st tc pc ps := rfl

/-- A run of a lifted backend action leaves the traversal state unchanged. Port of
`ML-V Core/Frame.lean:94`. -/
theorem runPure_liftM {st : ErasureState} {ps : PureState} {tc : TravCtx} (x : PureM α) :
    (_root_.liftM x : EraseT PureM α).runPure st tc pc ps =
      ((x.run pc).run ps >>= fun r => .ok ((r.1, st), r.2)) := rfl

/-- Every successful run of `x` from a state satisfying `I` ends with a result and a state
satisfying `Q`. -/
def HT (tc : TravCtx) (pc : PureCtx) (I : ErasureState → Prop) (x : EraseT PureM α)
    (Q : α → ErasureState → Prop) : Prop :=
  ∀ st ps a st' ps', I st → x.runPure st tc pc ps = .ok ((a, st'), ps') → Q a st'

theorem HT.pure {I : ErasureState → Prop} {Q : α → ErasureState → Prop} {a : α}
    (h : ∀ s, I s → Q a s) : HT tc pc I (Pure.pure a) Q := by
  intro st ps a' st' ps' hI hr
  cases hr
  exact h _ hI

theorem HT.bind {I : ErasureState → Prop} {R : α → ErasureState → Prop}
    {Q : β → ErasureState → Prop} {x : EraseT PureM α} {k : α → EraseT PureM β}
    (hx : HT tc pc I x R) (hk : ∀ a, HT tc pc (R a) (k a) Q) : HT tc pc I (x >>= k) Q := by
  intro st ps b st' ps' hI hr
  rw [runPure_bind] at hr
  rcases hx' : x.runPure st tc pc ps with _ | ⟨⟨a, s₁⟩, ps₁⟩
  · rw [hx'] at hr; cases hr
  · rw [hx'] at hr
    exact hk a s₁ ps₁ b st' ps' (hx st ps a s₁ ps₁ hI hx') hr

theorem HT.mono {I I' : ErasureState → Prop} {Q Q' : α → ErasureState → Prop}
    {x : EraseT PureM α} (h : HT tc pc I x Q) (hI : ∀ s, I' s → I s)
    (hQ : ∀ a s, Q a s → Q' a s) : HT tc pc I' x Q' :=
  fun st ps a st' ps' h' hr => hQ _ _ (h st ps a st' ps' (hI _ h') hr)

theorem HT.get {I : ErasureState → Prop} :
    HT tc pc I (MonadState.get : EraseT PureM ErasureState) (fun a s => I s ∧ a = s) := by
  intro st ps a st' ps' hI hr
  cases hr
  exact ⟨hI, rfl⟩

theorem HT.modify {I : ErasureState → Prop} (f : ErasureState → ErasureState) :
    HT tc pc I (_root_.modify f : EraseT PureM PUnit) (fun _ s => ∃ s₀, I s₀ ∧ s = f s₀) := by
  intro st ps a st' ps' hI hr
  cases hr
  exact ⟨st, hI, rfl⟩

theorem HT.read_bind {I : ErasureState → Prop} {Q : α → ErasureState → Prop}
    {k : TravCtx → EraseT PureM α} (h : HT tc pc I (k tc) Q) : HT tc pc I (read >>= k) Q :=
  fun st ps a st' ps' hI hr => h st ps a st' ps' hI (by rwa [runPure_read_bind] at hr)

theorem HT.liftM {I : ErasureState → Prop} (x : PureM α) :
    HT tc pc I (_root_.liftM x : EraseT PureM α)
      (fun a s => I s ∧ ∃ ps ps', (x.run pc).run ps = .ok (a, ps')) := by
  intro st ps a st' ps' hI hr
  rw [runPure_liftM] at hr
  rcases hx : (x.run pc).run ps with _ | ⟨b, ps₁⟩
  · rw [hx] at hr; cases hr
  · rw [hx] at hr
    cases hr
    exact ⟨hI, ps, ps₁, hx⟩

theorem HT.throwM {I : ErasureState → Prop} {Q : α → ErasureState → Prop} (err : EraseError) :
    HT tc pc I (_root_.liftM (throw err : PureM α) : EraseT PureM α) Q :=
  fun _ _ _ _ _ _ hr => nomatch hr

theorem HT.getConst {I : ErasureState → Prop} (n : Name) :
    HT tc pc I (getConst (m := PureM) n) (fun ci s => I s ∧ findConst pc.decls n = some ci) := by
  unfold Erasure.getConst
  refine HT.bind (R := fun r s => I s ∧ r = findConst pc.decls n) ?_ fun r => ?_
  · intro st ps a st' ps' hI hr
    cases hr
    exact ⟨hI, rfl⟩
  · split
    · next ci => exact HT.pure fun s hs => ⟨hs.1, hs.2.symm⟩
    · exact HT.throwM _

theorem HT.getOrFail {γ : Type} [Inhabited γ] {I : ErasureState → Prop} (o : Option γ)
    (msg : String) : HT tc pc I (getOrFail (m := PureM) o msg) (fun a s => I s ∧ o = some a) := by
  cases o with
  | some a => exact HT.pure fun s hs => ⟨hs, rfl⟩
  | none => exact HT.throwM _

/-- `List.mapM` with an invariant indexed by the processed prefix of the list `L`. -/
theorem HT.mapM {f : α → EraseT PureM β} {P : α → β → Prop}
    {I : List α → ErasureState → Prop} {L : List α}
    (hf : ∀ pre a rest, pre ++ a :: rest = L →
      HT tc pc (I pre) (f a) (fun b s => I (pre ++ [a]) s ∧ P a b)) :
    ∀ (l pre : List α), pre ++ l = L →
      HT tc pc (I pre) (l.mapM f) (fun bs s => I L s ∧ List.Forall₂ P l bs)
  | [], pre, h => by
    rw [List.mapM_nil]
    exact HT.pure fun s hs => ⟨by rw [List.append_nil] at h; exact h ▸ hs, .nil⟩
  | a :: l, pre, h => by
    rw [List.mapM_cons]
    refine HT.bind (hf pre a l h) fun b => ?_
    intro st ps bs st' ps' ⟨hI, hP⟩ hr
    rw [runPure_bind] at hr
    rcases hl : (l.mapM f).runPure st tc pc ps with _ | ⟨⟨bs', s₁⟩, ps₁⟩
    · rw [hl] at hr; cases hr
    · rw [hl] at hr
      cases hr
      obtain ⟨hI', hF⟩ := HT.mapM hf l (pre ++ [a]) (by simpa using h) st ps bs' s₁ ps₁ hI hl
      exact ⟨hI', .cons hP hF⟩

theorem HT.of_fact {I : ErasureState → Prop} {Q : α → ErasureState → Prop} {p : Prop}
    {x : EraseT PureM α} (h : p → HT tc pc I x Q) : HT tc pc (fun s => I s ∧ p) x Q :=
  fun st ps a st' ps' ⟨hI, hp⟩ hr => h hp st ps a st' ps' hI hr

theorem HT.any {I : ErasureState → Prop} {x : EraseT PureM α} :
    HT tc pc I x (fun _ _ => True) :=
  fun _ _ _ _ _ _ _ => trivial

theorem HT.pure_eq {I : ErasureState → Prop} {a : α} :
    HT tc pc I (Pure.pure a) (fun b s => I s ∧ b = a) :=
  HT.pure fun _ h => ⟨h, rfl⟩

theorem isExtern_run {n : Name} {ps ps' : PureState} {a : Bool}
    (h : ((Backend.isExtern (m := PureM) n).run pc).run ps = .ok (a, ps')) :
    a = pc.view.isExtern n := by
  cases h
  rfl

theorem pureM_isPropFormerType_run (e : Expr) (ps : PureState) :
    ((PureM.isPropFormerType e).run pc).run ps =
      (Pure.isPropFormerType ⟨pc.decls⟩ oracleFuel [] e).map (·, ps) := by
  unfold PureM.isPropFormerType
  have hr : ReaderT.run (read : PureM PureCtx) pc = Pure.pure pc := rfl
  simp only [ReaderT.run_bind, hr, pure_bind]
  rcases Pure.isPropFormerType ⟨pc.decls⟩ oracleFuel [] e with err | b
  · rfl
  · rfl

theorem isPropFormerType_run (e : Expr) (ps : PureState) :
    ((Backend.isPropFormerType (m := PureM) e).run pc).run ps =
      (Pure.isPropFormerType ⟨pc.decls⟩ oracleFuel [] e).map (·, ps) :=
  pureM_isPropFormerType_run e ps

end

/-! ## The run of `register_inductive` -/

/-- The λ□ body that `register_inductive` builds for the type `p.1` at position `p.2` of its
block: one constructor per Lean constructor, each with all its fields, and the flag of
`Pure.isPropFormerType` on the type's declared type. -/
def BodyOK (σ : EvalEnv) (p : Name × Nat) (ob : OneInductiveBody) : Prop :=
  ∃ ivn, findDecl σ.decls p.1 = some (.inductInfo ivn) ∧ ob.ctors.length = ivn.ctors.length ∧
    (∀ (k : Nat) cn, ivn.ctors[k]? = some cn → ∃ (cv : ConstructorVal) (cb : ConstructorBody),
      findDecl σ.decls cn = some (.ctorInfo cv) ∧ ob.ctors[k]? = some cb ∧
      cb.nargs = cv.numFields) ∧
    Pure.isPropFormerType ⟨σ.decls⟩ oracleFuel [] ivn.type = .ok ob.propositional

/-- What `register_inductive` builds for the constructor `cn`: its λ□ body with all its fields and
the mask that keeps every field. -/
def CtorOK (pc : PureCtx) (cn : Name) (out : ConstructorBody × ConstructorArgMask) : Prop :=
  ∃ cv, findConst pc.decls cn = some (.ctorInfo cv) ∧ out.1.nargs = cv.numFields ∧
    out.2 = Array.replicate cv.numFields .keep

/-- The state after `register_inductive` has registered the types `pre` of a block named `bk`,
from the state `st₀`: constants and λ□ environment unchanged, every type of `pre` registered at
its position with masks that keep every field, the other entries unchanged. -/
def Registered (σ : EvalEnv) (st₀ : ErasureState) (bk : Kername) (pre : List (Name × Nat))
    (s : ErasureState) : Prop :=
  s.constants = st₀.constants ∧ s.gdecls = st₀.gdecls ∧
    (∀ T, (∀ p ∈ pre, p.1 ≠ T) → s.inductives[T]? = st₀.inductives[T]?) ∧
    ∀ p ∈ pre, ∃ ivn masks, findDecl σ.decls p.1 = some (.inductInfo ivn) ∧
      s.inductives[p.1]? = some (⟨bk, p.2⟩, masks) ∧ KeepMasks σ ivn masks

/-- The element at a position of the first list of `Forall₂` has a partner at that position. -/
theorem forall₂_get {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ R l l') : ∀ {k : Nat} {a : α}, l[k]? = some a →
      ∃ b, l'[k]? = some b ∧ R a b := by
  induction h with
  | nil => intro k a h; simp at h
  | cons hab _ ih =>
    intro k a h
    cases k with
    | zero => simp at h; subst h; exact ⟨_, rfl, hab⟩
    | succ k => simpa using ih (by simpa using h)

/-- Lists related by `Forall₂` have the same length. -/
theorem forall₂_length {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ R l l') : l.length = l'.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- In a list of distinct names with their positions, a name differs from every name before
it. -/
theorem zipIdx_prefix_ne {l : List Name} (hnd : l.Nodup) {pre rest : List (Name × Nat)}
    {n : Name} {j : Nat} (h : pre ++ (n, j) :: rest = l.zipIdx) : ∀ p ∈ pre, p.1 ≠ n := by
  have h2 := congrArg (List.map Prod.fst) h
  rw [List.zipIdx_map_fst] at h2
  rw [← h2, List.map_append, List.map_cons] at hnd
  intro p hp heq
  exact (List.nodup_append.1 hnd).2.2 p.1 (List.mem_map_of_mem hp) n List.mem_cons_self heq

section
variable {tc : TravCtx} {pc : PureCtx}

/-- A run of `register_inductive` at the pure backend: either the type is registered and the
state is unchanged, or the whole block is registered at once (`Registered`), each type with a body
that `BodyOK` describes, and the block is consed to the λ□ environment. -/
theorem register_inductive_run {σ : EvalEnv} {iv : InductiveVal} (hdecls : pc.decls = σ.decls)
    (hirr : tc.config.remove_irrel_constr_args = false)
    (hext : ∀ cn cv, findDecl σ.decls cn = some (.ctorInfo cv) →
      tc.config.1 = .preferAxiom → pc.view.isExtern cn = false)
    (hnd : iv.all.Nodup) (st₀ : ErasureState) :
    HT tc pc (· = st₀) (register_inductive (m := PureM) iv) (fun r s =>
      (st₀.inductives[iv.name]? = some r ∧ s = st₀) ∨
      (st₀.inductives[iv.name]? = none ∧ ∃ s₁ bodies,
        Registered σ st₀ (mutualBlockKername iv.all) iv.all.zipIdx s₁ ∧
        List.Forall₂ (BodyOK σ) iv.all.zipIdx bodies ∧ s₁.inductives[iv.name]? = some r ∧
        s = { s₁ with gdecls := s₁.gdecls.cons (mutualBlockKername iv.all,
          .inductiveDecl { npars := iv.numParams, bodies }) })) := by
  rw [Erasure.register_inductive]
  refine HT.bind HT.get fun s => ?_
  split
  · next iid hiid =>
    refine HT.pure fun s' ⟨h1, h2⟩ => .inl ⟨?_, ?_⟩
    · subst h1 h2; rwa [Std.HashMap.get?_eq_getElem?] at hiid
    · exact h1
  · next hnone =>
    refine HT.bind (R := fun bodies s' => s = st₀ ∧
      Registered σ st₀ (mutualBlockKername iv.all) iv.all.zipIdx s' ∧
      List.Forall₂ (BodyOK σ) iv.all.zipIdx bodies) ?_ fun bodies => ?_
    · refine HT.mono (HT.mapM (I := fun pre s' => s = st₀ ∧
          Registered σ st₀ (mutualBlockKername iv.all) pre s') (P := BodyOK σ)
          (L := iv.all.zipIdx) (fun pre p rest hpre => ?_) _ [] rfl) ?_ ?_
      rotate_left
      · rintro s' ⟨rfl, rfl⟩
        exact ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ h => nomatch h⟩
      · rintro bodies' s' ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h1, h2, h3⟩
      obtain ⟨n, j⟩ := p
      dsimp only
      refine HT.bind (HT.getConst _) fun ci => ?_
      split
      · next inf =>
        refine HT.of_fact fun hinf => ?_
        refine HT.bind (HT.mapM (I := fun _ s' => s = st₀ ∧
            Registered σ st₀ (mutualBlockKername iv.all) pre s') (P := CtorOK pc)
            (L := inf.ctors) (fun pre' cn rest' _ => ?_) _ [] rfl) fun outs => ?_
        · refine HT.bind (HT.liftM _) fun a => HT.of_fact fun ha => ?_
          obtain ⟨_, _, ha⟩ := ha
          have ha' := isExtern_run ha
          refine HT.read_bind ?_
          split
          · next hc =>
            refine HT.bind (HT.liftM _) fun _ => HT.bind HT.any fun _ => ?_
            refine HT.bind (HT.getConst _) fun ci => ?_
            split
            · next cv =>
              refine HT.of_fact fun hcv => ?_
              exfalso
              rw [Bool.and_eq_true, ha'] at hc
              have hx : tc.config.1 = .preferAxiom := by
                obtain ⟨-, h2⟩ := hc
                revert h2
                cases tc.config.1 <;> first | (intro; rfl) | (intro h; cases h)
              have := hext cn cv (hdecls ▸ hcv) hx
              rw [this] at hc
              exact Bool.false_ne_true hc.1
            · exact HT.throwM _
          · next hc =>
            refine HT.bind (HT.getConst _) fun ci => ?_
            split
            · next cv =>
              refine HT.of_fact fun hcv => ?_
              refine HT.read_bind ?_
              split
              · next hrm => exact absurd hrm (by simp [hirr])
              · refine HT.bind HT.pure_eq fun am => HT.of_fact fun ham => ?_
                subst ham
                refine HT.pure fun s' hs' => ⟨hs', cv, hcv, ?_, rfl⟩
                show Array.count ConstructorArgRelevance.keep
                  (Array.replicate cv.numFields ConstructorArgRelevance.keep) = cv.numFields
                generalize cv.numFields = m
                induction m with
                | zero => rfl
                | succ m ih => rw [Array.replicate_succ, Array.count_push, ih]; rfl
            · exact HT.throwM _
        · refine HT.of_fact fun hF => ?_
          have hne := zipIdx_prefix_ne hnd hpre
          have hinf' : findDecl σ.decls n = some (.inductInfo inf) := hdecls ▸ hinf
          have hcv : ∀ (k : Nat) cn, inf.ctors[k]? = some cn → ∃ cv out,
              findDecl σ.decls cn = some (.ctorInfo cv) ∧ outs[k]? = some out ∧
              out.1.nargs = cv.numFields ∧ out.2 = Array.replicate cv.numFields .keep := by
            intro k cn hk
            obtain ⟨out, hout, cv, hc, h1, h2⟩ := forall₂_get hF hk
            exact ⟨cv, out, hdecls ▸ hc, hout, h1, h2⟩
          have hlen := forall₂_length hF
          have tail : ∀ projs : List ProjectionBody, HT tc pc
              (fun s₁ => s = st₀ ∧ Registered σ st₀ (mutualBlockKername iv.all) pre s₁)
              (_root_.modify (fun s : ErasureState => { s with
                  inductives := (s.inductives.insert n
                    ({ mutualBlockName := mutualBlockKername iv.all, idx := j }, outs.unzip.2)) }) >>=
                fun _ => (_root_.liftM (Backend.isPropFormerType (m := PureM) inf.type) :
                  EraseT PureM Bool) >>= fun propositional =>
                (Pure.pure { name := toString n, propositional, ctors := outs.unzip.1, projs } :
                  EraseT PureM OneInductiveBody))
              (fun b s₁ => (s = st₀ ∧
                Registered σ st₀ (mutualBlockKername iv.all) (pre ++ [(n, j)]) s₁) ∧
                BodyOK σ (n, j) b) := by
            intro projs
            refine HT.bind (HT.modify _) fun _ => HT.bind (HT.liftM _) fun b => HT.pure ?_
            rintro s₂ ⟨⟨s₁, ⟨rfl, hreg⟩, rfl⟩, _, _, hb⟩
            rw [isPropFormerType_run] at hb
            have hb' : Pure.isPropFormerType ⟨σ.decls⟩ oracleFuel [] inf.type = .ok b := by
              rw [← hdecls]
              rcases h : Pure.isPropFormerType ⟨pc.decls⟩ oracleFuel [] inf.type with _ | b' <;>
                rw [h] at hb <;> cases hb
              rfl
            obtain ⟨hc₁, hg₁, hold, hnew⟩ := hreg
            have hmask : KeepMasks σ inf outs.unzip.2 := by
              refine ⟨by simp [hlen], fun k cn cv hk hc => ?_⟩
              obtain ⟨cv', out, hc', hout, -, h2⟩ := hcv k cn hk
              rw [hc] at hc'
              cases hc'
              simp [List.unzip_snd, hout, h2]
            refine ⟨⟨rfl, hc₁, hg₁, fun T hT => ?_, fun p hp => ?_⟩, ?_⟩
            · have hTn : n ≠ T := hT (n, j) (by simp)
              rw [Std.HashMap.getElem?_insert, ite_eq_right_of_eq_false _ _ (by simpa using hTn)]
              exact hold T fun p hp => hT p (by simp [hp])
            · rcases List.mem_append.1 hp with hp | hp
              · have hpn := hne p hp
                obtain ⟨ivn, masks, h1, h2, h3⟩ := hnew p hp
                refine ⟨ivn, masks, h1, ?_, h3⟩
                rw [Std.HashMap.getElem?_insert, ite_eq_right_of_eq_false _ _ (by simpa using Ne.symm hpn)]
                exact h2
              · simp only [List.mem_singleton] at hp
                subst hp
                exact ⟨inf, _, hinf', Std.HashMap.getElem?_insert_self, hmask⟩
            · refine ⟨inf, hinf', by simp [hlen], fun k cn hk => ?_, hb'⟩
              obtain ⟨cv, out, hc, hout, h1, -⟩ := hcv k cn hk
              exact ⟨cv, out.1, hc, by simp [List.unzip_fst, hout], h1⟩
          split
          · exact HT.bind (HT.getOrFail _ _) fun _ => HT.bind HT.pure_eq fun projs =>
              HT.mono (tail projs) (fun _ h => h.1.1) fun _ _ h => h
          · exact HT.bind HT.pure_eq fun projs => HT.mono (tail projs) (fun _ h => h.1) fun _ _ h => h
      · exact HT.throwM _
    · refine HT.bind (HT.modify _) fun _ => HT.bind HT.get fun s₂ => ?_
      refine HT.mono (HT.getOrFail _ _) (fun _ h => h) fun r s₃ ⟨⟨h₃, h₄⟩, h₅⟩ => ?_
      obtain ⟨s₀, ⟨rfl, hreg, hF⟩, rfl⟩ := h₃
      subst h₄
      refine .inr ⟨?_, s₀, bodies, hreg, hF, h₅, rfl⟩
      cases h : s.inductives[iv.name]? with
      | none => rfl
      | some iid => exact (hnone iid (by rwa [Std.HashMap.get?_eq_getElem?])).elim

end

/-- The λ□ inductive of a type at position `j` of its block. -/
theorem indIdOf_member {σ : EvalEnv} {T : Name} {ivT : InductiveVal} {j : Nat}
    (hT : findDecl σ.decls T = some (.inductInfo ivT)) (hnd : ivT.all.Nodup)
    (hj : ivT.all[j]? = some T) : IndIdOf σ T = some ⟨blockKername ivT, j⟩ := by
  unfold IndIdOf
  rw [hT]
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hj
  have : ivT.all.idxOf? T = some j := List.idxOf?_eq_some_iff.mpr ⟨hlt, hget, fun i hi h =>
    List.pairwise_iff_getElem.1 hnd i j (by omega) hlt hi (h.trans hget.symm)⟩
  simp [this]

/-- The newest block of a λ□ environment, at its kername. -/
theorem lookupInd_cons_self {bk : Kername} {mib : MutualInductiveBody} {l : GlobalDeclarations}
    {j : Nat} : lookupInd ((bk, .inductiveDecl mib) :: l) ⟨bk, j⟩ = (mib.bodies[j]?).map (mib, ·) := by
  simp [lookupInd, List.find?, kername_beq_self]


end RegisterInd

open RegisterInd StateLemmas Restrict in
/-- `register_inductive` at the pure backend keeps the state invariant: on a registered type it
returns the registered λ□ inductive and masks; otherwise it registers the type's whole block, each
type at its position with masks that keep every field, and conses one λ□ block whose bodies erase
the block's types (`ErasesInd`: parameters, constructors with their field counts, and the
propositional flag, which is `EvalEnv.propInd` by `isPropFormerType_iff`), under a fresh block
name. The constants are not touched. The premises: the type's declaration in the closure,
constructor fields kept, the facts the fragment test checks (`PhaseIDecl`: no `@[extern]`
constructor under `preferAxiom`, the inductives' sorts; `BlockNamesInj`), and the block's shape
(its names are distinct and contain the type; every member of the closure lists the same block and
parameter count), which con-leche's frontend and `DeclsOf?` check of an accepted program
(`blockShapeOK`). Port of `ML-V Core/RegisterInd.lean:755` with the block's shape as premises in
place of Metalean's environment. Reference: `erase_mutual_inductive_body`
(`MR E/ErasureFunction.v:1325`), the `InductiveDecl` step of `erase_global_deps`
(`MR E/ErasureFunction.v:1602`). -/
theorem register_inductive_ok {cert : BoxCert} {σ : EvalEnv} {st st' : ErasureState}
    {tc : TravCtx} {pc : PureCtx} {ps ps' : PureState} {iv : InductiveVal}
    {r : InductiveId × InductiveArgMasks}
    (hok : StateOK cert σ st) (hdecls : pc.decls = σ.decls)
    (hirr : tc.config.remove_irrel_constr_args = false)
    (hph : ∀ ci ∈ σ.decls, PhaseIDecl pc.view tc.config σ.decls ci)
    (hbn : BlockNamesInj σ.decls)
    (hiv : findDecl σ.decls iv.name = some (.inductInfo iv))
    (hnd : iv.all.Nodup) (hmem : iv.name ∈ iv.all)
    (hcoσ : ∀ n ∈ iv.all, ∀ ivn, findDecl σ.decls n = some (.inductInfo ivn) →
      ivn.all = iv.all ∧ ivn.numParams = iv.numParams)
    (h : (register_inductive (m := PureM) iv).runPure st tc pc ps = .ok ((r, st'), ps')) :
    StateOK cert σ st' ∧ LenvExt st.gdecls st'.gdecls ∧ st'.constants = st.constants ∧
      IndIdOf σ iv.name = some r.1 ∧ KeepMasks σ iv r.2 := by
  have hext : ∀ cn cv, findDecl σ.decls cn = some (.ctorInfo cv) →
      tc.config.1 = .preferAxiom → pc.view.isExtern cn = false := by
    intro cn cv hc hx
    obtain ⟨hm, hn⟩ := findDecl_eq_some hc
    have := (hph _ hm).2 hx
    rwa [show cv.name = cn from hn] at this
  rcases register_inductive_run hdecls hirr hext hnd st st ps r st' ps' rfl h with
    ⟨hr, rfl⟩ | ⟨hnone, s₁, bodies, ⟨hc₁, hg₁, hold, hnew⟩, hF, hr, rfl⟩
  · -- the type is registered
    obtain ⟨h1, -, ivT, hT, hk⟩ := hok.inductives iv.name r hr
    rw [hiv] at hT
    cases hT
    exact ⟨hok, ⟨[], rfl, by simp⟩, rfl, h1, hk⟩
  · -- the block is registered
    have hbk : blockKername iv = mutualBlockKername iv.all := rfl
    generalize mutualBlockKername iv.all = bk at hbk hnew hr ⊢
    generalize hmib : ({ npars := iv.numParams, bodies } : MutualInductiveBody) = mib
    have hpos : ∀ n ∈ iv.all, ∃ j, iv.all[j]? = some n := fun n hn => List.mem_iff_getElem?.mp hn
    have hfst : ∀ p ∈ iv.all.zipIdx, p.1 ∈ iv.all := fun p hp => by
      rw [← List.zipIdx_map_fst 0 iv.all]
      exact List.mem_map_of_mem hp
    -- what the run registered for the type at position `j`
    have hmemb : ∀ j n, iv.all[j]? = some n → ∃ ivn masks ob,
        findDecl σ.decls n = some (.inductInfo ivn) ∧ s₁.inductives[n]? = some (⟨bk, j⟩, masks) ∧
        KeepMasks σ ivn masks ∧ bodies[j]? = some ob ∧ BodyOK σ (n, j) ob := by
      intro j n hj
      have hz : iv.all.zipIdx[j]? = some (n, j) := by simp [hj]
      obtain ⟨ivn, masks, hf, hs, hk⟩ := hnew (n, j) (List.mem_of_getElem? hz)
      obtain ⟨ob, hob, hbody⟩ := forall₂_get hF hz
      exact ⟨ivn, masks, ob, hf, hs, hk, hob, hbody⟩
    -- no type of the block was registered before
    have hfree : ∀ n ∈ iv.all, st.inductives[n]? = none := by
      intro n hn
      cases hs : st.inductives[n]? with
      | none => rfl
      | some r' =>
        obtain ⟨-, -, ivn, hf, -⟩ := hok.inductives n r' hs
        obtain ⟨r'', h''⟩ := hok.whole n r' hs ivn hf iv.name ((hcoσ n hn ivn hf).1 ▸ hmem)
        rw [hnone] at h''
        cases h''
    have hold' : ∀ T, T ∉ iv.all → s₁.inductives[T]? = st.inductives[T]? :=
      fun T hT => hold T fun p hp heq => hT (heq ▸ hfst p hp)
    -- the block name is fresh
    have hfresh : st.gdecls.find? (·.1 == bk) = none := by
      rw [List.find?_eq_none]
      intro d hd hdk
      have hdk' := kername_eq_of_beq hdk
      have hivm : ∃ ci ∈ σ.decls, ci = .inductInfo iv := ⟨_, (findDecl_eq_some hiv).1, rfl⟩
      rcases hok.entries d hd with ⟨c, hc⟩ | ⟨T, r', hT, hname⟩
      · obtain ⟨hk, -, -, -, hnb, -⟩ := hok.registered c d.1 hc
        exact hnb iv hivm (by rw [← hk, hdk', ← hbk])
      · obtain ⟨hid, -, ivT, hT', -⟩ := hok.inductives T r' hT
        unfold IndIdOf at hid
        rw [hT'] at hid
        obtain ⟨j, hj, hj'⟩ := Option.map_eq_some_iff.1 hid
        have hb : blockKername ivT = blockKername iv := by
          rw [hbk, ← hdk', ← hname, ← hj']
        have hall := (hbn ivT iv ⟨_, (findDecl_eq_some hT').1, rfl⟩ hivm).1 hb
        have hTm : T ∈ iv.all := hall ▸ List.isSome_idxOf?.mp (by rw [hj]; rfl)
        rw [hfree T hTm] at hT
        cases hT
    have hx : LenvExt st.gdecls ((bk, .inductiveDecl mib) :: st.gdecls) :=
      ⟨[(bk, .inductiveDecl mib)], rfl, by simpa using hfresh⟩
    -- the new block erases every type of the block
    have herase : ∀ n ∈ iv.all, ErasesInd σ ((bk, .inductiveDecl mib) :: st.gdecls) n := by
      intro n hn
      obtain ⟨j, hj⟩ := hpos n hn
      obtain ⟨ivn, -, -, hf, -⟩ := hmemb j n hj
      obtain ⟨hall, hpar⟩ := hcoσ n hn ivn hf
      refine ⟨ivn, hf, fun j' n' hj' => ?_⟩
      rw [hall] at hj'
      obtain ⟨ivn', -, ob, hf', -, -, hob, ivb, hfb, hlen, hctors, hprop⟩ := hmemb j' n' hj'
      rw [hf'] at hfb
      cases hfb
      refine ⟨ivn', mib, ob, hf', ?_, by rw [← hmib, hpar], hlen, hctors,
        isPropFormerType_iff hf' (hph _ (findDecl_eq_some hf').1) hprop⟩
      have hb : blockKername ivn = bk := by
        show mutualBlockKername ivn.all = bk
        rw [hall]
        exact hbk
      rw [hb, lookupInd_cons_self, ← hmib]
      simp [hob]
    obtain ⟨j₀, hj₀⟩ := hpos iv.name hmem
    obtain ⟨iv₀, masks₀, -, hf₀, hs₀, hk₀, -⟩ := hmemb j₀ iv.name hj₀
    rw [hiv] at hf₀
    cases hf₀
    rw [hs₀] at hr
    cases hr
    have hx' : LenvExt st.gdecls ((bk, .inductiveDecl mib) :: s₁.gdecls) := by rw [hg₁]; exact hx
    refine ⟨⟨fun c kn hc => ?_, fun T r' hT => ?_, fun d hd => ?_, fun T r' hT ivT hfT n hn => ?_,
      fun kn cb b hl hb => ?_⟩, hx', hc₁, ?_, hk₀⟩
    · rw [show s₁.constants = st.constants from hc₁] at hc
      obtain ⟨hk, ci, cb, hf, hem, hl, hd, hb⟩ := hok.registered c kn hc
      exact ⟨hk, ci, cb, hf, hem, lookupConst_ext hx' hl, hd, fun b h => (hb b h).ext hx'⟩
    · by_cases hTm : T ∈ iv.all
      · obtain ⟨j, hj⟩ := hpos T hTm
        obtain ⟨ivn, masks, -, hf, hs, hk, -⟩ := hmemb j T hj
        change s₁.inductives[T]? = some r' at hT
        rw [hs] at hT
        cases hT
        obtain ⟨hall, -⟩ := hcoσ T hTm ivn hf
        refine ⟨?_, by rw [hg₁]; exact herase T hTm, ivn, hf, hk⟩
        have hb : blockKername ivn = bk := by
          show mutualBlockKername ivn.all = bk
          rw [hall]
          exact hbk
        rw [indIdOf_member hf (hall ▸ hnd) (hall ▸ hj), hb]
      · change s₁.inductives[T]? = some r' at hT
        rw [hold' T hTm] at hT
        obtain ⟨h1, h2, h3⟩ := hok.inductives T r' hT
        exact ⟨h1, ErasesInd.ext hx' h2, h3⟩
    · rcases List.mem_cons.1 hd with rfl | hd
      · exact .inr ⟨iv.name, _, hs₀, rfl⟩
      · rw [hg₁] at hd
        rcases hok.entries d hd with ⟨c, hc⟩ | ⟨T, r', hT, hn⟩
        · exact .inl ⟨c, by rw [show s₁.constants = st.constants from hc₁]; exact hc⟩
        · have hTm : T ∉ iv.all := fun hTm => by rw [hfree T hTm] at hT; cases hT
          exact .inr ⟨T, r', by rw [← hold' T hTm] at hT; exact hT, hn⟩
    · have hsome : ∀ m : Name, (∃ r'' : InductiveId × InductiveArgMasks, st.inductives[m]? = some r'') →
          ∃ r'' : InductiveId × InductiveArgMasks, s₁.inductives[m]? = some r'' := by
        intro m ⟨r'', hm⟩
        by_cases hmm : m ∈ iv.all
        · obtain ⟨j, hj⟩ := hpos m hmm
          obtain ⟨_, masks, -, -, hs, -⟩ := hmemb j m hj
          exact ⟨_, hs⟩
        · exact ⟨r'', by rw [hold' m hmm]; exact hm⟩
      change s₁.inductives[T]? = some r' at hT
      by_cases hTm : T ∈ iv.all
      · obtain ⟨hall, -⟩ := hcoσ T hTm ivT hfT
        rw [hall] at hn
        obtain ⟨j, hj⟩ := hpos n hn
        obtain ⟨_, masks, -, -, hs, -⟩ := hmemb j n hj
        exact ⟨_, hs⟩
      · rw [hold' T hTm] at hT
        exact hsome n (hok.whole T r' hT ivT hfT n hn)
    · rcases lookupConst_cons hl with ⟨-, hcd⟩ | ⟨-, hl'⟩
      · cases hcd
      · rw [hg₁] at hl'
        exact hok.closed kn cb b hl' hb
    · rw [indIdOf_member hiv hnd hj₀, hbk]

end EraseProof
