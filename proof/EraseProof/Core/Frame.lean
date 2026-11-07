import EraseProof.Oracle.Agree

/-!
# The traversal's frame lemma

The traversal `Erasure.visitExpr` and the functions it calls (`LeanToLambdaBox/Erasure.lean`), run
at the pure backend `Erasure.PureM`, give the same result under two lists of locals that agree on a
set `S` of free variables containing the visited term's and closed under the first list's types and
values (`LocalsSupport`, `LocalsAgree`): `visit_agree`. Both runs start from the same traversal
state and the same counter of fresh variables, so a binder pushes the same fresh local on both
sides and `S` grows by its variable.

The traversal reads the locals through the oracle (`Pure.isErasable`, `Pure.inferType`,
`Pure.whnf`, `Pure.typeLevel`; their frame lemmas are in `Oracle/Agree.lean`) and through the binder
names of `mkLambda`, `mkLetIn` and `mkAlt`. Everything else it visits has its free variables in `S`,
under the premises of `visit_agree`:
* the declarations' read expressions are closed (`ClosedDecls`), and `visitMutual` erases only
  such a value: a constant whose spine the oracle did not box is not a theorem, a constant that
  `visitConstApp` passes to `visitConst` is not a recognized `casesOn`, and the other members of a
  declaration's block have no value (`OwnBlockValues`);
* under `nat := .machine` the visited terms mention neither `Nat.succ` nor `Int.casesOn`
  (`MachineFree`): `visitConstructor` erases `Nat.succ` as `Nat.add`, whose value it erases
  without asking the oracle;
* the constructors of the inductive of a recognized `casesOn` have no index field
  (`NoIndexFields`), so `visitCases` substitutes no index into an alternative, and the recognizer
  gives no catch-all, so the discriminant is never let-bound: both substitutions use
  `Expr.replace`, whose results the logic does not know.

Reference: none; MetaRocq erases a constant body in the empty context
(`MR E/ErasureFunction.v:1309 erase_constant_body`), where this traversal keeps the caller's locals
(DV-13). Port of `L4 Core/FrameA.lean` and `L4 Core/Frame.lean`, extended to the functions of the
traversal that lean4lean's fragment did not reach.
-/

open Lean Erasure

namespace EraseProof

/-- Under `nat := .machine`, `e` mentions neither `Nat.succ` nor `Int.casesOn`, which
`Erasure.exprConsts` excludes under that configuration. -/
def MachineFree (cfg : ErasureConfig) : Expr → Prop
  | .const c _ => cfg.nat = .machine → c ≠ ``Nat.succ ∧ c ≠ ``Int.casesOn
  | .app f a => MachineFree cfg f ∧ MachineFree cfg a
  | .lam _ t b _ | .forallE _ t b _ => MachineFree cfg t ∧ MachineFree cfg b
  | .letE _ t v b _ => MachineFree cfg t ∧ MachineFree cfg v ∧ MachineFree cfg b
  | .mdata _ e | .proj _ _ e => MachineFree cfg e
  | _ => True

/-- The only member of a declaration's block with a value is the declaration itself, as in a
program related to a Metalean environment (definitions, theorems and opaques are alone in their
blocks; the blocks of inductive types and recursors list inductive types). -/
def OwnBlockValues (decls : List ConstantInfo) : Prop :=
  ∀ ci ∈ decls, ∀ n ∈ ci.all, n = ci.name ∨
    ∀ ci', findConst decls n = some ci' → ci'.value? (allowOpaque := true) = none

/-- The constructors of the inductive of a recognized `casesOn` have no field that is an index of
the constructor's type (`Erasure.indexFields`, with the inductive's parameter count as
`visitCases` computes it), as the fragment test checks. -/
def NoIndexFields (decls : List ConstantInfo) : Prop :=
  ∀ n ci iv, casesInfo? decls n = some ci → findConst decls ci.indName = some (.inductInfo iv) →
    ∀ cn ∈ iv.ctors, ∀ cv, findConst decls cn = some (.ctorInfo cv) →
      (indexFields iv.numParams cv.type).all (·.isNone) = true

namespace TravFrame

variable {α β : Type} {pc : PureCtx} {cfg : ErasureConfig} {S : FVarId → Prop}

/-! ## Runs that agree -/

/-- The runs of `x` under two lists of locals that agree on `S` are equal, under any reader
context of configuration `cfg`, and every result of the first satisfies `P`. -/
def RA (pc : PureCtx) (cfg : ErasureConfig) (S : FVarId → Prop) (P : α → Prop)
    (x : EraseT PureM α) : Prop :=
  ∀ (st : ErasureState) (ps : PureState) (tc : TravCtx) (ls₁ ls₂ : List Local),
    tc.config = cfg → LocalsSupport S ls₁ → LocalsAgree S ls₁ ls₂ →
    x.runPure st { tc with locals := ls₁ } pc ps = x.runPure st { tc with locals := ls₂ } pc ps ∧
    ∀ a st' ps', x.runPure st { tc with locals := ls₁ } pc ps = .ok ((a, st'), ps') → P a

/-- An action that runs alike under any locals. -/
def Blind (pc : PureCtx) (x : EraseT PureM α) : Prop :=
  ∀ (st : ErasureState) (ps : PureState) (tc : TravCtx) (ls₁ ls₂ : List Local),
    x.runPure st { tc with locals := ls₁ } pc ps = x.runPure st { tc with locals := ls₂ } pc ps

theorem runPure_bind {st : ErasureState} {ps : PureState} {tc : TravCtx} (x : EraseT PureM α)
    (k : α → EraseT PureM β) :
    (x >>= k).runPure st tc pc ps =
      x.runPure st tc pc ps >>= fun r => (k r.1.1).runPure r.1.2 tc pc r.2 := rfl

theorem runPure_read_bind {st : ErasureState} {ps : PureState} {tc : TravCtx}
    (k : TravCtx → EraseT PureM α) :
    (read >>= k).runPure st tc pc ps = (k tc).runPure st tc pc ps := rfl

theorem runPure_liftM {st : ErasureState} {ps : PureState} {tc : TravCtx} (x : PureM α) :
    (_root_.liftM x : EraseT PureM α).runPure st tc pc ps =
      ((x.run pc).run ps >>= fun r => .ok ((r.1, st), r.2)) := rfl

theorem RA.mono {P Q : α → Prop} {x : EraseT PureM α} (h : RA pc cfg S P x)
    (hPQ : ∀ a, P a → Q a) : RA pc cfg S Q x := fun st ps tc ls₁ ls₂ hc hS hag =>
  ⟨(h st ps tc ls₁ ls₂ hc hS hag).1,
    fun a st' ps' ha => hPQ a ((h st ps tc ls₁ ls₂ hc hS hag).2 a st' ps' ha)⟩

theorem RA.of_blind {x : EraseT PureM α} (h : Blind pc x) : RA pc cfg S (fun _ => True) x :=
  fun st ps tc ls₁ ls₂ _ _ _ => ⟨h st ps tc ls₁ ls₂, fun _ _ _ _ => trivial⟩

theorem RA.pure {P : α → Prop} {a : α} (h : P a) : RA pc cfg S P (Pure.pure a) :=
  fun _ _ _ _ _ _ _ _ => ⟨rfl, fun _ _ _ e => by cases e; exact h⟩

theorem RA.bind {P : α → Prop} {Q : β → Prop} {x : EraseT PureM α} {k : α → EraseT PureM β}
    (hx : RA pc cfg S P x) (hk : ∀ a, P a → RA pc cfg S Q (k a)) :
    RA pc cfg S Q (x >>= k) := by
  intro st ps tc ls₁ ls₂ hc hS hag
  obtain ⟨e, hP⟩ := hx st ps tc ls₁ ls₂ hc hS hag
  rw [runPure_bind, runPure_bind, ← e]
  rcases h : x.runPure st { tc with locals := ls₁ } pc ps with _ | ⟨⟨a, st'⟩, ps'⟩
  · exact ⟨rfl, fun _ _ _ h' => nomatch h'⟩
  · exact hk a (hP a st' ps' h) st' ps' tc ls₁ ls₂ hc hS hag

theorem RA.bind' {Q : β → Prop} {x : EraseT PureM α} {k : α → EraseT PureM β}
    (hx : Blind pc x) (hk : ∀ a, RA pc cfg S Q (k a)) : RA pc cfg S Q (x >>= k) :=
  RA.bind (RA.of_blind hx) fun a _ => hk a

theorem RA.read_bind {P : α → Prop} {k : TravCtx → EraseT PureM α}
    (hk : ∀ c, c.config = cfg → RA pc cfg S P (k c))
    (hk' : ∀ (tc : TravCtx) (ls₁ ls₂ : List Local),
      k { tc with locals := ls₁ } = k { tc with locals := ls₂ }) :
    RA pc cfg S P (read >>= k) := by
  intro st ps tc ls₁ ls₂ hc hS hag
  have e : ∀ c, (read >>= k).runPure st c pc ps = (k c).runPure st c pc ps := fun _ => rfl
  rw [e, e, ← hk' tc ls₁ ls₂]
  exact hk { tc with locals := ls₁ } hc st ps tc ls₁ ls₂ hc hS hag

theorem RA.ite {P : α → Prop} {c : Prop} [Decidable c] {a b : EraseT PureM α}
    (ha : c → RA pc cfg S P a) (hb : ¬c → RA pc cfg S P b) : RA pc cfg S P (if c then a else b) := by
  split
  · exact ha ‹c›
  · exact hb ‹¬c›

theorem Blind.get : Blind pc (MonadState.get : EraseT PureM ErasureState) := fun _ _ _ _ _ => rfl

theorem Blind.modify (f : ErasureState → ErasureState) :
    Blind pc (_root_.modify f : EraseT PureM PUnit) := fun _ _ _ _ _ => rfl

theorem Blind.liftM (y : PureM α) : Blind pc (_root_.liftM y : EraseT PureM α) :=
  fun _ _ _ _ _ => rfl

/-- `List.forIn` with an invariant `I` of the accumulator. -/
theorem RA.forIn {I : β → Prop} {f : α → β → EraseT PureM (ForInStep β)} :
    ∀ {l : List α} {b : β}, I b →
      (∀ a ∈ l, ∀ b, I b → RA pc cfg S (fun r => I r.value) (f a b)) →
      RA pc cfg S I (forIn l b f)
  | [], b, hb, _ => by rw [List.forIn_nil]; exact RA.pure hb
  | a :: l, b, hb, h => by
    rw [List.forIn_cons]
    refine RA.bind (h a (.head _) b hb) fun r hr => ?_
    cases r with
    | done b' => exact RA.pure hr
    | yield b' => exact RA.forIn hr fun c hc => h c (.tail _ hc)

/-- `List.mapM` with a property of every result. -/
theorem RA.mapM {P : β → Prop} {f : α → EraseT PureM β} :
    ∀ {l : List α}, (∀ a ∈ l, RA pc cfg S P (f a)) → RA pc cfg S (fun r => ∀ b ∈ r, P b) (l.mapM f)
  | [], _ => by rw [List.mapM_nil]; exact RA.pure fun _ h => nomatch h
  | a :: l, h => by
    rw [List.mapM_cons]
    refine RA.bind (h a (.head _)) fun b hb => RA.bind (RA.mapM fun c hc => h c (.tail _ hc))
      fun r hr => RA.pure ?_
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    exacts [hb, hr x hx]

/-! ## Binders -/

theorem fvarsIn_mono {p q : FVarId → Prop} (hpq : ∀ y, p y → q y) :
    ∀ {e : Expr}, FVarsIn p e → FVarsIn q e
  | .fvar _, h => hpq _ h
  | .app f a, h => ⟨fvarsIn_mono hpq (e := f) h.1, fvarsIn_mono hpq (e := a) h.2⟩
  | .lam _ t b _, h | .forallE _ t b _, h =>
    ⟨fvarsIn_mono hpq (e := t) h.1, fvarsIn_mono hpq (e := b) h.2⟩
  | .letE _ t v b _, h => ⟨fvarsIn_mono hpq (e := t) h.1, fvarsIn_mono hpq (e := v) h.2.1,
    fvarsIn_mono hpq (e := b) h.2.2⟩
  | .mdata _ e, h | .proj _ _ e, h => fvarsIn_mono hpq (e := e) h
  | .bvar _, _ | .sort _, _ | .const .., _ | .lit _, _ | .mvar _, _ => trivial

theorem findLocal_cons_self (l : Local) (ls : List Local) :
    Pure.findLocal (l :: ls) l.fvarId = some l := by
  simp [Pure.findLocal, (fvarId_beq_iff _ _).2 rfl]

theorem findLocal_cons_ne {l : Local} {ls : List Local} {y : FVarId} (h : l.fvarId ≠ y) :
    Pure.findLocal (l :: ls) y = Pure.findLocal ls y := by
  have hne : (l.fvarId == y) = false := Bool.eq_false_iff.2 fun h' => h ((fvarId_beq_iff _ _).1 h')
  simp only [Pure.findLocal, List.find?_cons, hne]

theorem LocalsSupport.push {ls : List Local} {l : Local} (hS : LocalsSupport S ls)
    (hty : FVarsIn S l.type) (hval : ∀ v, l.value? = some v → FVarsIn S v) :
    LocalsSupport (fun y => S y ∨ y = l.fvarId) (l :: ls) := by
  have mono : ∀ {e}, FVarsIn S e → FVarsIn (fun y => S y ∨ y = l.fvarId) e :=
    fvarsIn_mono fun _ h => .inl h
  intro y hy l' hl'
  by_cases h : l.fvarId = y
  · subst h
    rw [findLocal_cons_self, Option.some.injEq] at hl'
    subst hl'
    exact ⟨mono hty, fun v hv => mono (hval v hv)⟩
  · rw [findLocal_cons_ne h] at hl'
    have ⟨h1, h2⟩ := hS y (hy.resolve_right (Ne.symm h)) l' hl'
    exact ⟨mono h1, fun v hv => mono (h2 v hv)⟩

theorem LocalsAgree.push {ls₁ ls₂ : List Local} {l : Local} (hag : LocalsAgree S ls₁ ls₂) :
    LocalsAgree (fun y => S y ∨ y = l.fvarId) (l :: ls₁) (l :: ls₂) := by
  intro y hy
  by_cases h : l.fvarId = y
  · subst h; rw [findLocal_cons_self, findLocal_cons_self]
  · rw [findLocal_cons_ne h, findLocal_cons_ne h]
    exact hag y (hy.resolve_right (Ne.symm h))

/-- Pushing a local whose type and value have their free variables in `S`. -/
theorem RA.push {P : α → Prop} {x : FVarId} {n : Name} {ty : Expr} {val : Option Expr}
    {f : LocalContext → LocalContext} {y : EraseT PureM α} (hty : FVarsIn S ty)
    (hval : ∀ v, val = some v → FVarsIn S v)
    (hy : RA pc cfg (fun z => S z ∨ z = x) P y) :
    RA pc cfg S P (withReader
      (fun ctx => { ctx with lctx := f ctx.lctx, locals := ⟨x, n, ty, val⟩ :: ctx.locals }) y) := by
  intro st ps tc ls₁ ls₂ hc hS hag
  exact hy st ps { tc with lctx := f tc.lctx } (⟨x, n, ty, val⟩ :: ls₁) (⟨x, n, ty, val⟩ :: ls₂) hc
    (TravFrame.LocalsSupport.push (l := ⟨x, n, ty, val⟩) hS hty hval)
    (TravFrame.LocalsAgree.push (l := ⟨x, n, ty, val⟩) hag)

theorem RA.withLocalDecl {P : α → Prop} {n : Name} {ty : Expr} {bi : BinderInfo}
    {k : FVarId → EraseT PureM α} (hty : FVarsIn S ty)
    (hk : ∀ x, RA pc cfg (fun z => S z ∨ z = x) P (k x)) :
    RA pc cfg S P (withLocalDecl (m := PureM) n ty bi k) := by
  unfold Erasure.withLocalDecl
  exact RA.bind' (Blind.liftM _) fun x =>
    RA.push (n := n) (val := none) (f := fun l => l.mkLocalDecl x n ty bi) hty
      (fun _ h => by cases h) (hk x)

theorem RA.withLocalDef {P : α → Prop} {n : Name} {ty v : Expr} {nd : Bool}
    {k : FVarId → EraseT PureM α} (hty : FVarsIn S ty) (hv : FVarsIn S v)
    (hk : ∀ x, RA pc cfg (fun z => S z ∨ z = x) P (k x)) :
    RA pc cfg S P (withLocalDef (m := PureM) n ty v nd k) := by
  unfold Erasure.withLocalDef
  exact RA.bind' (Blind.liftM _) fun x =>
    RA.push (n := n) (val := some v) (f := fun l => l.mkLetDecl x n ty v nd) hty
      (fun _ h => by cases h; exact hv) (hk x)

theorem RA.fvar_to_name {x : FVarId} (hx : S x) :
    RA pc cfg S (fun _ => True) (fvar_to_name (m := PureM) x) := by
  intro st ps tc ls₁ ls₂ _ _ hag
  refine ⟨?_, fun _ _ _ _ => trivial⟩
  have h : List.find? (fun l => l.fvarId == x) ls₁ = List.find? (fun l => l.fvarId == x) ls₂ :=
    hag x hx
  have e : ∀ c : TravCtx, (Erasure.fvar_to_name (m := PureM) x).runPure st c pc ps =
      ((getOrFail (List.find? (fun l => l.fvarId == x) c.locals) "fvar_to_name: unknown local" >>=
        fun l => Pure.pure (binderNameOf l.userName)) : EraseT PureM BinderName).runPure st c pc ps :=
    fun _ => rfl
  rw [e, e]
  dsimp only
  rw [h]
  cases List.find? (fun l => l.fvarId == x) ls₂ <;> rfl

/-! ## Actions that throw or do not read the locals -/

theorem RA.throwM {P : α → Prop} (err : EraseError) :
    RA pc cfg S P (_root_.liftM (throw err : PureM α) : EraseT PureM α) :=
  fun _ _ _ _ _ _ _ _ => ⟨rfl, fun _ _ _ h => nomatch h⟩

theorem RA.getOrFail {γ : Type} [Inhabited γ] (o : Option γ) (msg : String) :
    RA pc cfg S (fun a => o = some a) (getOrFail (m := PureM) o msg) := by
  cases o with
  | some a => exact RA.pure rfl
  | none => exact RA.throwM _

theorem RA.getConst (n : Name) :
    RA pc cfg S (fun ci => findConst pc.decls n = some ci) (getConst (m := PureM) n) := by
  unfold Erasure.getConst
  refine RA.bind (P := fun r => r = findConst pc.decls n) (fun st ps tc ls₁ ls₂ _ _ _ =>
    ⟨rfl, fun a st' ps' h => by cases h; rfl⟩) fun r hr => ?_
  subst hr
  split
  · rename_i ci h; exact RA.pure h
  · exact RA.throwM _

theorem Blind.bind {x : EraseT PureM α} {k : α → EraseT PureM β} (hx : Blind pc x)
    (hk : ∀ a, Blind pc (k a)) : Blind pc (x >>= k) := by
  intro st ps tc ls₁ ls₂
  rw [runPure_bind, runPure_bind, hx st ps tc ls₁ ls₂]
  congr 1
  funext r
  exact hk r.1.1 r.1.2 r.2 tc ls₁ ls₂

theorem Blind.addAxiom (n : Name) : Blind pc (addAxiom (m := PureM) n) := by
  unfold Erasure.addAxiom
  refine Blind.bind Blind.get fun s => ?_
  dsimp only
  split
  · exact Blind.bind (Blind.liftM _) fun _ => Blind.modify _
  · exact Blind.modify _

/-! ## The oracle's calls, which read the locals -/

/-- A call of the backend on the locals: `g` runs as `F` on the locals, and `F` answers alike on
two lists of locals that agree on `S`, with results in `Q`. -/
theorem RA.call {γ : Type} {Q : γ → Prop} {P : α → Prop} {g : LocalContext → List Local → PureM γ}
    {F : List Local → Except EraseError γ} {k : γ → EraseT PureM α}
    (hrun : ∀ lctx ls ps, ((g lctx ls).run pc).run ps = (F ls).map (·, ps))
    (hF : ∀ ls₁ ls₂, LocalsSupport S ls₁ → LocalsAgree S ls₁ ls₂ →
      F ls₁ = F ls₂ ∧ ∀ a, F ls₁ = .ok a → Q a)
    (hk : ∀ a, Q a → RA pc cfg S P (k a)) :
    RA pc cfg S P (read >>= fun c₁ => read >>= fun c₂ =>
      (_root_.liftM (g c₁.lctx c₂.locals) : EraseT PureM γ) >>= k) := by
  intro st ps tc ls₁ ls₂ hc hS hag
  have e : ∀ ls, (read >>= fun c₁ => read >>= fun c₂ =>
      (_root_.liftM (g c₁.lctx c₂.locals) : EraseT PureM γ) >>= k).runPure st
        { tc with locals := ls } pc ps =
      (match F ls with
        | .ok a => (k a).runPure st { tc with locals := ls } pc ps
        | .error err => .error err) := by
    intro ls
    rw [runPure_read_bind, runPure_read_bind, runPure_bind, runPure_liftM, hrun]
    dsimp only
    cases F ls <;> rfl
  obtain ⟨hF₁, hF₂⟩ := hF ls₁ ls₂ hS hag
  rw [e, e, ← hF₁]
  rcases hF' : F ls₁ with err | a
  · exact ⟨rfl, fun _ _ _ h => nomatch h⟩
  · exact hk a (hF₂ a hF') st ps tc ls₁ ls₂ hc hS hag

theorem inferType_run (lctx : LocalContext) (ls : List Local) (e : Expr) (ps : PureState) :
    ((Backend.inferType (m := PureM) lctx ls e).run pc).run ps =
      (Pure.inferType ⟨pc.decls⟩ oracleFuel ls [] e).map (·, ps) := by
  change (((match Pure.inferType ⟨pc.decls⟩ oracleFuel ls [] e with
    | .ok t => (Pure.pure t : PureM Expr) | .error err => throw err).run pc).run ps) = _
  cases Pure.inferType ⟨pc.decls⟩ oracleFuel ls [] e <;> rfl

theorem whnf_run (lctx : LocalContext) (ls : List Local) (e : Expr) (ps : PureState) :
    ((Backend.whnf (m := PureM) lctx ls e).run pc).run ps =
      (Pure.whnf ⟨pc.decls⟩ oracleFuel ls e).map (·, ps) := by
  change (((match Pure.whnf ⟨pc.decls⟩ oracleFuel ls e with
    | .ok t => (Pure.pure t : PureM Expr) | .error err => throw err).run pc).run ps) = _
  cases Pure.whnf ⟨pc.decls⟩ oracleFuel ls e <;> rfl

theorem typeLevel_run (lctx : LocalContext) (ls : List Local) (e : Expr) (ps : PureState) :
    ((Backend.typeLevel (m := PureM) lctx ls e).run pc).run ps =
      (Pure.typeLevel ⟨pc.decls⟩ oracleFuel ls e).map (·, ps) := by
  change (((match Pure.typeLevel ⟨pc.decls⟩ oracleFuel ls e with
    | .ok t => (Pure.pure t : PureM Level) | .error err => throw err).run pc).run ps) = _
  cases Pure.typeLevel ⟨pc.decls⟩ oracleFuel ls e <;> rfl

theorem isErasable_run (lctx : LocalContext) (ls : List Local) (e : Expr) (ps : PureState) :
    ((Backend.isErasable (m := PureM) lctx ls e).run pc).run ps =
      (Pure.isErasable ⟨pc.decls⟩ oracleFuel ls e).map (·, ps) := by
  change (((match Pure.isErasable ⟨pc.decls⟩ oracleFuel ls e with
    | .ok t => (Pure.pure t : PureM Bool) | .error err => throw err).run pc).run ps) = _
  cases Pure.isErasable ⟨pc.decls⟩ oracleFuel ls e <;> rfl

section
variable (hcl : ClosedDecls pc.decls)
include hcl

theorem RA.inferType {P : α → Prop} {e : Expr} {k : Expr → EraseT PureM α} (he : FVarsIn S e)
    (hk : ∀ T, FVarsIn S T → RA pc cfg S P (k T)) :
    RA pc cfg S P (read >>= fun c₁ => read >>= fun c₂ =>
      (_root_.liftM (Backend.inferType (m := PureM) c₁.lctx c₂.locals e) : EraseT PureM Expr) >>=
        k) :=
  RA.call (g := fun lctx ls => Backend.inferType (m := PureM) lctx ls e)
    (F := fun ls => Pure.inferType ⟨pc.decls⟩ oracleFuel ls [] e) (inferType_run (pc := pc) · · e)
    (fun _ _ hS hag => OracleAgree.inferType_agree (cx := ⟨pc.decls⟩) hcl hS hag oracleFuel [] e he (by simp)) hk

theorem RA.whnf {P : α → Prop} {e : Expr} {k : Expr → EraseT PureM α} (he : FVarsIn S e)
    (hk : ∀ w, (FVarsIn S w ∨ OracleAgree.RecTele pc.decls w) → RA pc cfg S P (k w)) :
    RA pc cfg S P (read >>= fun c₁ => read >>= fun c₂ =>
      (_root_.liftM (Backend.whnf (m := PureM) c₁.lctx c₂.locals e) : EraseT PureM Expr) >>= k) :=
  RA.call (g := fun lctx ls => Backend.whnf (m := PureM) lctx ls e)
    (F := fun ls => Pure.whnf ⟨pc.decls⟩ oracleFuel ls e) (whnf_run (pc := pc) · · e)
    (fun _ _ hS hag => OracleAgree.whnf_agree (cx := ⟨pc.decls⟩) hcl hS hag oracleFuel e he) hk

theorem typeLevel_agree {ls₁ ls₂ : List Local} {e : Expr} (hS : LocalsSupport S ls₁)
    (hag : LocalsAgree S ls₁ ls₂) (he : FVarsIn S e) (f : Nat) :
    Pure.typeLevel ⟨pc.decls⟩ f ls₁ e = Pure.typeLevel ⟨pc.decls⟩ f ls₂ e := by
  unfold Pure.typeLevel
  have ⟨iT, fT⟩ := OracleAgree.inferType_agree (cx := ⟨pc.decls⟩) hcl hS hag f [] e he (by simp)
  refine OracleAgree.bind_congr_ok iT fun T hT => ?_
  have ⟨iS, fS⟩ := OracleAgree.inferType_agree (cx := ⟨pc.decls⟩) hcl hS hag f [] T (fT T (iT ▸ hT)) (by simp)
  refine OracleAgree.bind_congr_ok iS fun U hU => ?_
  have ⟨iw, _⟩ := OracleAgree.whnf_agree (cx := ⟨pc.decls⟩) hcl hS hag f U (fS U (iS ▸ hU))
  exact OracleAgree.bind_congr_ok iw fun _ _ => rfl

theorem RA.typeLevel {P : α → Prop} {e : Expr} {k : Level → EraseT PureM α} (he : FVarsIn S e)
    (hk : ∀ u, RA pc cfg S P (k u)) :
    RA pc cfg S P (read >>= fun c₁ => read >>= fun c₂ =>
      (_root_.liftM (Backend.typeLevel (m := PureM) c₁.lctx c₂.locals e) : EraseT PureM Level) >>=
        k) :=
  RA.call (Q := fun _ => True) (g := fun lctx ls => Backend.typeLevel (m := PureM) lctx ls e)
    (F := fun ls => Pure.typeLevel ⟨pc.decls⟩ oracleFuel ls e)
    (typeLevel_run (pc := pc) · · e)
    (fun _ _ hS hag => ⟨typeLevel_agree hcl hS hag he oracleFuel, fun _ _ => trivial⟩) fun u _ => hk u

end

/-! ## Terms -/

theorem mf_lift : ∀ {e : Expr} {s d : Nat}, MachineFree cfg e →
    MachineFree cfg (e.liftLooseBVars' s d) := by
  intro e
  induction e <;> intro s d h <;> simp_all [Expr.liftLooseBVars', MachineFree]

theorem mf_inst {a : Expr} (ha : MachineFree cfg a) :
    ∀ {b : Expr} {d : Nat}, MachineFree cfg b → MachineFree cfg (b.instantiate1' a d) := by
  intro b
  induction b with
  | bvar i =>
    intro d _
    simp only [Expr.instantiate1']
    split_ifs
    · trivial
    · exact mf_lift ha
    · trivial
  | _ => intro d h; simp_all [Expr.instantiate1', MachineFree]

/-- The arguments of an application spine satisfy `Q`. -/
def SpineArgs (Q : Expr → Prop) : Expr → Prop
  | .app f a => SpineArgs Q f ∧ Q a
  | _ => True

theorem spineArgs_of {Q : Expr → Prop} (h : ∀ {f a : Expr}, Q (.app f a) → Q f ∧ Q a) :
    ∀ {e : Expr}, Q e → SpineArgs Q e
  | .app f _, he => ⟨spineArgs_of h (e := f) (h he).1, (h he).2⟩
  | .bvar _, _ | .fvar _, _ | .mvar _, _ | .sort _, _ | .const .., _ | .lam .., _ | .forallE .., _
  | .letE .., _ | .lit _, _ | .mdata .., _ | .proj .., _ => trivial

theorem getAppFn_of {Q : Expr → Prop} (h : ∀ {f a : Expr}, Q (.app f a) → Q f ∧ Q a) :
    ∀ {e : Expr}, Q e → Q e.getAppFn
  | .app f _, he => getAppFn_of h (e := f) (h he).1
  | .bvar _, he | .fvar _, he | .mvar _, he | .sort _, he | .const .., he | .lam .., he
  | .forallE .., he | .letE .., he | .lit _, he | .mdata .., he | .proj .., he => he

theorem withAppAux_eq {γ : Sort _} (k : Expr → Array Expr → γ) :
    ∀ (e : Expr) (as : Array Expr) (i : Nat),
      Expr.withAppAux k e as i = k e.getAppFn (Expr.withAppAux (fun _ as => as) e as i)
  | .app f a, as, i => by
    rw [Expr.withAppAux, Expr.withAppAux]
    exact withAppAux_eq k f _ _
  | .bvar _, _, _ | .fvar _, _, _ | .mvar _, _, _ | .sort _, _, _ | .const .., _, _
  | .lam .., _, _ | .forallE .., _, _ | .letE .., _, _ | .lit _, _, _ | .mdata .., _, _
  | .proj .., _, _ => rfl

theorem withAppAux_args {Q : Expr → Prop} :
    ∀ (e : Expr) (as : Array Expr) (i : Nat), SpineArgs Q e → (∀ a ∈ as, Q a) →
      ∀ a ∈ Expr.withAppAux (fun _ as => as) e as i, Q a
  | .app f a, as, i, h, has => by
    rw [Expr.withAppAux]
    refine withAppAux_args f (as.set! i a) (i - 1) h.1 fun b hb => ?_
    rcases Array.mem_or_eq_of_mem_setIfInBounds hb with hb | rfl
    exacts [has b hb, h.2]
  | .bvar _, _, _, _, has | .fvar _, _, _, _, has | .mvar _, _, _, _, has
  | .sort _, _, _, _, has | .const .., _, _, _, has | .lam .., _, _, _, has
  | .forallE .., _, _, _, has | .letE .., _, _, _, has | .lit _, _, _, _, has
  | .mdata .., _, _, _, has | .proj .., _, _, _, has => has

/-- `Expr.withApp` passes the head and the arguments `withApp (fun _ as => as)`. -/
theorem withApp_eq {γ : Sort _} (e : Expr) (k : Expr → Array Expr → γ) :
    e.withApp k = k e.getAppFn (e.withApp fun _ as => as) := by
  unfold Expr.withApp
  exact withAppAux_eq k e _ _

/-- The arguments `Expr.withApp` passes satisfy what the spine's arguments satisfy. -/
theorem withApp_args {Q : Expr → Prop} {e : Expr} (hQ : Q (mkSort .zero)) (he : SpineArgs Q e) :
    ∀ a ∈ e.withApp (fun _ as => as), Q a := by
  unfold Expr.withApp
  exact withAppAux_args e _ _ he fun a ha => by
    rw [Array.mem_replicate] at ha
    rw [ha.2]; exact hQ

/-- Free variables in `S` and no excluded constant. -/
def Good (S : FVarId → Prop) (cfg : ErasureConfig) (e : Expr) : Prop :=
  FVarsIn S e ∧ MachineFree cfg e

theorem Good.app {f a : Expr} (h : Good S cfg (.app f a)) : Good S cfg f ∧ Good S cfg a :=
  ⟨⟨h.1.1, h.2.1⟩, ⟨h.1.2, h.2.2⟩⟩

theorem Good.mono {S' : FVarId → Prop} {e : Expr} (hS : ∀ y, S y → S' y) (h : Good S cfg e) :
    Good S' cfg e := ⟨fvarsIn_mono hS h.1, h.2⟩

theorem Good.sort : Good S cfg (mkSort .zero) := ⟨trivial, trivial⟩

theorem Good.inst {x : FVarId} {b : Expr} {d : Nat} (hb : Good S cfg b) :
    Good (fun z => S z ∨ z = x) cfg (b.instantiate1' (.fvar x) d) :=
  ⟨OracleAgree.fvarsIn_inst (show FVarsIn (fun z => S z ∨ z = x) (.fvar x) from .inr rfl)
      (fvarsIn_mono (fun _ h => .inl h) hb.1), mf_inst (show MachineFree cfg (.fvar x) from trivial) hb.2⟩

/-- A theorem's spine is erasable for the oracle. -/
theorem isErasable_thm {cx : Pure.Ctx} {fuel : Nat} {ls : List Local} {e : Expr} {c : Name}
    {us : List Level} {v : TheoremVal} (h : e.getAppFn = .const c us)
    (hc : findConst cx.decls c = some (.thmInfo v)) : Pure.isErasable cx fuel ls e = .ok true := by
  have hs := (OracleAgree.spine_fst e).trans h
  unfold Pure.isErasable
  rcases hsp : spine e with ⟨hd, as⟩
  rw [hsp] at hs
  subst hs
  simp only [hc]
  rfl

/-- The head of `e` is not a theorem of `decls`. -/
def NoThmHead (decls : List ConstantInfo) (e : Expr) : Prop :=
  ∀ c us v, e.getAppFn = .const c us → findConst decls c ≠ some (.thmInfo v)

theorem isErasable_run' (e : Expr) :
    ∀ (lctx : LocalContext) (ls : List Local) (ps : PureState),
      ((Backend.isErasable (m := PureM) lctx ls e).run pc).run ps =
        (Pure.isErasable ⟨pc.decls⟩ oracleFuel ls e).map (·, ps) :=
  fun lctx ls ps => isErasable_run lctx ls e ps

/-- The oracle call that starts each unfolding of `visitExpr`: when it does not box, the head is
not a theorem. -/
theorem RA.oracle (hcl : ClosedDecls pc.decls) {e : Expr} {K : EraseT PureM LBTerm}
    (he : FVarsIn S e) (hK : NoThmHead pc.decls e → RA pc cfg S (fun _ => True) K) :
    RA pc cfg S (fun _ => True) (read >>= fun c₁ => read >>= fun c₂ =>
      (_root_.liftM (Backend.isErasable (m := PureM) c₁.lctx c₂.locals e) : EraseT PureM Bool) >>=
        fun b => if b = true then Pure.pure LBTerm.box else K) := by
  by_cases hn : NoThmHead pc.decls e
  · refine RA.call (Q := fun _ => True) (g := fun lctx ls => Backend.isErasable (m := PureM) lctx ls e)
      (F := fun ls => Pure.isErasable ⟨pc.decls⟩ oracleFuel ls e) (isErasable_run' e)
      (fun _ _ hS hag => ⟨Pure.isErasable_agree hcl hS hag he, fun _ _ => trivial⟩)
      fun b _ => RA.ite (fun _ => RA.pure trivial) fun _ => hK hn
  · simp only [NoThmHead, not_forall, not_not] at hn
    obtain ⟨c, us, v, hfn, hc⟩ := hn
    refine RA.call (Q := (· = true))
      (g := fun lctx ls => Backend.isErasable (m := PureM) lctx ls e)
      (F := fun ls => Pure.isErasable ⟨pc.decls⟩ oracleFuel ls e) (isErasable_run' e)
      (fun _ _ hS hag => ⟨Pure.isErasable_agree hcl hS hag he, fun a h => by
        rw [isErasable_thm hfn hc] at h; cases h; rfl⟩) fun b hb => ?_
    subst hb
    exact RA.pure trivial

/-! ## Binder helpers -/

theorem RA.mkLambda {x : FVarId} {body : LBTerm} (hx : S x) :
    RA pc cfg S (fun _ => True) (mkLambda (m := PureM) x body) := by
  unfold Erasure.mkLambda
  exact RA.bind (RA.fvar_to_name hx) fun _ _ => RA.pure trivial

theorem RA.mkLetIn {x : FVarId} {v body : LBTerm} (hx : S x) :
    RA pc cfg S (fun _ => True) (mkLetIn (m := PureM) x v body) := by
  unfold Erasure.mkLetIn
  exact RA.bind (RA.fvar_to_name hx) fun _ _ => RA.pure trivial

theorem RA.mkAlt {xs : List FVarId} {body : LBTerm} (hxs : ∀ x ∈ xs, S x) :
    RA pc cfg S (fun _ => True) (mkAlt (m := PureM) xs body) := by
  unfold Erasure.mkAlt
  refine RA.bind (RA.mapM fun x hx => RA.fvar_to_name (hxs x hx)) fun _ _ =>
    RA.bind (RA.forIn (I := fun _ => True) trivial fun a _ b _ => ?_) fun _ _ => RA.pure trivial
  obtain ⟨_, _⟩ := a
  exact RA.pure trivial

theorem RA.forallMonocular (hcl : ClosedDecls pc.decls) {P : α → Prop} {t : Expr}
    {k : FVarId → Expr → EraseT PureM α} (ht : FVarsIn S t)
    (hk : ∀ x b, FVarsIn (fun z => S z ∨ z = x) b → RA pc cfg (fun z => S z ∨ z = x) P (k x b)) :
    RA pc cfg S P (forallMonocular (m := PureM) t k) := by
  rw [Erasure.forallMonocular]
  split
  · refine RA.bind (RA.pure (P := fun w => w = t) rfl) fun w hw => ?_
    subst hw
    dsimp only
    split
    · exact RA.withLocalDecl ht.1 fun x => hk x _ (OracleAgree.fvarsIn_inst
        (show FVarsIn (fun z => S z ∨ z = x) (.fvar x) from .inr rfl)
        (fvarsIn_mono (fun _ h => .inl h) ht.2))
    · exact RA.throwM _
  · refine RA.whnf hcl ht fun w hw => ?_
    dsimp only
    split
    · have hw' := OracleAgree.good_forallE (cx := ⟨pc.decls⟩) hw rfl
      exact RA.withLocalDecl hw'.1 fun x => hk x _ (OracleAgree.fvarsIn_inst
        (show FVarsIn (fun z => S z ∨ z = x) (.fvar x) from .inr rfl)
        (fvarsIn_mono (fun _ h => .inl h) hw'.2))
    · exact RA.throwM _

theorem RA.withAppEtaToMinArity_go (hcl : ClosedDecls pc.decls) {arity : Nat} {f : Expr}
    {k : Expr → Array Expr → EraseT PureM LBTerm}
    (hk : ∀ (S' : FVarId → Prop) (args : Array Expr), (∀ a ∈ args, Good S' cfg a) →
      RA pc cfg S' (fun _ => True) (k f args)) :
    ∀ (fuel : Nat) {S : FVarId → Prop} {T : Expr} {args : Array Expr}, FVarsIn S T →
      (∀ a ∈ args, Good S cfg a) →
      RA pc cfg S (fun _ => True) (withAppEtaToMinArity.go (m := PureM) arity k fuel T f args)
  | 0, _, _, _, _, _ => by rw [withAppEtaToMinArity.go]; exact RA.throwM _
  | fuel + 1, S, T, args, hT, hargs => by
    rw [withAppEtaToMinArity.go]
    refine RA.ite (fun _ => hk S args hargs) fun _ => RA.forallMonocular hcl hT fun x b hb => ?_
    refine RA.bind (RA.withAppEtaToMinArity_go hcl hk fuel hb fun a ha => ?_) fun _ _ =>
      RA.mkLambda (.inr rfl)
    rcases Array.mem_push.1 ha with ha | rfl
    · exact (hargs a ha).mono fun _ h => .inl h
    · exact ⟨.inr rfl, trivial⟩

/-- `withAppEtaToMinArity` passes its continuation the head of the term and arguments whose free
variables are the term's or the fresh variables of the η-expansion. -/
theorem RA.withAppEtaToMinArity (hcl : ClosedDecls pc.decls) {fuel arity : Nat} {e : Expr}
    {k : Expr → Array Expr → EraseT PureM LBTerm} (he : Good S cfg e)
    (hk : ∀ (S' : FVarId → Prop) (args : Array Expr), (∀ a ∈ args, Good S' cfg a) →
      RA pc cfg S' (fun _ => True) (k e.getAppFn args)) :
    RA pc cfg S (fun _ => True) (withAppEtaToMinArity (m := PureM) fuel e arity k) := by
  rw [Erasure.withAppEtaToMinArity]
  refine RA.inferType hcl he.1 fun T hT => ?_
  rw [withApp_eq]
  exact RA.withAppEtaToMinArity_go hcl hk fuel hT (withApp_args Good.sort (spineArgs_of Good.app he))

/-- `lambdaOrIntroToArity` passes its continuation a body and binders whose free variables are
the alternative's, its type's, or the fresh variables it introduces. -/
theorem RA.lambdaOrIntroToArity (hcl : ClosedDecls pc.decls) {P : α → Prop} [Inhabited α] :
    ∀ (n : Nat) {S : FVarId → Prop} {e type : Expr} {k : Expr → List FVarId → EraseT PureM α},
      Good S cfg e → FVarsIn S type →
      (∀ (S' : FVarId → Prop) e' xs, (∀ y, S y → S' y) → (∀ x ∈ xs, S' x) → Good S' cfg e' →
        RA pc cfg S' P (k e' xs)) →
      RA pc cfg S P (lambdaOrIntroToArity (m := PureM) e type n k)
  | 0, S, e, _, k, he, _, hk => by
    rw [Erasure.lambdaOrIntroToArity]
    exact hk S e [] (fun _ h => h) (fun _ h => nomatch h) he
  | n + 1, S, e, type, k, he, htype, hk => by
    rw [Erasure.lambdaOrIntroToArity, Erasure.lambdaMonocularOrIntro]
    refine RA.forallMonocular hcl htype fun x b hb => ?_
    have hk' : ∀ (S' : FVarId → Prop) e' xs, (∀ y, (S y ∨ y = x) → S' y) → (∀ y ∈ xs, S' y) →
        Good S' cfg e' → RA pc cfg S' P (k e' (x :: xs)) := fun S' e' xs hS hxs he' =>
      hk S' e' (x :: xs) (fun y h => hS y (.inl h)) (fun y hy => by
        rcases List.mem_cons.1 hy with rfl | hy
        exacts [hS _ (.inr rfl), hxs y hy]) he'
    split
    · exact RA.lambdaOrIntroToArity hcl n (Good.inst (b := _) ⟨he.1.2, he.2.2⟩) hb hk'
    · exact RA.lambdaOrIntroToArity hcl n
        ⟨⟨fvarsIn_mono (fun _ h => .inl h) he.1, .inr rfl⟩, he.2, trivial⟩ hb hk'

/-! ## Actions that do not read the locals -/

/-- The constructor step of `register_inductive`. -/
macro (name := _raCtorTail) "ra_ctor_tail" : tactic => `(tactic| (
  refine RA.bind (RA.getConst _) fun _ _ => ?_
  split
  · refine RA.read_bind (fun _ _ => RA.ite (fun _ => ?_) (fun _ => ?_)) (fun _ _ _ => rfl)
    · exact RA.read_bind (fun _ _ => RA.bind' (Blind.liftM _) fun _ => RA.pure trivial)
        (fun _ _ _ => rfl)
    · exact RA.bind (RA.pure (P := fun _ => True) trivial) fun _ _ => RA.pure trivial
  · exact RA.throwM _))

theorem RA.register_inductive (iv : InductiveVal) :
    RA pc cfg S (fun _ => True) (register_inductive (m := PureM) iv) := by
  rw [Erasure.register_inductive]
  refine RA.bind' Blind.get fun s => ?_
  split
  · exact RA.pure trivial
  · refine RA.bind (RA.mapM (P := fun _ => True) fun p _ => ?_) fun _ _ => ?_
    · obtain ⟨ind_name, idx⟩ := p
      dsimp only
      refine RA.bind (RA.getConst _) fun ci _ => ?_
      split
      · refine RA.bind (RA.mapM (P := fun _ => True) fun c _ => ?_) fun r _ => ?_
        · refine RA.bind' (Blind.liftM _) fun _ => RA.read_bind (fun _ _ => ?_) (fun _ _ _ => rfl)
          refine RA.ite (fun _ => ?_) (fun _ => ?_)
          · refine RA.bind' (Blind.liftM _) fun _ => RA.bind' (Blind.addAxiom _) fun _ => ?_
            ra_ctor_tail
          · ra_ctor_tail
        · refine RA.ite (fun _ => ?_) (fun _ => ?_)
          · refine RA.bind (RA.getOrFail _ _) fun _ _ => RA.bind (RA.pure (P := fun _ => True) trivial)
              fun _ _ => RA.bind' (Blind.modify _) fun _ => RA.bind' (Blind.liftM _) fun _ =>
                RA.pure trivial
          · exact RA.bind (RA.pure (P := fun _ => True) trivial) fun _ _ =>
              RA.bind' (Blind.modify _) fun _ => RA.bind' (Blind.liftM _) fun _ => RA.pure trivial
      · exact RA.throwM _
    · refine RA.bind' (Blind.modify _) fun _ => RA.bind' Blind.get fun _ => ?_
      exact RA.mono (RA.getOrFail _ _) fun _ _ => trivial

/-! ## Facts about the recognizer and the declarations -/

theorem ctorAlts_ctor {decls : List ConstantInfo} :
    ∀ {cs : List Name} {as : List CasesAltInfo}, ctorAlts decls cs = some as →
      ∀ a ∈ as, ∃ c k, a = .ctor c k
  | [], as, h, a, ha => by cases h; cases ha
  | c :: cs, as, h, a, ha => by
    unfold ctorAlts at h
    split at h
    · rename_i cv as' _ hcs
      cases h
      rcases List.mem_cons.1 ha with rfl | ha
      · exact ⟨_, _, rfl⟩
      · exact ctorAlts_ctor hcs a ha
    · cases h

/-- A recognized `casesOn` is `T.casesOn` for its inductive `T`, and its alternatives are one per
constructor (no catch-all). -/
theorem casesInfo?_spec {decls : List ConstantInfo} {n : Name} {ci : CasesInfo}
    (h : casesInfo? decls n = some ci) :
    (∃ T, n = .str T "casesOn" ∧ ci.indName = T) ∧ ∀ a ∈ ci.altNumParams, ∃ c k, a = .ctor c k := by
  unfold casesInfo? at h
  split at h
  · rename_i T
    split at h
    · dsimp only at h
      split at h
      · rename_i alts _ _ _ halts _
        split at h
        · cases h
          exact ⟨⟨T, rfl, rfl⟩, fun a ha => ctorAlts_ctor halts a (by simpa using ha)⟩
        · cases h
      · cases h
    · cases h
  · cases h

/-- What `visit_agree` assumes of the declarations. -/
structure DeclsOK (pc : PureCtx) (cfg : ErasureConfig) : Prop where
  closed : ClosedDecls pc.decls
  mf : ∀ ci ∈ pc.decls, ∀ x, ReadExpr pc.decls ci x → MachineFree cfg x
  blk : OwnBlockValues pc.decls
  idx : NoIndexFields pc.decls

/-- A constant whose value `visitMutual` may erase: not a theorem, not a recognized `casesOn`. -/
def GoodConst (decls : List ConstantInfo) (n : Name) : Prop :=
  (∀ v, findConst decls n ≠ some (.thmInfo v)) ∧ casesInfo? decls n = none

/-- A recognized `casesOn` that is not `Int.casesOn` under `nat := .machine`. -/
def CasesOK (decls : List ConstantInfo) (cfg : ErasureConfig) (ci : CasesInfo) : Prop :=
  ∃ n, casesInfo? decls n = some ci ∧ (cfg.nat = .machine → n ≠ ``Int.casesOn)

theorem RA.casesInfo (n : Name) :
    RA pc cfg S (fun r => r = casesInfo? pc.decls n)
      (_root_.liftM (Backend.casesInfo? (m := PureM) n) : EraseT PureM _) :=
  fun _ _ _ _ _ _ _ _ => ⟨rfl, fun _ _ _ h => by cases h; rfl⟩

theorem RA.ctorArity (n : Name) :
    RA pc cfg S (fun r => r = ctorArity? pc.decls n)
      (_root_.liftM (Backend.ctorArity? (m := PureM) n) : EraseT PureM _) :=
  fun _ _ _ _ _ _ _ _ => ⟨rfl, fun _ _ _ h => by cases h; rfl⟩

theorem RA.declInfo (c : ErasureConfig) (n : Name) :
    RA pc cfg S (fun r => r = findConst pc.decls n)
      (_root_.liftM (Backend.declInfo? (m := PureM) c n) : EraseT PureM _) :=
  fun _ _ _ _ _ _ _ _ => ⟨rfl, fun _ _ _ h => by cases h; rfl⟩

theorem RA.withReaderFix {P : α → Prop} {x : EraseT PureM α} (f : TravCtx → TravCtx)
    (hf : ∀ (tc : TravCtx) (ls : List Local), f { tc with locals := ls } = { f tc with locals := ls })
    (hfc : ∀ tc, (f tc).config = tc.config) (hx : RA pc cfg S P x) :
    RA pc cfg S P (withReader f x) := by
  intro st ps tc ls₁ ls₂ hc hS hag
  have e : ∀ c, (withReader f x).runPure st c pc ps = x.runPure st (f c) pc ps := fun _ => rfl
  rw [e, e, hf tc ls₁, hf tc ls₂]
  exact hx st ps (f tc) ls₁ ls₂ ((hfc tc).trans hc) hS hag

theorem Blind.panic {γ : Type} [Inhabited γ] (msg : String) :
    Blind pc (panic msg : EraseT PureM γ) := fun _ _ _ _ _ => rfl

/-- `value!` is `value?`'s value, or `default`, a constant, without one. -/
theorem value!_eq (ci : ConstantInfo) :
    ci.value! (allowOpaque := true) =
      (ci.value? (allowOpaque := true)).getD (.const `_inhabitedExprDummy []) := by
  cases ci <;> rfl

theorem mem_filter {γ : Type} {m : ConstructorArgMask} {arr : Array γ} {x : γ}
    (h : x ∈ filter m arr) : x ∈ arr := by
  unfold filter at h
  simp only [Array.mem_filterMap] at h
  obtain ⟨⟨r, a⟩, hm, hr⟩ := h
  have ha : a ∈ arr := (Array.of_mem_zip hm).2
  cases r <;> simp at hr
  subst hr; exact ha

theorem mem_slice {γ : Type} {xs : Array γ} {i j : Nat} {a : γ}
    (h : a ∈ Std.Slice.toArray (xs.toSubarray i j)) : a ∈ xs := by
  rw [← Subarray.toArray_eq_sliceToArray, ← Subarray.toArray_toList, List.mem_toArray,
    Subarray.toList_eq, Array.array_toSubarray, Array.mem_toList_iff] at h
  obtain ⟨k, hk, rfl⟩ := Array.mem_extract_iff_getElem.1 h
  exact Array.getElem_mem _

theorem Good.dummy : Good S cfg (.const `_inhabitedExprDummy []) :=
  ⟨trivial, fun _ => ⟨by decide, by decide⟩⟩

/-- The value that `visitMutual` erases for a constant it is called on. -/
theorem value_good (hD : DeclsOK pc cfg) {n : Name} {ci : ConstantInfo}
    (hc : findConst pc.decls n = some ci) (hn : GoodConst pc.decls n) {v : Expr}
    (hv : ci.value? (allowOpaque := true) = some v) : Good S cfg v := by
  obtain ⟨hmem, hname⟩ := findDecl_eq_some (l := pc.decls) hc
  have hread : ReadExpr pc.decls ci v := by
    cases ci with
    | defnInfo d =>
      cases hv
      refine .inr (.inl ⟨d, rfl, rfl, ?_⟩)
      have hd : d.name = n := hname
      simp only [EvalEnv.casesOn?, hd, hn.2, Option.isNone_none]
    | opaqueInfo o => cases hv; exact .inr (.inr ⟨o, rfl, rfl⟩)
    | thmInfo t => exact absurd hc (hn.1 t)
    | axiomInfo | quotInfo | inductInfo | ctorInfo | recInfo => cases hv
  exact ⟨OracleAgree.fvarsIn_false (hD.closed ci hmem v hread), hD.mf ci hmem v hread⟩

/-- The value that `visitMutual`'s fix branch erases for a member of the block. -/
theorem member_good (hD : DeclsOK pc cfg) {n : Name} {ci : ConstantInfo}
    (hc : findConst pc.decls n = some ci) (hn : GoodConst pc.decls n) {n' : Name}
    (hn' : n' ∈ ci.all) {ci' : ConstantInfo} (hc' : findConst pc.decls n' = some ci') :
    Good S cfg (ci'.value! (allowOpaque := true)) := by
  obtain ⟨hmem, hname⟩ := findDecl_eq_some (l := pc.decls) hc
  rw [value!_eq]
  rcases hD.blk ci hmem n' hn' with h | h
  · rw [h, hname, hc] at hc'
    cases hc'
    cases hv : ci.value? (allowOpaque := true) with
    | none => exact Good.dummy
    | some v => exact value_good hD hc hn hv
  · rw [h ci' hc']
    exact Good.dummy

theorem RA.prepare (cfg' : ErasureConfig) (e : Expr) :
    RA pc cfg S (fun a => a = e)
      (_root_.liftM (Backend.prepare (m := PureM) cfg' e) : EraseT PureM Expr) :=
  fun _ _ _ _ _ _ _ _ => ⟨rfl, fun _ _ _ h => by cases h; rfl⟩

theorem RA.mkDef (n : Name) (xs : List Name) (t : LBTerm) :
    RA pc cfg S (fun _ => True) (mkDef (m := PureM) n xs t) := by
  unfold Erasure.mkDef
  refine RA.bind (RA.forIn (I := fun _ => True) trivial fun a _ b _ => ?_) fun _ _ => RA.pure trivial
  obtain ⟨_, _⟩ := a
  exact RA.read_bind (fun _ _ => RA.pure trivial) (fun _ _ _ => rfl)

/-- Decompose the parts of `visitMutual` that do not read the locals; `T.expr` erases values. -/
macro (name := _raMut) "ra_mut" T:term : tactic => `(tactic| repeat' (first
  | with_reducible_and_instances first
    | refine RA.bind (RA.getConst _) fun _ _ => ?_
    | refine RA.bind (RA.getOrFail _ _) fun _ _ => ?_
    | (refine RA.bind (RA.prepare _ _) fun _ h => ?_; subst h; refine ($T).expr ?_)
    | refine RA.bind' (Blind.liftM _) fun _ => ?_
    | refine RA.bind' Blind.get fun _ => ?_
    | refine RA.bind' (Blind.modify _) fun _ => ?_
    | refine RA.bind' (Blind.addAxiom _) fun _ => ?_
    | refine RA.bind (RA.mkDef _ _ _) fun _ _ => ?_
    | refine RA.bind (RA.mapM (P := fun _ => True) fun _ _ => ?_) fun _ _ => ?_
    | refine RA.bind (RA.forIn (I := fun _ => True) trivial fun _ _ _ _ => ?_) fun _ _ => ?_
    | refine RA.bind (RA.withReaderFix (P := fun _ => True) _ (fun _ _ => rfl) (fun _ => rfl) ?_)
        fun _ _ => ?_
    | refine RA.read_bind (fun _ _ => ?_) (fun _ _ _ => rfl)
    | refine RA.ite (fun _ => ?_) (fun _ => ?_)
    | refine RA.bind (RA.pure (P := fun _ => True) trivial) fun _ _ => ?_
    | exact RA.mkDef _ _ _
    | exact RA.forIn (I := fun _ => True) trivial fun _ _ _ _ => ?_
    | exact RA.pure trivial
    | exact RA.throwM _
    | exact RA.of_blind (Blind.liftM _)
    | exact RA.of_blind Blind.get
    | exact RA.of_blind (Blind.modify _)
    | exact RA.of_blind (Blind.addAxiom _)
  | split))

/-- `visitMutual` after its recursion test: the non-recursive branch erases the declaration's
value (`value_good`), the fix branch the values of the block's members (`member_good`). -/
macro (name := _raJp) "ra_jp" T:term "," hD:term "," hci:term "," hn:term : tactic => `(tactic| (
  refine RA.ite (fun _ => ?_) (fun _ => ?_)
  · refine RA.bind (RA.getOrFail _ _) fun _ he => ?_
    refine RA.bind (RA.withReaderFix (P := fun _ => True) _ (fun _ _ => rfl) (fun _ => rfl) ?_)
      fun _ _ => ?_
    · refine RA.read_bind (fun _ _ => ?_) (fun _ _ _ => rfl)
      exact RA.bind (RA.prepare _ _) fun _ h => h ▸ ($T).expr (value_good $hD $hci $hn he)
    · ra_mut $T
  · refine RA.bind (RA.mapM (P := fun _ => True) fun _ _ => ?_) fun _ _ => ?_
    · exact RA.of_blind (Blind.liftM _)
    · refine RA.withReaderFix (P := fun _ => True) _ (fun _ _ => rfl) (fun _ => rfl) ?_
      refine RA.bind (RA.mapM (P := fun _ => True) fun _ hmem => ?_) fun _ _ => ?_
      · refine RA.bind (RA.getConst _) fun _ hc' => ?_
        refine RA.bind (RA.withReaderFix (P := fun _ => True) _ (fun _ _ => rfl) (fun _ => rfl) ?_)
          fun _ _ => RA.mkDef _ _ _
        refine RA.read_bind (fun _ _ => ?_) (fun _ _ _ => rfl)
        refine RA.bind (RA.prepare _ _) fun _ h => ?_
        subst h
        exact ($T).expr (member_good $hD $hci $hn hmem hc')
      · refine RA.bind (RA.forIn (I := fun _ => True) trivial fun _ _ _ _ => ?_) fun _ _ =>
          RA.pure trivial
        ra_mut $T))

theorem Good.app' {f a : Expr} (hf : Good S cfg f) (ha : Good S cfg a) : Good S cfg (.app f a) :=
  ⟨⟨hf.1, ha.1⟩, ⟨hf.2, ha.2⟩⟩

theorem Good.mkAppN2 {c : Name} {a b : Expr} (hc : cfg.nat = .machine → c ≠ ``Nat.succ ∧ c ≠ ``Int.casesOn)
    (ha : Good S cfg a) (hb : Good S cfg b) : Good S cfg (mkAppN (.const c []) #[a, b]) :=
  ⟨⟨⟨trivial, ha.1⟩, hb.1⟩, ⟨⟨hc, ha.2⟩, hb.2⟩⟩

/-- The `Nat` branch of `visitCasesOn` under `nat := .machine`, after the zero alternative. -/
macro (name := _raNatcase) "ra_natcase" T:term "," halts:term : tactic => `(tactic| (
  refine RA.bind (RA.getConst _) fun _ _ => ?_
  refine RA.bind (RA.register_inductive _) fun _ _ => ?_
  refine RA.withLocalDecl trivial fun x => ?_
  split
  · rename_i hk
    refine RA.bind (($T).expr ?_) fun _ _ => ?_
    · exact Good.app' ((($halts) _ _ hk).mono fun _ h => .inl h)
        (Good.mkAppN2 (fun _ => ⟨by decide, by decide⟩) ⟨.inr rfl, trivial⟩ ⟨trivial, trivial⟩)
    refine RA.bind (($T).expr (Good.mkAppN2 (a := .fvar x) (b := .lit (.natVal 0))
      (fun _ => ⟨by decide, by decide⟩) ⟨.inr rfl, trivial⟩ ⟨trivial, trivial⟩)) fun _ _ => ?_
    exact RA.bind (RA.mkAlt fun _ h => nomatch h) fun _ _ => RA.bind (RA.mkAlt fun _ h => nomatch h)
      fun _ _ => RA.mkLetIn (.inr rfl)
  · refine RA.bind (RA.pure (P := fun _ => True) trivial) fun _ _ => ?_
    refine RA.bind (($T).expr (Good.mkAppN2 (a := .fvar x) (b := .lit (.natVal 0))
      (fun _ => ⟨by decide, by decide⟩) ⟨.inr rfl, trivial⟩ ⟨trivial, trivial⟩)) fun _ _ => ?_
    exact RA.bind (RA.mkAlt fun _ h => nomatch h) fun _ _ => RA.bind (RA.mkAlt fun _ h => nomatch h)
      fun _ _ => RA.mkLetIn (.inr rfl)))

theorem rco_forIn {β : Type} (r : Std.Rco Nat) (b : β) (f : Nat → β → EraseT PureM (ForInStep β)) :
    forIn r b f = forIn r.toList b f := by
  rw [← forIn'_eq_forIn r b (fun a _ acc => f a acc) f (fun _ _ _ => rfl),
    Std.Rco.forIn'_eq_forIn'_toList, forIn'_eq_forIn _ _ _ f (fun _ _ _ => rfl)]

theorem subarray_forIn {β : Type} (s : Subarray Expr) (b : β)
    (f : Expr → β → EraseT PureM (ForInStep β)) :
    forIn s b f = forIn s.toList b f := Subarray.forIn_eq_forIn_toList

theorem mem_subarray_toList {xs : Array Expr} {i : Nat} {a : Expr}
    (h : a ∈ (xs.toSubarray i).toList) : a ∈ xs := by
  rw [Subarray.toList_eq, Array.array_toSubarray, Array.mem_toList_iff] at h
  obtain ⟨k, hk, rfl⟩ := Array.mem_extract_iff_getElem.1 h
  exact Array.getElem_mem _

theorem next?_subarray {s s' : Subarray CasesAltInfo} {a : CasesAltInfo}
    (h : Std.Stream.next? s = some (a, s')) : a ∈ s.array ∧ s'.array = s.array := by
  unfold Std.Stream.next? Std.instStreamSubarray at h
  dsimp only at h
  split at h
  · cases h; exact ⟨Array.getElem_mem _, rfl⟩
  · cases h

/-- The tail of `visitCases` once the alternatives `m` are collected, with no catch-all and no
index substituted. -/
theorem slice_good {args : Array Expr} (hargs : ∀ a ∈ args, Good S cfg a) (i j : Nat) :
    ∀ a ∈ Std.Slice.toArray (args.toSubarray i j), Good S cfg a :=
  fun a ha => hargs a (mem_slice ha)

/-- The tail of `visitCases` once the alternatives `m` are collected, with no catch-all and no
index substituted. -/
macro (name := _raCasesTail) "ra_cases_tail" T:term "," hm:term "," hd:term "," hargs:term "," hname:term : tactic =>
  `(tactic| (
  refine RA.ite (fun _ => ?_) (fun _ => ?_)
  · refine RA.bind (RA.getOrFail _ _) fun _ _ => ?_
    split
    all_goals first
      | exact absurd ‹(none : Option (Nat × Expr)) = some _› (by simp)
      | exact RA.bind (RA.pure (P := fun _ => True) trivial) fun _ _ =>
          ($T).appArgs (slice_good $hargs _ _)
      | split
        · exfalso; simp_all
        · exact RA.bind (($T).expr (($hm) _ _ ‹_›)) fun _ _ =>
            RA.bind (RA.pure (P := fun _ => True) trivial) fun _ _ =>
              ($T).appArgs (slice_good $hargs _ _)
  · refine RA.bind (($T).expr $hd) fun _ _ => ?_
    refine RA.ite (fun _ => ?_) (fun _ => ?_)
    all_goals
      refine RA.bind (($T).casesOnF $hname $hm) fun _ _ =>
        RA.bind (P := fun _ => True) ?_ fun _ _ => RA.pure trivial
      rw [subarray_forIn]
      exact RA.forIn (I := fun _ => True) trivial fun a ha _ _ =>
        RA.bind (($T).expr (($hargs) a (mem_subarray_toList ha))) fun _ _ => RA.pure trivial))

/-! ## The traversal at one fuel -/

/-- The frame property of every function of the traversal at fuel `fuel`. -/
structure Trav (pc : PureCtx) (cfg : ErasureConfig) (fuel : Nat) : Prop where
  expr : ∀ {S e}, Good S cfg e → RA pc cfg S (fun _ => True) (visitExpr (m := PureM) fuel e)
  lit : ∀ {S} (l : Literal), RA pc cfg S (fun _ => True) (visitLiteral (m := PureM) fuel l)
  lam : ∀ {S e}, Good S cfg e → RA pc cfg S (fun _ => True) (visitLambda (m := PureM) fuel e)
  letE : ∀ {S e}, Good S cfg e → RA pc cfg S (fun _ => True) (visitLet (m := PureM) fuel e)
  proj : ∀ {S s i e}, Good S cfg e →
    RA pc cfg S (fun _ => True) (visitProj (m := PureM) fuel s i e)
  app : ∀ {S e}, Good S cfg e → NoThmHead pc.decls e →
    RA pc cfg S (fun _ => True) (visitApp (m := PureM) fuel e)
  const : ∀ {S c us}, GoodConst pc.decls c →
    RA pc cfg S (fun _ => True) (visitConst (m := PureM) fuel (.const c us))
  constApp : ∀ {S e}, Good S cfg e → NoThmHead pc.decls e →
    RA pc cfg S (fun _ => True) (visitConstApp (m := PureM) fuel e)
  recF : ∀ {S r e c us}, Good S cfg e → e.getAppFn = .const c us → GoodConst pc.decls c →
    RA pc cfg S (fun _ => True) (visitRec (m := PureM) fuel r e)
  ctor : ∀ {S c args}, (∀ a ∈ args, Good S cfg a) → (cfg.nat = .machine → c ≠ ``Nat.succ) →
    RA pc cfg S (fun _ => True) (visitConstructor (m := PureM) fuel c args)
  appArgs : ∀ {S f args}, (∀ a ∈ args, Good S cfg a) →
    RA pc cfg S (fun _ => True) (visitAppArgs (m := PureM) fuel f args)
  casesF : ∀ {S ci args}, CasesOK pc.decls cfg ci → (∀ a ∈ args, Good S cfg a) →
    RA pc cfg S (fun _ => True) (visitCases (m := PureM) fuel ci args)
  casesOnF : ∀ {S iv} {alts : Std.HashMap Name (Nat × Expr)} {d},
    (cfg.nat = .machine → iv.name ≠ ``Int) →
    (∀ (k : Name) (v : Nat × Expr), alts[k]? = some v → Good S cfg v.2) →
    RA pc cfg S (fun _ => True) (visitCasesOn (m := PureM) fuel iv alts ∅ none d)
  alt : ∀ {S k mask e}, Good S cfg e →
    RA pc cfg S (fun _ => True) (visitAlt (m := PureM) fuel k mask [] e)
  kername : ∀ {S n}, GoodConst pc.decls n →
    RA pc cfg S (fun _ => True) (get_constant_kername (m := PureM) fuel n)
  mutualF : ∀ {S n}, GoodConst pc.decls n →
    RA pc cfg S (fun _ => True) (visitMutual (m := PureM) fuel n)

theorem Trav.zero : Trav pc cfg 0 where
  expr _ := by rw [visitExpr]; exact RA.throwM _
  lit _ := by rw [visitLiteral]; exact RA.throwM _
  lam _ := by rw [visitLambda]; exact RA.throwM _
  letE _ := by rw [visitLet]; exact RA.throwM _
  proj _ := by rw [visitProj]; exact RA.throwM _
  app _ _ := by rw [visitApp]; exact RA.throwM _
  const _ := by rw [visitConst]; exact RA.throwM _
  constApp _ _ := by rw [visitConstApp]; exact RA.throwM _
  recF _ _ _ := by rw [visitRec]; exact RA.throwM _
  ctor _ _ := by rw [visitConstructor]; exact RA.throwM _
  appArgs _ := by rw [visitAppArgs]; exact RA.throwM _
  casesF _ _ := by rw [visitCases]; exact RA.throwM _
  casesOnF _ _ := by rw [visitCasesOn]; exact RA.throwM _
  alt _ := by rw [visitAlt]; exact RA.throwM _
  kername _ := by rw [get_constant_kername]; exact RA.throwM _
  mutualF _ := by rw [visitMutual]; exact RA.throwM _

section Steps
variable {fuel : Nat} (hD : DeclsOK pc cfg) (T : Trav pc cfg fuel)
include hD T

theorem step_expr {e : Expr} (he : Good S cfg e) :
    RA pc cfg S (fun _ => True) (visitExpr (m := PureM) (fuel + 1) e) := by
  cases e with
  | app f a => rw [visitExpr]; exact RA.oracle hD.closed he.1 fun hn => T.app he hn
  | const c us => rw [visitExpr]; exact RA.oracle hD.closed he.1 fun hn => T.app he hn
  | proj s i b => rw [visitExpr]; exact RA.oracle hD.closed he.1 fun _ => T.proj he
  | mdata d b => rw [visitExpr]; exact RA.oracle hD.closed he.1 fun _ => T.expr he
  | lam => rw [visitExpr]; exact RA.oracle hD.closed he.1 fun _ => T.lam he
  | letE => rw [visitExpr]; exact RA.oracle hD.closed he.1 fun _ => T.letE he
  | lit l => rw [visitExpr]; exact RA.oracle hD.closed he.1 fun _ => T.lit l
  | fvar => rw [visitExpr]; exact RA.oracle hD.closed he.1 fun _ => RA.pure trivial
  | bvar | sort | forallE | mvar =>
    rw [visitExpr]; exact RA.oracle hD.closed he.1 fun _ => RA.throwM _

theorem step_lit (l : Literal) :
    RA pc cfg S (fun _ => True) (visitLiteral (m := PureM) (fuel + 1) l) := by
  rw [visitLiteral]
  refine RA.read_bind (fun c hc => ?_) (fun _ _ _ => rfl)
  split
  · refine RA.ite (fun _ => RA.read_bind (fun _ _ => RA.throwM _) (fun _ _ _ => rfl)) fun _ => ?_
    refine RA.ite (fun _ => T.ctor (fun _ h => by simp at h) fun h => by simp) fun _ => ?_
    exact T.ctor (fun a h => by simp at h; subst h; exact ⟨trivial, trivial⟩)
      fun h => by subst hc; simp_all
  · exact RA.ite (fun _ => RA.pure trivial) fun _ => RA.of_blind (Blind.panic _)
  · exact RA.of_blind (Blind.panic _)

omit hD in
theorem step_lam {e : Expr} (he : Good S cfg e) :
    RA pc cfg S (fun _ => True) (visitLambda (m := PureM) (fuel + 1) e) := by
  cases e with
  | lam n t b bi =>
    rw [visitLambda, lambdaMonocular]
    exact RA.withLocalDecl he.1.1 fun x => RA.bind (T.expr (Good.inst ⟨he.1.2, he.2.2⟩))
      fun _ _ => RA.mkLambda (.inr rfl)
  | _ => rw [visitLambda, lambdaMonocular] <;> first | exact RA.throwM _ | simp

omit hD in
theorem step_letE {e : Expr} (he : Good S cfg e) :
    RA pc cfg S (fun _ => True) (visitLet (m := PureM) (fuel + 1) e) := by
  cases e with
  | letE n t v b nd =>
    rw [visitLet, letMonocular]
    refine RA.withLocalDef he.1.1 he.1.2.1 fun x => ?_
    exact RA.bind (T.expr ((show Good S cfg v from ⟨he.1.2.1, he.2.2.1⟩).mono fun _ h => .inl h))
      fun _ _ => RA.bind (T.expr (Good.inst ⟨he.1.2.2, he.2.2.2⟩)) fun _ _ => RA.mkLetIn (.inr rfl)
  | _ => rw [visitLet, letMonocular] <;> first | exact RA.throwM _ | simp

omit hD in
theorem step_proj {s : Name} {i : Nat} {e : Expr} (he : Good S cfg e) :
    RA pc cfg S (fun _ => True) (visitProj (m := PureM) (fuel + 1) s i e) := by
  rw [visitProj]
  refine RA.bind (RA.getConst _) fun ci _ => ?_
  split
  · refine RA.bind (RA.register_inductive _) fun r _ => ?_
    obtain ⟨_, _⟩ := r
    exact RA.bind (RA.getOrFail _ _) fun _ _ => RA.bind (T.expr he) fun _ _ => RA.pure trivial
  · exact RA.throwM _

omit hD in
theorem step_app {e : Expr} (he : Good S cfg e) (hn : NoThmHead pc.decls e) :
    RA pc cfg S (fun _ => True) (visitApp (m := PureM) (fuel + 1) e) := by
  rw [visitApp]
  split
  · exact T.constApp he hn
  · rw [withApp_eq]
    exact RA.bind (T.expr (getAppFn_of Good.app he)) fun _ _ =>
      T.appArgs (withApp_args Good.sort (spineArgs_of Good.app he))

omit hD in
theorem step_const {c : Name} {us : List Level} (hc : GoodConst pc.decls c) :
    RA pc cfg S (fun _ => True) (visitConst (m := PureM) (fuel + 1) (.const c us)) := by
  rw [visitConst]
  refine RA.read_bind (fun _ _ => ?_) (fun _ _ _ => rfl)
  split
  · exact RA.pure trivial
  · exact RA.bind (T.kername hc) fun _ _ => RA.pure trivial

omit hD in
theorem step_appArgs {f : LBTerm} {args : Array Expr} (hargs : ∀ a ∈ args, Good S cfg a) :
    RA pc cfg S (fun _ => True) (visitAppArgs (m := PureM) (fuel + 1) f args) := by
  rw [visitAppArgs, ← Array.foldlM_toList]
  have h' : ∀ a ∈ args.toList, Good S cfg a := fun a ha => hargs a (Array.mem_toList_iff.mp ha)
  generalize args.toList = l at h'
  induction l generalizing f with
  | nil => exact RA.pure trivial
  | cons a l ihl =>
    rw [List.foldlM_cons]
    exact RA.bind (RA.bind (Q := fun _ => True) (T.expr (h' a (.head _))) fun _ _ => RA.pure trivial)
      fun _ _ =>
      ihl fun b hb => h' b (.tail _ hb)

omit hD in
theorem step_kername {n : Name} (hn : GoodConst pc.decls n) :
    RA pc cfg S (fun _ => True) (get_constant_kername (m := PureM) (fuel + 1) n) := by
  rw [get_constant_kername]
  refine RA.bind' Blind.get fun _ => ?_
  split
  · exact RA.pure trivial
  · exact RA.bind (T.mutualF hn) fun _ _ => RA.bind' Blind.get fun _ =>
      RA.mono (RA.getOrFail _ _) fun _ _ => trivial

theorem step_rec {r : RecursorVal} {e : Expr} {c : Name} {us : List Level} (he : Good S cfg e)
    (h : e.getAppFn = .const c us) (hc : GoodConst pc.decls c) :
    RA pc cfg S (fun _ => True) (visitRec (m := PureM) (fuel + 1) r e) := by
  have hargs := withApp_args Good.sort (spineArgs_of Good.app he)
  rw [visitRec]
  refine RA.bind (RA.mapM (P := fun _ => True) fun t _ => ?_) fun ivs _ => ?_
  · refine RA.bind (RA.getConst _) fun ci _ => ?_
    split
    · exact RA.pure trivial
    · exact RA.throwM _
  refine RA.bind (RA.mapM (P := fun _ => True) fun t _ => ?_) fun cvs _ => ?_
  · refine RA.bind (RA.getConst _) fun ci _ => ?_
    split
    · exact RA.pure trivial
    · exact RA.throwM _
  refine RA.read_bind (fun _ _ => ?_) (fun _ _ _ => rfl)
  refine RA.ite (fun _ => ?_) (fun _ => ?_)
  · rw [withApp_eq, h]
    exact RA.bind (T.const hc) fun _ _ => T.appArgs hargs
  split
  · refine RA.bind (RA.forIn (I := fun _ => True) trivial fun _ _ _ _ => ?_) fun _ _ => ?_
    · dsimp only
      split
      · exact RA.pure trivial
      · exact RA.bind (RA.register_inductive _) fun _ _ => RA.pure trivial
    refine RA.bind (RA.getOrFail _ _) fun _ _ => ?_
    refine RA.withAppEtaToMinArity hD.closed he fun S' args hargs' => ?_
    have hext : ∀ i j, ∀ b ∈ args.extract i j, Good S' cfg b := fun i j b hb => by
      obtain ⟨k, hk, rfl⟩ := Array.mem_extract_iff_getElem.1 hb
      exact hargs' _ (Array.getElem_mem _)
    refine RA.bind (RA.getOrFail _ _) fun maj hmaj => ?_
    refine RA.typeLevel hD.closed (hargs' maj (Array.mem_of_getElem? hmaj)).1 fun _ => ?_
    refine RA.bind (RA.mapM (P := fun _ => True) fun a ha =>
      T.expr (hext _ _ a (Array.mem_toList_iff.mp ha))) fun _ _ => ?_
    exact RA.bind (T.appArgs (hext _ _)) fun _ _ => T.appArgs (hext _ _)
  · exact RA.throwM _

theorem step_constApp {e : Expr} (he : Good S cfg e) (hn : NoThmHead pc.decls e) :
    RA pc cfg S (fun _ => True) (visitConstApp (m := PureM) (fuel + 1) e) := by
  rw [visitConstApp, withApp_eq]
  have hargs := withApp_args Good.sort (spineArgs_of Good.app he)
  have hhead := getAppFn_of Good.app he
  split
  · rename_i declName us h
    rw [h] at hhead
    refine RA.bind (RA.casesInfo _) fun r hr => ?_
    subst hr
    split
    · rename_i ci hci
      exact RA.withAppEtaToMinArity hD.closed he fun S' args hargs =>
        T.casesF ⟨declName, hci, fun hm => (hhead.2 hm).2⟩ hargs
    · rename_i hci
      refine RA.bind (RA.ctorArity _) fun r hr => ?_
      subst hr
      split
      · exact RA.withAppEtaToMinArity hD.closed he fun S' args hargs =>
          T.ctor hargs fun hm => (hhead.2 hm).1
      · refine RA.bind (P := fun _ => True)
          (fun _ _ _ _ _ _ _ _ => ⟨rfl, fun _ _ _ _ => trivial⟩) fun _ _ => ?_
        split
        · exact RA.withAppEtaToMinArity hD.closed he fun S' args hargs =>
            RA.bind (RA.getOrFail _ _) fun a ha =>
              RA.bind (T.expr (hargs a (Array.mem_of_getElem? ha))) fun _ _ =>
                T.appArgs fun b hb => by
                  obtain ⟨k, hk, rfl⟩ := Array.mem_extract_iff_getElem.1 hb
                  exact hargs _ (Array.getElem_mem _)
        · exact RA.withAppEtaToMinArity hD.closed he fun S' args hargs =>
            RA.bind (RA.getOrFail _ _) fun a ha =>
              RA.bind (T.expr (hargs a (Array.mem_of_getElem? ha))) fun _ _ =>
                T.appArgs fun b hb => by
                  obtain ⟨k, hk, rfl⟩ := Array.mem_extract_iff_getElem.1 hb
                  exact hargs _ (Array.getElem_mem _)
        · refine T.recF he h ⟨fun v => hn declName us v h, ?_⟩
          cases hc : casesInfo? pc.decls declName
          · rfl
          · exact absurd hc (hci _)
        · rw [h]
          refine RA.bind (T.const ⟨fun v => hn declName us v h, ?_⟩) fun _ _ => T.appArgs hargs
          cases hc : casesInfo? pc.decls declName
          · rfl
          · exact absurd hc (hci _)
  · exact RA.of_blind fun _ _ _ _ _ => rfl


omit hD in
theorem step_ctor {c : Name} {args : Array Expr} (hargs : ∀ a ∈ args, Good S cfg a)
    (hns : cfg.nat = .machine → c ≠ ``Nat.succ) :
    RA pc cfg S (fun _ => True) (visitConstructor (m := PureM) (fuel + 1) c args) := by
  have hfil : ∀ (info : ConstructorVal) (mask : ConstructorArgMask), ∀ a ∈
      Std.Slice.toArray (args.toSubarray 0 info.numParams) ++
        filter mask (args.toSubarray info.numParams (info.numParams + info.numFields)).toArray ++
        Std.Slice.toArray (args.toSubarray (info.numParams + info.numFields)), Good S cfg a := by
    intro info mask a ha
    simp only [Array.mem_append] at ha
    rcases ha with (ha | ha) | ha
    · exact hargs a (mem_slice ha)
    · refine hargs a (mem_slice (j := info.numParams + info.numFields) (i := info.numParams) ?_)
      rw [← Subarray.toArray_eq_sliceToArray]
      exact mem_filter ha
    · exact hargs a (mem_slice ha)
  rw [visitConstructor]
  refine RA.bind (RA.getConst _) fun ci _ => ?_
  split
  · rename_i info _
    dsimp only
    refine RA.bind (RA.getConst _) fun ci' _ => ?_
    split
    · refine RA.bind (RA.register_inductive _) fun r _ => ?_
      obtain ⟨indid, argmasks⟩ := r
      dsimp only
      refine RA.bind (RA.getOrFail _ _) fun mask _ => ?_
      refine RA.bind' (Blind.liftM _) fun _ => RA.read_bind (fun _ _ => ?_) (fun _ _ _ => rfl)
      refine RA.ite (fun _ => T.appArgs hargs) fun _ => ?_
      refine RA.read_bind (fun c' hc' => ?_) (fun _ _ _ => rfl)
      split
      · exact RA.ite (fun _ => T.lit _) fun _ => RA.bind' (Blind.panic _) fun _ => T.lit _
      · subst hc'
        exact absurd rfl (hns ‹_ = Config.Nat.machine›)
      · exact T.appArgs (hfil info mask)
      · exact T.appArgs (hfil info mask)
    · exact RA.throwM _
  · exact RA.throwM _

theorem step_alt {k : Nat} {mask : ConstructorArgMask} {e : Expr} (he : Good S cfg e) :
    RA pc cfg S (fun _ => True) (visitAlt (m := PureM) (fuel + 1) k mask [] e) := by
  rw [visitAlt]
  refine RA.inferType hD.closed he.1 fun T' hT => ?_
  refine RA.lambdaOrIntroToArity hD.closed k he hT fun S' e' xs _ hxs he' => ?_
  simp only [List.isEmpty_nil, ↓reduceIte]
  exact RA.bind (T.expr he') fun _ _ => RA.mkAlt fun x hx =>
    hxs x (List.mem_toArray.1 (mem_filter (Array.mem_toList_iff.1 hx)))

theorem step_mutual {n : Name} (hn : GoodConst pc.decls n) :
    RA pc cfg S (fun _ => True) (visitMutual (m := PureM) (fuel + 1) n) := by
  rw [visitMutual]
  refine RA.read_bind (fun c _ => ?_) (fun _ _ _ => rfl)
  refine RA.bind (RA.declInfo c.config n) fun r hr => ?_
  subst hr
  refine RA.bind (RA.getOrFail _ _) fun ci hci => ?_
  refine RA.bind' (Blind.liftM _) fun _ => RA.bind' (Blind.liftM _) fun _ => ?_
  extract_lets lN nr kn fvn jp jp2
  have hjp : ∀ u, RA pc cfg S (fun _ => True) (jp u) := by
    intro u
    simp only [jp, nr, kn, fvn]
    ra_jp T, hD, hci, hn
  clear_value jp
  have hjp2 : ∀ u, RA pc cfg S (fun _ => True) (jp2 u) := by
    intro u
    simp only [jp2]
    refine RA.bind' (Blind.liftM _) fun _ => RA.read_bind (fun _ _ => ?_) (fun _ _ _ => rfl)
    split
    · exact RA.bind' (Blind.liftM _) fun _ => RA.of_blind (Blind.addAxiom _)
    · exact hjp ()
    · exact RA.bind' (Blind.liftM _) fun _ => RA.of_blind (Blind.addAxiom _)
    · exact RA.bind' (Blind.liftM _) fun _ => hjp ()
  clear_value jp2
  refine RA.ite (fun _ => ?_) (fun _ => hjp ())
  exact RA.ite (fun _ => RA.bind' (Blind.liftM _) fun _ => RA.bind' (Blind.modify _) fun r => hjp2 r)
    fun _ => hjp2 ()

omit hD in
theorem step_casesOn {iv : InductiveVal} {alts : Std.HashMap Name (Nat × Expr)} {d : LBTerm}
    (hint : cfg.nat = .machine → iv.name ≠ ``Int)
    (halts : ∀ (k : Name) (v : Nat × Expr), alts[k]? = some v → Good S cfg v.2) :
    RA pc cfg S (fun _ => True) (visitCasesOn (m := PureM) (fuel + 1) iv alts ∅ none d) := by
  rw [visitCasesOn]
  refine RA.bind (RA.pure (P := fun _ => True) trivial) fun _ _ => ?_
  dsimp only
  refine RA.read_bind (fun c hc => ?_) (fun _ _ _ => rfl)
  split
  · split
    · rename_i hk
      exact RA.bind (T.expr (halts _ _ hk)) fun _ _ => by ra_natcase T, halts
    · exact RA.bind (RA.pure (P := fun _ => True) trivial) fun _ _ => by ra_natcase T, halts
  · exfalso
    subst hc
    exact hint ‹_ = Config.Nat.machine› ‹_›
  · refine RA.bind (RA.register_inductive _) fun r _ => ?_
    obtain ⟨indid, argmasks⟩ := r
    dsimp only
    refine RA.bind (RA.forIn (I := fun _ => True) trivial fun ctorName _ acc _ => ?_) fun _ _ =>
      RA.pure trivial
    split
    · exact RA.pure trivial
    · split
      · rename_i hk
        rw [Std.HashMap.getD_empty]
        exact RA.bind (T.alt (halts _ _ hk)) fun _ _ => RA.pure trivial
      · exact RA.bind (RA.pure (P := fun _ => True) trivial) fun _ _ => RA.pure trivial

theorem step_cases {ci : CasesInfo} {args : Array Expr} (hci : CasesOK pc.decls cfg ci)
    (hargs : ∀ a ∈ args, Good S cfg a) :
    RA pc cfg S (fun _ => True) (visitCases (m := PureM) (fuel + 1) ci args) := by
  obtain ⟨n, hn, hint⟩ := hci
  obtain ⟨⟨T₀, hT₀, hind⟩, hctor⟩ := casesInfo?_spec hn
  have hint' : cfg.nat = .machine → ci.indName ≠ ``Int := fun hm h => hint hm (by rw [hT₀, ← hind, h])
  rw [visitCases]
  refine RA.bind (RA.getOrFail _ _) fun discr hdiscr => ?_
  have hd : Good S cfg discr := hargs discr (Array.mem_of_getElem? hdiscr)
  refine RA.bind (RA.getConst _) fun ci1 hci1 => ?_
  split
  · rename_i indVal
    refine RA.bind (RA.getConst _) fun ci2 _ => ?_
    split
    · refine RA.ite (fun _ => RA.pure trivial) fun _ => ?_
      refine RA.typeLevel hD.closed hd.1 fun u => ?_
      dsimp only
      rw [rco_forIn]
      have hname : cfg.nat = .machine → indVal.name ≠ ``Int := by
        have := (findDecl_eq_some (l := pc.decls) hci1).2
        intro hm h
        exact hint' hm (by rw [← this]; exact h)
      refine RA.bind (RA.forIn (I := fun (acc : Std.HashMap Name (Nat × Expr) × Option (Nat × Expr) ×
          Subarray CasesAltInfo) => (∀ (k : Name) (v : Nat × Expr), acc.1[k]? = some v → Good S cfg v.2) ∧
          acc.2.1 = none ∧
          acc.2.2.array = ci.altNumParams) ⟨fun _ _ h => by simp at h, rfl, by
            show (ci.altNumParams[*...*]).array = _; simp⟩ fun i _ acc hacc => ?_) fun r hr => ?_
      · obtain ⟨m, ca, st⟩ := acc
        obtain ⟨hm, hca, hst⟩ := hacc
        dsimp only
        split
        · exact RA.pure ⟨hm, hca, hst⟩
        · rename_i altInfo s' hnext
          have ⟨hmem, hs'⟩ := next?_subarray hnext
          rw [hst] at hmem
          obtain ⟨c, k, rfl⟩ := hctor _ hmem
          dsimp only
          refine RA.bind (RA.getOrFail _ _) fun alt halt => RA.pure ⟨?_, hca, hs'.trans hst⟩
          intro k' v hv
          simp only [ForInStep.value] at hv
          rw [Std.HashMap.getElem?_insert] at hv
          split at hv
          · cases hv; exact hargs _ (Array.mem_of_getElem? halt)
          · exact hm _ _ hv
      · obtain ⟨m, ca, st⟩ := r
        obtain ⟨hm, rfl, -⟩ := hr
        dsimp only
        refine RA.ite (fun _ => ?_) (fun _ => ?_)
        · refine RA.bind (RA.forIn (I := fun s => s = ∅) rfl fun cn hcn s hs => ?_) fun s₁ hs₁ => ?_
          · subst hs
            refine RA.bind (RA.getConst _) fun c' hc' => ?_
            split
            · rename_i ctorVal
              refine RA.ite (fun _ => RA.pure rfl) fun hne => ?_
              exact absurd (hD.idx n ci indVal hn hci1 cn hcn ctorVal hc') hne
            · exact RA.bind (RA.throwM (P := fun _ => False) _) fun _ h => h.elim
          · subst hs₁
            ra_cases_tail T, hm, hd, hargs, hname
        · ra_cases_tail T, hm, hd, hargs, hname
    · exact RA.throwM _
  · exact RA.throwM _

end Steps

theorem Trav.succ (hD : DeclsOK pc cfg) {fuel : Nat} (T : Trav pc cfg fuel) :
    Trav pc cfg (fuel + 1) where
  expr he := step_expr hD T he
  lit l := step_lit hD T l
  lam he := step_lam T he
  letE he := step_letE T he
  proj he := step_proj T he
  app he hn := step_app T he hn
  const hc := step_const T hc
  constApp he hn := step_constApp hD T he hn
  recF he h hc := step_rec hD T he h hc
  ctor hargs hns := step_ctor T hargs hns
  appArgs hargs := step_appArgs T hargs
  casesF hci hargs := step_cases hD T hci hargs
  casesOnF hint halts := step_casesOn T hint halts
  alt he := step_alt hD T he
  kername hn := step_kername T hn
  mutualF hn := step_mutual hD T hn

theorem trav (hD : DeclsOK pc cfg) : ∀ fuel, Trav pc cfg fuel
  | 0 => Trav.zero
  | fuel + 1 => (trav hD fuel).succ hD

end TravFrame

/-- Traversal frame: at the pure backend, a run of `visitExpr` on a term whose free variables lie
in `S` does not depend on the locals outside `S`, when the declarations' read expressions are
closed (`ClosedDecls`), the visited term and the read expressions mention neither `Nat.succ` nor
`Int.casesOn` under `nat := .machine` (`MachineFree`), the only member of a declaration's block
with a value is the declaration itself (`OwnBlockValues`), and the constructors of recognized
`casesOn` constants have no index fields (`NoIndexFields`). Both runs start from the same state and
counter of fresh variables, which may be any. Reference: none; MetaRocq erases a constant body in
the empty context (`MR E/ErasureFunction.v:1309 erase_constant_body`); DV-13; port of
`L4 Core/Frame.lean:400`. -/
theorem visit_agree {S : FVarId → Prop} {pc : PureCtx} {tc : TravCtx} {st : ErasureState}
    {ps : PureState} {ls₁ ls₂ : List Local} {fuel : Nat} {e : Expr}
    (hcl : ClosedDecls pc.decls) (hmf : MachineFree tc.config e)
    (hmfd : ∀ ci ∈ pc.decls, ∀ x, ReadExpr pc.decls ci x → MachineFree tc.config x)
    (hblk : OwnBlockValues pc.decls) (hidx : NoIndexFields pc.decls)
    (hS : LocalsSupport S ls₁) (hag : LocalsAgree S ls₁ ls₂) (he : FVarsIn S e) :
    (visitExpr (m := PureM) fuel e).runPure st { tc with locals := ls₁ } pc ps =
      (visitExpr (m := PureM) fuel e).runPure st { tc with locals := ls₂ } pc ps :=
  ((TravFrame.trav ⟨hcl, hmfd, hblk, hidx⟩ fuel).expr ⟨he, hmf⟩ st ps tc ls₁ ls₂ rfl hS hag).1

end EraseProof
