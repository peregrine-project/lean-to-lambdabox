import EraseProof.Core.StepsCases

/-!
# The traversal's counter and masks

Two invariants of every run of the shipping traversal (`Erasure.visitExpr` and the functions it
calls, `LeanToLambdaBox/Erasure.lean`) at the pure backend `Erasure.PureM`, without any premise on
the program, the state or the context: the counter of fresh variables never decreases, and every
inductive type the state registers has masks that keep every field (`MasksOK`, the `KeepMasks` of
`StateOK`). Both are read by the existence of the marking (`markOf_exists`): a binder opened after
a sibling's run gets a variable that no earlier binder has, and `visitConstructor` and
`visitCasesOn` visit every field of a constructor.

`TravMono` is the invariant of one action; its closure lemmas cover the monadic operations the
traversal uses (`trav_mono` applies them along a body), and `travMonoAt` proves it of the sixteen
functions of the traversal by induction on the fuel; `register_inductive_masks` is the one step
that reads the program: the masks it builds from the constructors' declarations. Reference: none
(DV-13: MetaRocq's `erase` is de Bruijn and keeps no masks).
-/

open Lean Erasure

namespace EraseProof

namespace Steps

open RegisterInd

/-- Every inductive type that `st` registers is an inductive of `σ` whose masks keep every field
(`KeepMasks`). Reference: none (DV-23, as `KeepMasks`). -/
def MasksOK (σ : EvalEnv) (st : ErasureState) : Prop :=
  ∀ (T : Name) (r : InductiveId × InductiveArgMasks), st.inductives[T]? = some r →
    ∃ iv, findDecl σ.decls T = some (.inductInfo iv) ∧ KeepMasks σ iv r.2

/-- Every successful run of `x` at the pure backend over `pc`, from any state, context and counter,
does not decrease the counter and keeps `MasksOK`. Reference: none (DV-13). -/
def TravMono (σ : EvalEnv) (pc : PureCtx) {α : Type} (x : EraseT PureM α) : Prop :=
  ∀ st tc ps r st' ps', x.runPure st tc pc ps = .ok ((r, st'), ps') →
    ps.next ≤ ps'.next ∧ (MasksOK σ st → MasksOK σ st')

/-! ## Closure under the monadic operations of the traversal -/

section
variable {σ : EvalEnv} {pc : PureCtx} {α β γ : Type}

theorem TravMono.pure (a : α) : TravMono σ pc (Pure.pure a : EraseT PureM α) := by
  intro st tc ps r st' ps' h; cases h; exact ⟨Nat.le_refl _, id⟩

theorem TravMono.bind {x : EraseT PureM α} {k : α → EraseT PureM β}
    (hx : TravMono σ pc x) (hk : ∀ a, TravMono σ pc (k a)) : TravMono σ pc (x >>= k) := by
  intro st tc ps r st' ps' h
  rw [runPure_bind] at h
  obtain ⟨⟨⟨a, st₁⟩, ps₁⟩, h1, h2⟩ := ok_of_bind h
  obtain ⟨n1, m1⟩ := hx _ _ _ _ _ _ h1
  obtain ⟨n2, m2⟩ := hk a _ _ _ _ _ _ h2
  exact ⟨Nat.le_trans n1 n2, m2 ∘ m1⟩

theorem TravMono.get : TravMono σ pc (MonadState.get : EraseT PureM ErasureState) := by
  intro st tc ps r st' ps' h; cases h; exact ⟨Nat.le_refl _, id⟩

theorem TravMono.read : TravMono σ pc (read : EraseT PureM TravCtx) := by
  intro st tc ps r st' ps' h; cases h; exact ⟨Nat.le_refl _, id⟩

theorem TravMono.modify {f : ErasureState → ErasureState}
    (hf : ∀ s, MasksOK σ s → MasksOK σ (f s)) :
    TravMono σ pc (_root_.modify f : EraseT PureM PUnit) := by
  intro st tc ps r st' ps' h; cases h; exact ⟨Nat.le_refl _, hf st⟩

theorem TravMono.withReader {f : TravCtx → TravCtx} {x : EraseT PureM α}
    (hx : TravMono σ pc x) : TravMono σ pc (withReader f x) :=
  fun st tc ps r st' ps' h => hx st (f tc) ps r st' ps' h

theorem TravMono.liftM (x : PureM α)
    (hx : ∀ a ps ps', (x.run pc).run ps = .ok (a, ps') → ps.next ≤ ps'.next) :
    TravMono σ pc (_root_.liftM x : EraseT PureM α) := by
  intro st tc ps r st' ps' h
  rw [runPure_liftM] at h
  obtain ⟨⟨a, ps₁⟩, h1, h2⟩ := ok_of_bind h
  cases h2
  exact ⟨hx _ _ _ h1, id⟩

theorem TravMono.ite {c : Prop} [Decidable c] {a b : EraseT PureM α} (ha : TravMono σ pc a)
    (hb : TravMono σ pc b) : TravMono σ pc (if c then a else b) := by
  split
  · exact ha
  · exact hb

theorem TravMono.forIn {f : γ → β → EraseT PureM (ForInStep β)}
    (hf : ∀ a b, TravMono σ pc (f a b)) : ∀ (l : List γ) (b : β), TravMono σ pc (forIn l b f)
  | [], b => by rw [List.forIn_nil]; exact TravMono.pure b
  | a :: l, b => by
    rw [List.forIn_cons]
    refine TravMono.bind (hf a b) fun r => ?_
    cases r with
    | done b' => exact TravMono.pure b'
    | yield b' => exact TravMono.forIn hf l b'

theorem TravMono.mapM {f : γ → EraseT PureM β} (hf : ∀ a, TravMono σ pc (f a)) :
    ∀ l : List γ, TravMono σ pc (l.mapM f)
  | [] => by rw [List.mapM_nil]; exact TravMono.pure _
  | a :: l => by
    rw [List.mapM_cons]
    exact TravMono.bind (hf a) fun _ => TravMono.bind (TravMono.mapM hf l) fun _ => TravMono.pure _

theorem TravMono.foldlM {f : β → γ → EraseT PureM β} (hf : ∀ b a, TravMono σ pc (f b a)) :
    ∀ (l : List γ) (b : β), TravMono σ pc (l.foldlM f b)
  | [], b => by rw [List.foldlM_nil]; exact TravMono.pure b
  | a :: l, b => by
    rw [List.foldlM_cons]
    exact TravMono.bind (hf b a) fun b' => TravMono.foldlM hf l b'

theorem TravMono.foldlM_array {f : β → γ → EraseT PureM β} (hf : ∀ b a, TravMono σ pc (f b a))
    (as : Array γ) (b : β) : TravMono σ pc (as.foldlM f b) := by
  rw [← Array.foldlM_toList]
  exact TravMono.foldlM hf _ _

theorem TravMono.forIn_rco {f : Nat → β → EraseT PureM (ForInStep β)}
    (hf : ∀ a b, TravMono σ pc (f a b)) (r : Std.Rco Nat) (b : β) :
    TravMono σ pc (ForIn.forIn r b f) := by
  rw [rco_forIn]
  exact TravMono.forIn hf _ _

theorem TravMono.forIn_subarray {f : Expr → β → EraseT PureM (ForInStep β)}
    (hf : ∀ a b, TravMono σ pc (f a b)) (s : Subarray Expr) (b : β) :
    TravMono σ pc (ForIn.forIn s b f) := by
  rw [subarray_forIn]
  exact TravMono.forIn hf _ _

theorem TravMono.optionMapM {f : γ → EraseT PureM β} (hf : ∀ a, TravMono σ pc (f a)) :
    ∀ o : Option γ, TravMono σ pc (o.mapM f)
  | none => TravMono.pure none
  | some a => TravMono.bind (hf a) fun _ => TravMono.pure _

theorem TravMono.withApp {k : Expr → Array Expr → EraseT PureM α}
    (hk : ∀ f as, TravMono σ pc (k f as)) (e : Expr) : TravMono σ pc (e.withApp k) := by
  unfold Expr.withApp
  rw [withAppAux_eq]
  exact hk _ _

theorem TravMono.panic [Inhabited α] (msg : String) :
    TravMono σ pc (_root_.panic msg : EraseT PureM α) := by
  intro st tc ps r st' ps' h; cases h; exact ⟨Nat.le_refl _, id⟩

theorem TravMono.panicWithPosWithDecl [Inhabited α] (mn dn : String) (line col : Nat)
    (msg : String) :
    TravMono σ pc (_root_.panicWithPosWithDecl mn dn line col msg : EraseT PureM α) := by
  intro st tc ps r st' ps' h; cases h; exact ⟨Nat.le_refl _, id⟩

theorem TravMono.getConst (n : Name) : TravMono σ pc (getConst (m := PureM) n) := by
  intro st tc ps r st' ps' h
  obtain ⟨-, rfl, rfl⟩ := getConst_run h
  exact ⟨Nat.le_refl _, id⟩

theorem TravMono.getOrFail {δ : Type} [Inhabited δ] (o : Option δ) (msg : String) :
    TravMono σ pc (getOrFail (m := PureM) o msg) := by
  intro st tc ps r st' ps' h
  obtain ⟨-, rfl, rfl⟩ := getOrFail_run h
  exact ⟨Nat.le_refl _, id⟩

/-- A run of an action that answers with the states unchanged. -/
theorem le_of_map {r : Except EraseError γ} {ps ps' : PureState} {a : γ}
    (h : r.map (·, ps) = .ok (a, ps')) : ps.next ≤ ps'.next := by
  cases r <;> cases h
  exact Nat.le_refl _

/-- The pure backend's `inferType` is the oracle's, at `oracleFuel`. -/
theorem inferType_run (lctx : LocalContext) (ls : List Local) (e : Expr) (ps : PureState) :
    ((Backend.inferType (m := PureM) lctx ls e).run pc).run ps =
      (Pure.inferType ⟨pc.decls⟩ oracleFuel ls [] e).map (·, ps) := by
  change (((match Pure.inferType ⟨pc.decls⟩ oracleFuel ls [] e with
    | .ok t => (Pure.pure t : PureM Expr) | .error err => throw err).run pc).run ps) = _
  cases Pure.inferType ⟨pc.decls⟩ oracleFuel ls [] e <;> rfl

/-- The pure backend's `whnf` is the oracle's, at `oracleFuel`. -/
theorem whnf_run (lctx : LocalContext) (ls : List Local) (e : Expr) (ps : PureState) :
    ((Backend.whnf (m := PureM) lctx ls e).run pc).run ps =
      (Pure.whnf ⟨pc.decls⟩ oracleFuel ls e).map (·, ps) := by
  change (((match Pure.whnf ⟨pc.decls⟩ oracleFuel ls e with
    | .ok t => (Pure.pure t : PureM Expr) | .error err => throw err).run pc).run ps) = _
  cases Pure.whnf ⟨pc.decls⟩ oracleFuel ls e <;> rfl

/-- `TravMono` as a Hoare triple on the state, at one context. -/
theorem TravMono.toHT {x : EraseT PureM α} (h : TravMono σ pc x) (tc : TravCtx) :
    HT tc pc (MasksOK σ) x (fun _ s => MasksOK σ s) :=
  fun st ps a st' ps' hI hr => (h st tc ps a st' ps' hr).2 hI

end

/-! ## The tactic, the helpers with continuations, `register_inductive` -/

set_option hygiene false in
/-- The counter after a lifted call of the pure backend (`h`): it advances only at
`freshFVarId`. -/
macro (name := _travMonoLift) "trav_mono_lift" : tactic => `(tactic| first
  | (cases h <;> first | exact Nat.le_refl _ | exact Nat.le_succ _)
  | (rw [isErasable_run] at h; exact le_of_map h)
  | (rw [typeLevel_run] at h; exact le_of_map h)
  | (rw [isPropFormerType_run] at h; exact le_of_map h)
  | (rw [inferType_run] at h; exact le_of_map h)
  | (rw [whnf_run] at h; exact le_of_map h))

set_option hygiene false in
/-- One step of `TravMono` over a body of the traversal: the induction hypothesis `ih`, the
closure lemmas (matched up to reducible unfolding), the helpers unfolded, a `match` or `if`
split. -/
macro (name := _travMonoStep) "trav_mono_step" : tactic => `(tactic| first
  | with_reducible exact ih.expr _ | with_reducible exact ih.lit _
  | with_reducible exact ih.lam _ | with_reducible exact ih.letE _
  | with_reducible exact ih.proj _ _ _ | with_reducible exact ih.app _
  | with_reducible exact ih.const _ | with_reducible exact ih.constApp _
  | with_reducible exact ih.recr _ _ | with_reducible exact ih.ctor _ _
  | with_reducible exact ih.appArgs _ _ | with_reducible exact ih.cases _ _
  | with_reducible exact ih.caseOf _ _ _ _ _ | with_reducible exact ih.alt _ _ _ _
  | with_reducible exact ih.kername _ | with_reducible exact ih.mutDecl _
  | with_reducible exact TravMono.pure _ | with_reducible exact TravMono.get
  | with_reducible exact TravMono.read | with_reducible exact TravMono.getConst _
  | with_reducible exact TravMono.getOrFail _ _
  | with_reducible exact TravMono.register_inductive hd _
  | with_reducible exact TravMono.panic _
  | with_reducible exact TravMono.panicWithPosWithDecl _ _ _ _ _
  | ((with_reducible refine TravMono.modify ?_); exact fun _ h => h)
  | ((with_reducible refine TravMono.liftM _ fun _ _ _ h => ?_); trav_mono_lift)
  | with_reducible refine TravMono.withApp (fun _ _ => ?_) _
  | with_reducible refine TravMono.etaGo (fun _ _ => ?_) _ _ _ _
  | with_reducible refine TravMono.lambdaOrIntroToArity _ _ (fun _ _ => ?_) _ _
  | with_reducible refine TravMono.forIn (fun _ _ => ?_) _ _
  | with_reducible refine TravMono.forIn_rco (fun _ _ => ?_) _ _
  | with_reducible refine TravMono.forIn_subarray (fun _ _ => ?_) _ _
  | with_reducible refine TravMono.mapM (fun _ => ?_) _
  | with_reducible refine TravMono.optionMapM (fun _ => ?_) _
  | with_reducible refine TravMono.foldlM_array (fun _ _ => ?_) _ _
  | with_reducible refine TravMono.withReader ?_
  | with_reducible refine TravMono.bind ?_ fun _ => ?_
  | with_reducible refine TravMono.ite ?_ ?_
  | with_reducible exact hk _ _
  | simp only [Erasure.withLocalDecl, Erasure.withLocalDef, Erasure.lambdaMonocular,
      Erasure.letMonocular, Erasure.forallMonocular, Erasure.lambdaMonocularOrIntro,
      Erasure.mkLambda, Erasure.mkLetIn, Erasure.mkAlt, Erasure.mkDef, Erasure.fvar_to_name,
      Erasure.addAxiom, Erasure.withAppEtaToMinArity]
  | split
  | dsimp only)

/-- `TravMono` over a body of the traversal. -/
macro (name := _travMono) "trav_mono" : tactic => `(tactic| repeat' trav_mono_step)

section
variable {σ : EvalEnv} {pc : PureCtx} {α : Type}

theorem TravMono.addAxiom (n : Name) : TravMono σ pc (addAxiom (m := PureM) n) := by
  unfold Erasure.addAxiom
  trav_mono

/-- `TravMono` of the η-expansion loop of `withAppEtaToMinArity`, for a continuation with
`TravMono`. -/
theorem TravMono.etaGo {arity : Nat} {k : Expr → Array Expr → EraseT PureM LBTerm}
    (hk : ∀ f as, TravMono σ pc (k f as)) : ∀ (n : Nat) (type f : Expr) (args : Array Expr),
      TravMono σ pc (withAppEtaToMinArity.go (m := PureM) arity k n type f args)
  | 0, _, _, _ => by rw [withAppEtaToMinArity.go]; trav_mono
  | n + 1, type, f, args => by
    rw [withAppEtaToMinArity.go]
    trav_mono

/-- `TravMono` of `lambdaOrIntroToArity`, for a continuation with `TravMono`. -/
theorem TravMono.lambdaOrIntroToArity [Inhabited α] :
    ∀ (n : Nat) (k : Expr → List FVarId → EraseT PureM α), (∀ e xs, TravMono σ pc (k e xs)) →
      ∀ e type, TravMono σ pc (lambdaOrIntroToArity (m := PureM) e type n k)
  | 0, k, hk, e, type => by rw [Erasure.lambdaOrIntroToArity]; exact hk _ _
  | n + 1, k, hk, e, type => by
    rw [Erasure.lambdaOrIntroToArity]
    trav_mono

/-- The mask that keeps every field of `n` fields keeps `n` fields. -/
theorem arrayCount_keep_replicate (n : Nat) :
    Array.count ConstructorArgRelevance.keep (Array.replicate n .keep) = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Array.replicate_succ, Array.count_push, ih]; rfl

/-- `register_inductive` at the pure backend keeps `MasksOK` and returns what the state registers
for the type: every type of the block it registers gets the masks of its constructors, which keep
every field (`Erasure.PureM`'s `argMask`, and the masks without `remove_irrel_constr_args`). -/
theorem register_inductive_masks (hd : pc.decls = σ.decls) (iv : InductiveVal) (tc : TravCtx) :
    HT tc pc (MasksOK σ) (register_inductive (m := PureM) iv)
      (fun r s => MasksOK σ s ∧ s.inductives[iv.name]? = some r) := by
  rw [Erasure.register_inductive]
  refine HT.bind HT.get fun s => ?_
  split
  · next iid hiid =>
    refine HT.pure fun s' ⟨h1, h2⟩ => ⟨h1, ?_⟩
    subst h2
    rwa [Std.HashMap.get?_eq_getElem?] at hiid
  · refine HT.bind (R := fun _ s' => MasksOK σ s') ?_ fun bodies => ?_
    · refine HT.mono (HT.mapM (I := fun _ s' => MasksOK σ s') (P := fun _ _ => True)
          (L := iv.all.zipIdx) (fun pre p rest _ => ?_) _ [] rfl) (fun _ h => h.1)
          fun _ _ h => h.1
      obtain ⟨n, j⟩ := p
      dsimp only
      refine HT.bind (HT.getConst _) fun ci => ?_
      split
      · next inf =>
        refine HT.of_fact fun hinf => ?_
        refine HT.bind (HT.mapM (I := fun _ s' => MasksOK σ s') (P := CtorOK pc)
          (L := inf.ctors) (fun pre' cn rest' _ => ?_) _ [] rfl) fun outs => ?_
        · refine HT.bind (HT.liftM _) fun a => HT.of_fact fun _ => ?_
          refine HT.read_bind ?_
          split
          · refine HT.bind (HT.liftM _) fun _ => HT.of_fact fun _ => ?_
            refine HT.bind (TravMono.toHT (TravMono.addAxiom _) tc) fun _ => ?_
            refine HT.bind (HT.getConst _) fun ci => ?_
            split
            · next cv =>
              refine HT.of_fact fun hcv => ?_
              repeat (with_reducible refine HT.read_bind ?_)
              split
              · first
                  | refine HT.bind (HT.read_bind (HT.liftM _)) fun am => HT.of_fact fun ham => ?_
                  | refine HT.bind (HT.liftM _) fun am => HT.of_fact fun ham => ?_
                obtain ⟨_, _, ham⟩ := ham
                cases ham
                exact HT.pure fun s hs => ⟨hs, cv, hcv, arrayCount_keep_replicate _, rfl⟩
              · refine HT.bind HT.pure_eq fun am => HT.of_fact fun ham => ?_
                subst ham
                exact HT.pure fun s hs => ⟨hs, cv, hcv, arrayCount_keep_replicate _, rfl⟩
            · exact HT.throwM _
          · refine HT.bind (HT.getConst _) fun ci => ?_
            split
            · next cv =>
              refine HT.of_fact fun hcv => ?_
              repeat (with_reducible refine HT.read_bind ?_)
              split
              · first
                  | refine HT.bind (HT.read_bind (HT.liftM _)) fun am => HT.of_fact fun ham => ?_
                  | refine HT.bind (HT.liftM _) fun am => HT.of_fact fun ham => ?_
                obtain ⟨_, _, ham⟩ := ham
                cases ham
                exact HT.pure fun s hs => ⟨hs, cv, hcv, arrayCount_keep_replicate _, rfl⟩
              · refine HT.bind HT.pure_eq fun am => HT.of_fact fun ham => ?_
                subst ham
                exact HT.pure fun s hs => ⟨hs, cv, hcv, arrayCount_keep_replicate _, rfl⟩
            · exact HT.throwM _
        · refine HT.of_fact fun hF => ?_
          have hlen := forall₂_length hF
          have hmask : KeepMasks σ inf outs.unzip.2 := by
            refine ⟨by simp [hlen], fun k cn cv hk hc => ?_⟩
            obtain ⟨out, hout, cv', hc', -, h2⟩ := forall₂_get hF hk
            rw [hd] at hc'
            have hcc : (some (ConstantInfo.ctorInfo cv') : Option ConstantInfo) =
                some (.ctorInfo cv) := hc'.symm.trans hc
            cases hcc
            simp [List.unzip_snd, hout, h2]
          have hins : ∀ (id : InductiveId) (masks : InductiveArgMasks), KeepMasks σ inf masks →
              ∀ s : ErasureState, MasksOK σ s →
                MasksOK σ { s with inductives := s.inductives.insert n (id, masks) } := by
            intro id masks hm s hs T r hT
            rw [Std.HashMap.getElem?_insert] at hT
            split at hT
            · next hnT =>
              cases hT
              rw [← beq_iff_eq.1 hnT]
              exact ⟨inf, hd ▸ hinf, hm⟩
            · exact hs T r hT
          refine HT.mono (TravMono.toHT ?_ tc) (fun _ h => h) fun _ _ h => ⟨h, trivial⟩
          trav_mono
          all_goals refine TravMono.modify (hins _ _ ?_)
          all_goals exact hmask
      · exact HT.throwM _
    · refine HT.bind (HT.modify _) fun _ => HT.bind HT.get fun s₂ => ?_
      refine HT.mono (HT.getOrFail _ _) (fun _ h => h) fun r s₃ ⟨⟨h₃, h₄⟩, h₅⟩ => ?_
      obtain ⟨s₀, hs₀, rfl⟩ := h₃
      subst h₄
      exact ⟨hs₀, h₅⟩

/-- `register_inductive` allocates no variable and keeps `MasksOK`. -/
theorem TravMono.register_inductive (hd : pc.decls = σ.decls) (iv : InductiveVal) :
    TravMono σ pc (register_inductive (m := PureM) iv) := by
  intro st tc ps r st' ps' h
  rw [KeepsPS.register_inductive iv _ _ _ _ _ _ h]
  exact ⟨Nat.le_refl _, fun hm => (register_inductive_masks hd iv tc st ps r st' ps' hm h).1⟩

end

/-! ## The functions of the traversal -/

/-- `TravMono` of the sixteen functions of the traversal at the fuel `fuel`. -/
structure TravMonoAt (σ : EvalEnv) (pc : PureCtx) (fuel : Nat) : Prop where
  expr : ∀ e, TravMono σ pc (visitExpr (m := PureM) fuel e)
  lit : ∀ l, TravMono σ pc (visitLiteral (m := PureM) fuel l)
  lam : ∀ e, TravMono σ pc (visitLambda (m := PureM) fuel e)
  letE : ∀ e, TravMono σ pc (visitLet (m := PureM) fuel e)
  proj : ∀ s i e, TravMono σ pc (visitProj (m := PureM) fuel s i e)
  app : ∀ e, TravMono σ pc (visitApp (m := PureM) fuel e)
  const : ∀ e, TravMono σ pc (visitConst (m := PureM) fuel e)
  constApp : ∀ e, TravMono σ pc (visitConstApp (m := PureM) fuel e)
  recr : ∀ r e, TravMono σ pc (visitRec (m := PureM) fuel r e)
  ctor : ∀ c args, TravMono σ pc (visitConstructor (m := PureM) fuel c args)
  appArgs : ∀ f args, TravMono σ pc (visitAppArgs (m := PureM) fuel f args)
  cases : ∀ ci args, TravMono σ pc (visitCases (m := PureM) fuel ci args)
  caseOf : ∀ iv alts idx ca d, TravMono σ pc (visitCasesOn (m := PureM) fuel iv alts idx ca d)
  alt : ∀ n mask vals e, TravMono σ pc (visitAlt (m := PureM) fuel n mask vals e)
  kername : ∀ n, TravMono σ pc (get_constant_kername (m := PureM) fuel n)
  mutDecl : ∀ n, TravMono σ pc (visitMutual (m := PureM) fuel n)

section
variable {σ : EvalEnv} {pc : PureCtx} {n : Nat}

/-- `TravMono` of `visitExpr` at a successor fuel, from `TravMonoAt` at the fuel before. -/
theorem travMono_visitExpr (ih : TravMonoAt σ pc n) (e : Expr) :
    TravMono σ pc (visitExpr (m := PureM) (n + 1) e) := by
  cases e <;> rw [Erasure.visitExpr] <;> trav_mono

/-- `TravMono` of `visitLiteral` at a successor fuel, from `TravMonoAt` at the fuel before. -/
theorem travMono_visitLiteral (ih : TravMonoAt σ pc n) (l : Literal) :
    TravMono σ pc (visitLiteral (m := PureM) (n + 1) l) := by
  rw [Erasure.visitLiteral.eq_2]
  trav_mono

/-- `TravMono` of `visitLambda` at a successor fuel, from `TravMonoAt` at the fuel before. -/
theorem travMono_visitLambda (ih : TravMonoAt σ pc n) (e : Expr) :
    TravMono σ pc (visitLambda (m := PureM) (n + 1) e) := by
  rw [Erasure.visitLambda.eq_2]
  trav_mono

/-- `TravMono` of `visitLet` at a successor fuel, from `TravMonoAt` at the fuel before. -/
theorem travMono_visitLet (ih : TravMonoAt σ pc n) (e : Expr) :
    TravMono σ pc (visitLet (m := PureM) (n + 1) e) := by
  rw [Erasure.visitLet.eq_2]
  trav_mono

/-- `TravMono` of `visitProj` at a successor fuel, from `TravMonoAt` at the fuel before. -/
theorem travMono_visitProj (hd : pc.decls = σ.decls) (ih : TravMonoAt σ pc n) (s : Name) (i : Nat)
    (e : Expr) :
    TravMono σ pc (visitProj (m := PureM) (n + 1) s i e) := by
  rw [Erasure.visitProj.eq_2]
  trav_mono

/-- `TravMono` of `visitApp` at a successor fuel, from `TravMonoAt` at the fuel before. -/
theorem travMono_visitApp (ih : TravMonoAt σ pc n) (e : Expr) :
    TravMono σ pc (visitApp (m := PureM) (n + 1) e) := by
  rw [Erasure.visitApp.eq_2]
  trav_mono

/-- `TravMono` of `visitConst` at a successor fuel, from `TravMonoAt` at the fuel before. -/
theorem travMono_visitConst (ih : TravMonoAt σ pc n) (e : Expr) :
    TravMono σ pc (visitConst (m := PureM) (n + 1) e) := by
  cases e <;> rw [Erasure.visitConst]
  all_goals first | (intro _ _ h; cases h; done) | trav_mono

/-- `TravMono` of `visitConstApp` at a successor fuel, from `TravMonoAt` at the fuel before. -/
theorem travMono_visitConstApp (ih : TravMonoAt σ pc n) (e : Expr) :
    TravMono σ pc (visitConstApp (m := PureM) (n + 1) e) := by
  rw [Erasure.visitConstApp.eq_2]
  trav_mono

/-- `TravMono` of `visitRec` at a successor fuel, from `TravMonoAt` at the fuel before. -/
theorem travMono_visitRec (hd : pc.decls = σ.decls) (ih : TravMonoAt σ pc n) (r : RecursorVal)
    (e : Expr) :
    TravMono σ pc (visitRec (m := PureM) (n + 1) r e) := by
  rw [Erasure.visitRec.eq_2]
  trav_mono

/-- `TravMono` of `visitConstructor` at a successor fuel, from `TravMonoAt` at the fuel
before. -/
theorem travMono_visitConstructor (hd : pc.decls = σ.decls) (ih : TravMonoAt σ pc n) (c : Name)
    (args : Array Expr) :
    TravMono σ pc (visitConstructor (m := PureM) (n + 1) c args) := by
  rw [Erasure.visitConstructor.eq_2]
  trav_mono

/-- `TravMono` of `visitAppArgs` at a successor fuel, from `TravMonoAt` at the fuel before. -/
theorem travMono_visitAppArgs (ih : TravMonoAt σ pc n) (f : LBTerm) (args : Array Expr) :
    TravMono σ pc (visitAppArgs (m := PureM) (n + 1) f args) := by
  rw [Erasure.visitAppArgs.eq_2]
  trav_mono

/-- `TravMono` of `visitCases` at a successor fuel, from `TravMonoAt` at the fuel before. -/
theorem travMono_visitCases (ih : TravMonoAt σ pc n) (ci : CasesInfo) (args : Array Expr) :
    TravMono σ pc (visitCases (m := PureM) (n + 1) ci args) := by
  rw [Erasure.visitCases.eq_2]
  trav_mono

/-- `TravMono` of `visitCasesOn` at a successor fuel, from `TravMonoAt` at the fuel before. -/
theorem travMono_visitCasesOn (hd : pc.decls = σ.decls) (ih : TravMonoAt σ pc n) (iv : InductiveVal)
    (alts : Std.HashMap Name (Nat × Expr)) (idx : Std.HashMap Name (List (Option Expr)))
    (ca : Option (Nat × Expr)) (d : LBTerm) :
    TravMono σ pc (visitCasesOn (m := PureM) (n + 1) iv alts idx ca d) := by
  cases ca <;> rw [Erasure.visitCasesOn] <;> trav_mono

/-- `TravMono` of `visitAlt` at a successor fuel, from `TravMonoAt` at the fuel before. -/
theorem travMono_visitAlt (ih : TravMonoAt σ pc n) (k : Nat) (mask : ConstructorArgMask)
    (vals : List (Option Expr)) (e : Expr) :
    TravMono σ pc (visitAlt (m := PureM) (n + 1) k mask vals e) := by
  rw [Erasure.visitAlt.eq_2]
  trav_mono

/-- `TravMono` of `get_constant_kername` at a successor fuel, from `TravMonoAt` at the fuel
before. -/
theorem travMono_get_constant_kername (ih : TravMonoAt σ pc n) (c : Name) :
    TravMono σ pc (get_constant_kername (m := PureM) (n + 1) c) := by
  rw [Erasure.get_constant_kername.eq_2]
  trav_mono

/-- `TravMono` of `visitMutual` at a successor fuel, from `TravMonoAt` at the fuel before. -/
theorem travMono_visitMutual (ih : TravMonoAt σ pc n) (c : Name) :
    TravMono σ pc (visitMutual (m := PureM) (n + 1) c) := by
  rw [Erasure.visitMutual.eq_2]
  trav_mono

end

/-- Every run of every function of the traversal at the pure backend, at every fuel, does not
decrease the counter of fresh variables and keeps the registered masks keeping every field
(`MasksOK`), over a context whose declarations are `σ`'s. Reference: none (DV-13, DV-23). -/
theorem travMonoAt {σ : EvalEnv} {pc : PureCtx} (hd : pc.decls = σ.decls) :
    ∀ fuel, TravMonoAt σ pc fuel
  | 0 => by
    constructor <;> intros <;>
      simp only [Erasure.visitExpr.eq_1, Erasure.visitLiteral.eq_1, Erasure.visitLambda.eq_1,
        Erasure.visitLet.eq_1, Erasure.visitProj.eq_1, Erasure.visitApp.eq_1,
        Erasure.visitConst.eq_1, Erasure.visitConstApp.eq_1, Erasure.visitRec.eq_1,
        Erasure.visitConstructor.eq_1, Erasure.visitAppArgs.eq_1, Erasure.visitCases.eq_1,
        Erasure.visitCasesOn.eq_1, Erasure.visitAlt.eq_1, Erasure.get_constant_kername.eq_1,
        Erasure.visitMutual.eq_1] <;>
      trav_mono
  | n + 1 => by
    have ih := travMonoAt hd n
    exact ⟨travMono_visitExpr ih, travMono_visitLiteral ih, travMono_visitLambda ih,
      travMono_visitLet ih, travMono_visitProj hd ih, travMono_visitApp ih, travMono_visitConst ih,
      travMono_visitConstApp ih, travMono_visitRec hd ih, travMono_visitConstructor hd ih,
      travMono_visitAppArgs ih, travMono_visitCases ih, travMono_visitCasesOn hd ih,
      travMono_visitAlt ih, travMono_get_constant_kername ih, travMono_visitMutual ih⟩

end Steps

end EraseProof
