import EraseProof.Core.RegisterInd

/-!
# Runs of the traversal's environment helpers at the pure backend

`getConst`, `getOrFail`, the backend's `inferType` and `isExtern`, and the counter: the
environment and bookkeeping actions that `visitConstructor`, `visitProj` and
`withAppEtaToMinArity` (`LeanToLambdaBox/Erasure.lean`) run, and `register_inductive` allocates
no free variable (`KeepsPS.register_inductive`). Copy of `ML-V Core/StepsCtor.lean:41-207`.
-/

open Lean Erasure

namespace EraseProof

namespace Steps

open RegisterInd

section
variable {pc : PureCtx}

/-- A run of `getConst` at the pure backend: the declaration of the closure, states unchanged.
Copy of `ML-V Core/StepsCtor.lean:42`. -/
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

/-- A successful run of `getConst` found the declaration and kept both states. Copy of
`ML-V Core/StepsCtor.lean:54`. -/
theorem getConst_run {n : Name} {tc : TravCtx} {st st' : ErasureState} {ps ps' : PureState}
    {ci : ConstantInfo}
    (h : (getConst (m := PureM) n).runPure st tc pc ps = .ok ((ci, st'), ps')) :
    findConst pc.decls n = some ci ∧ st' = st ∧ ps' = ps := by
  rw [getConst_eq] at h
  split at h
  · cases h; exact ⟨‹_›, rfl, rfl⟩
  · cases h

/-- A run of `x` at the pure backend that keeps the counter. Copy of
`ML-V Core/StepsCtor.lean:64`. -/
def KeepsPS (pc : PureCtx) {α : Type} (x : EraseT PureM α) : Prop :=
  ∀ st tc ps r st' ps', x.runPure st tc pc ps = .ok ((r, st'), ps') → ps' = ps

theorem KeepsPS.pure {α : Type} (a : α) : KeepsPS pc (Pure.pure a : EraseT PureM α) := by
  intro st tc ps r st' ps' h; cases h; rfl

theorem KeepsPS.bind {α β : Type} {x : EraseT PureM α} {k : α → EraseT PureM β}
    (hx : KeepsPS pc x) (hk : ∀ a, KeepsPS pc (k a)) : KeepsPS pc (x >>= k) := by
  intro st tc ps r st' ps' h
  rw [runPure_bind] at h
  obtain ⟨⟨⟨a, st₁⟩, ps₁⟩, h1, h2⟩ := ok_of_bind h
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
  obtain ⟨⟨a, ps₁⟩, h1, h2⟩ := ok_of_bind h
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

/-- `register_inductive` allocates no free variable. Copy of `ML-V Core/StepsCtor.lean:151`. -/
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

/-- The pure backend's `inferType` is the oracle's, at `oracleFuel`. Copy of
`ML-V Core/StepsCtor.lean:180`. -/
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

/-- The pure backend's `isExtern` reads the view. Copy of `ML-V Core/StepsCtor.lean:194`. -/
theorem isExtern_runPure {n : Name} {tc : TravCtx} {st : ErasureState} {ps : PureState} :
    (liftM (Backend.isExtern (m := PureM) n) : EraseT PureM Bool).runPure st tc pc ps =
      .ok ((pc.view.isExtern n, st), ps) := rfl

/-- A successful `getOrFail` returns the option's value and keeps both states. Copy of
`ML-V Core/StepsCtor.lean:199`. -/
theorem getOrFail_run {γ : Type} [Inhabited γ] {o : Option γ} {msg : String} {tc : TravCtx}
    {st st' : ErasureState} {ps ps' : PureState} {a : γ}
    (h : (getOrFail (m := PureM) o msg).runPure st tc pc ps = .ok ((a, st'), ps')) :
    o = some a ∧ st' = st ∧ ps' = ps := by
  cases o with
  | some b => cases h; exact ⟨rfl, rfl, rfl⟩
  | none => cases h

end

end Steps

end EraseProof
