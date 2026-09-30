import EraseProof.Core.FrameA

/-!
# The traversal's frame lemmas

The traversal `Erasure.visitExpr` and the functions it calls (`LeanToLambdaBox/Erasure.lean`), run
at the pure backend `Erasure.PureM` over closed declarations (`EraseProof.ClosedDecls`), give the
same result under two lists of locals that agree on a set `S` of free variables containing the
visited term's and closed under the locals' types and values (`EraseProof.LocalsSupport`,
`EraseProof.LocalsAgree`): `EraseProof.visit_agree`, a corollary of one induction on the fuel,
`EraseProof.traversal_agree`, which assembles the steps of `Core/FrameA.lean` with the steps below
for `Erasure.visitExpr`, `Erasure.visitAppArgs`, `Erasure.visitConst`,
`Erasure.get_constant_kername` and `Erasure.visitMutual`; the runs of the last three do not depend
on the locals at all (`EraseProof.LocalsBlind`).

Reference: none; MetaRocq erases a constant body in the empty context
(`MR E/ErasureFunction.v:1309 erase_constant_body`), where this traversal keeps the caller's locals
(DV-13).
-/

open Lean Lean4Lean Erasure

namespace EraseProof

variable {α β : Type} {pc : PureCtx}

/-! ## Actions that do not read the locals -/

/-- The runs of `x` at the pure backend over `pc` are the same under any two lists of locals, from
any traversal state, reader context and backend state. Reference: none (DV-13). -/
def LocalsBlind (pc : PureCtx) (x : EraseT PureM α) : Prop :=
  ∀ (st : ErasureState) (ps : PureState) (tc : TravCtx) (ls₁ ls₂ : List Local),
    x.runPure st { tc with locals := ls₁ } pc ps = x.runPure st { tc with locals := ls₂ } pc ps

/-- A bind does not read the locals when its first action does not and the continuation does not
on each result that a run of the first action can return. Reference: none. -/
theorem LocalsBlind.bind {x : EraseT PureM α} {k : α → EraseT PureM β} (hx : LocalsBlind pc x)
    (hk : ∀ a, (∃ st tc ps st' ps', x.runPure st tc pc ps = .ok ((a, st'), ps')) →
      LocalsBlind pc (k a)) :
    LocalsBlind pc (x >>= k) := fun st ps tc ls₁ ls₂ =>
  runPure_bind_agree (hx st ps tc ls₁ ls₂) fun a st' ps' h =>
    hk a ⟨_, _, _, _, _, h⟩ st' ps' tc ls₁ ls₂

/-- A bind on `read` does not read the locals when the continuation does not, and the
continuation depends on the reader context only through its fields other than the locals.
Reference: none. -/
theorem LocalsBlind.read_bind {k : TravCtx → EraseT PureM α} (hk : ∀ c, LocalsBlind pc (k c))
    (hk' : ∀ (tc : TravCtx) (ls₁ ls₂ : List Local),
      k { tc with locals := ls₁ } = k { tc with locals := ls₂ }) :
    LocalsBlind pc (read >>= k) := fun st ps tc ls₁ ls₂ => by
  rw [runPure_read_bind, runPure_read_bind, hk' tc ls₁ ls₂]
  exact hk _ st ps tc ls₁ ls₂

/-- Setting the fixpoint variables of the reader context keeps an action from reading the
locals. Reference: none. -/
theorem LocalsBlind.withReader {x : EraseT PureM α} (X : Option (Std.HashMap Name FVarId))
    (hx : LocalsBlind pc x) :
    LocalsBlind pc (withReader (fun env => { env with fixvars := X }) x) :=
  fun st ps tc ls₁ ls₂ => by
    rw [runPure_withReader, runPure_withReader]
    exact hx st ps { tc with fixvars := X } ls₁ ls₂

/-- `pure` does not read the locals. Reference: none. -/
theorem LocalsBlind.pure (a : α) : LocalsBlind pc (Pure.pure a : EraseT PureM α) :=
  fun _ _ _ _ _ => rfl

/-- `get` does not read the locals. Reference: none. -/
theorem LocalsBlind.get : LocalsBlind pc (MonadState.get : EraseT PureM ErasureState) :=
  fun _ _ _ _ _ => rfl

/-- `modify` does not read the locals. Reference: none. -/
theorem LocalsBlind.modify (f : ErasureState → ErasureState) :
    LocalsBlind pc (_root_.modify f : EraseT PureM PUnit) :=
  fun _ _ _ _ _ => rfl

/-- An action of the backend lifted to the traversal does not read the locals. Reference: none. -/
theorem LocalsBlind.liftM (y : PureM α) : LocalsBlind pc (_root_.liftM y : EraseT PureM α) :=
  fun _ _ _ _ _ => rfl

/-- A conditional does not read the locals when its branches do not. Reference: none. -/
theorem LocalsBlind.ite {c : Prop} [Decidable c] {a b : EraseT PureM α}
    (ha : c → LocalsBlind pc a) (hb : ¬c → LocalsBlind pc b) :
    LocalsBlind pc (if c then a else b) := by
  by_cases h : c
  · rw [if_pos h]; exact ha h
  · rw [if_neg h]; exact hb h

/-- `List.mapM` does not read the locals when the mapped action does not on any element.
Reference: none. -/
theorem LocalsBlind.mapM {f : α → EraseT PureM β} :
    ∀ {l : List α}, (∀ a ∈ l, LocalsBlind pc (f a)) → LocalsBlind pc (l.mapM f)
  | [], _ => by rw [List.mapM_nil]; exact .pure _
  | a :: l, h => by
    rw [List.mapM_cons]
    exact .bind (h a (.head _)) fun _ _ =>
      .bind (mapM fun b hb => h b (.tail _ hb)) fun _ _ => .pure _

/-- A `for` loop over a list does not read the locals when its body does not on any element and
loop state. Reference: none. -/
theorem LocalsBlind.forIn {f : α → β → EraseT PureM (ForInStep β)} :
    ∀ {l : List α} {b : β}, (∀ a ∈ l, ∀ b, LocalsBlind pc (f a b)) →
      LocalsBlind pc (forIn l b f)
  | [], b, _ => by rw [List.forIn_nil]; exact .pure _
  | a :: l, b, h => by
    rw [List.forIn_cons]
    refine .bind (h a (.head _) b) fun r _ => ?_
    cases r with
    | done => exact .pure _
    | yield b' => exact forIn fun c hc => h c (.tail _ hc)

/-- `Erasure.getConst` does not read the locals. Reference: none. -/
theorem LocalsBlind.getConst (n : Name) : LocalsBlind pc (getConst (m := PureM) n) := by
  unfold Erasure.getConst
  refine .bind (.liftM _) fun r _ => ?_
  cases r with
  | some => exact .pure _
  | none => exact fun _ _ _ _ _ => rfl

/-- `Erasure.addAxiom` does not read the locals. Reference: none. -/
theorem LocalsBlind.addAxiom (n : Name) : LocalsBlind pc (addAxiom (m := PureM) n) := by
  unfold Erasure.addAxiom
  refine .bind .get fun s _ => ?_
  dsimp only
  split
  · exact .bind (fun _ _ _ _ _ => rfl) fun _ _ => .modify _
  · exact .modify _

/-- `Erasure.mkDef`, which reads the fixpoint variables of the reader context, does not read the
locals. Reference: none. -/
theorem LocalsBlind.mkDef (n : Name) (xs : List Name) (t : LBTerm) :
    LocalsBlind pc (mkDef (m := PureM) n xs t) := by
  unfold Erasure.mkDef
  dsimp only
  refine .bind (.forIn fun a _ b => ?_) fun _ _ => .pure _
  exact .read_bind (fun c => .pure _) fun _ _ _ => rfl

/-! ## What `visitMutual` visits -/

/-- `value!` is `value?`'s value, or `default`, a constant, without one. Reference: none. -/
theorem value!_eq (ci : ConstantInfo) :
    ci.value! (allowOpaque := true) =
      (ci.value? (allowOpaque := true)).getD (.const `_inhabitedExprDummy []) := by
  cases ci <;> rfl

/-- Over closed declarations, the term `value!` of a declaration, or of any constant info without
a value, has no free variable. Reference: none (closed PCUIC declarations; DV-13). -/
theorem closed_value! (hcl : ClosedDecls pc.decls) {ci : ConstantInfo}
    (hci : ci ∈ pc.decls ∨ ci.value? (allowOpaque := true) = none) :
    FVarsIn (fun _ => False) (ci.value! (allowOpaque := true)) := by
  rw [value!_eq]
  cases hv : ci.value? (allowOpaque := true) with
  | none => intro u hu; cases hu
  | some v =>
    rcases hci with hci | hci
    · exact (hcl ci hci).2 v hv
    · rw [hv] at hci; cases hci

/-- The declaration that `visitMutual` reads through `Erasure.PureM.declInfo?` is a declaration of
`pc`, or `default`, which has no value. Reference: none. -/
theorem findConst_get!_mem (n : Name) :
    (findConst pc.decls n).get! ∈ pc.decls ∨
      (findConst pc.decls n).get!.value? (allowOpaque := true) = none := by
  cases h : findConst pc.decls n with
  | none => exact .inr rfl
  | some ci => exact .inl (List.mem_of_find?_eq_some h)

/-- A declaration that a run of `Erasure.getConst` returns at the pure backend is a declaration of
`pc`. Reference: none. -/
theorem getConst_yields {n : Name} {ci : ConstantInfo}
    (h : ∃ st tc ps st' ps',
      (getConst (m := PureM) n).runPure st tc pc ps = .ok ((ci, st'), ps')) :
    ci ∈ pc.decls ∨ ci.value? (allowOpaque := true) = none := by
  obtain ⟨st, tc, ps, st', ps', h⟩ := h
  refine .inl ?_
  unfold getConst at h
  rw [runPure_bind, runPure_liftM] at h
  cases hc : findConst pc.decls n with
  | none =>
    have : ((Backend.findConst? (m := PureM) n).run pc).run ps = .ok (none, ps) := by
      show Except.ok (findConst pc.decls n, ps) = _; rw [hc]
    rw [this] at h
    cases h
  | some ci' =>
    have : ((Backend.findConst? (m := PureM) n).run pc).run ps = .ok (some ci', ps) := by
      show Except.ok (findConst pc.decls n, ps) = _; rw [hc]
    rw [this] at h
    cases h
    exact List.mem_of_find?_eq_some hc

/-- A run of the pure backend's `prepare` returns the term it is given. Reference: none. -/
theorem prepare_yields {cfg : ErasureConfig} {e a : Expr}
    (h : ∃ st tc ps st' ps',
      (_root_.liftM (Backend.prepare (m := PureM) cfg e) : EraseT PureM Expr).runPure st tc pc ps =
        .ok ((a, st'), ps')) : a = e := by
  obtain ⟨st, tc, ps, st', ps', h⟩ := h
  cases h
  rfl

/-! ## Steps -/

/-- One unfolding of `Erasure.visitMutual` at the pure backend does not read the locals, given
that `Erasure.visitExpr` at one less fuel does not on closed terms (`ih`): every term it visits is
the value of a declaration of `pc` (`EraseProof.ClosedDecls`), and every other action reads the
reader context only for its configuration and fixpoint variables. Reference: none;
`MR E/ErasureFunction.v:1309 erase_constant_body` erases a constant body in the empty context
(DV-13). -/
theorem visitMutual_step {fuel : Nat} (hcl : ClosedDecls pc.decls)
    (ih : ∀ {tc : TravCtx} {st : ErasureState} {ps : PureState} {ls₁ ls₂ : List Local}
      {e : Expr}, FVarsIn (fun _ => False) e →
      (visitExpr (m := PureM) fuel e).runPure st { tc with locals := ls₁ } pc ps =
        (visitExpr (m := PureM) fuel e).runPure st { tc with locals := ls₂ } pc ps)
    (n : Name) : LocalsBlind pc (visitMutual (m := PureM) (fuel + 1) n) := by
  rw [visitMutual]
  refine .bind (.liftM _) fun r hr => ?_
  obtain ⟨_, _, _, _, _, h⟩ := hr
  cases h
  dsimp only
  repeat' first
    | with_reducible_and_instances first
      | exact LocalsBlind.pure _
      | exact LocalsBlind.get
      | exact LocalsBlind.modify _
      | exact LocalsBlind.liftM _
      | exact LocalsBlind.getConst _
      | exact LocalsBlind.addAxiom _
      | exact LocalsBlind.mkDef _ _ _
      | refine LocalsBlind.read_bind (fun _ => ?_) (fun _ _ _ => rfl)
      | refine LocalsBlind.withReader _ ?_
      | refine LocalsBlind.mapM (fun _ _ => ?_)
      | refine LocalsBlind.forIn (fun _ _ _ => ?_)
      | refine LocalsBlind.bind ?_ (fun _ _ => ?_)
      | refine LocalsBlind.ite (fun _ => ?_) (fun _ => ?_)
    | split
  all_goals
    rename_i hprep
    obtain rfl := prepare_yields hprep
    refine fun st ps tc ls₁ ls₂ => ih ?_
    first
    | exact closed_value! hcl (findConst_get!_mem _)
    | exact closed_value! hcl (getConst_yields ‹_›)

/-- One unfolding of `Erasure.get_constant_kername` at the pure backend does not read the locals,
given that `Erasure.visitMutual` at one less fuel does not (`ih`). Reference: none; the `tConst`
case of `MR E/ErasureFunction.v:989 erase` (DV-13). -/
theorem get_constant_kername_step {fuel : Nat}
    (ih : ∀ n, LocalsBlind pc (visitMutual (m := PureM) fuel n)) (n : Name) :
    LocalsBlind pc (get_constant_kername (m := PureM) (fuel + 1) n) := by
  rw [get_constant_kername]
  refine .bind .get fun s _ => ?_
  split
  · exact .pure _
  · exact .bind (ih _) fun _ _ => .bind .get fun _ _ => .pure _

/-- One unfolding of `Erasure.visitConst` at the pure backend does not read the locals, given that
`Erasure.get_constant_kername` at one less fuel does not (`ih`): it reads the reader context only
for the fixpoint variables. Reference: none; the `tConst` case of
`MR E/ErasureFunction.v:989 erase` (DV-13). -/
theorem visitConst_step {fuel : Nat}
    (ih : ∀ n, LocalsBlind pc (get_constant_kername (m := PureM) fuel n)) (e : Expr) :
    LocalsBlind pc (visitConst (m := PureM) (fuel + 1) e) := by
  cases e with
  | const d us =>
    rw [visitConst]
    refine .read_bind (fun c => ?_) (fun _ _ _ => rfl)
    split
    · exact .pure _
    · exact .bind (ih _) fun _ _ => .pure _
  | _ => exact fun _ _ _ _ _ => rfl

/-- One unfolding of `Erasure.visitAppArgs` at the pure backend runs alike under two lists of
locals that agree on `S`, given the same property of `Erasure.visitExpr` at one less fuel (`ih`)
and arguments with free variables in `S`. Reference: none; the `tApp` case of
`MR E/ErasureFunction.v:989 erase` (`:1009`) (DV-13). -/
theorem visitAppArgs_step {S : FVarId → Prop} {tc : TravCtx} {st : ErasureState}
    {ps : PureState} {ls₁ ls₂ : List Local} {fuel : Nat} {f : LBTerm} {args : Array Expr}
    (ih : ∀ {S : FVarId → Prop} {tc : TravCtx} {st : ErasureState} {ps : PureState}
      {ls₁ ls₂ : List Local} {e : Expr}, LocalsSupport S ls₁ → LocalsAgree S ls₁ ls₂ →
      FVarsIn S e →
      (visitExpr (m := PureM) fuel e).runPure st { tc with locals := ls₁ } pc ps =
        (visitExpr (m := PureM) fuel e).runPure st { tc with locals := ls₂ } pc ps)
    (hS : LocalsSupport S ls₁) (hag : LocalsAgree S ls₁ ls₂) (he : ∀ a ∈ args, FVarsIn S a) :
    (visitAppArgs (m := PureM) (fuel + 1) f args).runPure st { tc with locals := ls₁ } pc ps =
      (visitAppArgs (m := PureM) (fuel + 1) f args).runPure st { tc with locals := ls₂ } pc ps := by
  rw [visitAppArgs, ← Array.foldlM_toList]
  have he' : ∀ a ∈ args.toList, FVarsIn S a := fun a ha => he a (Array.mem_toList_iff.mp ha)
  generalize args.toList = l at he'
  induction l generalizing f st ps with
  | nil => rfl
  | cons a l ihl =>
    rw [List.foldlM_cons]
    exact runPure_bind_agree
      (runPure_bind_agree (ih hS hag (he' a (.head _))) fun _ _ _ _ => rfl)
      fun _ _ _ _ => ihl fun b hb => he' b (.tail _ hb)

/-- One unfolding of `Erasure.visitExpr` at the pure backend runs alike under two lists of locals
that agree on `S`, given the same property, at one less fuel, of `Erasure.visitExpr` (`ihE`, for
metadata), `Erasure.visitLambda` (`ihL`), `Erasure.visitLet` (`ihLt`) and `Erasure.visitApp`
(`ihA`, for applications and constants): the oracle call agrees (`EraseProof.oracle_agree`); a
projection or a literal is never answered `false` by the oracle, whose type inference fails on
them; the other branches do not read the locals. Reference: none; the cases of
`MR E/ErasureFunction.v:989 erase` (DV-13). -/
theorem visitExpr_step {S : FVarId → Prop} {tc : TravCtx} {st : ErasureState} {ps : PureState}
    {ls₁ ls₂ : List Local} {fuel : Nat} {e : Expr} (hcl : ClosedDecls pc.decls)
    (ihE : ∀ {S : FVarId → Prop} {tc : TravCtx} {st : ErasureState} {ps : PureState}
      {ls₁ ls₂ : List Local} {e : Expr}, LocalsSupport S ls₁ → LocalsAgree S ls₁ ls₂ →
      FVarsIn S e →
      (visitExpr (m := PureM) fuel e).runPure st { tc with locals := ls₁ } pc ps =
        (visitExpr (m := PureM) fuel e).runPure st { tc with locals := ls₂ } pc ps)
    (ihL : ∀ {S : FVarId → Prop} {tc : TravCtx} {st : ErasureState} {ps : PureState}
      {ls₁ ls₂ : List Local} {e : Expr}, LocalsSupport S ls₁ → LocalsAgree S ls₁ ls₂ →
      FVarsIn S e →
      (visitLambda (m := PureM) fuel e).runPure st { tc with locals := ls₁ } pc ps =
        (visitLambda (m := PureM) fuel e).runPure st { tc with locals := ls₂ } pc ps)
    (ihLt : ∀ {S : FVarId → Prop} {tc : TravCtx} {st : ErasureState} {ps : PureState}
      {ls₁ ls₂ : List Local} {e : Expr}, LocalsSupport S ls₁ → LocalsAgree S ls₁ ls₂ →
      FVarsIn S e →
      (visitLet (m := PureM) fuel e).runPure st { tc with locals := ls₁ } pc ps =
        (visitLet (m := PureM) fuel e).runPure st { tc with locals := ls₂ } pc ps)
    (ihA : ∀ {S : FVarId → Prop} {tc : TravCtx} {st : ErasureState} {ps : PureState}
      {ls₁ ls₂ : List Local} {e : Expr}, LocalsSupport S ls₁ → LocalsAgree S ls₁ ls₂ →
      FVarsIn S e →
      (visitApp (m := PureM) fuel e).runPure st { tc with locals := ls₁ } pc ps =
        (visitApp (m := PureM) fuel e).runPure st { tc with locals := ls₂ } pc ps)
    (hS : LocalsSupport S ls₁) (hag : LocalsAgree S ls₁ ls₂) (he : FVarsIn S e) :
    (visitExpr (m := PureM) (fuel + 1) e).runPure st { tc with locals := ls₁ } pc ps =
      (visitExpr (m := PureM) (fuel + 1) e).runPure st { tc with locals := ls₂ } pc ps := by
  have fails : ∀ {e'}, Pure.isErasable ⟨pc.decls⟩ oracleFuel ls₁ e' =
      .error (.outOfFragment "literal, projection or metavariable") →
      Pure.isErasable ⟨pc.decls⟩ oracleFuel ls₁ e' ≠ .ok false :=
    fun h h' => nomatch h.symm.trans h'
  cases e with
  | app | const => rw [visitExpr]; exact oracle_agree hcl hS hag he fun _ => ihA hS hag he
  | lam => rw [visitExpr]; exact oracle_agree hcl hS hag he fun _ => ihL hS hag he
  | letE => rw [visitExpr]; exact oracle_agree hcl hS hag he fun _ => ihLt hS hag he
  | mdata => rw [visitExpr]; exact oracle_agree hcl hS hag he fun _ => ihE hS hag he
  | proj | lit => rw [visitExpr]; exact oracle_agree hcl hS hag he fun h => absurd h (fails rfl)
  | fvar | bvar | sort | forallE | mvar =>
    rw [visitExpr]; exact oracle_agree hcl hS hag he fun _ => rfl

/-! ## The frame lemmas -/

/-- The traversal's frame property at every fuel, for every function of the traversal that the
pure backend reaches: over closed declarations, `Erasure.visitExpr`, `Erasure.visitAppArgs`,
`Erasure.visitLambda`, `Erasure.visitLet`, `Erasure.visitApp` and `Erasure.visitConstApp` run alike
under two lists of locals that agree on a set `S` containing the visited terms' free variables and
closed under the locals (`EraseProof.LocalsSupport`, `EraseProof.LocalsAgree`), and
`Erasure.visitMutual`, `Erasure.get_constant_kername` and `Erasure.visitConst` do not read the
locals. Proved by induction on the fuel with the steps of this file and of `Core/FrameA.lean`.
Reference: none (DV-13). -/
theorem traversal_agree (hcl : ClosedDecls pc.decls) (fuel : Nat) :
    (∀ {S : FVarId → Prop} {tc : TravCtx} {st : ErasureState} {ps : PureState}
      {ls₁ ls₂ : List Local} {e : Expr}, LocalsSupport S ls₁ → LocalsAgree S ls₁ ls₂ →
      FVarsIn S e →
      (visitExpr (m := PureM) fuel e).runPure st { tc with locals := ls₁ } pc ps =
        (visitExpr (m := PureM) fuel e).runPure st { tc with locals := ls₂ } pc ps) ∧
    (∀ {S : FVarId → Prop} {tc : TravCtx} {st : ErasureState} {ps : PureState}
      {ls₁ ls₂ : List Local} {f : LBTerm} {args : Array Expr}, LocalsSupport S ls₁ →
      LocalsAgree S ls₁ ls₂ → (∀ a ∈ args, FVarsIn S a) →
      (visitAppArgs (m := PureM) fuel f args).runPure st { tc with locals := ls₁ } pc ps =
        (visitAppArgs (m := PureM) fuel f args).runPure st { tc with locals := ls₂ } pc ps) ∧
    (∀ n, LocalsBlind pc (visitMutual (m := PureM) fuel n)) ∧
    (∀ n, LocalsBlind pc (get_constant_kername (m := PureM) fuel n)) ∧
    (∀ e, LocalsBlind pc (visitConst (m := PureM) fuel e)) ∧
    (∀ {S : FVarId → Prop} {tc : TravCtx} {st : ErasureState} {ps : PureState}
      {ls₁ ls₂ : List Local} {e : Expr}, LocalsSupport S ls₁ → LocalsAgree S ls₁ ls₂ →
      FVarsIn S e →
      (visitLambda (m := PureM) fuel e).runPure st { tc with locals := ls₁ } pc ps =
        (visitLambda (m := PureM) fuel e).runPure st { tc with locals := ls₂ } pc ps) ∧
    (∀ {S : FVarId → Prop} {tc : TravCtx} {st : ErasureState} {ps : PureState}
      {ls₁ ls₂ : List Local} {e : Expr}, LocalsSupport S ls₁ → LocalsAgree S ls₁ ls₂ →
      FVarsIn S e →
      (visitLet (m := PureM) fuel e).runPure st { tc with locals := ls₁ } pc ps =
        (visitLet (m := PureM) fuel e).runPure st { tc with locals := ls₂ } pc ps) ∧
    (∀ {S : FVarId → Prop} {tc : TravCtx} {st : ErasureState} {ps : PureState}
      {ls₁ ls₂ : List Local} {e : Expr}, LocalsSupport S ls₁ → LocalsAgree S ls₁ ls₂ →
      FVarsIn S e →
      (visitApp (m := PureM) fuel e).runPure st { tc with locals := ls₁ } pc ps =
        (visitApp (m := PureM) fuel e).runPure st { tc with locals := ls₂ } pc ps) ∧
    (∀ {S : FVarId → Prop} {tc : TravCtx} {st : ErasureState} {ps : PureState}
      {ls₁ ls₂ : List Local} {e : Expr}, LocalsSupport S ls₁ → LocalsAgree S ls₁ ls₂ →
      FVarsIn S e →
      (visitConstApp (m := PureM) fuel e).runPure st { tc with locals := ls₁ } pc ps =
        (visitConstApp (m := PureM) fuel e).runPure st { tc with locals := ls₂ } pc ps) := by
  induction fuel with
  | zero =>
    exact ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ _ _ => rfl,
      fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
      fun _ _ _ => rfl, fun _ _ _ => rfl⟩
  | succ n ih =>
    obtain ⟨hE, hA, hM, hK, hC, hL, hLt, hAp, hCA⟩ := ih
    exact ⟨visitExpr_step hcl hE hL hLt hAp, visitAppArgs_step hE,
      visitMutual_step hcl fun he => hE (S := fun _ => False) (fun _ h => h.elim)
        (fun _ h => h.elim) he,
      get_constant_kername_step hM, visitConst_step hK,
      visitLambda_agree hE, visitLet_agree hE, visitApp_agree hCA hE hA,
      visitConstApp_agree (fun _ _ _ => hC _ _ _ _ _ _) hA⟩

/-- Traversal frame: a run of `visitExpr` on a term whose free variables lie in `S` does not
depend on the locals outside `S`, given closed declarations. The first component of
`traversal_agree`. Used for a `let` value
(`ls₁ = l :: ls`, `ls₂ = ls`, `S := (· ≠ l.fvarId)`) and a constant body (`ls₂ = []`,
`S := fun _ => False`). Reference: none; MetaRocq erases a constant body in the empty context
(`MR E/ErasureFunction.v:1309 erase_constant_body`); DV-13. -/
theorem visit_agree {S : FVarId → Prop} {pc : PureCtx} {tc : TravCtx} {st : ErasureState}
    {ps : PureState} {ls₁ ls₂ : List Local} {fuel : Nat} {e : Expr}
    (hcl : ClosedDecls pc.decls) (hS : LocalsSupport S ls₁) (hag : LocalsAgree S ls₁ ls₂)
    (he : FVarsIn S e) :
    (visitExpr (m := PureM) fuel e).runPure st { tc with locals := ls₁ } pc ps =
      (visitExpr (m := PureM) fuel e).runPure st { tc with locals := ls₂ } pc ps :=
  (traversal_agree hcl fuel).1 hS hag he

end EraseProof
