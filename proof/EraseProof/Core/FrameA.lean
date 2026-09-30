import EraseProof.Oracle.Agree

/-!
# Frame steps of the traversal at the pure backend

The traversal `Erasure.visitExpr` and the functions it calls (`LeanToLambdaBox/Erasure.lean`), run
at the pure backend `Erasure.PureM`, give the same result under two lists of locals that agree on
a set `S` of free variables containing the visited term's and closed under the locals' types and
values (`EraseProof.LocalsSupport`, `EraseProof.LocalsAgree`), given closed declarations. This
file proves that property for one unfolding of `Erasure.visitLambda`, `Erasure.visitLet`,
`Erasure.visitApp` and `Erasure.visitConstApp`, and for the oracle call that starts each unfolding
of `Erasure.visitExpr`. Each lemma takes the same property of the functions the step calls, at one
less fuel, as hypotheses (`ih…`); the frame lemma `visit_agree` assembles them by induction on the
fuel. Both runs start from the same traversal state and backend state, so a binder pushes the same
fresh local on both sides, and the support set grows by that local's variable.

Reference: none; MetaRocq erases a constant body in the empty context
(`MR E/ErasureFunction.v:1309 erase_constant_body`), where this traversal keeps the caller's locals
(DV-13).
-/

open Lean Lean4Lean Erasure

namespace EraseProof

variable {α β : Type} {pc : PureCtx} {st : ErasureState} {ps : PureState}

/-! ## Runs at the pure backend -/

/-- A run of a bind runs the continuation from the state the first action leaves. Reference:
none. -/
theorem runPure_bind {tc : TravCtx} (x : EraseT PureM α) (k : α → EraseT PureM β) :
    (x >>= k).runPure st tc pc ps =
      x.runPure st tc pc ps >>= fun r => (k r.1.1).runPure r.1.2 tc pc r.2 := rfl

/-- A run of `withReader f x` runs `x` under the reader context `f tc`. Reference: none. -/
theorem runPure_withReader {tc : TravCtx} (f : TravCtx → TravCtx) (x : EraseT PureM α) :
    (withReader f x).runPure st tc pc ps = x.runPure st (f tc) pc ps := rfl

/-- A run of a bind on `read` passes the reader context to the continuation. Reference: none. -/
theorem runPure_read_bind {tc : TravCtx} (k : TravCtx → EraseT PureM α) :
    (read >>= k).runPure st tc pc ps = (k tc).runPure st tc pc ps := rfl

/-- A run of an action of the backend lifted to the traversal leaves the traversal state
unchanged. Reference: none. -/
theorem runPure_liftM {tc : TravCtx} (x : PureM α) :
    (liftM x : EraseT PureM α).runPure st tc pc ps =
      ((x.run pc).run ps >>= fun r => .ok ((r.1, st), r.2)) := rfl

/-- A run of the oracle call of the pure backend (`Backend.isErasable` of `Erasure.PureM`) is the
oracle `Erasure.Pure.isErasable` at `Erasure.oracleFuel` on the given locals; it ignores the
`LocalContext` and leaves the backend state unchanged. Reference: none. -/
theorem isErasable_run (lctx : LocalContext) (ls : List Local) (e : Expr) :
    ((Backend.isErasable (m := PureM) lctx ls e).run pc).run ps =
      (match Pure.isErasable ⟨pc.decls⟩ oracleFuel ls e with
        | .ok b => .ok (b, ps)
        | .error err => .error err) := by
  change (((match Pure.isErasable ⟨pc.decls⟩ oracleFuel ls e with
    | .ok b => (pure b : PureM Bool) | .error err => throw err).run pc).run ps) = _
  cases Pure.isErasable ⟨pc.decls⟩ oracleFuel ls e <;> rfl

/-- Runs of a bind under the reader contexts `c₁` and `c₂` agree when the first action's runs
agree and the continuation's runs agree after each successful result of the first action.
Reference: none. -/
theorem runPure_bind_agree {x : EraseT PureM α} {k : α → EraseT PureM β} {c₁ c₂ : TravCtx}
    (hx : x.runPure st c₁ pc ps = x.runPure st c₂ pc ps)
    (hk : ∀ a st' ps', x.runPure st c₁ pc ps = .ok ((a, st'), ps') →
      (k a).runPure st' c₁ pc ps' = (k a).runPure st' c₂ pc ps') :
    (x >>= k).runPure st c₁ pc ps = (x >>= k).runPure st c₂ pc ps := by
  rw [runPure_bind, runPure_bind]
  exact Except.bind_congr_ok hx fun r hr => hk r.1.1 r.1.2 r.2 (hx.trans hr)

/-- The name `mkLambda` and `mkLetIn` give to a variable is read from the locals
(`Erasure.fvar_to_name`), so runs under two reader contexts whose locals find the same local for
it agree. Reference: none. -/
theorem fvar_to_name_agree {x : FVarId} {c₁ c₂ : TravCtx}
    (h : Pure.findLocal c₁.locals x = Pure.findLocal c₂.locals x) :
    (fvar_to_name (m := PureM) x).runPure st c₁ pc ps =
      (fvar_to_name (m := PureM) x).runPure st c₂ pc ps := by
  change Except.ok ((binderNameOf (Pure.findLocal c₁.locals x).get!.userName, st), ps) =
    Except.ok ((binderNameOf (Pure.findLocal c₂.locals x).get!.userName, st), ps)
  rw [h]

/-! ## Binders -/

/-- Pushing the same local on both lists keeps `LocalsSupport` at the set grown by its variable,
when the local's type and value have their free variables in `S`. Reference: none (DV-13). -/
theorem LocalsSupport.push {S : FVarId → Prop} {ls : List Local} {l : Local}
    (hS : LocalsSupport S ls) (hty : FVarsIn S l.type)
    (hval : ∀ v, l.value? = some v → FVarsIn S v) :
    LocalsSupport (fun y => S y ∨ y = l.fvarId) (l :: ls) := by
  have mono : ∀ {e}, FVarsIn S e → FVarsIn (fun y => S y ∨ y = l.fvarId) e :=
    FVarsIn.mono fun _ h => .inl h
  intro y hy l' hl'
  by_cases h : l.fvarId = y
  · subst h
    simp only [Pure.findLocal, List.find?_cons, beq_self_eq_true, Option.some.injEq] at hl'
    subst hl'
    exact ⟨mono hty, fun v hv => mono (hval v hv)⟩
  · have hne : (l.fvarId == y) = false := by simpa using h
    simp only [Pure.findLocal, List.find?_cons, hne] at hl'
    have ⟨h1, h2⟩ := hS y (hy.resolve_right (Ne.symm h)) l' hl'
    exact ⟨mono h1, fun v hv => mono (h2 v hv)⟩

/-- Pushing the same local on both lists keeps `LocalsAgree` at the set grown by its variable.
No freshness is needed: the pushed local is found first on both sides. Reference: none (DV-13). -/
theorem LocalsAgree.push {S : FVarId → Prop} {ls₁ ls₂ : List Local} {l : Local}
    (hag : LocalsAgree S ls₁ ls₂) :
    LocalsAgree (fun y => S y ∨ y = l.fvarId) (l :: ls₁) (l :: ls₂) := by
  intro y hy
  by_cases h : l.fvarId = y
  · subst h; simp [Pure.findLocal]
  · have hne : (l.fvarId == y) = false := by simpa using h
    simp only [Pure.findLocal, List.find?_cons, hne]
    exact hag y (hy.resolve_right (Ne.symm h))

/-! ## The oracle call -/

/-- The oracle call that starts each unfolding of `Erasure.visitExpr` (its equations for
`fuel + 1`, one per constructor, whose branch is `K`): the runs agree when the oracle's answers
agree (`EraseProof.Pure.isErasable_agree`) and `K`'s runs agree whenever the oracle answers
`false`. Reference: none; the erasability test `is_erasableb` that starts every case of
`MR E/ErasureFunction.v:989 erase` (`:992`), there under a context of de Bruijn binders
(DV-13). -/
theorem oracle_agree {S : FVarId → Prop} {tc : TravCtx} {ls₁ ls₂ : List Local} {e : Expr}
    {K : EraseT PureM LBTerm} (hcl : ClosedDecls pc.decls) (hS : LocalsSupport S ls₁)
    (hag : LocalsAgree S ls₁ ls₂) (he : FVarsIn S e)
    (hK : Pure.isErasable ⟨pc.decls⟩ oracleFuel ls₁ e = .ok false →
      K.runPure st { tc with locals := ls₁ } pc ps = K.runPure st { tc with locals := ls₂ } pc ps) :
    (do
        let c₁ ← read
        let c₂ ← read
        let b ← liftM (Backend.isErasable (m := PureM) c₁.lctx c₂.locals e)
        if b = true then pure LBTerm.box else K : EraseT PureM LBTerm).runPure
          st { tc with locals := ls₁ } pc ps =
      (do
        let c₁ ← read
        let c₂ ← read
        let b ← liftM (Backend.isErasable (m := PureM) c₁.lctx c₂.locals e)
        if b = true then pure LBTerm.box else K : EraseT PureM LBTerm).runPure
          st { tc with locals := ls₂ } pc ps := by
  have run : ∀ c : TravCtx, (do
        let c₁ ← read
        let c₂ ← read
        let b ← liftM (Backend.isErasable (m := PureM) c₁.lctx c₂.locals e)
        if b = true then pure LBTerm.box else K : EraseT PureM LBTerm).runPure st c pc ps =
      (match Pure.isErasable ⟨pc.decls⟩ oracleFuel c.locals e with
        | .ok b => (if b = true then pure LBTerm.box else K : EraseT PureM LBTerm).runPure st c pc ps
        | .error err => .error err) := by
    intro c
    rw [runPure_read_bind, runPure_read_bind, runPure_bind, runPure_liftM, isErasable_run]
    cases Pure.isErasable ⟨pc.decls⟩ oracleFuel c.locals e <;> rfl
  rw [run, run]
  dsimp only
  rw [← Pure.isErasable_agree (cx := ⟨pc.decls⟩) (fuel := oracleFuel) hcl hS hag he]
  cases h : Pure.isErasable ⟨pc.decls⟩ oracleFuel ls₁ e with
  | error => rfl
  | ok b =>
    cases b
    · exact hK h
    · rfl

/-! ## Binder steps -/

/-- One unfolding of `Erasure.visitLambda` at the pure backend runs alike under two lists of
locals that agree on `S`, given the same property of `Erasure.visitExpr` at one less fuel (`ih`):
the λ's local is pushed on both sides, and the body is visited at the set grown by its variable.
Reference: none; the `tLambda` case of `MR E/ErasureFunction.v:989 erase` (`:1003`) extends the
de Bruijn context where the traversal pushes a local (DV-13). -/
theorem visitLambda_agree {S : FVarId → Prop} {tc : TravCtx} {ls₁ ls₂ : List Local} {fuel : Nat}
    {e : Expr}
    (ih : ∀ {S : FVarId → Prop} {tc : TravCtx} {st : ErasureState} {ps : PureState}
      {ls₁ ls₂ : List Local} {e : Expr}, LocalsSupport S ls₁ → LocalsAgree S ls₁ ls₂ →
      FVarsIn S e →
      (visitExpr (m := PureM) fuel e).runPure st { tc with locals := ls₁ } pc ps =
        (visitExpr (m := PureM) fuel e).runPure st { tc with locals := ls₂ } pc ps)
    (hS : LocalsSupport S ls₁) (hag : LocalsAgree S ls₁ ls₂) (he : FVarsIn S e) :
    (visitLambda (m := PureM) (fuel + 1) e).runPure st { tc with locals := ls₁ } pc ps =
      (visitLambda (m := PureM) (fuel + 1) e).runPure st { tc with locals := ls₂ } pc ps := by
  rw [visitLambda]
  cases e with
  | lam n ty b bi =>
    refine runPure_bind_agree rfl fun x st' ps' _ => ?_
    rw [runPure_withReader, runPure_withReader]
    let l : Local := ⟨x, n, ty, none⟩
    have hag' := hag.push (l := l)
    refine runPure_bind_agree ?_ fun r st'' ps'' _ => ?_
    · exact ih (tc := { tc with lctx := tc.lctx.mkLocalDecl x n ty bi })
        (hS.push (l := l) he.1 fun _ h => nomatch h) hag'
        (FVarsIn.instantiate1 (FVarsIn.mono (fun _ h => .inl h) he.2) (.inr rfl))
    · exact runPure_bind_agree (fvar_to_name_agree (hag' x (.inr rfl))) fun _ _ _ _ => rfl
  | _ => rfl

/-- One unfolding of `Erasure.visitLet` at the pure backend runs alike under two lists of locals
that agree on `S`, given the same property of `Erasure.visitExpr` at one less fuel (`ih`): the
`let`'s local is pushed on both sides, and its value and body are visited at the set grown by its
variable. Reference: none; the `tLetIn` case of `MR E/ErasureFunction.v:989 erase` (`:1005`)
erases the value in the outer context and extends it for the body only (DV-13). -/
theorem visitLet_agree {S : FVarId → Prop} {tc : TravCtx} {ls₁ ls₂ : List Local} {fuel : Nat}
    {e : Expr}
    (ih : ∀ {S : FVarId → Prop} {tc : TravCtx} {st : ErasureState} {ps : PureState}
      {ls₁ ls₂ : List Local} {e : Expr}, LocalsSupport S ls₁ → LocalsAgree S ls₁ ls₂ →
      FVarsIn S e →
      (visitExpr (m := PureM) fuel e).runPure st { tc with locals := ls₁ } pc ps =
        (visitExpr (m := PureM) fuel e).runPure st { tc with locals := ls₂ } pc ps)
    (hS : LocalsSupport S ls₁) (hag : LocalsAgree S ls₁ ls₂) (he : FVarsIn S e) :
    (visitLet (m := PureM) (fuel + 1) e).runPure st { tc with locals := ls₁ } pc ps =
      (visitLet (m := PureM) (fuel + 1) e).runPure st { tc with locals := ls₂ } pc ps := by
  rw [visitLet]
  cases e with
  | letE n ty v b nd =>
    refine runPure_bind_agree rfl fun x st' ps' _ => ?_
    rw [runPure_withReader, runPure_withReader]
    let l : Local := ⟨x, n, ty, some v⟩
    have hS' := hS.push (l := l) he.1 fun _ h => by cases h; exact he.2.1
    have hag' := hag.push (l := l)
    have mono : ∀ {e}, FVarsIn S e → FVarsIn (fun y => S y ∨ y = x) e :=
      FVarsIn.mono fun _ h => .inl h
    refine runPure_bind_agree ?_ fun r₁ st₁ ps₁ _ => runPure_bind_agree ?_ fun r₂ st₂ ps₂ _ => ?_
    · exact ih (tc := { tc with lctx := tc.lctx.mkLetDecl x n ty v nd }) hS' hag' (mono he.2.1)
    · exact ih (tc := { tc with lctx := tc.lctx.mkLetDecl x n ty v nd }) hS' hag'
        (FVarsIn.instantiate1 (mono he.2.2) (.inr rfl))
    · exact runPure_bind_agree (fvar_to_name_agree (hag' x (.inr rfl))) fun _ _ _ _ => rfl
  | _ => rfl

/-! ## Application steps -/

/-- The head of an application has its free variables among the application's. Reference:
none (as `Lean4Lean.Closed.getAppFn`, `Lean4Lean/Verify/Typing/Lemmas.lean:180`). -/
theorem FVarsIn.getAppFn {S : FVarId → Prop} : ∀ {e : Expr}, FVarsIn S e → FVarsIn S e.getAppFn
  | .app f _, h => FVarsIn.getAppFn (e := f) h.1
  | .bvar _, h | .fvar _, h | .mvar _, h | .sort _, h | .const .., h | .lam .., h
  | .forallE .., h | .letE .., h | .lit _, h | .mdata .., h | .proj .., h => h

/-- The arguments of an application have their free variables among the application's.
Reference: none (as `Lean4Lean.Closed.getAppArgsRevList`,
`Lean4Lean/Verify/Typing/Lemmas.lean:185`). -/
theorem FVarsIn.getAppArgsRevList {S : FVarId → Prop} :
    ∀ {e : Expr}, FVarsIn S e → ∀ a ∈ e.getAppArgsRevList, FVarsIn S a
  | .app f _, h, a, ha => by
    simp only [Expr.getAppArgsRevList, List.mem_cons] at ha
    rcases ha with rfl | ha
    exacts [h.2, FVarsIn.getAppArgsRevList (e := f) h.1 a ha]
  | .bvar _, _, _, ha | .fvar _, _, _, ha | .mvar _, _, _, ha | .sort _, _, _, ha
  | .const .., _, _, ha | .lam .., _, _, ha | .forallE .., _, _, ha | .letE .., _, _, ha
  | .lit _, _, _, ha | .mdata .., _, _, ha | .proj .., _, _, ha => nomatch ha

/-- `FVarsIn.getAppArgsRevList` for the array `Expr.getAppArgs` that `Expr.withApp` passes.
Reference: none. -/
theorem FVarsIn.getAppArgs {S : FVarId → Prop} {e : Expr} (h : FVarsIn S e) :
    ∀ a ∈ e.getAppArgs, FVarsIn S a := by
  intro a ha
  rw [Expr.getAppArgs_eq_rev, List.mem_toArray, List.mem_reverse] at ha
  exact FVarsIn.getAppArgsRevList h a ha

/-- One unfolding of `Erasure.visitApp` at the pure backend runs alike under two lists of locals
that agree on `S`, given the same property, at one less fuel, of `Erasure.visitConstApp` (`ihCA`,
for an application of a constant), of `Erasure.visitExpr` (`ihE`, for another head) and of
`Erasure.visitAppArgs` (`ihA`, for the arguments). Reference: none; the `tApp` case of
`MR E/ErasureFunction.v:989 erase` (`:1009`) (DV-13). -/
theorem visitApp_agree {S : FVarId → Prop} {tc : TravCtx} {ls₁ ls₂ : List Local} {fuel : Nat}
    {e : Expr}
    (ihCA : ∀ {S : FVarId → Prop} {tc : TravCtx} {st : ErasureState} {ps : PureState}
      {ls₁ ls₂ : List Local} {e : Expr}, LocalsSupport S ls₁ → LocalsAgree S ls₁ ls₂ →
      FVarsIn S e →
      (visitConstApp (m := PureM) fuel e).runPure st { tc with locals := ls₁ } pc ps =
        (visitConstApp (m := PureM) fuel e).runPure st { tc with locals := ls₂ } pc ps)
    (ihE : ∀ {S : FVarId → Prop} {tc : TravCtx} {st : ErasureState} {ps : PureState}
      {ls₁ ls₂ : List Local} {e : Expr}, LocalsSupport S ls₁ → LocalsAgree S ls₁ ls₂ →
      FVarsIn S e →
      (visitExpr (m := PureM) fuel e).runPure st { tc with locals := ls₁ } pc ps =
        (visitExpr (m := PureM) fuel e).runPure st { tc with locals := ls₂ } pc ps)
    (ihA : ∀ {S : FVarId → Prop} {tc : TravCtx} {st : ErasureState} {ps : PureState}
      {ls₁ ls₂ : List Local} {f : LBTerm} {args : Array Expr}, LocalsSupport S ls₁ →
      LocalsAgree S ls₁ ls₂ → (∀ a ∈ args, FVarsIn S a) →
      (visitAppArgs (m := PureM) fuel f args).runPure st { tc with locals := ls₁ } pc ps =
        (visitAppArgs (m := PureM) fuel f args).runPure st { tc with locals := ls₂ } pc ps)
    (hS : LocalsSupport S ls₁) (hag : LocalsAgree S ls₁ ls₂) (he : FVarsIn S e) :
    (visitApp (m := PureM) (fuel + 1) e).runPure st { tc with locals := ls₁ } pc ps =
      (visitApp (m := PureM) (fuel + 1) e).runPure st { tc with locals := ls₂ } pc ps := by
  rw [visitApp]
  split
  · exact ihCA hS hag he
  · rw [Expr.withApp_eq]
    exact runPure_bind_agree (ihE hS hag (FVarsIn.getAppFn he)) fun _ _ _ _ =>
      ihA hS hag (FVarsIn.getAppArgs he)

/-- One unfolding of `Erasure.visitConstApp` at the pure backend runs alike under two lists of
locals that agree on `S`, given the same property, at one less fuel, of `Erasure.visitConst`
(`ihC`, for the head) and of `Erasure.visitAppArgs` (`ihA`, for the arguments): the pure backend
has no `casesOn` and no constructors (`Erasure.PureM.casesInfo?`, `Erasure.PureM.ctorArity?`), so
the application is erased as the erased head applied to the erased arguments. Reference: none;
the `tApp` case of `MR E/ErasureFunction.v:989 erase` (`:1009`) (DV-13). -/
theorem visitConstApp_agree {S : FVarId → Prop} {tc : TravCtx} {ls₁ ls₂ : List Local}
    {fuel : Nat} {e : Expr}
    (ihC : ∀ {S : FVarId → Prop} {tc : TravCtx} {st : ErasureState} {ps : PureState}
      {ls₁ ls₂ : List Local} {e : Expr}, LocalsSupport S ls₁ → LocalsAgree S ls₁ ls₂ →
      FVarsIn S e →
      (visitConst (m := PureM) fuel e).runPure st { tc with locals := ls₁ } pc ps =
        (visitConst (m := PureM) fuel e).runPure st { tc with locals := ls₂ } pc ps)
    (ihA : ∀ {S : FVarId → Prop} {tc : TravCtx} {st : ErasureState} {ps : PureState}
      {ls₁ ls₂ : List Local} {f : LBTerm} {args : Array Expr}, LocalsSupport S ls₁ →
      LocalsAgree S ls₁ ls₂ → (∀ a ∈ args, FVarsIn S a) →
      (visitAppArgs (m := PureM) fuel f args).runPure st { tc with locals := ls₁ } pc ps =
        (visitAppArgs (m := PureM) fuel f args).runPure st { tc with locals := ls₂ } pc ps)
    (hS : LocalsSupport S ls₁) (hag : LocalsAgree S ls₁ ls₂) (he : FVarsIn S e) :
    (visitConstApp (m := PureM) (fuel + 1) e).runPure st { tc with locals := ls₁ } pc ps =
      (visitConstApp (m := PureM) (fuel + 1) e).runPure st { tc with locals := ls₂ } pc ps := by
  rw [visitConstApp, Expr.withApp_eq]
  split
  · refine runPure_bind_agree rfl fun a st' ps' h => ?_
    cases h
    refine runPure_bind_agree rfl fun a st' ps' h => ?_
    cases h
    exact runPure_bind_agree (ihC hS hag (FVarsIn.getAppFn he)) fun _ _ _ _ =>
      ihA hS hag (FVarsIn.getAppArgs he)
  · rfl

end EraseProof
