import EraseProof.Core.Order
import EraseProof.Core.State
import EraseProof.Core.Glue
import EraseProof.Oracle
import EraseProof.Oracle.Atom

/-!
# Steps of the shipping core's correctness

`erasePure_erases` is proved by induction on the fuel of the shipping traversal
(`Erasure.visitExpr` and the functions it calls, `LeanToLambdaBox/Erasure.lean`) run at the pure
backend `Erasure.PureM`. Its statement at one fuel is `ExprSpec` for `visitExpr` and `MutualSpec`
for `visitMutual`: a successful run on a translated term returns an erasure of it (`Erases`) with
erased λ□ dependencies (`ErasesDeps`), keeps the state invariant `StateOK`, grows the λ□
environment freshly and registers only constants of a scope (`Grows`, `ScopeOK`), under locals
that mirror the model context (`CtxOK`). This module proves one step per case of the traversal,
each from the statement at smaller fuels (`ih`, `ihM`): a sort, a Π and terms without a
translation (`visitExpr_other_step`, with the `box` case `visitExpr_box` shared by every step), a
free variable, a λ, a `let`, an application, a constant, metadata, and `visitMutual` on a
declaration that is not a recursive definition (`visitMutual_nonrec_step`). The steps for recursive
declarations and the induction itself are elsewhere.

Reference: `erases_erase` (`MR E/ErasureFunction.v:1228`), case by case over `erase`
(`MR E/ErasureFunction.v:989`), with `erase_constant_body` (`MR E/ErasureFunction.v:1309`) and
`erase_global_erases_deps` (`MR E/ErasureFunctionProperties.v:172`); Letouzey Lemma 11.
-/

open Lean Lean4Lean Erasure

namespace EraseProof

/-- The free variable that the pure backend's `freshFVarId` allocates at the counter value `k`.
Reference: none (DV-13). -/
abbrev pureFVar (k : Nat) : FVarId := ⟨.num `_pure k⟩

/-- The traversal's context invariant at the pure backend, over the model context `Δ`: the
locals mirror `Δ` (`LocalsOK`, free-variable entries only); every variable the counter will
allocate is fresh for `Δ` and for the admissible targets `rc`, which are closed; the fix variables
of the block being erased have their targets in `rc`; the configuration is `cfg`. Reference: the
context `Γ` of `erases_erase` (`MR E/ErasureFunction.v:1228`), here a list of locals opened with
fresh variables (DV-13), with the fix variables of a recursive block (DV-7). -/
structure CtxOK (venv : VEnv) (Us : List Name) (rc : Name → LBTerm → Prop) (cfg : ErasureConfig)
    (tc : TravCtx) (Δ : VLCtx) (ps : PureState) : Prop where
  locals : LocalsOK venv Us tc.locals Δ
  fresh : ∀ k, ps.next ≤ k → pureFVar k ∉ Δ.fvars
  rcFresh : ∀ c t, rc c t → closedn 0 t = true ∧ ∀ k, ps.next ≤ k → hasFVar (pureFVar k) t = false
  fixvars : ∀ c x, tc.fixvars.bind (fun m => m[c]?) = some x → rc c (.fvar x)
  config : tc.config = cfg

/-- What a run of the traversal from the states `st`, `ps` to `st'`, `ps'` guarantees: the state
invariant holds after it (`StateOK`), the λ□ environment grows by fresh kernames (`LenvExt`), the
counter does not decrease, and every constant it registers is in the scope `S`. Reference: the
invariant `includes_deps` (`MR E/ErasureFunctionProperties.v:41`) of `erase_global_deps`
(`MR E/ErasureFunction.v:1602`), and `erase_global_deps_fresh`
(`MR E/ErasureFunctionProperties.v:1206`). -/
structure Grows (venv : VEnv) (σ : EvalEnv) (S : Name → Prop) (st st' : ErasureState)
    (ps ps' : PureState) : Prop where
  ok : StateOK venv σ st'
  ext : LenvExt st.gdecls st'.gdecls
  next : ps.next ≤ ps'.next
  scope : ∀ c kn, st.constants[c]? = none → st'.constants[c]? = some kn → S c

/-- The correctness of `visitExpr fuel e` at the pure backend over the declarations `decls`, the
statement `erasePure_erases` proves by induction on the fuel: from a state with `StateOK`, under
locals that mirror `Δ` (`CtxOK`), on a term translated in `Δ` whose value positions mention only
constants of a scope `S` or fix variables of the block being erased, a successful run returns an
erasure of `e` (`Erases`, with the atoms of `evalEnvOf view cfg decls` and the admissible targets
`rc`) whose λ□ dependencies are erased in the final environment, and it `Grows` within `S`.
Reference: `erases_erase` (`MR E/ErasureFunction.v:1228`) with `erase_global_erases_deps`
(`MR E/ErasureFunctionProperties.v:172`). -/
def ExprSpec (venv : VEnv) (view : EnvView) (cfg : ErasureConfig) (decls : List ConstantInfo)
    (fuel : Nat) (e : Expr) : Prop :=
  ∀ ⦃Us : List Name⦄ ⦃Δ : VLCtx⦄ ⦃rc : Name → LBTerm → Prop⦄ ⦃S : Name → Prop⦄ ⦃e' : VExpr⦄
    ⦃st : ErasureState⦄ ⦃tc : TravCtx⦄ ⦃ps : PureState⦄ ⦃r : LBTerm⦄ ⦃st' : ErasureState⦄
    ⦃ps' : PureState⦄,
    CtxOK venv Us rc cfg tc Δ ps → ScopeOK decls S →
    (∀ c, OccursV c e = true → S c ∨ (tc.fixvars.bind (fun m => m[c]?)).isSome) →
    StateOK venv (evalEnvOf view cfg decls) st → TrS venv Us Δ e e' →
    (visitExpr (m := PureM) fuel e).runPure st tc ⟨decls, view⟩ ps = .ok ((r, st'), ps') →
    Erases venv Us (evalEnvOf view cfg decls).isAtom rc Δ e r ∧
      ErasesDeps venv (evalEnvOf view cfg decls) st'.gdecls r ∧
      Grows venv (evalEnvOf view cfg decls) S st st' ps ps'

/-- The correctness of `visitMutual fuel c` at the pure backend: on a constant of a scope `S` that
is not registered, from a state with `StateOK`, a successful run registers `c` and `Grows` within
`S`. Reference: the `ConstantDecl` step of `erase_global_deps` (`MR E/ErasureFunction.v:1602`),
which erases a declaration with `erase_constant_body` (`MR E/ErasureFunction.v:1309`). -/
def MutualSpec (venv : VEnv) (view : EnvView) (cfg : ErasureConfig) (decls : List ConstantInfo)
    (fuel : Nat) (c : Name) : Prop :=
  ∀ ⦃S : Name → Prop⦄ ⦃st : ErasureState⦄ ⦃tc : TravCtx⦄ ⦃ps : PureState⦄ ⦃st' : ErasureState⦄
    ⦃ps' : PureState⦄,
    ScopeOK decls S → S c → tc.config = cfg → StateOK venv (evalEnvOf view cfg decls) st →
    st.constants[c]? = none →
    (visitMutual (m := PureM) fuel c).runPure st tc ⟨decls, view⟩ ps = .ok (((), st'), ps') →
    Grows venv (evalEnvOf view cfg decls) S st st' ps ps' ∧ ∃ kn, st'.constants[c]? = some kn

section
variable {venv : VEnv} {σ : EvalEnv} {S : Name → Prop} {pc : PureCtx}

/-- A run that changes neither state grows. Reference: none. -/
theorem Grows.refl {st : ErasureState} {ps : PureState} (hok : StateOK venv σ st) :
    Grows venv σ S st st ps ps :=
  ⟨hok, LenvExt.refl, Nat.le_refl _, fun _ _ h h' => by rw [h] at h'; cases h'⟩

/-- Consecutive runs grow. Reference: none (`extends` composes, `MR E/EGlobalEnv.v:189`). -/
theorem Grows.trans {st st₁ st₂ : ErasureState} {ps ps₁ ps₂ : PureState}
    (h₁ : Grows venv σ S st st₁ ps ps₁) (h₂ : Grows venv σ S st₁ st₂ ps₁ ps₂) :
    Grows venv σ S st st₂ ps ps₂ := by
  refine ⟨h₂.ok, h₁.ext.trans h₂.ext, Nat.le_trans h₁.next h₂.next, fun c kn h h' => ?_⟩
  cases h1 : st₁.constants[c]? with
  | none => exact h₂.scope c kn h1 h'
  | some kn₁ => exact h₁.scope c kn₁ h h1

/-- The context invariant survives the counter's growth. Reference: none (DV-13). -/
theorem CtxOK.mono {Us rc cfg tc Δ} {ps ps' : PureState} (h : CtxOK venv Us rc cfg tc Δ ps)
    (hle : ps.next ≤ ps'.next) : CtxOK venv Us rc cfg tc Δ ps' :=
  ⟨h.locals, fun k hk => h.fresh k (Nat.le_trans hle hk),
    fun c t ht => ⟨(h.rcFresh c t ht).1, fun k hk => (h.rcFresh c t ht).2 k (Nat.le_trans hle hk)⟩,
    h.fixvars, h.config⟩

/-- The context invariant does not read the `LocalContext` of the reader context, which the pure
backend never reads. Reference: none. -/
theorem CtxOK.setLctx {Us rc cfg tc Δ} {ps : PureState} (h : CtxOK venv Us rc cfg tc Δ ps)
    (L : LocalContext) : CtxOK venv Us rc cfg { tc with lctx := L } Δ ps :=
  ⟨h.locals, h.fresh, h.rcFresh, h.fixvars, h.config⟩

/-- A successful run of the oracle call that starts each unfolding of `Erasure.visitExpr` either
answered `true` and returned `□` without changing the states, or answered `false` and ran the
branch `K`. Reference: `is_erasableb` at the start of `erase` (`MR E/ErasureFunction.v:992`). -/
theorem oracle_run {e : Expr} {K : EraseT PureM LBTerm} {tc : TravCtx} {st st' : ErasureState}
    {ps ps' : PureState} {r : LBTerm}
    (h : (do
        let c₁ ← read
        let c₂ ← read
        let b ← liftM (Backend.isErasable (m := PureM) c₁.lctx c₂.locals e)
        if b = true then pure LBTerm.box else K : EraseT PureM LBTerm).runPure st tc pc ps =
      .ok ((r, st'), ps')) :
    (Pure.isErasable ⟨pc.decls⟩ oracleFuel tc.locals e = .ok true ∧ r = .box ∧ st' = st ∧
      ps' = ps) ∨
    (Pure.isErasable ⟨pc.decls⟩ oracleFuel tc.locals e = .ok false ∧
      K.runPure st tc pc ps = .ok ((r, st'), ps')) := by
  rw [runPure_read_bind, runPure_read_bind, runPure_bind, runPure_liftM, isErasable_run] at h
  cases hor : Pure.isErasable ⟨pc.decls⟩ oracleFuel tc.locals e with
  | error err => rw [hor] at h; cases h
  | ok b =>
    rw [hor] at h
    cases b with
    | true => cases h; exact .inl ⟨rfl, rfl, rfl, rfl⟩
    | false => exact .inr ⟨rfl, h⟩


/-- `Except`'s bind on a success. Reference: none. -/
theorem Except.ok_bind' {ε α β : Type} {a : α} {f : α → Except ε β} :
    ((Except.ok a : Except ε α) >>= f) = f a := rfl

/-- The pure backend's `freshFVarId` returns `pureFVar` of the counter and increments it.
Reference: none (DV-13). -/
theorem fresh_run {tc : TravCtx} {st : ErasureState} {ps : PureState} :
    (liftM (Backend.freshFVarId (m := PureM)) : EraseT PureM FVarId).runPure st tc pc ps =
      .ok ((pureFVar ps.next, st), ⟨ps.next + 1⟩) := rfl

/-- `mkLambda x body` closes `body` over `x` with the traversal's `abstract`, under the λ□ name of
the local found for `x` (`binderNameOf` of its user name). Reference: the `tLambda` case of `erase`
(`MR E/ErasureFunction.v:1003`); DV-13. -/
theorem mkLambda_run {tc : TravCtx} {st : ErasureState} {ps : PureState} {x : FVarId} {l : Local}
    {body : LBTerm} (h : Pure.findLocal tc.locals x = some l) :
    (mkLambda (m := PureM) x body).runPure st tc pc ps =
      .ok ((.lambda (binderNameOf l.userName) (_root_.abstract x body), st), ps) := by
  change Except.ok ((LBTerm.lambda (binderNameOf (Pure.findLocal tc.locals x).get!.userName)
    (_root_.abstract x body), st), ps) = _
  rw [h]; rfl

/-- `mkLetIn x val body` closes `body` over `x` with the traversal's `abstract`, under the λ□
name of the local found for `x`. Reference: the `tLetIn` case of `erase`
(`MR E/ErasureFunction.v:1005`); DV-13. -/
theorem mkLetIn_run {tc : TravCtx} {st : ErasureState} {ps : PureState} {x : FVarId} {l : Local}
    {val body : LBTerm} (h : Pure.findLocal tc.locals x = some l) :
    (mkLetIn (m := PureM) x val body).runPure st tc pc ps =
      .ok ((.letIn (binderNameOf l.userName) val (_root_.abstract x body), st), ps) := by
  change Except.ok ((LBTerm.letIn (binderNameOf (Pure.findLocal tc.locals x).get!.userName)
    val (_root_.abstract x body), st), ps) = _
  rw [h]; rfl

/-- Opening a binder with a free variable keeps the constants in value positions. Reference:
none. -/
theorem OccursV.instantiate1_fvar {c : Name} {x : FVarId} :
    ∀ (b : Expr) (k : Nat), OccursV c (b.instantiate1' (.fvar x) k) = OccursV c b
  | .bvar i, k => by
    simp only [Expr.instantiate1']
    split
    · rfl
    · split <;> rfl
  | .app f a, k => by
    simp only [Expr.instantiate1', OccursV, OccursV.instantiate1_fvar f,
      OccursV.instantiate1_fvar a]
  | .lam _ _ b _, k => by
    simp only [Expr.instantiate1', OccursV, OccursV.instantiate1_fvar b]
  | .letE _ _ v b _, k => by
    simp only [Expr.instantiate1', OccursV, OccursV.instantiate1_fvar v,
      OccursV.instantiate1_fvar b]
  | .mdata _ e, k => by simp only [Expr.instantiate1', OccursV, OccursV.instantiate1_fvar e]
  | .proj _ _ e, k => by simp only [Expr.instantiate1', OccursV, OccursV.instantiate1_fvar e]
  | .forallE .., _ | .const .., _ | .sort _, _ | .fvar _, _ | .mvar _, _ | .lit _, _ => rfl

/-- A body of `abstract1D x k ds` is the abstraction of a body of `ds`. Reference: none. -/
theorem mem_abstract1D {x : FVarId} {k : Nat} : ∀ {ds : List (@FixDef LBTerm)} {d : @FixDef LBTerm},
    d ∈ abstract1D x k ds → ∃ d₀ ∈ ds, d.body = abstract1 x k d₀.body
  | [], _, h => nomatch h
  | ⟨_, b, _⟩ :: ds, d, h => by
    simp only [abstract1D, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨_, .head _, rfl⟩
    · obtain ⟨d₀, hd₀, hb⟩ := mem_abstract1D h
      exact ⟨d₀, .tail _ hd₀, hb⟩

/-- Abstracting a variable keeps the erased dependencies, which do not see variables.
Reference: `erases_deps_lift` (`MR E/EDeps.v:44`), for the traversal's abstraction (DV-13). -/
theorem ErasesDeps.abstract1 {lenv : GlobalDeclarations} {t : LBTerm} {x : FVarId}
    (h : ErasesDeps venv σ lenv t) : ∀ k, ErasesDeps venv σ lenv (abstract1 x k t) := by
  induction h with
  | box => intro; exact .box
  | bvar => intro; exact .bvar
  | fvar =>
    intro k
    simp only [EraseProof.abstract1]
    split
    · exact .bvar
    · exact .fvar
  | lambda _ ih => intro k; exact .lambda (ih _)
  | letIn _ _ ihv ihb => intro k; exact .letIn (ihv _) (ihb _)
  | app _ _ ihf iha => intro k; exact .app (ihf _) (iha _)
  | const hc hl hd hb _ => intro; exact .const hc hl hd hb
  | fix _ ih =>
    intro k
    refine .fix fun d hd => ?_
    obtain ⟨d₀, hd₀, hb⟩ := mem_abstract1D hd
    rw [hb]
    exact ih d₀ hd₀ _


variable {P decls : List ConstantInfo} {view : EnvView} {cfg : ErasureConfig}

/-- The `box` step, shared by every case of `visitExpr`: when the oracle answers `true` on a
translated term, `□` erases it (`Pure.isErasable_sound`, `Erases.box`). Reference: the
`is_erasableb` case of `erases_erase` (`MR E/ErasureFunction.v:1228`, `:993`), rule `erases_box`
(`MR E/Extract.v:140`). -/
theorem visitExpr_box {Us : List Name} {rc : Name → LBTerm → Prop} {tc : TravCtx} {Δ : VLCtx}
    {ps : PureState} {st : ErasureState} {e : Expr} {e' : VExpr}
    (hG : CoreEnv venv P decls) (hctx : CtxOK venv Us rc cfg tc Δ ps)
    (hok : StateOK venv (evalEnvOf view cfg decls) st) (he : TrS venv Us Δ e e')
    (hor : Pure.isErasable ⟨decls⟩ oracleFuel tc.locals e = .ok true) :
    Erases venv Us (evalEnvOf view cfg decls).isAtom rc Δ e .box ∧
      ErasesDeps venv (evalEnvOf view cfg decls) st.gdecls .box ∧
      Grows venv (evalEnvOf view cfg decls) S st st ps ps :=
  ⟨.box (Pure.isErasable_sound hG.prog hG.sub hctx.locals he hor), .box, .refl hok⟩

/-- The counter's variables are distinct. Reference: none. -/
theorem pureFVar_inj {k k' : Nat} (h : pureFVar k = pureFVar k') : k = k' := by
  cases h; rfl

/-- Pushing the local of the next fresh variable keeps the context invariant, with the counter
advanced. Reference: the extension of `wf_local` (`MR common/theories/EnvironmentTyping.v:2251`)
by a binder; DV-13. -/
theorem CtxOK.push {Us : List Name} {rc : Name → LBTerm → Prop} {tc : TravCtx} {Δ : VLCtx}
    {ps : PureState} {l : Local} {d : VLocalDecl} {L : LocalContext}
    (hctx : CtxOK venv Us rc cfg tc Δ ps) (hl : l.fvarId = pureFVar ps.next)
    (hloc : LocalsOK venv Us (l :: tc.locals) ((some (l.fvarId, []), d) :: Δ)) :
    CtxOK venv Us rc cfg { tc with lctx := L, locals := l :: tc.locals }
      ((some (l.fvarId, []), d) :: Δ) ⟨ps.next + 1⟩ := by
  refine ⟨hloc, fun k hk hmem => ?_, fun c t ht => ⟨(hctx.rcFresh c t ht).1, fun k hk =>
    (hctx.rcFresh c t ht).2 k (Nat.le_of_succ_le hk)⟩, hctx.fixvars, hctx.config⟩
  simp only [VLCtx.fvars_cons_some, List.mem_cons] at hmem
  rcases hmem with h | h
  · rw [hl] at h
    have := pureFVar_inj h
    dsimp only at hk
    omega
  · exact hctx.fresh k (Nat.le_of_succ_le hk) h

/-- The `lam` step of `erasePure_erases`, from `visitExpr` at the fuels up to `fuel` (`ih`): the
body, opened with a fresh variable, translates in the context extended by its free-variable entry
(`TrS.inst_fvar`) and is erased there; its erasure is closed (`Erases.closed`), so the traversal's
`abstract` is `abstract1` (`abstract_eq_abstract1`), which erases the source body under the λ's
de Bruijn entry (`Erases.uninstantiateN`). Reference: the `tLambda` case of `erases_erase`
(`MR E/ErasureFunction.v:1228`), rule `erases_tLambda` (`MR E/Extract.v:93`); DV-13. -/
theorem visitExpr_lam_step (hG : CoreEnv venv P decls) {fuel : Nat}
    (ih : ∀ m ≤ fuel, ∀ e, ExprSpec venv view cfg decls m e) {n : Name} {A b : Expr}
    {bi : BinderInfo} : ExprSpec venv view cfg decls (fuel + 1) (.lam n A b bi) := by
  intro Us Δ rc S e' st tc ps r st' ps' hctx hsc hocc hok he hrun
  rw [visitExpr] at hrun
  rcases oracle_run hrun with ⟨hor, rfl, rfl, rfl⟩ | ⟨-, hrun⟩
  · exact visitExpr_box hG hctx hok he hor
  cases fuel with
  | zero => cases hrun
  | succ k =>
  rw [visitLambda] at hrun
  simp only [lambdaMonocular, withLocalDecl] at hrun
  rw [runPure_bind, fresh_run, Except.ok_bind'] at hrun
  dsimp only at hrun
  rw [runPure_withReader, runPure_bind] at hrun
  obtain ⟨⟨⟨r₀, st₁⟩, ps₁⟩, hbody, hrun⟩ := Except.ok_of_bind hrun
  dsimp only at hrun
  generalize hx : pureFVar ps.next = x at hbody hrun
  rw [mkLambda_run (l := ⟨x, n, A, none⟩) (by simp [Pure.findLocal])] at hrun
  cases hrun
  cases he with
  | @lam A' _ _ _ _ _ _ hA htA hb =>
  have hxΔ : x ∉ Δ.fvars := hx ▸ hctx.fresh ps.next (Nat.le_refl _)
  have hloc : LocalsOK venv Us (⟨x, n, A, none⟩ :: tc.locals) ((some (x, []), .vlam A') :: Δ) :=
    .lam hctx.locals hxΔ rfl htA hA
  have hctx' := hctx.push (l := ⟨x, n, A, none⟩) (L := tc.lctx.mkLocalDecl x n A bi) hx.symm hloc
  have hwf := hloc.wf
  have hbody' : TrS venv Us ((some (x, []), .vlam A') :: Δ) (b.instantiate1' (.fvar x)) _ :=
    TrS.inst_fvar hG.prog.ordered hwf.1 hb
  have ⟨her, hdeps, hgr⟩ := ih k (Nat.le_succ _) _ hctx' hsc
    (fun c hc => by
      rw [OccursV.instantiate1_fvar] at hc
      exact hocc c hc) hok hbody' hbody
  have hsc' : FVarsIn (· ≠ x) b :=
    (TrS.fvarsIn (TrS.lam hA htA hb : TrS venv Us Δ (.lam n A b bi) _)).2.mono
      fun y hy hyx => hxΔ (hyx ▸ hy)
  have hrcx : RcFresh rc x := fun c t ht =>
    ⟨(hctx.rcFresh c t ht).1, hx ▸ (hctx.rcFresh c t ht).2 _ (Nat.le_refl _)⟩
  have hcl : closedn 0 r₀ = true := by
    have := Erases.closed (fun c t ht => (hctx.rcFresh c t ht).1) hbody' her
    rwa [show VLCtx.bvars ((some (x, []), VLocalDecl.vlam A') :: Δ) = 0 from hwf.2] at this
  rw [abstract_eq_abstract1 hcl]
  refine ⟨.lam htA (Erases.uninstantiateN .zero hrcx hsc' her), .lambda (hdeps.abstract1 0),
    ⟨hgr.ok, hgr.ext, Nat.le_trans (Nat.le_succ _) hgr.next, hgr.scope⟩⟩


/-- The `fvar` step of `erasePure_erases`: a free variable the oracle keeps erases to itself.
Reference: the `tVar` case of `erases_erase` (`MR E/ErasureFunction.v:1228`), rule `erases_tVar`
(`MR E/Extract.v:90`); DV-13. -/
theorem visitExpr_fvar_step (hG : CoreEnv venv P decls) {fuel : Nat} {x : FVarId} :
    ExprSpec venv view cfg decls (fuel + 1) (.fvar x) := by
  intro Us Δ rc S e' st tc ps r st' ps' hctx hsc hocc hok he hrun
  rw [visitExpr] at hrun
  rcases oracle_run hrun with ⟨hor, rfl, rfl, rfl⟩ | ⟨-, hrun⟩
  · exact visitExpr_box hG hctx hok he hor
  cases hrun
  exact ⟨.fvar, .fvar, .refl hok⟩

/-- The `mdata` step of `erasePure_erases`, from `visitExpr` at `fuel` (`ih`): metadata is
transparent. Reference: none (PCUIC has no metadata). -/
theorem visitExpr_mdata_step (hG : CoreEnv venv P decls) {fuel : Nat}
    (ih : ∀ m ≤ fuel, ∀ e, ExprSpec venv view cfg decls m e) {d : MData} {e : Expr} :
    ExprSpec venv view cfg decls (fuel + 1) (.mdata d e) := by
  intro Us Δ rc S e' st tc ps r st' ps' hctx hsc hocc hok he hrun
  rw [visitExpr] at hrun
  rcases oracle_run hrun with ⟨hor, rfl, rfl, rfl⟩ | ⟨-, hrun⟩
  · exact visitExpr_box hG hctx hok he hor
  cases he with
  | mdata he =>
  have ⟨her, hdeps, hgr⟩ := ih fuel (Nat.le_refl _) e hctx hsc hocc hok he hrun
  exact ⟨.mdata her, hdeps, hgr⟩

/-- The types and values of the locals mention only the free variables of the context they
mirror. Reference: the closedness of `wf_local` entries
(`MR common/theories/EnvironmentTyping.v:2251`); DV-13. -/
theorem LocalsOK.support {Us : List Name} {ls : List Local} {Δ : VLCtx}
    (hloc : LocalsOK venv Us ls Δ) {y : FVarId} {l : Local} (hl : Pure.findLocal ls y = some l) :
    FVarsIn (· ∈ Δ.fvars) l.type ∧ ∀ v, l.value? = some v → FVarsIn (· ∈ Δ.fvars) v := by
  induction hloc generalizing l with
  | nil => cases hl
  | @lam ls A' l₀ Δ _ _ hv hA _ ih =>
    have mono : ∀ {e}, FVarsIn (· ∈ Δ.fvars) e →
        FVarsIn (· ∈ VLCtx.fvars ((some (l₀.fvarId, []), VLocalDecl.vlam A') :: Δ)) e :=
      FVarsIn.mono fun _ h => by simp only [VLCtx.fvars_cons_some]; exact .tail _ h
    simp only [Pure.findLocal, List.find?_cons] at hl
    split at hl
    · cases hl
      exact ⟨mono hA.fvarsIn, fun v h => by rw [hv] at h; cases h⟩
    · have ⟨h1, h2⟩ := ih hl
      exact ⟨mono h1, fun v h => mono (h2 v h)⟩
  | @letE ls val T' v' l₀ Δ _ _ hv hT hval _ ih =>
    have mono : ∀ {e}, FVarsIn (· ∈ Δ.fvars) e →
        FVarsIn (· ∈ VLCtx.fvars ((some (l₀.fvarId, []), VLocalDecl.vlet T' v') :: Δ)) e :=
      FVarsIn.mono fun _ h => by simp only [VLCtx.fvars_cons_some]; exact .tail _ h
    simp only [Pure.findLocal, List.find?_cons] at hl
    split at hl
    · cases hl
      exact ⟨mono hT.fvarsIn, fun v h => by rw [hv] at h; cases h; exact mono hval.fvarsIn⟩
    · have ⟨h1, h2⟩ := ih hl
      exact ⟨mono h1, fun v h => mono (h2 v h)⟩

/-- The `letE` step of `erasePure_erases`, from `visitExpr` at the fuels up to `fuel` (`ih`): the
value is visited under the `let`'s own local, which it does not mention, so as under the caller's
locals (`visit_agree`), and erased there; the body as in `visitExpr_lam_step`, under the `let`'s
free-variable entry. Reference: the `tLetIn` case of `erases_erase` (`MR E/ErasureFunction.v:1228`),
rule `erases_tLetIn` (`MR E/Extract.v:96`); DV-13. -/
theorem visitExpr_letE_step (hG : CoreEnv venv P decls) {fuel : Nat}
    (ih : ∀ m ≤ fuel, ∀ e, ExprSpec venv view cfg decls m e) {n : Name} {T v b : Expr}
    {nd : Bool} : ExprSpec venv view cfg decls (fuel + 1) (.letE n T v b nd) := by
  intro Us Δ rc S e' st tc ps r st' ps' hctx hsc hocc hok he hrun
  rw [visitExpr] at hrun
  rcases oracle_run hrun with ⟨hor, rfl, rfl, rfl⟩ | ⟨-, hrun⟩
  · exact visitExpr_box hG hctx hok he hor
  cases fuel with
  | zero => cases hrun
  | succ k =>
  rw [visitLet] at hrun
  simp only [letMonocular, withLocalDef] at hrun
  rw [runPure_bind, fresh_run, Except.ok_bind'] at hrun
  dsimp only at hrun
  rw [runPure_withReader, runPure_bind] at hrun
  obtain ⟨⟨⟨tv, st₁⟩, ps₁⟩, hval, hrun⟩ := Except.ok_of_bind hrun
  dsimp only at hrun
  rw [runPure_bind] at hrun
  obtain ⟨⟨⟨tb, st₂⟩, ps₂⟩, hbody, hrun⟩ := Except.ok_of_bind hrun
  dsimp only at hrun
  generalize hx : pureFVar ps.next = x at hval hbody hrun
  rw [mkLetIn_run (l := ⟨x, n, T, some v⟩) (by simp [Pure.findLocal])] at hrun
  cases hrun
  have hfv := TrS.fvarsIn he
  cases he with
  | @letE v₀ T' _ _ _ _ _ _ _ hvT htT htv hb =>
  have hxΔ : x ∉ Δ.fvars := hx ▸ hctx.fresh ps.next (Nat.le_refl _)
  -- the value, under the `let`'s own local, is visited as under the caller's locals
  have hval' : (visitExpr (m := PureM) k v).runPure st
      { tc with lctx := tc.lctx.mkLetDecl x n T v nd } ⟨decls, view⟩ ⟨ps.next + 1⟩ =
        .ok ((tv, st₁), ps₁) := by
    rw [← hval]
    refine (visit_agree (S := (· ≠ x)) (tc := { tc with lctx := tc.lctx.mkLetDecl x n T v nd })
      (ls₁ := ⟨x, n, T, some v⟩ :: tc.locals) (ls₂ := tc.locals) hG.closed ?_ ?_ ?_).symm
    · intro y hy l hl
      have hne : (x == y) = false := by simpa using Ne.symm hy
      simp only [Pure.findLocal, List.find?_cons, hne] at hl
      have ⟨h1, h2⟩ := hctx.locals.support hl
      exact ⟨h1.mono fun z hz hzx => hxΔ (hzx ▸ hz),
        fun w hw => (h2 w hw).mono fun z hz hzx => hxΔ (hzx ▸ hz)⟩
    · intro y hy
      have hne : (x == y) = false := by simpa using Ne.symm hy
      simp [Pure.findLocal, hne]
    · exact hfv.2.1.mono fun z hz hzx => hxΔ (hzx ▸ hz)
  have hctxv : CtxOK venv Us rc cfg { tc with lctx := tc.lctx.mkLetDecl x n T v nd } Δ
      ⟨ps.next + 1⟩ := (hctx.setLctx _).mono (Nat.le_succ _)
  have ⟨herv, hdepsv, hgrv⟩ := ih k (Nat.le_succ _) v hctxv hsc
    (fun c hc => hocc c (by simp [OccursV, hc])) hok htv hval'
  have hloc : LocalsOK venv Us (⟨x, n, T, some v⟩ :: tc.locals)
      ((some (x, []), .vlet T' v₀) :: Δ) :=
    .letE hctx.locals hxΔ rfl htT htv hvT
  have hctx' := (hctx.push (l := ⟨x, n, T, some v⟩) (L := tc.lctx.mkLetDecl x n T v nd)
    hx.symm hloc).mono hgrv.next
  have hwf := hloc.wf
  have hbody' : TrS venv Us ((some (x, []), .vlet T' v₀) :: Δ) (b.instantiate1' (.fvar x)) _ :=
    TrS.inst_fvar hG.prog.ordered hwf.1 hb
  have ⟨herb, hdepsb, hgrb⟩ := ih k (Nat.le_succ _) _ hctx' hsc
    (fun c hc => by
      rw [OccursV.instantiate1_fvar] at hc
      exact hocc c (by simp [OccursV, hc])) hgrv.ok hbody' hbody
  have hsc' : FVarsIn (· ≠ x) b := hfv.2.2.mono fun y hy hyx => hxΔ (hyx ▸ hy)
  have hrcx : RcFresh rc x := fun c t ht =>
    ⟨(hctx.rcFresh c t ht).1, hx ▸ (hctx.rcFresh c t ht).2 _ (Nat.le_refl _)⟩
  have hcl : closedn 0 tb = true := by
    have := Erases.closed (fun c t ht => (hctx.rcFresh c t ht).1) hbody' herb
    rwa [show VLCtx.bvars ((some (x, []), VLocalDecl.vlet T' v₀) :: Δ) = 0 from hwf.2] at this
  rw [abstract_eq_abstract1 hcl]
  exact ⟨.letE htT htv herv (Erases.uninstantiateN .zero hrcx hsc' herb),
    .letIn (hdepsv.ext hgrb.ext) (hdepsb.abstract1 0),
    (Grows.trans ⟨hgrv.ok, hgrv.ext, Nat.le_trans (Nat.le_succ _) hgrv.next, hgrv.scope⟩ hgrb)⟩


/-- The head of a translated application spine translates. Reference: `inversion_App`
(`MR P/PCUICInversion.v:188`). -/
theorem TrS.mkAppList_head {Us : List Name} {Δ : VLCtx} :
    ∀ (l : List Expr) {f : Expr} {e' : VExpr}, TrS venv Us Δ (Expr.mkAppList f l) e' →
      ∃ f', TrS venv Us Δ f f'
  | [], _, _, h => ⟨_, h⟩
  | _ :: l, _, _, h => by
    obtain ⟨_, h1⟩ := TrS.mkAppList_head l h
    cases h1 with
    | app _ _ hf _ => exact ⟨_, hf⟩

/-- A constant in a value position of the head of a spine is in a value position of the spine.
Reference: none. -/
theorem OccursV.mkAppList_head {c : Name} :
    ∀ (l : List Expr) {f : Expr}, OccursV c f = true → OccursV c (Expr.mkAppList f l) = true
  | [], _, h => h
  | _ :: l, _, h => OccursV.mkAppList_head l (by simp [OccursV, h])

/-- A spine headed by an atom constant is an atom spine. Reference: none (DV-11). -/
theorem AtomSpine.of_getAppFn {σ : EvalEnv} {c : Name} {us : List Level} (ha : σ.isAtom c = true) :
    ∀ {e : Expr}, e.getAppFn = .const c us → AtomSpine σ e
  | .const .., h => by cases h; exact .const ha
  | .app f _, h => .app (AtomSpine.of_getAppFn ha (e := f) h)
  | .bvar _, h | .fvar _, h | .mvar _, h | .sort _, h | .lam .., h | .forallE .., h
  | .letE .., h | .lit _, h | .mdata .., h | .proj .., h => nomatch h

/-- `visitConst` at the pure backend, from `visitMutual` at the fuels up to `j` (`ihM`), on a
constant that is no atom and is in the scope or a fix variable: a fix variable of the block being
erased erases the constant to its admissible target (`Erases.constRec`, DV-7); another constant
erases to the `tConst` of its kername, which `get_constant_kername` returns after registering the
constant through `visitMutual` if needed (`get_constant_kername_ok`, `StateOK.kername`).
Reference: the `tConst` case of `erases_erase` (`MR E/ErasureFunction.v:1228`), rule
`erases_tConst` (`MR E/Extract.v:104`), and `erase_global_erases_deps`
(`MR E/ErasureFunctionProperties.v:172`). -/
theorem visitConst_spec {j : Nat}
    (ihM : ∀ m ≤ j, ∀ c, MutualSpec venv view cfg decls m c) {Us : List Name} {Δ : VLCtx}
    {rc : Name → LBTerm → Prop} {st st' : ErasureState} {tc : TravCtx} {ps ps' : PureState}
    {r : LBTerm} {c : Name} {us : List Level}
    (hctx : CtxOK venv Us rc cfg tc Δ ps) (hsc : ScopeOK decls S)
    (hS : S c ∨ (tc.fixvars.bind (fun m => m[c]?)).isSome)
    (hok : StateOK venv (evalEnvOf view cfg decls) st)
    (hat : (evalEnvOf view cfg decls).isAtom c = false)
    (hrun : (visitConst (m := PureM) j (.const c us)).runPure st tc ⟨decls, view⟩ ps =
      .ok ((r, st'), ps')) :
    Erases venv Us (evalEnvOf view cfg decls).isAtom rc Δ (.const c us) r ∧
      ErasesDeps venv (evalEnvOf view cfg decls) st'.gdecls r ∧
      Grows venv (evalEnvOf view cfg decls) S st st' ps ps' := by
  cases j with
  | zero => cases hrun
  | succ i =>
  rw [visitConst, runPure_read_bind] at hrun
  cases hfx : tc.fixvars.bind (fun hmap => hmap[c]?) with
  | some x =>
    rw [hfx] at hrun
    cases hrun
    exact ⟨.constRec hat (hctx.fixvars c x hfx), .fvar, .refl hok⟩
  | none =>
    rw [hfx] at hrun
    dsimp only at hrun
    rw [runPure_bind] at hrun
    obtain ⟨⟨⟨kn, st₁⟩, ps₁⟩, hk, hrun⟩ := Except.ok_of_bind hrun
    cases hrun
    cases i with
    | zero => cases hk
    | succ h =>
    obtain ⟨hcase, huniq⟩ := get_constant_kername_ok hk
    rcases hcase with ⟨hreg, rfl, rfl⟩ | ⟨hnew, hmut⟩
    · obtain ⟨rfl, hdeps⟩ := hok.kername hreg
      exact ⟨.const hat, hdeps, .refl hok⟩
    · have hSc : S c := hS.resolve_right (by simp [hfx])
      obtain ⟨hgr, kn', hkn'⟩ :=
        ihM h (Nat.le_succ_of_le (Nat.le_succ _)) c hsc hSc hctx.config hok hnew hmut
      cases huniq kn' hkn'
      obtain ⟨rfl, hdeps⟩ := hgr.ok.kername hkn'
      exact ⟨.const hat, hdeps, hgr⟩

/-- `visitAppArgs (j + 1) tf args` at the pure backend, from `visitExpr` at `j` (`ih`): applying an
erasure of the head to the erasures of the arguments, one at a time, erases the spine. Reference:
the `tApp` case of `erases_erase` (`MR E/ErasureFunction.v:1228`), rule `erases_tApp`
(`MR E/Extract.v:101`). -/
theorem visitAppArgs_spec {j : Nat}
    (ih : ∀ e, ExprSpec venv view cfg decls j e) {Us : List Name} {Δ : VLCtx}
    {rc : Name → LBTerm → Prop} {st st' : ErasureState} {tc : TravCtx} {ps ps' : PureState}
    {r tf : LBTerm} {f₀ : Expr} {args : Array Expr} {e' : VExpr}
    (hctx : CtxOK venv Us rc cfg tc Δ ps) (hsc : ScopeOK decls S)
    (hocc : ∀ c, OccursV c (Expr.mkAppList f₀ args.toList) = true →
      S c ∨ (tc.fixvars.bind (fun m => m[c]?)).isSome)
    (hok : StateOK venv (evalEnvOf view cfg decls) st)
    (he : TrS venv Us Δ (Expr.mkAppList f₀ args.toList) e')
    (hf : Erases venv Us (evalEnvOf view cfg decls).isAtom rc Δ f₀ tf)
    (hdf : ErasesDeps venv (evalEnvOf view cfg decls) st.gdecls tf)
    (hrun : (visitAppArgs (m := PureM) (j + 1) tf args).runPure st tc ⟨decls, view⟩ ps =
      .ok ((r, st'), ps')) :
    Erases venv Us (evalEnvOf view cfg decls).isAtom rc Δ (Expr.mkAppList f₀ args.toList) r ∧
      ErasesDeps venv (evalEnvOf view cfg decls) st'.gdecls r ∧
      Grows venv (evalEnvOf view cfg decls) S st st' ps ps' := by
  rw [visitAppArgs, ← Array.foldlM_toList] at hrun
  generalize args.toList = l at hocc he hrun
  induction l generalizing f₀ tf st ps e' with
  | nil =>
    cases hrun
    exact ⟨hf, hdf, .refl hok⟩
  | cons a l ihl =>
    rw [List.foldlM_cons, runPure_bind] at hrun
    obtain ⟨⟨⟨x, st₁⟩, ps₁⟩, hx, hrun⟩ := Except.ok_of_bind hrun
    rw [runPure_bind] at hx
    obtain ⟨⟨⟨ta, st₂⟩, ps₂⟩, ha, hx⟩ := Except.ok_of_bind hx
    cases hx
    obtain ⟨_, hfa⟩ := TrS.mkAppList_head l he
    cases hfa with
    | app _ _ _ hta =>
    have ⟨hera, hdepsa, hgra⟩ := ih a hctx hsc
      (fun c hc => hocc c (OccursV.mkAppList_head l (by simp [OccursV, hc]))) hok hta ha
    have ⟨her, hdeps, hgr⟩ := ihl (f₀ := .app f₀ a) (tf := .app tf ta)
      (hctx := hctx.mono hgra.next) (hocc := hocc) (hok := hgra.ok) (he := he)
      (hf := .app hf hera) (hdf := .app (hdf.ext hgra.ext) hdepsa) (hrun := hrun)
    exact ⟨her, hdeps, hgra.trans hgr⟩

/-- `visitApp (k + 1)` at the pure backend, on a spine the oracle does not erase, from `visitExpr`
and `visitMutual` at the fuels up to `k` (`ih`, `ihM`): a spine headed by a constant is erased head
first by `visitConst` (the head is no atom, else the oracle would have answered `true`,
`Pure.isErasable_atom`), another spine by erasing its head with `visitExpr`; then the arguments.
Reference: the `tApp` and `tConst` cases of `erases_erase` (`MR E/ErasureFunction.v:1228`). -/
theorem visitApp_spec {k : Nat}
    (ih : ∀ m ≤ k, ∀ e, ExprSpec venv view cfg decls m e)
    (ihM : ∀ m ≤ k, ∀ c, MutualSpec venv view cfg decls m c) {Us : List Name} {Δ : VLCtx}
    {rc : Name → LBTerm → Prop} {st st' : ErasureState} {tc : TravCtx} {ps ps' : PureState}
    {r : LBTerm} {e : Expr} {e' : VExpr}
    (hctx : CtxOK venv Us rc cfg tc Δ ps) (hsc : ScopeOK decls S)
    (hocc : ∀ c, OccursV c e = true → S c ∨ (tc.fixvars.bind (fun m => m[c]?)).isSome)
    (hok : StateOK venv (evalEnvOf view cfg decls) st) (he : TrS venv Us Δ e e')
    (hor : Pure.isErasable ⟨decls⟩ oracleFuel tc.locals e = .ok false)
    (hrun : (visitApp (m := PureM) (k + 1) e).runPure st tc ⟨decls, view⟩ ps =
      .ok ((r, st'), ps')) :
    Erases venv Us (evalEnvOf view cfg decls).isAtom rc Δ e r ∧
      ErasesDeps venv (evalEnvOf view cfg decls) st'.gdecls r ∧
      Grows venv (evalEnvOf view cfg decls) S st st' ps ps' := by
  have heq := Expr.mkAppList_getAppArgsList e
  have hl : e.getAppArgs.toList = e.getAppArgsList := Expr.getAppArgs_toList
  rw [← heq, ← hl] at hocc he ⊢
  rw [visitApp] at hrun
  split at hrun
  · rename_i c us hc
    cases k with
    | zero => cases hrun
    | succ j =>
    rw [visitConstApp, Expr.withApp_eq] at hrun
    split at hrun
    · rename_i c' us' hc'
      rw [hc] at hc'
      cases hc'
      rw [runPure_bind] at hrun
      rw [show (liftM (Backend.casesInfo? (m := PureM) c) : EraseT PureM _).runPure st tc
        ⟨decls, view⟩ ps = .ok ((none, st), ps) from rfl, Except.ok_bind'] at hrun
      dsimp only at hrun
      rw [runPure_bind] at hrun
      rw [show (liftM (Backend.ctorArity? (m := PureM) c) : EraseT PureM _).runPure st tc
        ⟨decls, view⟩ ps = .ok ((none, st), ps) from rfl, Except.ok_bind'] at hrun
      dsimp only at hrun
      rw [runPure_bind] at hrun
      obtain ⟨⟨⟨tf, st₁⟩, ps₁⟩, hf, hrun⟩ := Except.ok_of_bind hrun
      have hat : (evalEnvOf view cfg decls).isAtom c = false := by
        cases ha : (evalEnvOf view cfg decls).isAtom c with
        | false => rfl
        | true =>
          have := Pure.isErasable_atom (cx := ⟨decls⟩) (σ := evalEnvOf view cfg decls) rfl
            (AtomSpine.of_getAppFn ha hc) hor
          cases this
      rw [hc] at hf
      have ⟨herf, hdf, hgf⟩ := visitConst_spec (fun m hm => ihM m (Nat.le_succ_of_le hm)) hctx hsc
        (hocc c (OccursV.mkAppList_head _ (by rw [hc]; simp [OccursV]))) hok hat hf
      rw [← hc] at herf
      cases j with
      | zero => cases hrun
      | succ i =>
      have ⟨her, hdeps, hgr⟩ := visitAppArgs_spec (ih i (Nat.le_succ_of_le (Nat.le_succ _)))
        (hctx.mono hgf.next) hsc hocc hgf.ok he herf hdf hrun
      exact ⟨her, hdeps, hgf.trans hgr⟩
    · rename_i hne
      exact absurd hc (hne c us)
  · rw [Expr.withApp_eq, runPure_bind] at hrun
    obtain ⟨⟨⟨tf, st₁⟩, ps₁⟩, hf, hrun⟩ := Except.ok_of_bind hrun
    obtain ⟨_, htf⟩ := TrS.mkAppList_head _ he
    have ⟨herf, hdf, hgf⟩ := ih k (Nat.le_refl _) _ hctx hsc
      (fun c hc => hocc c (OccursV.mkAppList_head _ hc)) hok htf hf
    cases k with
    | zero => cases hrun
    | succ i =>
    have ⟨her, hdeps, hgr⟩ := visitAppArgs_spec (ih i (Nat.le_succ _))
      (hctx.mono hgf.next) hsc hocc hgf.ok he herf hdf hrun
    exact ⟨her, hdeps, hgf.trans hgr⟩

/-- The `app` step of `erasePure_erases`, from `visitExpr` and `visitMutual` at the fuels up to
`fuel` (`ih`, `ihM`), through `visitApp_spec`. Reference: the `tApp` case of `erases_erase`
(`MR E/ErasureFunction.v:1228`), rule `erases_tApp` (`MR E/Extract.v:101`). -/
theorem visitExpr_app_step (hG : CoreEnv venv P decls) {fuel : Nat}
    (ih : ∀ m ≤ fuel, ∀ e, ExprSpec venv view cfg decls m e)
    (ihM : ∀ m ≤ fuel, ∀ c, MutualSpec venv view cfg decls m c) {f a : Expr} :
    ExprSpec venv view cfg decls (fuel + 1) (.app f a) := by
  intro Us Δ rc S e' st tc ps r st' ps' hctx hsc hocc hok he hrun
  rw [visitExpr] at hrun
  rcases oracle_run hrun with ⟨hor, rfl, rfl, rfl⟩ | ⟨hor, hrun⟩
  · exact visitExpr_box hG hctx hok he hor
  cases fuel with
  | zero => cases hrun
  | succ k =>
  exact visitApp_spec (fun m hm => ih m (Nat.le_succ_of_le hm))
    (fun m hm => ihM m (Nat.le_succ_of_le hm)) hctx hsc hocc hok he hor hrun

/-- The `const` step of `erasePure_erases`, from `visitExpr` and `visitMutual` at the fuels up to
`fuel` (`ih`, `ihM`): a constant is erased as an application to no argument (`visitApp_spec`).
Reference: the `tConst` case of `erases_erase` (`MR E/ErasureFunction.v:1228`), rule
`erases_tConst` (`MR E/Extract.v:104`). -/
theorem visitExpr_const_step (hG : CoreEnv venv P decls) {fuel : Nat}
    (ih : ∀ m ≤ fuel, ∀ e, ExprSpec venv view cfg decls m e)
    (ihM : ∀ m ≤ fuel, ∀ c, MutualSpec venv view cfg decls m c) {c : Name} {us : List Level} :
    ExprSpec venv view cfg decls (fuel + 1) (.const c us) := by
  intro Us Δ rc S e' st tc ps r st' ps' hctx hsc hocc hok he hrun
  rw [visitExpr] at hrun
  rcases oracle_run hrun with ⟨hor, rfl, rfl, rfl⟩ | ⟨hor, hrun⟩
  · exact visitExpr_box hG hctx hok he hor
  cases fuel with
  | zero => cases hrun
  | succ k =>
  exact visitApp_spec (fun m hm => ih m (Nat.le_succ_of_le hm))
    (fun m hm => ihM m (Nat.le_succ_of_le hm)) hctx hsc hocc hok he hor hrun


/-- The type the oracle infers for a sort or a Π is a sort. Reference: `infer` on `tSort` and
`tProd` (`MR S/PCUICSafeRetyping.v:306`, `:308`). -/
theorem Pure.inferType_type {cx : Pure.Ctx} {ls : List Local} {Γ : List Expr} {e : Expr}
    (hk : e.isSort ∨ e.isForall) : ∀ {f T}, Pure.inferType cx f ls Γ e = .ok T → ∃ w, T = .sort w
  | 0, _, h => absurd h (by rw [Pure.inferType]; exact Except.throw_ne_ok)
  | f + 1, T, h => by
    cases e with
    | sort u => rw [Pure.inferType] at h; cases h; exact ⟨_, rfl⟩
    | forallE n t b bi =>
      rw [Pure.inferType] at h
      obtain ⟨_, _, h⟩ := Except.ok_of_bind h
      obtain ⟨_, _, h⟩ := Except.ok_of_bind h
      split at h
      · obtain ⟨_, _, h⟩ := Except.ok_of_bind h
        obtain ⟨_, _, h⟩ := Except.ok_of_bind h
        split at h
        · cases h; exact ⟨_, rfl⟩
        · exact absurd h Except.throw_ne_ok
      · exact absurd h Except.throw_ne_ok
    | _ => simp [Expr.isSort, Expr.isForall] at hk

/-- The oracle answers "erasable" on a sort or a Π whenever it answers: its type is a sort, an
arity. Reference: `is_erasableb` (`MR E/ErasureFunction.v:894`) on a type. -/
theorem Pure.isErasable_type {cx : Pure.Ctx} {ls : List Local} {e : Expr} {fuel : Nat} {b : Bool}
    (hk : e.isSort ∨ e.isForall) (h : Pure.isErasable cx fuel ls e = .ok b) : b = true := by
  simp only [Pure.isErasable] at h
  obtain ⟨T, h1, h⟩ := Except.ok_of_bind h
  obtain ⟨w, rfl⟩ := Pure.inferType_type hk h1
  obtain ⟨b', h2, h⟩ := Except.ok_of_bind h
  obtain rfl := Pure.isArity_arityShape .sort h2
  cases h
  rfl

/-- The steps of `erasePure_erases` on the remaining shapes: a sort or a Π is erased to `□`, since
the oracle answers `true` on it when it answers (`Pure.isErasable_type`); a bound variable, a
metavariable, a literal or a projection has no translation in a context of free-variable entries.
Reference: the `tSort` and `tProd` cases of `erase` (`MR E/ErasureFunction.v:998`, `:1002`),
unreachable after `is_erasableb`. -/
theorem visitExpr_other_step (hG : CoreEnv venv P decls) {fuel : Nat} {e : Expr}
    (hk : (e.isBVar || e.isSort || e.isForall || e.isMVar || e.isLit || e.isProj) = true) :
    ExprSpec venv view cfg decls (fuel + 1) e := by
  intro Us Δ rc S e' st tc ps r st' ps' hctx hsc hocc hok he hrun
  have htype : e.isSort ∨ e.isForall → Erases venv Us (evalEnvOf view cfg decls).isAtom rc Δ e r ∧
      ErasesDeps venv (evalEnvOf view cfg decls) st'.gdecls r ∧
      Grows venv (evalEnvOf view cfg decls) S st st' ps ps' := fun hs => by
    cases e <;> simp only [Expr.isSort, Expr.isForall, Bool.false_eq_true, or_self] at hs <;>
    · rw [visitExpr] at hrun
      rcases oracle_run hrun with ⟨hor, rfl, rfl, rfl⟩ | ⟨hor, -⟩
      · exact visitExpr_box hG hctx hok he hor
      · cases Pure.isErasable_type (by simp [Expr.isSort, Expr.isForall]) hor
  cases e with
  | bvar i =>
    cases he with
    | bvar h =>
      have := VLCtx.find?_inl_lt h
      rw [hctx.locals.wf.2] at this
      exact absurd this (Nat.not_lt_zero _)
  | mvar | lit | proj => cases he
  | sort | forallE => exact htype (by simp [Expr.isSort, Expr.isForall])
  | _ => simp [Expr.isBVar, Expr.isSort, Expr.isForall, Expr.isMVar, Expr.isLit, Expr.isProj] at hk

/-- A run of `x` at the pure backend keeps the registered constants, the λ□ environment and the
counter; the auto-inlining bookkeeping of `visitMutual` is such a run. Reference: none. -/
def KeepsCG (pc : PureCtx) {α : Type} (x : EraseT PureM α) : Prop :=
  ∀ st tc ps r st' ps', x.runPure st tc pc ps = .ok ((r, st'), ps') →
    st'.constants = st.constants ∧ st'.gdecls = st.gdecls ∧ ps' = ps

/-- `pure` keeps the state. Reference: none. -/
theorem KeepsCG.pure {α : Type} (a : α) : KeepsCG pc (Pure.pure a : EraseT PureM α) := by
  intro st tc ps r st' ps' h; cases h; exact ⟨rfl, rfl, rfl⟩

/-- `get` keeps the state. Reference: none. -/
theorem KeepsCG.get : KeepsCG pc (MonadState.get : EraseT PureM ErasureState) := by
  intro st tc ps r st' ps' h; cases h; exact ⟨rfl, rfl, rfl⟩

/-- A `modify` that keeps the registered constants and the λ□ environment. Reference: none. -/
theorem KeepsCG.modify {f : ErasureState → ErasureState}
    (hf : ∀ s, (f s).constants = s.constants ∧ (f s).gdecls = s.gdecls) :
    KeepsCG pc (_root_.modify f : EraseT PureM PUnit) := by
  intro st tc ps r st' ps' h; cases h; exact ⟨(hf st).1, (hf st).2, rfl⟩

/-- The pure backend's `log` keeps the state. Reference: none. -/
theorem KeepsCG.log (m : String) :
    KeepsCG pc (liftM (Backend.log (m := PureM) m) : EraseT PureM Unit) := by
  intro st tc ps r st' ps' h; cases h; exact ⟨rfl, rfl, rfl⟩

/-- The pure backend's `isInstance` keeps the state. Reference: none. -/
theorem KeepsCG.isInstance (n : Name) :
    KeepsCG pc (liftM (Backend.isInstance (m := PureM) n) : EraseT PureM Bool) := by
  intro st tc ps r st' ps' h; cases h; exact ⟨rfl, rfl, rfl⟩

/-- A bind of runs that keep the state keeps it. Reference: none. -/
theorem KeepsCG.bind {α β : Type} {x : EraseT PureM α} {k : α → EraseT PureM β}
    (hx : KeepsCG pc x) (hk : ∀ a, KeepsCG pc (k a)) : KeepsCG pc (x >>= k) := by
  intro st tc ps r st' ps' h
  rw [runPure_bind] at h
  obtain ⟨⟨⟨a, st₁⟩, ps₁⟩, h1, h2⟩ := Except.ok_of_bind h
  obtain ⟨c1, g1, p1⟩ := hx _ _ _ _ _ _ h1
  obtain ⟨c2, g2, p2⟩ := hk a _ _ _ _ _ _ h2
  exact ⟨c2.trans c1, g2.trans g1, p2.trans p1⟩

/-- A bind on `read` keeps the state when the continuation does. Reference: none. -/
theorem KeepsCG.read_bind {α : Type} {k : TravCtx → EraseT PureM α} (hk : ∀ c, KeepsCG pc (k c)) :
    KeepsCG pc (read >>= k) := by
  intro st tc ps r st' ps' h
  rw [runPure_read_bind] at h
  exact hk tc _ _ _ _ _ _ h

/-- A conditional keeps the state when its branches do. Reference: none. -/
theorem KeepsCG.ite {α : Type} {c : Prop} [Decidable c] {a b : EraseT PureM α}
    (ha : c → KeepsCG pc a) (hb : ¬c → KeepsCG pc b) : KeepsCG pc (if c then a else b) := by
  by_cases h : c
  · rw [if_pos h]; exact ha h
  · rw [if_neg h]; exact hb h

/-- What `KeepsCG` says of a successful run. Reference: none. -/
theorem KeepsCG.run {α : Type} {x : EraseT PureM α} {st st' : ErasureState} {tc : TravCtx}
    {ps ps' : PureState} {r : α} (h : KeepsCG pc x)
    (hrun : x.runPure st tc pc ps = .ok ((r, st'), ps')) :
    st'.constants = st.constants ∧ st'.gdecls = st.gdecls ∧ ps' = ps :=
  h _ _ _ _ _ _ hrun

/-- At the pure backend, the traversal's `name_occurs` is `nameOccurs` (no `_unsafe_rec`
stripping). Reference: none (DV-7). -/
theorem name_occurs_eq : name_occurs (m := PureM) = nameOccurs := by
  funext n e
  induction e <;> simp [name_occurs, nameOccurs, remove_unsafe_rec, *]
  rfl

/-- The non-recursive `const` step of `erasePure_erases`, from `visitExpr` at the fuels up to
`fuel` (`ih`): `visitMutual` on a declaration that is an axiom, is remapped (`axiomatized`), or
is a definition, theorem or opaque that is not recursive (`hnr`). An axiom or a remapped
declaration is registered by `addAxiom` (`addAxiom_ok`). Otherwise the value is erased as in the
empty context (`visit_agree`, DV-13), in a scope that holds no member of the declaration's block
(`CoreEnv.valueScope`), so the declaration is still unregistered when `StateOK.registerDef`
registers it; the auto-inlining bookkeeping after it keeps the state (`KeepsCG`). Reference:
`erase_constant_body` (`MR E/ErasureFunction.v:1309`) in the `ConstantDecl` step of
`erase_global_deps` (`MR E/ErasureFunction.v:1602`); `erase_global_deps_fresh`
(`MR E/ErasureFunctionProperties.v:1206`). -/
theorem visitMutual_nonrec_step (hG : CoreEnv venv P decls) {fuel : Nat}
    (ih : ∀ m ≤ fuel, ∀ e, ExprSpec venv view cfg decls m e) {c : Name} {ci : ConstantInfo}
    (hci : findDecl decls c = some ci)
    (hnr : ∀ v, ci.value? (allowOpaque := true) = some v → axiomatized view cfg ci = false →
      RecursiveDecl ci = false) :
    MutualSpec venv view cfg decls (fuel + 1) c := by
  intro S st tc ps st' ps' hsc hc hcfg hok hnew hrun
  have hname : ci.name = c := by simpa using List.find?_some hci
  have hci' : ci ∈ decls := List.mem_of_find?_eq_some hci
  have hciP : ci ∈ P := List.mem_of_find?_eq_some (hG.sub ci hci')
  have hall : ci.all.length = 1 := by
    cases hv : ci.value? (allowOpaque := true) with
    | none => rw [hG.prog.all_of_value?_none hciP hv]; rfl
    | some v =>
      cases hax : axiomatized view cfg ci with
      | true =>
        simp only [axiomatized, Bool.and_eq_true, beq_iff_eq] at hax
        exact hax.1.1
      | false =>
        have := hnr v hv hax
        simp only [RecursiveDecl, Bool.or_eq_false_iff, bne_eq_false_iff_eq] at this
        exact this.1
  -- an axiom: `addAxiom` registers it
  have haxiom : ∀ {sd : ErasureState}, sd.constants = st.constants → sd.gdecls = st.gdecls →
      (ci.value? (allowOpaque := true) = none ∨ axiomatized view cfg ci = true) →
      (addAxiom (m := PureM) c).runPure sd tc ⟨decls, view⟩ ps = .ok (((), st'), ps') →
      Grows venv (evalEnvOf view cfg decls) S st st' ps ps' ∧
        ∃ kn, st'.constants[c]? = some kn := by
    intro sd hcd hgd hax hrun
    obtain ⟨st'', hrun'', hc'', hok'', hext''⟩ :=
      addAxiom_ok (hok.congr hcd hgd) hG.inj hci (by rw [hcd]; exact hnew) hax
    rw [hrun''] at hrun
    cases hrun
    refine ⟨⟨hok'', by rw [← hgd]; exact hext'', Nat.le_refl _, fun c' kn h0 h1 => ?_⟩,
      toKername c, by rw [hc'']; exact Std.HashMap.getElem?_insert_self⟩
    rw [hc'', Std.HashMap.getElem?_insert] at h1
    split at h1
    · rename_i hcc
      rw [← beq_iff_eq.1 hcc]
      exact hc
    · rw [hcd, h0] at h1
      cases h1
  have hctx0 : CtxOK venv ci.levelParams (fun _ _ => False) cfg
      { lctx := tc.lctx, locals := [], config := tc.config } [] ps :=
    ⟨.nil, (fun _ _ h => nomatch h), (fun _ _ h => h.elim), (fun _ _ h => nomatch h), hcfg⟩
  rw [visitMutual, runPure_bind] at hrun
  rw [show (liftM (Backend.declInfo? (m := PureM) c) : EraseT PureM _).runPure st tc
    ⟨decls, view⟩ ps = .ok ((some ci, st), ps) by
      show Except.ok ((findConst decls c, st), ps) = _; rw [show findConst decls c = _ from hci],
    Except.ok_bind'] at hrun
  dsimp only at hrun
  rw [runPure_bind, show (liftM (Backend.inlineAttr? (m := PureM) c) : EraseT PureM _).runPure st
    tc ⟨decls, view⟩ ps = .ok ((view.inlineAttr? c, st), ps) from rfl, Except.ok_bind'] at hrun
  dsimp only at hrun
  rw [runPure_bind, show (liftM (Backend.inlineAttr? (m := PureM) c) : EraseT PureM _).runPure st
    tc ⟨decls, view⟩ ps = .ok ((view.inlineAttr? c, st), ps) from rfl, Except.ok_bind'] at hrun
  dsimp only at hrun
  simp only [Option.get!_some, hall, beq_self_eq_true, Bool.true_and, ↓reduceIte] at hrun
  -- the `@[inline]` bookkeeping before the value touches only `inlinings`
  rcases hia : view.inlineAttr? c with _ | ⟨_ | _ | _ | _ | _⟩ <;>
    simp only [hia, ↓reduceIte, Bool.false_eq_true] at hrun
  all_goals first
    | (rw [runPure_bind] at hrun
       replace hrun := Except.ok_of_bind hrun
       obtain ⟨⟨⟨_, sa⟩, pa⟩, h1, hrun⟩ := hrun
       obtain ⟨ca, ga, hpa⟩ := KeepsCG.run (KeepsCG.log _) h1
       subst pa
       rw [runPure_bind] at hrun
       replace hrun := Except.ok_of_bind hrun
       obtain ⟨⟨⟨_, sb⟩, pb⟩, h2, hrun⟩ := hrun
       obtain ⟨cb, gb, hpb⟩ := KeepsCG.run (KeepsCG.modify fun _ => ⟨rfl, rfl⟩) h2
       subst pb
       have hcb : sb.constants = st.constants := cb.trans ca
       have hgb : sb.gdecls = st.gdecls := gb.trans ga
       clear ca ga cb gb h1 h2)
    | (obtain ⟨sb, hsb⟩ : ∃ sb, sb = st := ⟨st, rfl⟩
       rw [← hsb] at hrun
       have hcb : sb.constants = st.constants := by rw [hsb]
       have hgb : sb.gdecls = st.gdecls := by rw [hsb]
       clear hsb)
  -- the value and the `@[extern]` test
  all_goals
    rw [runPure_bind] at hrun
    replace hrun := Except.ok_of_bind hrun
    obtain ⟨⟨⟨_, sc⟩, pc'⟩, h1, hrun⟩ := hrun
    cases h1
    rw [runPure_read_bind, hcfg] at hrun
    dsimp only at hrun
  -- `cfg.1` is the configuration's `extern` policy
  all_goals
    rcases hv : ci.value? (allowOpaque := true) with _ | v <;> cases hie : view.isExtern c <;>
      cases hext : cfg.1 <;> simp only [hv, hie, hext] at hrun
  all_goals first
    | -- an axiom
      (rw [runPure_bind] at hrun
       replace hrun := Except.ok_of_bind hrun
       obtain ⟨⟨⟨_, sd⟩, pd⟩, h1, hrun⟩ := hrun
       obtain ⟨cd, gd, hpd⟩ := KeepsCG.run (KeepsCG.log _) h1
       subst pd
       exact haxiom (cd.trans hcb) (gd.trans hgb)
         (by first
           | exact .inl hv
           | exact .inr (by rw [axiomatized, hall, hname, hie, hext]; rfl)) hrun)
    | -- a definition, after the log of `@[extern]` with `preferLogical`
      (rw [runPure_bind] at hrun
       replace hrun := Except.ok_of_bind hrun
       obtain ⟨⟨⟨_, sb⟩, pd⟩, h1, hrun⟩ := hrun
       obtain ⟨cd, gd, hpd⟩ := KeepsCG.run (KeepsCG.log _) h1
       subst pd
       replace hcb := cd.trans hcb
       replace hgb := gd.trans hgb
       clear cd gd h1)
    | skip
  -- a definition: its value is erased as in the empty context, then registered
  all_goals
    have hax : axiomatized view cfg ci = false := by rw [axiomatized, hall, hname, hie, hext]; rfl
    have hrec := hnr v hv hax
    have hval : ci.value! (allowOpaque := true) = v := by rw [value!_eq, hv]; rfl
    have hocc : OccursV c v = false := by
      simp only [RecursiveDecl, Bool.or_eq_false_iff, hval, hname] at hrec
      exact hrec.2
    have hno : name_occurs (m := PureM) c v = false := by
      rw [name_occurs_eq, nameOccurs_eq_OccursV]; exact hocc
    simp only [hval, hno, Bool.not_false, ↓reduceIte] at hrun
    have hvcl : FVarsIn (fun _ => False) v := (hG.closed ci hci').2 v hv
    obtain ⟨v', htr⟩ := hG.prog.value_tr hciP hv
    have hoccS : ∀ d, OccursV d v = true → S d := by
      obtain ⟨ci₀, hci₀, -, hval₀⟩ := hsc c hc
      rw [hci] at hci₀
      cases hci₀
      exact hval₀ v hv
    obtain ⟨S', hsc', hvS', hcS'⟩ := hG.valueScope hci hv
    have hmem : ci.all = [c] := by
      obtain ⟨a, ha⟩ := List.length_eq_one_iff.1 hall
      have := hG.prog.name_mem_all hciP
      rw [ha, hname, List.mem_singleton] at this
      rw [ha, this]
    rw [runPure_bind] at hrun
    replace hrun := Except.ok_of_bind hrun
    obtain ⟨⟨⟨t, st₂⟩, ps₂⟩, hW, hrun⟩ := hrun
    rw [runPure_withReader, runPure_read_bind, runPure_bind] at hW
    replace hW := Except.ok_of_bind hW
    obtain ⟨⟨⟨v₁, s₁⟩, p₁⟩, hp, hW⟩ := hW
    cases hp
    rw [runPure_bind] at hrun
    replace hrun := Except.ok_of_bind hrun
    obtain ⟨⟨⟨_, st₃⟩, ps₃⟩, hm, hrun⟩ := hrun
    cases hm
    obtain ⟨hc', hg', rfl⟩ := KeepsCG.run (by
      repeat' first
        | with_reducible_and_instances first
          | exact KeepsCG.pure _
          | exact KeepsCG.get
          | exact KeepsCG.log _
          | exact KeepsCG.isInstance _
          | refine KeepsCG.modify fun _ => ⟨rfl, rfl⟩
          | refine KeepsCG.read_bind fun _ => ?_
          | refine KeepsCG.bind ?_ fun _ => ?_
          | refine KeepsCG.ite (fun _ => ?_) (fun _ => ?_)) hrun
    dsimp only at hW hrun
    have hW' : (visitExpr (m := PureM) fuel v).runPure sb
        { lctx := tc.lctx, locals := [], config := tc.config } ⟨decls, view⟩ ps =
          .ok ((t, st₂), ps') := by
      rw [← hW]
      exact (visit_agree (S := fun _ => False) (pc := ⟨decls, view⟩)
        (tc := { lctx := tc.lctx, locals := [], config := tc.config }) (ls₁ := tc.locals)
        (ls₂ := []) hG.closed (fun _ h => h.elim) (fun _ h => h.elim) hvcl).symm
    have hokb : StateOK venv (evalEnvOf view cfg decls) sb := hok.congr hcb hgb
    have ⟨her, hdeps, hgr⟩ := ih fuel (Nat.le_refl _) v hctx0 hsc (fun d hd => .inl (hoccS d hd))
      hokb htr hW'
    obtain ⟨-, -, hgr'⟩ := ih fuel (Nat.le_refl _) v hctx0 hsc'
      (fun d hd => .inl ((hvS' d hd).resolve_left fun hd' => by
        rw [hmem, List.mem_singleton] at hd'
        rw [hd', hocc] at hd
        cases hd)) hokb htr hW'
    have hnew₂ : st₂.constants[c]? = none := by
      cases h : st₂.constants[c]? with
      | none => rfl
      | some kn =>
        exact ((hcS' c (by rw [hmem]; exact .head _))
          (hgr'.scope c kn (by rw [hcb]; exact hnew) h)).elim
    have ⟨hok₃, hext₃⟩ := StateOK.registerDef hgr.ok hG.inj hG.closed hci hnew₂ hax hrec hv htr
      (her.mono_rc fun _ _ h => h.elim) hdeps
    refine ⟨⟨hok₃.congr hc' hg', ?_, hgr.next, ?_⟩, toKername c, ?_⟩
    · rw [hg', ← hgb]
      exact hgr.ext.trans hext₃
    · intro c' kn h0 h1
      rw [hc'] at h1
      change (st₂.constants.insert c (toKername c))[c']? = some kn at h1
      rw [Std.HashMap.getElem?_insert] at h1
      split at h1
      · rename_i hcc
        rw [← beq_iff_eq.1 hcc]
        exact hc
      · exact hgr.scope c' kn (by rw [hcb]; exact h0) h1
    · rw [hc']
      exact Std.HashMap.getElem?_insert_self

end

end EraseProof

