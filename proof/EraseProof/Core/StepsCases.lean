import EraseProof.Core.StepsB
import EraseProof.Simulation.Iota

/-!
# The `casesOn` step of the pure traversal

The step of `visitExpr` on an application or a constant whose head is a recognized `casesOn`
constant (`Steps.StepsB.cases`): `visitConstApp` η-expands the spine to the `casesOn`'s arity
(`withAppEtaToMinArity`) and erases the saturated spine with `visitCases`. This module proves the
step from the correctness of `visitCases` on saturated spines (`CasesSatSpec`): the η-expansion
of a spine with fewer arguments than the arity is related by `Erases.eta` and `Erases.lam`, the
binders being those of the `casesOn`'s declared type, which the recognizer requires to have the
arity's leading `Π`s.

Reference: the `tCase` case of `erases_erase` (`MR E/ErasureFunction.v:1228`); the η-expansion is
DV-23.
-/

open Lean Erasure
open Metalean (Defeq TypeEq EnvWF)

namespace EraseProof

namespace StepsCases

open Steps TravFrame

/-! ## The recognizer and the arity -/

/-- A recognized `casesOn` (`casesInfo?`) is a definition of `decls` for the inductive
`ci.indName` of `decls`, its arity is `casesArity` of that inductive, and its declared type has at
least that many leading `Π`s. -/
theorem casesInfo?_arity {decls : List ConstantInfo} {c : Name} {ci : CasesInfo}
    (h : casesInfo? decls c = some ci) :
    ∃ iv d, findDecl decls ci.indName = some (.inductInfo iv) ∧
      findDecl decls c = some (.defnInfo d) ∧ ci.arity = casesArity iv ∧
      casesArity iv ≤ forallArity d.type := by
  unfold casesInfo? at h
  split at h
  next T =>
    split at h
    next d I R hd hI hR =>
      dsimp only at h
      split at h
      next j body alts before hj hb ha hbe =>
        split at h
        next hok =>
          cases h
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
          exact ⟨I, d, hI, hd, rfl, hok.1.1.1.1.1.1.1.1.2⟩
        next => cases h
      next => cases h
    next => cases h
  next => cases h

/-- Instantiating a bound variable keeps the leading `Π`s. -/
theorem forallArity_inst (a : Expr) : ∀ (b : Expr) (d : Nat),
    forallArity b ≤ forallArity (b.instantiate1' a d)
  | .forallE _ _ b _, d => by
    simp only [forallArity, Expr.instantiate1']
    exact Nat.succ_le_succ (forallArity_inst a b (d + 1))
  | .bvar _, _ | .fvar _, _ | .mvar _, _ | .sort _, _ | .const .., _ | .app .., _ | .lam .., _
  | .letE .., _ | .lit _, _ | .mdata .., _ | .proj .., _ => by
    simp [forallArity]

/-- Instantiating universe parameters keeps the leading `Π`s. -/
theorem forallArity_instLevels (ps : List Name) (us : List Level) :
    ∀ e : Expr, forallArity (Pure.instLevels ps us e) = forallArity e
  | .forallE _ _ b _ => by
    simp only [Pure.instLevels, forallArity, forallArity_instLevels ps us b]
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const .. | .app .. | .lam .. | .letE .. | .lit _
  | .mdata .. | .proj .. => by simp [Pure.instLevels, forallArity]

/-- `piInst` succeeds on a type with at least as many leading `Π`s as arguments. -/
theorem piInst_isSome : ∀ (as : List Expr) {ty : Expr}, as.length ≤ forallArity ty →
    ∃ T, piInst as ty = some T ∧ forallArity ty - as.length ≤ forallArity T
  | [], ty, _ => ⟨ty, rfl, by simp⟩
  | a :: as, .forallE x A b bi, h => by
    simp only [List.length_cons, forallArity] at h
    obtain ⟨T, hT, hle⟩ := piInst_isSome as (ty := b.instantiate1' a)
      (Nat.le_trans (by omega) (forallArity_inst a b 0))
    refine ⟨T, hT, ?_⟩
    have := forallArity_inst a b 0
    simp only [forallArity, List.length_cons]
    omega
  | _ :: _, .bvar _, h | _ :: _, .fvar _, h | _ :: _, .mvar _, h | _ :: _, .sort _, h
  | _ :: _, .const .., h | _ :: _, .app .., h | _ :: _, .lam .., h | _ :: _, .letE .., h
  | _ :: _, .lit _, h | _ :: _, .mdata .., h | _ :: _, .proj .., h => by
    simp [forallArity] at h

/-- `lamsOf` succeeds on a type with at least as many leading `Π`s as binders. -/
theorem lamsOf_isSome (body : Expr) : ∀ (k : Nat) {ty : Expr}, k ≤ forallArity ty →
    ∃ e, lamsOf k ty body = some e
  | 0, _, _ => ⟨body, rfl⟩
  | k + 1, .forallE x A b bi, h => by
    simp only [forallArity] at h
    obtain ⟨e, he⟩ := lamsOf_isSome body k (ty := b) (by omega)
    exact ⟨.lam x A e bi, by simp [lamsOf, he]⟩
  | _ + 1, .bvar _, h | _ + 1, .fvar _, h | _ + 1, .mvar _, h | _ + 1, .sort _, h
  | _ + 1, .const .., h | _ + 1, .app .., h | _ + 1, .lam .., h | _ + 1, .letE .., h
  | _ + 1, .lit _, h | _ + 1, .mdata .., h | _ + 1, .proj .., h => by
    simp [forallArity] at h

/-- The oracle's type of a constant spine whose declared type has at least as many leading `Π`s
as arguments is the declared type instantiated at the levels and the arguments (`piInst`). -/
theorem inferType_spine {cx : Pure.Ctx} {ls : List Local} {c : Name} {us : List Level}
    {ci : ConstantInfo} (hci : findConst cx.decls c = some ci) :
    ∀ (as : List Expr) {f : Nat} {T : Expr},
      as.length ≤ forallArity (Pure.instLevels ci.levelParams us ci.type) →
      Pure.inferType cx f ls [] (mkAppN (.const c us) as.toArray) = .ok T →
      piInst as (Pure.instLevels ci.levelParams us ci.type) = some T := by
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
    rw [SrcDefeq.mkAppN_snoc] at h
    cases f with
    | zero => simp [Pure.inferType, throw, throwThe, MonadExceptOf.throw] at h
    | succ f =>
      simp only [Pure.inferType] at h
      obtain ⟨Tg, h1, h⟩ := OracleWhnf.ok_of_bind h
      obtain ⟨W, h2, h⟩ := OracleWhnf.ok_of_bind h
      have hp := ih (by omega) h1
      obtain ⟨Tg', hTg', hle⟩ := piInst_isSome as (ty := Pure.instLevels ci.levelParams us ci.type)
        (by omega)
      rw [hp] at hTg'
      cases hTg'
      cases Tg with
      | forallE x A b bi =>
        have hW := OracleInfer.whnf_forallE h2
        subst hW
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        rw [SimIota.piInst_append, hp]
        rfl
      | _ => simp [forallArity] at hle; omega

/-- `forallMonocular` on a `Π` opens it with the next fresh variable, without reduction. -/
theorem forallMonocular_run {α : Type} {x : Name} {A b : Expr} {bi : BinderInfo}
    {k : FVarId → Expr → EraseT PureM α} {st : ErasureState} {tc : TravCtx} {pc : PureCtx}
    {ps : PureState} :
    (forallMonocular (m := PureM) (.forallE x A b bi) k).runPure st tc pc ps =
      (k (pureFVar ps.next) (b.instantiate1' (.fvar (pureFVar ps.next)))).runPure st
        { tc with lctx := tc.lctx.mkLocalDecl (pureFVar ps.next) x A bi,
                  locals := ⟨pureFVar ps.next, x, A, none⟩ :: tc.locals } pc ⟨ps.next + 1⟩ :=
  rfl

/-! ## Free variables of an η-expansion -/

theorem fvarsIn_piInst {p : FVarId → Prop} : ∀ {as : List Expr} {ty T : Expr},
    piInst as ty = some T → FVarsIn p ty → (∀ a ∈ as, FVarsIn p a) → FVarsIn p T
  | [], _, _, h, hty, _ => by cases h; exact hty
  | a :: as, .forallE _ _ b _, T, h, hty, has => by
    simp only [piInst] at h
    exact fvarsIn_piInst h (OracleAgree.fvarsIn_inst (has a (.head _)) hty.2)
      fun a' ha' => has a' (.tail _ ha')
  | _ :: _, .bvar _, _, h, _, _ | _ :: _, .fvar _, _, h, _, _ | _ :: _, .mvar _, _, h, _, _
  | _ :: _, .sort _, _, h, _, _ | _ :: _, .const .., _, h, _, _ | _ :: _, .app .., _, h, _, _
  | _ :: _, .lam .., _, h, _, _ | _ :: _, .letE .., _, h, _, _ | _ :: _, .lit _, _, h, _, _
  | _ :: _, .mdata .., _, h, _, _ | _ :: _, .proj .., _, h, _, _ => by cases h

theorem fvarsIn_lamsOf {p : FVarId → Prop} : ∀ {m : Nat} {ty body e : Expr},
    lamsOf m ty body = some e → FVarsIn p ty → FVarsIn p body → FVarsIn p e
  | 0, _, _, _, h, _, hb => by cases h; exact hb
  | m + 1, .forallE _ _ b _, body, e, h, hty, hb => by
    simp only [lamsOf, Option.map_eq_some_iff] at h
    obtain ⟨e', h', rfl⟩ := h
    exact ⟨hty.1, fvarsIn_lamsOf h' hty.2 hb⟩
  | _ + 1, .bvar _, _, _, h, _, _ | _ + 1, .fvar _, _, _, h, _, _ | _ + 1, .mvar _, _, _, h, _, _
  | _ + 1, .sort _, _, _, h, _, _ | _ + 1, .const .., _, _, h, _, _ | _ + 1, .app .., _, _, h, _, _
  | _ + 1, .lam .., _, _, h, _, _ | _ + 1, .letE .., _, _, h, _, _ | _ + 1, .lit _, _, _, h, _, _
  | _ + 1, .mdata .., _, _, h, _, _ | _ + 1, .proj .., _, _, h, _, _ => by cases h

/-- The free variables of an η-expansion are those of the spine, when the head's declared type
has none. -/
theorem fvarsIn_etaSpine {p : FVarId → Prop} {σ : EvalEnv} {c : Name} {us : List Level}
    {as : List Expr} {e' : Expr} (h : σ.etaSpine? c us as = some e')
    (hty : ∀ ci, findDecl σ.decls c = some ci → FVarsIn p ci.type)
    (hk : FVarsIn p (mkAppN (.const c us) as.toArray)) : FVarsIn p e' := by
  rw [mkAppN_toArray, FVarsIn_foldl] at hk
  unfold EvalEnv.etaSpine? at h
  split at h
  · rename_i ci _ hci _
    split at h
    · obtain ⟨ty, hpi, h⟩ := Option.bind_eq_some_iff.1 h
      refine fvarsIn_lamsOf h
        (fvarsIn_piInst hpi (OracleAgree.fvarsIn_instLevels _ _ (hty ci hci)) hk.2) ?_
      rw [mkAppN_toArray, FVarsIn_foldl]
      refine ⟨trivial, fun a ha => ?_⟩
      rcases List.mem_append.1 ha with ha | ha
      · obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.1 ha
        exact OracleAgree.fvarsIn_lift (hk.2 a₀ ha₀)
      · obtain ⟨j, -, rfl⟩ := List.mem_map.1 ha
        trivial
    · cases h
  · cases h

/-! ## The η-expansion of a `casesOn` spine -/

/-- The arity of a recognized `casesOn` (`specialArity`) is the recognizer's. -/
theorem specialArity_cases {view : EnvView} {cfg : ErasureConfig} {decls : List ConstantInfo}
    {c : Name} {ci : CasesInfo} (h : casesInfo? decls c = some ci) :
    specialArity (evalEnvOf view cfg decls) c = some ci.arity := by
  obtain ⟨iv, d, hiv, hd, har, -⟩ := casesInfo?_arity h
  simp [specialArity, evalEnvOf, hd, EvalEnv.casesOn?, h, hiv, har]

/-- A spine with fewer arguments than the arity of its head, whose type `T` (the head's declared
type instantiated) has the remaining `Π`s, has an η-expansion whose outermost binder is `T`'s. -/
theorem etaSpine?_cases {σ : EvalEnv} {c : Name} {us : List Level} {as : List Expr}
    {ci₀ : ConstantInfo} {ar : Nat} {T : Expr} (hd : findDecl σ.decls c = some ci₀)
    (hspec : specialArity σ c = some ar) (hlt : as.length < ar)
    (hpi : piInst as (Pure.instLevels ci₀.levelParams us ci₀.type) = some T)
    (hT : ar - as.length ≤ forallArity T) :
    ∃ x A b bi b₀, T = .forallE x A b bi ∧ σ.etaSpine? c us as = some (.lam x A b₀ bi) := by
  obtain ⟨m, hm⟩ : ∃ m, ar - as.length = m + 1 := ⟨ar - as.length - 1, by omega⟩
  cases T with
  | forallE x A b bi =>
    simp only [forallArity] at hT
    obtain ⟨b₀, hb₀⟩ := lamsOf_isSome (mkAppN (.const c us)
      (as.map (·.liftLooseBVars' 0 (ar - as.length)) ++
        (List.range (ar - as.length)).reverse.map Expr.bvar).toArray) m (ty := b) (by omega)
    refine ⟨x, A, b, bi, b₀, rfl, ?_⟩
    rw [hm] at hb₀
    unfold EvalEnv.etaSpine?
    rw [hd, hspec]
    simp only [hlt, ↓reduceIte, hpi, Option.bind_some, hm, lamsOf, hb₀, Option.map_some]
  | _ => simp [forallArity] at hT; omega

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P decls : List ConstantInfo}
  {view : EnvView} {cfg : ErasureConfig}

/-- The correctness of `visitCases j ci` at the pure backend on the saturated spines of the
recognized `casesOn` constant `c` (at least `ci.arity` arguments), as `ExprSpec` states it for
`visitExpr`, without the oracle's answer on the spine. -/
def CasesSatSpec (E : Metalean.Env ζ) (B : Binds ζ) (view : EnvView) (cfg : ErasureConfig)
    (decls : List ConstantInfo) (j : Nat) (c : Name) (ci : CasesInfo) : Prop :=
  ∀ ⦃lps : List Name⦄ ⦃n : Nat⦄ ⦃Γ : Metalean.Ctx ζ lps.length 0 n⦄ ⦃Δ : MLCtx ζ lps.length n⦄
    ⦃S : Name → Prop⦄ ⦃us : List Level⦄ ⦃as : List Expr⦄ ⦃t : Metalean.Expr ζ lps.length n⦄
    ⦃st : ErasureState⦄ ⦃tc : TravCtx⦄ ⦃ps : PureState⦄ ⦃r : LBTerm⦄ ⦃st' : ErasureState⦄
    ⦃ps' : PureState⦄,
    CtxOK E B lps Γ Δ cfg tc ps → ScopeOK decls S →
    (∀ d, nameOccurs d (mkAppN (.const c us) as.toArray) = true → S d) →
    MachineFree cfg (mkAppN (.const c us) as.toArray) →
    NatPlain cfg (mkAppN (.const c us) as.toArray) →
    RecShaped cfg decls (mkAppN (.const c us) as.toArray) →
    StateOK E B (evalEnvOf view cfg decls) st →
    TrM E B lps Γ Δ (mkAppN (.const c us) as.toArray) t → (∃ T, E[Γ] ⊢ t : T) →
    ci.arity ≤ as.length →
    (visitCases (m := PureM) j ci as.toArray).runPure st tc ⟨decls, view⟩ ps =
      .ok ((r, st'), ps') →
    Erases E B lps (evalEnvOf view cfg decls) Γ Δ (mkAppN (.const c us) as.toArray) r ∧
      ErasesDeps E B (evalEnvOf view cfg decls) st'.gdecls r ∧
      Grows E B (evalEnvOf view cfg decls) S st st' ps ps'

/-- The η-expansion loop of `withAppEtaToMinArity` on a spine of a recognized `casesOn` constant
`c`, whose type `T` is the declared type of `c` instantiated at the arguments with the remaining
`Π`s: a short spine is opened, one fresh variable per missing argument (`CtxOK.pushFVar`), the
saturated spine is erased by `visitCases` (`CasesSatSpec`), and the binders are closed with the
traversal's `abstract`; the result erases the η-expansion of the spine (`EvalEnv.etaSpine?`,
`Erases.lam`, `Erases.abstract`), and a saturated spine is erased as `visitCases` erases it.
Reference: none (MetaRocq η-expands in λ□, `MR E/EEtaExpanded.v`; DV-23). -/
theorem go_spec (hG : CoreEnv E B P decls view cfg) {j : Nat} {c : Name} {ci : CasesInfo}
    {ci₀ : ConstantInfo} {us : List Level} (hsat : CasesSatSpec E B view cfg decls j c ci)
    (hd : findDecl decls c = some ci₀)
    (hspec : specialArity (evalEnvOf view cfg decls) c = some ci.arity)
    (hsp : ∀ b, B c = some b → b.isSpecial = false) :
    ∀ (f : Nat) {lps : List Name} {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
      {Δ : MLCtx ζ lps.length n} {S : Name → Prop} {as : List Expr} {T : Expr}
      {t : Metalean.Expr ζ lps.length n} {st : ErasureState} {tc : TravCtx} {ps : PureState}
      {r : LBTerm} {st' : ErasureState} {ps' : PureState},
      CtxOK E B lps Γ Δ cfg tc ps → ScopeOK decls S →
      (∀ d, nameOccurs d (mkAppN (.const c us) as.toArray) = true → S d) →
      MachineFree cfg (mkAppN (.const c us) as.toArray) →
      NatPlain cfg (mkAppN (.const c us) as.toArray) →
      RecShaped cfg decls (mkAppN (.const c us) as.toArray) →
      StateOK E B (evalEnvOf view cfg decls) st →
      TrM E B lps Γ Δ (mkAppN (.const c us) as.toArray) t → (∃ U, E[Γ] ⊢ t : U) →
      (as.length < ci.arity → piInst as (Pure.instLevels ci₀.levelParams us ci₀.type) = some T ∧
        ci.arity - as.length ≤ forallArity T ∧ ∃ T', TrM E B lps Γ Δ T T' ∧ E[Γ] ⊢ t : T') →
      (withAppEtaToMinArity.go (m := PureM) ci.arity
        (fun _ args => visitCases (m := PureM) j ci args) f T (.const c us) as.toArray).runPure
          st tc ⟨decls, view⟩ ps = .ok ((r, st'), ps') →
      (as.length < ci.arity → ∃ e', (evalEnvOf view cfg decls).etaSpine? c us as = some e' ∧
        Erases E B lps (evalEnvOf view cfg decls) Γ Δ e' r) ∧
      (ci.arity ≤ as.length →
        Erases E B lps (evalEnvOf view cfg decls) Γ Δ (mkAppN (.const c us) as.toArray) r) ∧
      ErasesDeps E B (evalEnvOf view cfg decls) st'.gdecls r ∧
      Grows E B (evalEnvOf view cfg decls) S st st' ps ps' := by
  have hns : ∀ as : List Expr, ¬ SpecialHead B (mkAppN (.const c us) as.toArray) := by
    rintro as ⟨c', us', b, hc', hb, hs⟩
    rw [SrcDefeq.getAppFn_mkAppN_const] at hc'
    cases hc'
    rw [hsp b hb] at hs
    cases hs
  intro f
  induction f with
  | zero =>
    intro lps n Γ Δ S as T t st tc ps r st' ps' _ _ _ _ _ _ _ _ _ _ hrun
    rw [withAppEtaToMinArity.go] at hrun
    cases hrun
  | succ f ih =>
    intro lps n Γ Δ S as T t st tc ps r st' ps' hctx hsc hocc hmf hnp hrf hok he ht0 hshape hrun
    rw [withAppEtaToMinArity.go] at hrun
    split at hrun
    · rename_i hge
      simp only [List.size_toArray, ge_iff_le] at hge
      have := hsat hctx hsc hocc hmf hnp hrf hok he ht0 hge hrun
      exact ⟨fun h => absurd hge (by omega), fun _ => this.1, this.2.1, this.2.2⟩
    · rename_i hge
      simp only [List.size_toArray, ge_iff_le, Nat.not_le] at hge
      obtain ⟨hpi, hTa, htyp⟩ := hshape hge
      obtain ⟨x, A, b, bi, b₀, rfl, heta⟩ := etaSpine?_cases (σ := evalEnvOf view cfg decls)
        (us := us) hd hspec hge hpi hTa
      rw [forallMonocular_run, runPure_bind] at hrun
      obtain ⟨⟨⟨r₁, st₁⟩, ps₁⟩, hgo, hrun⟩ := OracleWhnf.ok_of_bind hrun
      dsimp only at hrun
      rw [mkLambda_run (l := ⟨pureFVar ps.next, x, A, none⟩) rfl rfl] at hrun
      cases hrun
      obtain ⟨T', hTT', htT'⟩ := htyp
      obtain ⟨A₁, B₁, rfl, hA, hb⟩ := SrcDefeq.trM_forallE_inv hTT'
      obtain ⟨_, hTs⟩ := htT'.regular
      have hA₁ : E[Γ] ⊢ A₁ typ := (Metalean.Defeq.forallE_inv hTs).1
      have hxΔ := hctx.freshNext
      have hctx' := hctx.pushFVar (nm := x) hA hA₁ (tc.lctx.mkLocalDecl (pureFVar ps.next) x A bi)
      have harr : as.toArray.push (Expr.fvar (pureFVar ps.next)) =
          (as ++ [Expr.fvar (pureFVar ps.next)]).toArray := by simp
      rw [harr] at hgo
      have hsnoc := SrcDefeq.mkAppN_snoc c us as (Expr.fvar (pureFVar ps.next))
      have he' : TrM E B lps (Γ.snoc A₁) (Δ.pushLam (some (pureFVar ps.next)))
          (mkAppN (.const c us) (as ++ [Expr.fvar (pureFVar ps.next)]).toArray)
          (.app t.wk (.var (Fin.last n))) := by
        rw [hsnoc]
        exact .app (hns as) (TrM.weakFV hxΔ he)
          (TrM.fvar (by simp [MLCtx.pushLam, MLCtx.findF, MLDecl.denote,
            (fvarId_beq_iff (pureFVar ps.next) (pureFVar ps.next)).mpr rfl]))
      have ht' := app_var_typed htT' hctx'.wf
      have hpi' : piInst (as ++ [Expr.fvar (pureFVar ps.next)])
          (Pure.instLevels ci₀.levelParams us ci₀.type) =
          some (b.instantiate1' (Expr.fvar (pureFVar ps.next))) := by
        rw [SimIota.piInst_append, hpi]; rfl
      have hTa' : ci.arity - (as ++ [Expr.fvar (pureFVar ps.next)]).length ≤
          forallArity (b.instantiate1' (Expr.fvar (pureFVar ps.next))) := by
        have := forallArity_inst (Expr.fvar (pureFVar ps.next)) b 0
        simp only [forallArity] at hTa
        simp only [List.length_append, List.length_singleton]
        omega
      have ⟨hshort, hsat', hdeps, hgr⟩ := ih (S := S) hctx' hsc
        (fun d hd' => hocc d (by rw [hsnoc] at hd'; simpa [nameOccurs] using hd'))
        (by rw [hsnoc]; exact ⟨hmf, trivial⟩) (by rw [hsnoc]; exact ⟨hnp, trivial⟩)
        (by rw [hsnoc]; exact ⟨hrf, trivial⟩) hok he' ⟨_, ht'⟩
        (fun _ => ⟨hpi', hTa', B₁, TrM.inst_fvar hxΔ hb, ht'⟩) hgo
      obtain ⟨ar, har, -, hsh, hst⟩ := SimIota.etaSpine?_snoc (Expr.fvar (pureFVar ps.next)) heta
      rw [hspec] at har
      cases har
      have hb₀ : Erases E B lps (evalEnvOf view cfg decls) (Γ.snoc A₁)
          (Δ.pushLam (some (pureFVar ps.next))) (b₀.instantiate1' (Expr.fvar (pureFVar ps.next)))
          r₁ := by
        by_cases hlt' : as.length + 1 < ci.arity
        · obtain ⟨e', he'', her⟩ := hshort (by simpa using hlt')
          rw [hsh hlt'] at he''
          cases he''
          exact her
        · rw [hst (by omega)]
          exact hsat' (by simp; omega)
      have hcl : closedn 0 r₁ = true := by
        have hsp' : Erases E B lps (evalEnvOf view cfg decls) (Γ.snoc A₁)
            (Δ.pushLam (some (pureFVar ps.next)))
            (mkAppN (.const c us) (as ++ [Expr.fvar (pureFVar ps.next)]).toArray) r₁ := by
          by_cases hlt' : as.length + 1 < ci.arity
          · exact .eta (hsh hlt') hb₀
          · exact hsat' (by simp; omega)
        have := Erases.closed he' hsp'
        rwa [countP_none hctx'.nobv] at this
      have hfv : FVarsIn (· ≠ pureFVar ps.next) (Expr.lam x A b₀ bi) := by
        have h := fvarsIn_etaSpine heta
          (fun ci' hci' => fvarsIn_mono (fun _ h => h.elim)
            (AbsFV.closed_types hG.prog hG.sub c ci' hci').2) (TrM.fvarsIn he)
        exact fvarsIn_mono (fun y hy hyx => by subst hyx; simp [hxΔ] at hy) h
      refine ⟨fun _ => ⟨_, heta, .lam hA hA₁ (Erases.abstract hG.prog hG.sub hxΔ hfv.2 hcl hb₀)⟩,
        fun h => absurd h (by omega), .lambda (ErasesDeps.toBvar hdeps 0),
        ⟨hgr.inv, hgr.ext, Nat.le_trans (Nat.le_succ _) hgr.next, hgr.scope⟩⟩


/-- The `casesOn` step at `fuel + 1` from the correctness of `visitCases` on saturated spines
(`CasesSatSpec`) at the fuel `visitConstApp` passes it: after the oracle (`visitExpr_box`), a
spine headed by the recognized `casesOn` constant `c` reaches `withAppEtaToMinArity` with the
oracle's type of the spine, which is the declared type of `c` instantiated (`inferType_spine`,
the recognizer's `Π`s); a short spine erases as its η-expansion (`go_spec`, `Erases.eta`), a
saturated one as `visitCases` erases it. Reference: the `tCase` case of `erases_erase`
(`MR E/ErasureFunction.v:1228`); DV-23. -/
theorem cases_step_of_sat (hG : CoreEnv E B P decls view cfg) {fuel : Nat}
    (ih : StepIH E B view cfg decls fuel) {e : Expr} {c : Name} {us : List Level}
    {ci : CasesInfo} (hc : e.getAppFn = .const c us) (hci : casesInfo? decls c = some ci)
    (hsat : ∀ j, j + 2 = fuel → CasesSatSpec E B view cfg decls j c ci) :
    ExprSpec E B view cfg decls (fuel + 1) e := by
  intro lps n Γ Δ S t st tc ps r st' ps' hctx hsc hocc hmf hnp hrf hok he ht hrun
  have hor2 : (Pure.isErasable ⟨decls⟩ oracleFuel tc.locals e = .ok true ∧ r = .box ∧ st' = st ∧
      ps' = ps) ∨ (Pure.isErasable ⟨decls⟩ oracleFuel tc.locals e = .ok false ∧
      (visitApp (m := PureM) fuel e).runPure st tc ⟨decls, view⟩ ps = .ok ((r, st'), ps')) := by
    cases e with
    | app f a => rw [visitExpr] at hrun; exact oracle_run hrun
    | const c' us' => rw [visitExpr] at hrun; exact oracle_run hrun
    | _ => simp [Expr.getAppFn] at hc
  rcases hor2 with ⟨hor, rfl, rfl, rfl⟩ | ⟨-, hvA⟩
  · exact visitExpr_box hG hctx hok he ht hor
  clear hrun
  obtain ⟨iv, d, -, hd, har, hfa⟩ := casesInfo?_arity hci
  have hsp : mkAppN (.const c us) (spineArgs e).toArray = e := by
    rw [← hc]; exact mkAppN_spine e
  have hA : (e.withApp fun _ as => as) = (spineArgs e).toArray := by
    rw [← withApp_toList e, Array.toArray_toList]
  have hspc : ∀ b, B c = some b → b.isSpecial = false := by
    intro b hb
    cases hs : b.isSpecial
    · rfl
    · exfalso
      rcases SrcDefeq.special_kind hG.prog hb hs
        (SrcDefeq.findDecl_sub (σ := evalEnvOf view cfg decls) hG.sub hd) with
        ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> cases h
  cases fuel with
  | zero => rw [visitApp] at hvA; cases hvA
  | succ k =>
  rw [visitApp] at hvA
  split at hvA
  swap
  · rename_i hne; exact absurd hc (hne c us)
  cases k with
  | zero => rw [visitConstApp] at hvA; cases hvA
  | succ j =>
  rw [visitConstApp, withApp_eq] at hvA
  split at hvA
  swap
  · rename_i hne; exact absurd hc (hne c us)
  rename_i c' us' hc'
  rw [hc] at hc'
  cases hc'
  rw [runPure_bind, show (liftM (Backend.casesInfo? (m := PureM) c) :
      EraseT PureM (Option CasesInfo)).runPure st tc ⟨decls, view⟩ ps = .ok ((some ci, st), ps) by
    show Except.ok ((casesInfo? decls c, st), ps) = _; rw [hci], ok_bind'] at hvA
  dsimp only at hvA
  rw [Erasure.withAppEtaToMinArity, runPure_read_bind, runPure_read_bind, runPure_bind,
    runPure_liftM, inferType_run] at hvA
  cases hinf : Pure.inferType ⟨decls⟩ oracleFuel tc.locals [] e with
  | error err => rw [hinf] at hvA; cases hvA
  | «ok» T =>
  rw [hinf] at hvA
  dsimp only [Except.map] at hvA
  rw [ok_bind', ok_bind'] at hvA
  dsimp only at hvA
  rw [withApp_eq, hc, hA] at hvA
  have hdc : findConst decls c = some (.defnInfo d) := hd
  have hle : ∀ {as : List Expr}, as.length < ci.arity →
      as.length ≤ forallArity (Pure.instLevels d.levelParams us d.type) := fun h => by
    rw [forallArity_instLevels]; omega
  have he' : TrM E B lps Γ Δ (mkAppN (.const c us) (spineArgs e).toArray) t := by
    rw [hsp]; exact he
  have ⟨hshort, hsat', hdeps, hgr⟩ := go_spec (us := us) hG (hsat j rfl) hd
    (specialArity_cases hci) hspc j hctx hsc (by rw [hsp]; exact hocc) (by rw [hsp]; exact hmf)
    (by rw [hsp]; exact hnp) (by rw [hsp]; exact hrf) hok he' ht
    (fun hlt => by
      have hpi : piInst (spineArgs e) (Pure.instLevels d.levelParams us d.type) = some T :=
        inferType_spine (cx := ⟨decls⟩) (ls := tc.locals) hdc (spineArgs e) (hle hlt)
        (by rw [hsp]; exact hinf)
      obtain ⟨T₀, hT₀, hfT⟩ := piInst_isSome (spineArgs e) (hle hlt)
      rw [hpi] at hT₀
      cases hT₀
      rw [forallArity_instLevels] at hfT
      exact ⟨hpi, by omega, Pure.inferType_sound hG.prog hG.wf hG.sub hctx.wf hctx.locals
        hctx.nobv he ht hinf⟩) hvA
  refine ⟨?_, hdeps, hgr⟩
  by_cases hlt : (spineArgs e).length < ci.arity
  · obtain ⟨e', heta, her⟩ := hshort hlt
    have := Erases.eta heta her
    rwa [hsp] at this
  · have := hsat' (by omega)
    rwa [hsp] at this


end

end StepsCases

namespace Steps

/-- The field `cases` of `StepsB`, given the correctness of `visitCases` on the saturated spines
of every recognized `casesOn` constant (`StepsCases.CasesSatSpec`) at every fuel, from the
induction hypothesis at that fuel (`StepsCases.cases_step_of_sat`). Reference: the `tCase` case of
`erases_erase` (`MR E/ErasureFunction.v:1228`), rule `erases_tCase` (`MR E/Extract.v:111`). -/
theorem stepsB_cases_of_sat
    (hsat : ∀ {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ}
      {P decls : List ConstantInfo} {view : EnvView} {cfg : ErasureConfig} {j : Nat} {c : Name}
      {ci : CasesInfo}, CoreEnv E B P decls view cfg → StepIH E B view cfg decls j →
      casesInfo? decls c = some ci → StepsCases.CasesSatSpec E B view cfg decls j c ci) :
    ∀ {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P decls : List ConstantInfo}
      {view : EnvView} {cfg : ErasureConfig} {fuel : Nat} {e : Expr} {c : Name} {us : List Level}
      {ci : CasesInfo},
      CoreEnv E B P decls view cfg → StepIH E B view cfg decls fuel →
      e.getAppFn = .const c us → casesInfo? decls c = some ci →
      ExprSpec E B view cfg decls (fuel + 1) e :=
  fun hG ih hc hci => StepsCases.cases_step_of_sat hG ih hc hci fun _ hj =>
    hsat hG ⟨fun m hm => ih.expr m (by omega), fun m hm => ih.mutDecl m (by omega)⟩ hci

end Steps

end EraseProof
