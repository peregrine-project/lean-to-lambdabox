import EraseProof.Core.StepsCases
import EraseProof.Core.StepsCtor
import EraseProof.Core.StepsAssemble

/-!
# The `case` branch of `visitCases`

The branch of `visitCases` (`LeanToLambdaBox/Erasure.lean:870`) that emits a λ□ `case`: the
`casesOn` is large-eliminating and the discriminant's sort is never zero or its inductive does not
have exactly one constructor. Each alternative is erased under its fields' binders by `visitAlt`,
which peels the alternative's λs and η-introduces the missing ones (`lambdaOrIntroToArity`); the
result is related by `ErasesAlt`.

Reference: the `tCase` case of `erases_erase` (`MR E/ErasureFunction.v:1228`).
-/

open Lean Erasure
open Metalean (Defeq TypeEq EnvWF)

namespace EraseProof

namespace StepsCasesCase

open Steps TravFrame StepsCases

/-! ## The λs of an alternative and the `Π`s of its type -/

/-- The leading λs of `e` are the leading `Π`s of `T`, with the same binder names and domains. -/
def LamMatch : Expr → Expr → Prop
  | .lam x A b _, T => ∃ B bi, T = .forallE x A B bi ∧ LamMatch b B
  | .bvar _, _ | .fvar _, _ | .mvar _, _ | .sort _, _ | .const .., _ | .app .., _
  | .forallE .., _ | .letE .., _ | .lit _, _ | .mdata .., _ | .proj .., _ => True

/-- The oracle's type of a λ is a `Π` with the λ's binder name and domain. -/
theorem inferType_lamMatch {cx : Pure.Ctx} {ls : List Local} :
    ∀ (f : Nat) (Γo : List Expr) (e : Expr) {T : Expr}, Pure.inferType cx f ls Γo e = .ok T →
      LamMatch e T
  | 0, _, _, _, h => by simp [Pure.inferType, throw, throwThe, MonadExceptOf.throw] at h
  | f + 1, Γo, .lam x A b bi, T, h => by
    simp only [Pure.inferType] at h
    obtain ⟨B, hB, h⟩ := OracleWhnf.ok_of_bind h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨B, bi, rfl, inferType_lamMatch f _ b hB⟩
  | _ + 1, _, .bvar _, _, _ | _ + 1, _, .fvar _, _, _ | _ + 1, _, .mvar _, _, _
  | _ + 1, _, .sort _, _, _ | _ + 1, _, .const .., _, _ | _ + 1, _, .app .., _, _
  | _ + 1, _, .forallE .., _, _ | _ + 1, _, .letE .., _, _ | _ + 1, _, .lit _, _, _
  | _ + 1, _, .mdata .., _, _ | _ + 1, _, .proj .., _, _ => trivial

/-- Instantiating a bound variable with a free variable keeps `LamMatch`. -/
theorem LamMatch.inst (y : FVarId) : ∀ {e T : Expr} {d : Nat}, LamMatch e T →
    LamMatch (e.instantiate1' (.fvar y) d) (T.instantiate1' (.fvar y) d)
  | .lam x A b bi, T, d, h => by
    obtain ⟨B, bi', rfl, h⟩ := h
    exact ⟨_, bi', rfl, LamMatch.inst y h⟩
  | .bvar i, _, d, _ => by
    simp only [Expr.instantiate1']
    split_ifs <;> simp [LamMatch, Expr.liftLooseBVars']
  | .fvar _, _, _, _ | .mvar _, _, _, _ | .sort _, _, _, _ | .const .., _, _, _
  | .app .., _, _, _ | .forallE .., _, _, _ | .letE .., _, _, _ | .lit _, _, _, _
  | .mdata .., _, _, _ | .proj .., _, _, _ => by simp [Expr.instantiate1', LamMatch]

/-- Abstracting a variable that does not occur shifts the loose bound variables. -/
theorem absFV_fresh {x : FVarId} : ∀ {e : Expr} {d : Nat}, FVarsIn (· ≠ x) e →
    AbsFV.absFV x d e = e.liftLooseBVars' d 1
  | .bvar i, d, _ => by simp [AbsFV.absFV, Expr.liftLooseBVars']
  | .fvar y, d, h => by
    have : (y == x) = false := by
      rcases Bool.eq_false_or_eq_true (y == x) with h' | h'
      · exact absurd ((fvarId_beq_iff _ _).mp h') h
      · exact h'
    simp [AbsFV.absFV, Expr.liftLooseBVars', this]
  | .app f a, d, h => by
    simp only [AbsFV.absFV, Expr.liftLooseBVars', absFV_fresh (e := f) h.1, absFV_fresh (e := a) h.2]
  | .lam _ t b _, d, h | .forallE _ t b _, d, h => by
    simp only [AbsFV.absFV, Expr.liftLooseBVars', absFV_fresh (e := t) h.1, absFV_fresh (e := b) h.2]
  | .letE _ t v b _, d, h => by
    simp only [AbsFV.absFV, Expr.liftLooseBVars', absFV_fresh (e := t) h.1,
      absFV_fresh (e := v) h.2.1, absFV_fresh (e := b) h.2.2]
  | .mdata _ e, d, h | .proj _ _ e, d, h => by
    simp only [AbsFV.absFV, Expr.liftLooseBVars', absFV_fresh (e := e) h]
  | .mvar _, _, _ | .sort _, _, _ | .const .., _, _ | .lit _, _, _ => by
    simp [AbsFV.absFV, Expr.liftLooseBVars']

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {lps : List Name}

/-- Abstracting `x` into the bound variable `d`, on both sides, keeps the erasure of an
alternative, when the λ□ body has no loose index from `d` on below the alternative's binders. -/
theorem ErasesAlt.absN {σ : EvalEnv} (x : FVarId)
    (hty : ∀ c ci, findDecl σ.decls c = some ci →
      AbsFV.LBV 0 ci.type ∧ FVarsIn (fun _ => False) ci.type)
    {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n} {k : Nat} {e : Expr}
    {br : List BinderName × LBTerm} (h : ErasesAlt E B lps σ Γ Δ k e br) :
    ∀ (d : Nat) (Δ₁ : MLCtx ζ lps.length n), AbsFV.Rel x d Δ Δ₁ →
      closedn (d + br.1.length) br.2 = true →
      ErasesAlt E B lps σ Γ Δ₁ k (AbsFV.absFV x d e) (br.1, _root_.toBvar x (d + br.1.length) br.2) := by
  refine ErasesAlt.rec (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun Γ Δ k e br _ => ∀ (d : Nat) Δ₁, AbsFV.Rel x d Δ Δ₁ →
      closedn (d + br.1.length) br.2 = true →
      ErasesAlt E B lps σ Γ Δ₁ k (AbsFV.absFV x d e) (br.1, _root_.toBvar x (d + br.1.length) br.2))
    ?bvar ?fvar ?lam ?letE ?app ?const ?ctor ?cases ?casesReduced ?eta ?proj ?litZero ?litSucc
    ?quotMk ?quotLift ?recLet ?recFix ?mdata ?box ?done ?alam ?intro h
  case done =>
    intro _ _ _ _ _ he _ d Δ₁ W hcl
    simp only [List.length_nil, Nat.add_zero] at hcl ⊢
    exact .done (AbsFV.Erases.absN x hty he d _ W hcl)
  case alam =>
    intro _ _ _ _ _ _ _ _ _ _ _ hA hAt _ ih d Δ₁ W hcl
    have e1 : ∀ l : Nat, d + 1 + l = d + (l + 1) := fun l => by omega
    dsimp only at hcl ih ⊢
    simp only [List.length_cons] at hcl ⊢
    have := ih (d + 1) _ W.pushLam (by rw [e1]; exact hcl)
    rw [e1] at this
    simp only [AbsFV.absFV]
    exact .lam (AbsFV.TrM.absN hA W) hAt this
  case intro =>
    intro _ _ _ e _ _ _ _ _ _ _ he hty' _ ih d Δ₁ W hcl
    have e1 : ∀ l : Nat, d + 1 + l = d + (l + 1) := fun l => by omega
    dsimp only at hcl ih ⊢
    simp only [List.length_cons] at hcl ⊢
    have := ih (d + 1) _ W.pushLam (by rw [e1]; exact hcl)
    rw [e1] at this
    simp only [AbsFV.absFV, show (0 : Nat) < d + 1 by omega, ↓reduceIte] at this
    rw [show AbsFV.absFV x (d + 1) (e.liftLooseBVars' 0 1) =
      (AbsFV.absFV x d e).liftLooseBVars' 0 1 from AbsFV.absFV_lift x 1 e (Nat.zero_le d)] at this
    exact .intro (AbsFV.TrM.absN he W) hty' this
  all_goals intros; trivial

end

/-! ## Runs of the binder helpers -/

/-- `forallMonocular` opens the `Π` of its type or of the type's weak-head normal form with the
next fresh variable. -/
theorem forallMonocular_inv {α : Type} {T : Expr} {k : FVarId → Expr → EraseT PureM α}
    {st : ErasureState} {tc : TravCtx} {pc : PureCtx} {ps : PureState} {res : (α × ErasureState) × PureState}
    (h : (forallMonocular (m := PureM) T k).runPure st tc pc ps = .ok res) :
    ∃ y D C bi, (T = .forallE y D C bi ∨
        Pure.whnf ⟨pc.decls⟩ oracleFuel tc.locals T = .ok (.forallE y D C bi)) ∧
      (k (pureFVar ps.next) (C.instantiate1' (.fvar (pureFVar ps.next)))).runPure st
        { tc with lctx := tc.lctx.mkLocalDecl (pureFVar ps.next) y D bi,
                  locals := ⟨pureFVar ps.next, y, D, none⟩ :: tc.locals } pc ⟨ps.next + 1⟩ = .ok res := by
  cases hT : T.isForall with
  | true =>
    cases T with
    | forallE y D C bi => exact ⟨y, D, C, bi, .inl rfl, by rw [forallMonocular_run] at h; exact h⟩
    | _ => cases hT
  | false =>
    rw [forallMonocular, hT] at h
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    rw [runPure_read_bind, runPure_read_bind, runPure_bind, runPure_liftM, whnf_run] at h
    cases hw : Pure.whnf ⟨pc.decls⟩ oracleFuel tc.locals T with
    | error err => rw [hw] at h; cases h
    | «ok» W =>
      rw [hw] at h
      cases W with
      | forallE y D C bi => exact ⟨y, D, C, bi, .inr rfl, h⟩
      | _ => cases h

/-- The λ□ names of the locals `xs`, as `fvar_to_name` finds them. -/
def namesOf (ls : List Local) (xs : List FVarId) : Option (List BinderName) :=
  xs.mapM fun x => (ls.find? (·.fvarId == x)).map (binderNameOf ·.userName)

/-- The body of an alternative closed over the locals `xs`, the last one innermost (`mkAlt`). -/
def altBody : List FVarId → LBTerm → LBTerm
  | [], r => r
  | x :: xs, r => _root_.toBvar x xs.length (altBody xs r)

theorem altBody_foldl (r : LBTerm) : ∀ xs : List FVarId,
    xs.reverse.zipIdx.foldl (fun b p => _root_.toBvar p.1 p.2 b) r = altBody xs r
  | [] => rfl
  | x :: xs => by
    rw [List.reverse_cons, List.zipIdx_append, List.foldl_append, altBody_foldl r xs]
    simp [altBody]

/-- `mkAlt xs body` returns the names of the locals and the body closed over them. -/
theorem mkAlt_run {xs : List FVarId} {ns : List BinderName} {body : LBTerm} {st : ErasureState}
    {tc : TravCtx} {pc : PureCtx} {ps : PureState} (h : namesOf tc.locals xs = some ns) :
    (mkAlt (m := PureM) xs body).runPure st tc pc ps = .ok (((ns, altBody xs body), st), ps) := by
  have hm : ∀ (ys : List FVarId) (ms : List BinderName), namesOf tc.locals ys = some ms →
      (ys.mapM (fvar_to_name (m := PureM))).runPure st tc pc ps = .ok ((ms, st), ps) := by
    intro ys
    induction ys with
    | nil => intro ms h; cases h; rfl
    | cons y ys ih =>
      intro ms h
      simp only [namesOf, List.mapM_cons, Option.bind_eq_bind] at h
      cases hf : List.find? (fun x => x.fvarId == y) tc.locals with
      | none => rw [hf] at h; cases h
      | some l =>
        rw [hf] at h
        cases hr : namesOf tc.locals ys with
        | none => simp [namesOf] at hr; simp [hr] at h
        | some ms' =>
          simp only [namesOf] at hr
          simp [hr] at h
          subst h
          rw [List.mapM_cons, runPure_bind, fvar_to_name_run hf, ok_bind']
          dsimp only
          rw [runPure_bind, ih ms' hr, ok_bind']
          rfl
  unfold mkAlt
  rw [runPure_bind, hm xs ns h, ok_bind']
  dsimp only
  rw [List.forIn_pure_yield_eq_foldl]
  simp only [runPure_bind]
  rw [← altBody_foldl]
  rfl

theorem namesOf_length {ls : List Local} : ∀ {xs : List FVarId} {ns : List BinderName},
    namesOf ls xs = some ns → ns.length = xs.length
  | [], ns, h => by cases h; rfl
  | x :: xs, ns, h => by
    simp only [namesOf, List.mapM_cons, Option.bind_eq_bind] at h
    cases hf : List.find? (fun l => l.fvarId == x) ls with
    | none => rw [hf] at h; cases h
    | some l =>
      rw [hf] at h
      cases hr : namesOf ls xs with
      | none => simp [namesOf] at hr; simp [hr] at h
      | some ms =>
        simp only [namesOf] at hr
        simp [hr] at h
        subst h
        simp [namesOf_length (show namesOf ls xs = some ms from hr)]

theorem closedn_altBody {r : LBTerm} (hr : closedn 0 r = true) :
    ∀ xs : List FVarId, closedn xs.length (altBody xs r) = true
  | [] => hr
  | x :: xs => Steps.closedn_toBvar x _ xs.length (closedn_altBody hr xs)

/-! ## Opening one binder of an alternative -/

/-- The body that `lambdaMonocularOrIntro` passes on after opening a binder with `x`: the λ's
body instantiated, or the term applied to `x`. -/
def openAlt (e : Expr) (x : FVarId) : Expr :=
  match e with
  | .lam _ _ b _ => b.instantiate1' (.fvar x)
  | _ => .app e (.fvar x)

theorem lambdaMonocularOrIntro_eq {α : Type} [Inhabited α] (e T : Expr)
    (k : Expr → Expr → FVarId → EraseT PureM α) :
    lambdaMonocularOrIntro (m := PureM) e T k =
      forallMonocular (m := PureM) T fun x bt => k (openAlt e x) bt x := by
  cases e <;> rfl

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P : List ConstantInfo}
  {lps : List Name}

open InstPre in
/-- Opening a bound variable with a fresh free variable, in a context whose new entry is
convertible to the one the body was translated under. -/
theorem trM_open_conv (hE : EnvWF E)
    (hord : ∀ c {ι : Metalean.IndSig} (η : Metalean.Head ζ (.inductive ι)) (s : Fin ι.nsorts)
      (k : Fin (ι.nctors s)) (o : List Nat), B c = some (.ctor η s k o) →
      MetaOrderOK o (ι.ctors s k).nfields (ι.ctors s k).nrecFields)
    {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    (hΓ : E[Γ] ⊢ ok) (hnb : ∀ i, Δ.findB i = none) {x : FVarId} (hx : Δ.findF x = none)
    {A₀ A₁ : Metalean.Expr ζ lps.length n} (hA₀ : E[Γ] ⊢ A₀ typ) (hA : E[Γ] ⊢ A₁ ≡ A₀ typ)
    {b : Expr} {b' U : Metalean.Expr ζ lps.length (n + 1)}
    (hb : TrM E B lps (Γ.snoc A₁) (Δ.pushLam none) b b') (hbU : E[Γ.snoc A₁] ⊢ b' : U) :
    ∃ b'', TrM E B lps (Γ.snoc A₀) (Δ.pushLam (some x)) (b.instantiate1' (.fvar x)) b'' ∧
      E[Γ.snoc A₀] ⊢ b' ≡ b'' : U := by
  have hΓ₁ : E[Γ.snoc A₁] ⊢ ok := .snoc hΓ hA.left
  have hΓ₀ : E[Γ.snoc A₀] ⊢ ok := .snoc hΓ hA₀
  have hς : E[Γ.snoc A₀] ⊢ Metalean.Subst.id ⊣ Γ.snoc A₁ :=
    Metalean.SubstWF.snocConv hA (Metalean.SubstWF.id hΓ₁)
  have W : MLCtx.InstA E B lps (.fvar x) 0 Metalean.Subst.id (Δ.pushLam none)
      (Δ.pushLam (some x)) := by
    constructor
    · intro i t ht
      cases i with
      | zero =>
        simp only [MLCtx.pushLam, MLCtx.findB, MLDecl.denote, Option.some.injEq] at ht
        subst ht
        refine ⟨by omega, fun _ => ⟨.var (Fin.last n), ?_, ?_⟩, by omega⟩
        · rw [liftLooseBVars'_zero]
          exact PreTr.ofTrM (Γ := Γ.snoc A₀) (TrM.fvar (by simp [MLCtx.pushLam, MLCtx.findF,
            MLDecl.denote, (fvarId_beq_iff x x).mpr rfl]))
        · rw [Metalean.Expr.subst_id]; exact fun {_ _} => .refl
      | succ i =>
        simp [MLCtx.pushLam, MLCtx.findB, MLCtx.findB_map_wk, hnb i] at ht
    · intro y t ht
      simp only [MLCtx.pushLam, MLCtx.findF, MLCtx.findF_map_wk, Option.map_eq_some_iff] at ht
      obtain ⟨u, hu, rfl⟩ := ht
      have hyx : (x == y) = false := by
        rcases Bool.eq_false_or_eq_true (x == y) with h' | h'
        · rw [(fvarId_beq_iff _ _).mp h'] at hx; rw [hx] at hu; cases hu
        · exact h'
      refine ⟨u.wk, by simp [MLCtx.pushLam, MLCtx.findF, MLCtx.findF_map_wk, hyx, hu], ?_⟩
      rw [Metalean.Expr.subst_id]
      exact fun {_ _} => .refl
  obtain ⟨b'', htr, -, hd⟩ := RelInst.TrM.instA hE hord hΓ₀ hς W hb hbU
  rw [Metalean.Expr.subst_id, Metalean.Expr.subst_id] at hd
  exact ⟨b'', htr, hd⟩


/-- The translation and typing of the opened body and of the opened type, and the erasure of an
alternative from the erasure of its opened body, on one binder of an alternative `e` that is not a
λ: the binder is η-introduced (`ErasesAlt.intro`). The `Π` is `T`'s or its weak-head normal form's
(`forallMonocular`). -/
theorem open_intro (henv : ProgEnv P ζ E B) (hE : EnvWF E) {decls : List ConstantInfo}
    (hsub : SubEnv decls P) {σ : EvalEnv}
    (hty : ∀ c ci, findDecl σ.decls c = some ci →
      AbsFV.LBV 0 ci.type ∧ FVarsIn (fun _ => False) ci.type)
    {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n} {ls : List Local}
    (hΓ : E[Γ] ⊢ ok) (hloc : LocalsOK E B lps Γ Δ ls) {x : FVarId} (hx : Δ.findF x = none)
    {e T : Expr} {t T' : Metalean.Expr ζ lps.length n} (he : TrM E B lps Γ Δ e t)
    (hT : TrM E B lps Γ Δ T T') (ht : E[Γ] ⊢ t : T') {y : Name} {D C : Expr} {bi : BinderInfo}
    (hW : T = .forallE y D C bi ∨
      Pure.whnf ⟨decls⟩ oracleFuel ls T = .ok (.forallE y D C bi)) :
    ∃ D', TrM E B lps Γ Δ D D' ∧ E[Γ] ⊢ D' typ ∧
      (∃ t' T'', TrM E B lps (Γ.snoc D') (Δ.pushLam (some x)) (.app e (.fvar x)) t' ∧
        TrM E B lps (Γ.snoc D') (Δ.pushLam (some x)) (C.instantiate1' (.fvar x)) T'' ∧
        E[Γ.snoc D'] ⊢ t' : T'') ∧
      ∀ k ns tb, ErasesAlt E B lps σ (Γ.snoc D') (Δ.pushLam (some x)) k (.app e (.fvar x))
          (ns, tb) → closedn ns.length tb = true →
        ErasesAlt E B lps σ Γ Δ (k + 1) e (binderNameOf y :: ns, _root_.toBvar x ns.length tb) := by
  obtain ⟨D', C', hD, hC, hD', ht'⟩ : ∃ D' C', TrM E B lps Γ Δ D D' ∧
      TrM E B lps (Γ.snoc D') (Δ.pushLam none) C C' ∧ E[Γ] ⊢ D' typ ∧
      E[Γ] ⊢ t : .forallE D' C' := by
    obtain ⟨_, hTs⟩ := ht.regular
    rcases hW with rfl | hw
    · obtain ⟨D', C', rfl, hD, hC⟩ := SrcDefeq.trM_forallE_inv hT
      exact ⟨D', C', hD, hC, (Metalean.Defeq.forallE_inv hTs).1, ht⟩
    · obtain ⟨D', C', hD, hC, hD', heq⟩ :=
        Pure.whnf_forallE (cx := ⟨decls⟩) henv hE hsub hΓ hloc hT ⟨_, hTs⟩ hw
      exact ⟨D', C', hD, hC, hD', heq.conv ht⟩
  have hΓ' : E[Γ.snoc D'] ⊢ ok := .snoc hΓ hD'
  have hxv : TrM E B lps (Γ.snoc D') (Δ.pushLam (some x)) (.fvar x) (.var (Fin.last n)) :=
    TrM.fvar (by simp [MLCtx.pushLam, MLCtx.findF, MLDecl.denote, (fvarId_beq_iff x x).mpr rfl])
  have happ := app_var_typed ht' hΓ'
  have hew := TrM.weakFV (A := D') hx he
  refine ⟨D', hD, hD', ?_, ?_⟩
  · by_cases hsh : SpecialHead B e
    · obtain ⟨c, us, b, hc, hb, hs⟩ := hsh
      obtain ⟨bs, rfl⟩ := eq_mkAppN_of_getAppFn hc
      obtain ⟨bs', hlen, hargs, hsat⟩ := TrM.special_inv hb hs hew
      obtain ⟨t₂, hsat₂, hred⟩ := SatTr.append hsat [.var (Fin.last n)]
      have htr : TrM E B lps (Γ.snoc D') (Δ.pushLam (some x))
          (.app (mkAppN (.const c us) bs.toArray) (.fvar x)) t₂ := by
        rw [← SrcDefeq.mkAppN_snoc]
        refine .special hb hs (by simp [hlen]) (fun i a a' h₁ h₂ => ?_) hsat₂
        rcases Nat.lt_or_ge i bs.length with hi | hi
        · rw [List.getElem?_append_left hi] at h₁
          rw [List.getElem?_append_left (by omega)] at h₂
          exact hargs i a a' h₁ h₂
        · rw [List.getElem?_append_right hi] at h₁
          rw [List.getElem?_append_right (by omega)] at h₂
          obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.1 h₁
          obtain ⟨hk', rfl⟩ := List.getElem?_eq_some_iff.1 h₂
          simpa using hxv
      exact ⟨t₂, C', htr, TrM.inst_fvar hx hC, (Metalean.WHRedS.defeq hE hΓ' hred happ).right⟩
    · exact ⟨_, C', .app hsh hew hxv, TrM.inst_fvar hx hC, happ⟩
  · intro k ns tb h hcl
    have := ErasesAlt.absN x hty h 0 _ (AbsFV.Rel.zero x Δ) (by simpa using hcl)
    have hfv : FVarsIn (· ≠ x) e := by
      refine fvarsIn_mono (fun z hz hzx => ?_) (TrM.fvarsIn he)
      subst hzx; simp [hx] at hz
    simp only [AbsFV.absFV, absFV_fresh hfv, (fvarId_beq_iff x x).mpr rfl, ↓reduceIte,
      Nat.zero_add] at this
    exact .intro he ht' this

/-- The translation and typing of the opened body and of the opened type, and the erasure of an
alternative from the erasure of its opened body, on one binder of an alternative that is a λ,
whose type is a `Π` with the λ's binder name and domain (`LamMatch`): the λ is peeled
(`ErasesAlt.lam`), under the translation of its own domain. -/
theorem open_lam (henv : ProgEnv P ζ E B) (hE : EnvWF E) {σ : EvalEnv}
    (hty : ∀ c ci, findDecl σ.decls c = some ci →
      AbsFV.LBV 0 ci.type ∧ FVarsIn (fun _ => False) ci.type)
    {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    (hΓ : E[Γ] ⊢ ok) (hnb : ∀ i, Δ.findB i = none) {x : FVarId} (hx : Δ.findF x = none)
    {z : Name} {A b B₀ : Expr} {bi₀ bi : BinderInfo} {t T' : Metalean.Expr ζ lps.length n}
    (he : TrM E B lps Γ Δ (.lam z A b bi₀) t) (hT : TrM E B lps Γ Δ (.forallE z A B₀ bi) T')
    (ht : E[Γ] ⊢ t : T') :
    ∃ D', TrM E B lps Γ Δ A D' ∧ E[Γ] ⊢ D' typ ∧
      (∃ t' T'', TrM E B lps (Γ.snoc D') (Δ.pushLam (some x)) (b.instantiate1' (.fvar x)) t' ∧
        TrM E B lps (Γ.snoc D') (Δ.pushLam (some x)) (B₀.instantiate1' (.fvar x)) T'' ∧
        E[Γ.snoc D'] ⊢ t' : T'') ∧
      ∀ k ns tb, ErasesAlt E B lps σ (Γ.snoc D') (Δ.pushLam (some x)) k
          (b.instantiate1' (.fvar x)) (ns, tb) → closedn ns.length tb = true →
        ErasesAlt E B lps σ Γ Δ (k + 1) (.lam z A b bi₀)
          (binderNameOf z :: ns, _root_.toBvar x ns.length tb) := by
  obtain ⟨A₀, b₀, rfl, hA₀, hb₀⟩ := trM_lam_inv he
  obtain ⟨A₁, B₁, rfl, -, hB₁⟩ := SrcDefeq.trM_forallE_inv hT
  obtain ⟨tb, hbt, heq⟩ := Metalean.Defeq.lam_inv ht hΓ
  obtain ⟨h01, htb⟩ := Metalean.TypeEq.forallE_inj hE hΓ heq.symm
  obtain ⟨_, hTs⟩ := ht.regular
  obtain ⟨u, hBu⟩ := (Metalean.Defeq.forallE_inv hTs).2
  obtain ⟨B'', hB'', hd⟩ := trM_open_conv hE henv.metaOrderOK hΓ hnb hx h01.left h01.symm hB₁ hBu
  refine ⟨A₀, hA₀, h01.left, ⟨b₀, B'', TrM.inst_fvar hx hb₀, hB'',
    (htb.trans (Metalean.TypeEq.ofDefEq hd)).conv hbt⟩, fun k ns tb' h hcl => ?_⟩
  have := ErasesAlt.absN x hty h 0 _ (AbsFV.Rel.zero x Δ) (by simpa using hcl)
  have hfv : FVarsIn (· ≠ x) b := by
    have h' := (TrM.fvarsIn (TrM.lam (x := z) (bi := bi₀) hA₀ hb₀)).2
    refine fvarsIn_mono (fun w hw hwx => ?_) h'
    subst hwx; simp [hx] at hw
  rw [AbsFV.absFV_inst hfv, Nat.zero_add] at this
  exact .lam hA₀ h01.left this
end


/-! ## Opening an alternative to its arity -/

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P decls : List ConstantInfo}
  {view : EnvView} {cfg : ErasureConfig}

/-- `lambdaOrIntroToArity e T k K` at the pure backend, on a translated alternative `e` typed at
the translation of `T`, whose λs are `T`'s `Π`s (`LamMatch`): every successful run is a run of the
continuation `K` on the opened body and the `k` fresh variables, under locals and a context
extended by the opened binders, where an erasure of the opened body closed over the variables
(`altBody`, as `mkAlt` closes it) erases `e` under its `k` binders (`ErasesAlt`). `G` is a property
of the alternative that opening keeps. -/
theorem lambdaOrIntro_spec (hG : CoreEnv E B P decls view cfg) {α : Type} [Inhabited α]
    (Q : α → ErasureState → PureState → Prop) (G : Expr → Prop)
    (hGl : ∀ z A b bi y, G (.lam z A b bi) → G (b.instantiate1' (.fvar y)))
    (hGa : ∀ e y, G e → G (.app e (.fvar y))) :
    ∀ (k : Nat) {lps : List Name} {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
      {Δ : MLCtx ζ lps.length n} {e T : Expr} {t T' : Metalean.Expr ζ lps.length n}
      {tc : TravCtx} {ps : PureState} {st : ErasureState}
      {K : Expr → List FVarId → EraseT PureM α} {a : α} {st' : ErasureState} {ps' : PureState},
      CtxOK E B lps Γ Δ cfg tc ps → TrM E B lps Γ Δ e t → TrM E B lps Γ Δ T T' →
      E[Γ] ⊢ t : T' → LamMatch e T → G e →
      (∀ {m : Nat} (Γ' : Metalean.Ctx ζ lps.length 0 m) (Δ' : MLCtx ζ lps.length m) (e' : Expr)
          (t' : Metalean.Expr ζ lps.length m) (tc' : TravCtx) (ps₁ : PureState) (xs : List FVarId),
        CtxOK E B lps Γ' Δ' cfg tc' ps₁ → ps.next ≤ ps₁.next → TrM E B lps Γ' Δ' e' t' →
        (∃ U, E[Γ'] ⊢ t' : U) → G e' →
        (∃ L, tc'.locals = L ++ tc.locals ∧ ∀ l ∈ L, ∃ j, ps.next ≤ j ∧ l.fvarId = pureFVar j) →
        (∃ ns, namesOf tc'.locals xs = some ns) → xs.length = k →
        (∀ r, closedn 0 r = true → Erases E B lps (evalEnvOf view cfg decls) Γ' Δ' e' r →
          ∀ ns, namesOf tc'.locals xs = some ns →
            ErasesAlt E B lps (evalEnvOf view cfg decls) Γ Δ k e (ns, altBody xs r)) →
        (K e' xs).runPure st tc' ⟨decls, view⟩ ps₁ = .ok ((a, st'), ps') → Q a st' ps') →
      (lambdaOrIntroToArity (m := PureM) e T k K).runPure st tc ⟨decls, view⟩ ps =
        .ok ((a, st'), ps') → Q a st' ps' := by
  have hty := AbsFV.closed_types (σ := evalEnvOf view cfg decls) hG.prog hG.sub
  intro k
  induction k with
  | zero =>
    intro lps n Γ Δ e T t T' tc ps st K a st' ps' hctx he _ ht _ hGe hK hrun
    rw [lambdaOrIntroToArity] at hrun
    refine hK Γ Δ e t tc ps [] hctx (Nat.le_refl _) he ⟨_, ht⟩ hGe ⟨[], rfl, fun _ h => nomatch h⟩
      ⟨[], rfl⟩ rfl (fun r _ hr ns hns => ?_) hrun
    cases hns
    exact .done hr
  | succ k ih =>
    intro lps n Γ Δ e T t T' tc ps st K a st' ps' hctx he hT ht hm hGe hK hrun
    rw [lambdaOrIntroToArity, lambdaMonocularOrIntro_eq] at hrun
    obtain ⟨y, D, C, bi, hW, hrun⟩ := forallMonocular_inv hrun
    have hx := hctx.freshNext
    generalize hxd : pureFVar ps.next = x at hrun hx
    -- the opened binder
    obtain ⟨D', hD, hD', ⟨t₁, T₁, he₁, hT₁, ht₁⟩, hm₁, hG₁, hlift⟩ :
        ∃ D', TrM E B lps Γ Δ D D' ∧ E[Γ] ⊢ D' typ ∧
          (∃ t' T'', TrM E B lps (Γ.snoc D') (Δ.pushLam (some x)) (openAlt e x) t' ∧
            TrM E B lps (Γ.snoc D') (Δ.pushLam (some x)) (C.instantiate1' (.fvar x)) T'' ∧
            E[Γ.snoc D'] ⊢ t' : T'') ∧
          LamMatch (openAlt e x) (C.instantiate1' (.fvar x)) ∧ G (openAlt e x) ∧
          ∀ k ns tb, ErasesAlt E B lps (evalEnvOf view cfg decls) (Γ.snoc D')
              (Δ.pushLam (some x)) k (openAlt e x) (ns, tb) → closedn ns.length tb = true →
            ErasesAlt E B lps (evalEnvOf view cfg decls) Γ Δ (k + 1) e
              (binderNameOf y :: ns, _root_.toBvar x ns.length tb) := by
      cases e with
      | lam z A b bi₀ =>
        obtain ⟨B₀, bi₁, rfl, hmb⟩ := hm
        have hTe : Expr.forallE z A B₀ bi₁ = .forallE y D C bi := by
          rcases hW with h | h
          · exact h
          · exact (OracleInfer.whnf_forallE h).symm
        cases hTe
        obtain ⟨D', hD, hD', htr, hl⟩ :=
          open_lam hG.prog hG.wf hty hctx.wf hctx.nobv hx he hT ht
        exact ⟨D', hD, hD', htr, LamMatch.inst x hmb, hGl _ _ _ _ x hGe, hl⟩
      | _ =>
        obtain ⟨D', hD, hD', htr, hl⟩ :=
          open_intro hG.prog hG.wf hG.sub hty hctx.wf hctx.locals hx he hT ht hW
        exact ⟨D', hD, hD', htr, trivial, hGa _ x hGe, hl⟩
    subst hxd
    have hctx₁ := hctx.pushFVar (nm := y) hD hD' (tc.lctx.mkLocalDecl (pureFVar ps.next) y D bi)
    refine ih (K := fun e fs => K e (pureFVar ps.next :: fs)) hctx₁ he₁ hT₁ ht₁ hm₁ hG₁
      (fun Γ' Δ' e' t' tc' ps₁ xs hctx' hps he' ht' hGe' hL hns' hlen' hE' hrun' => ?_) hrun
    obtain ⟨L, hLe, hLj⟩ := hL
    have hfind : tc'.locals.find? (·.fvarId == pureFVar ps.next) =
        some ⟨pureFVar ps.next, y, D, none⟩ := by
      rw [hLe]
      dsimp only
      rw [List.find?_append, List.find?_cons, (fvarId_beq_iff _ _).mpr rfl]
      have : L.find? (·.fvarId == pureFVar ps.next) = none := by
        rw [List.find?_eq_none]
        intro l hl hb
        obtain ⟨j, hj, hjl⟩ := hLj l hl
        rw [hjl] at hb
        have := pureFVar_inj ((fvarId_beq_iff _ _).mp hb)
        dsimp only at hj
        omega
      rw [this]
      rfl
    refine hK Γ' Δ' e' t' tc' ps₁ (pureFVar ps.next :: xs) hctx' (by dsimp only at hps; omega)
      he' ht' hGe' ⟨L ++ [⟨pureFVar ps.next, y, D, none⟩], by rw [hLe]; simp, fun l hl => ?_⟩
      ?_ (by simp [hlen']) (fun r hr her ns hns => ?_) hrun'
    · rcases List.mem_append.1 hl with hl | hl
      · obtain ⟨j, hj, hjl⟩ := hLj l hl
        exact ⟨j, by dsimp only at hj; omega, hjl⟩
      · simp only [List.mem_singleton] at hl
        subst hl
        exact ⟨ps.next, Nat.le_refl _, rfl⟩
    · obtain ⟨ns', hns'⟩ := hns'
      refine ⟨binderNameOf y :: ns', ?_⟩
      simp only [namesOf] at hns' ⊢
      simp [List.mapM_cons, hfind, hns']
    · simp only [namesOf, List.mapM_cons, Option.bind_eq_bind, hfind] at hns
      cases hr' : namesOf tc'.locals xs with
      | none => simp [namesOf] at hr'; simp [hr'] at hns
      | some ns' =>
        simp only [namesOf] at hr'
        simp [hr'] at hns
        subst hns
        have hlen := namesOf_length (show namesOf tc'.locals xs = some ns' from hr')
        have := hlift k ns' (altBody xs r) (hE' r hr her ns' hr')
          (by rw [hlen]; exact closedn_altBody hr xs)
        rw [hlen] at this
        exact this

theorem ErasesDeps.altBody {σ : EvalEnv} {lenv : GlobalDeclarations} {r : LBTerm}
    (h : ErasesDeps E B σ lenv r) : ∀ xs, ErasesDeps E B σ lenv (StepsCasesCase.altBody xs r)
  | [] => h
  | _ :: xs => ErasesDeps.toBvar (ErasesDeps.altBody h xs) xs.length

/-- `visitAlt (j + 1) k masks [] alt` at the pure backend, with masks that keep every field and no
substituted field, from `visitExpr` at `j` (`ih`): on a translated, typed alternative, a successful
run erases it under its `k` field binders (`ErasesAlt`), with erased λ□ dependencies, and grows.
Reference: the branches of the `tCase` case of `erases_erase` (`MR E/ErasureFunction.v:1228`). -/
theorem visitAlt_spec (hG : CoreEnv E B P decls view cfg) {j : Nat}
    (ih : ∀ e, ExprSpec E B view cfg decls j e)
    {lps : List Name} {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    {S : Name → Prop} {st st' : ErasureState} {tc : TravCtx} {ps ps' : PureState} {k : Nat}
    {alt : Expr} {t : Metalean.Expr ζ lps.length n} {br : List BinderName × LBTerm}
    (hctx : CtxOK E B lps Γ Δ cfg tc ps) (hsc : ScopeOK decls S)
    (hocc : ∀ d, nameOccurs d alt = true → S d) (hmf : MachineFree cfg alt)
    (hnp : NatPlain cfg alt) (hrf : RecFree decls alt)
    (hok : StateOK E B (evalEnvOf view cfg decls) st) (he : TrM E B lps Γ Δ alt t)
    (ht : ∃ T, E[Γ] ⊢ t : T)
    (hrun : (visitAlt (m := PureM) (j + 1) k (Array.replicate k .keep) [] alt).runPure st tc
      ⟨decls, view⟩ ps = .ok ((br, st'), ps')) :
    ErasesAlt E B lps (evalEnvOf view cfg decls) Γ Δ k alt br ∧
      ErasesDeps E B (evalEnvOf view cfg decls) st'.gdecls br.2 ∧
      Grows E B (evalEnvOf view cfg decls) S st st' ps ps' := by
  rw [visitAlt, runPure_read_bind, runPure_read_bind, runPure_bind, inferType_runPure] at hrun
  cases hinf : Pure.inferType ⟨decls⟩ oracleFuel tc.locals [] alt with
  | error err => rw [hinf] at hrun; cases hrun
  | «ok» T =>
  rw [hinf] at hrun
  dsimp only [Except.map] at hrun
  rw [ok_bind'] at hrun
  dsimp only at hrun
  obtain ⟨T', hT', htT'⟩ := Pure.inferType_sound hG.prog hG.wf hG.sub hctx.wf hctx.locals
    hctx.nobv he ht hinf
  refine lambdaOrIntro_spec hG (fun br st' ps' => ErasesAlt E B lps (evalEnvOf view cfg decls) Γ Δ
      k alt br ∧ ErasesDeps E B (evalEnvOf view cfg decls) st'.gdecls br.2 ∧
      Grows E B (evalEnvOf view cfg decls) S st st' ps ps')
    (fun e => (∀ d, nameOccurs d e = true → S d) ∧ MachineFree cfg e ∧ NatPlain cfg e ∧
      RecFree decls e)
    (fun z A b bi y h => ⟨fun d hd => h.1 d
        (by rw [nameOccurs_inst_fvar] at hd; simpa [nameOccurs] using hd), mf_inst (a := .fvar y) trivial h.2.1.2,
      np_inst (a := .fvar y) trivial h.2.2.1.2, ConstsIn_inst_fvar h.2.2.2.2⟩)
    (fun e y h => ⟨fun d hd => h.1 d (by simpa [nameOccurs] using hd), ⟨h.2.1, trivial⟩,
      ⟨h.2.2.1, trivial⟩, ⟨h.2.2.2, trivial⟩⟩)
    k hctx he hT' htT' (inferType_lamMatch _ _ _ hinf) ⟨hocc, hmf, hnp, hrf⟩
    (fun Γ' Δ' e' t' tc' ps₁ xs hctx' hps he' ht' hGe' _ hns hlen hE' hrun' => ?_) hrun
  simp only [List.isEmpty_nil, ↓reduceIte] at hrun'
  rw [runPure_bind] at hrun'
  obtain ⟨⟨⟨r, st₁⟩, ps₂⟩, hr, hrun'⟩ := OracleWhnf.ok_of_bind hrun'
  obtain ⟨ns, hns⟩ := hns
  rw [filter_keep _ _ (by simp [hlen]), List.toList_toArray, mkAlt_run hns] at hrun'
  cases hrun'
  have ⟨her, hdeps, hgr⟩ := ih e' hctx' hsc hGe'.1 hGe'.2.1 hGe'.2.2.1 hGe'.2.2.2 hok he' ht' hr
  have hcl : closedn 0 r = true := by
    have := Erases.closed he' her
    rwa [countP_none hctx'.nobv] at this
  exact ⟨hE' r hcl her ns hns, ErasesDeps.altBody hdeps xs,
    ⟨hgr.inv, hgr.ext, Nat.le_trans hps hgr.next, hgr.scope⟩⟩

end

/-! ## Loops of the pure traversal -/


/-- A `for` loop over the list `L` at the pure backend whose body always continues: an invariant
`I` indexed by the processed prefix holds after every successful run. -/
theorem forIn_inv {α β : Type} {tc : TravCtx} {pc : PureCtx} {L : List α}
    (I : List α → β → ErasureState → PureState → Prop) (f : α → β → EraseT PureM (ForInStep β))
    (hf : ∀ pre a rest b st ps r st' ps', pre ++ a :: rest = L → I pre b st ps →
      (f a b).runPure st tc pc ps = .ok ((r, st'), ps') →
      ∃ b', r = .yield b' ∧ I (pre ++ [a]) b' st' ps') :
    ∀ (l pre : List α) (b : β) (st : ErasureState) (ps : PureState) (r : β) (st' : ErasureState)
      (ps' : PureState), pre ++ l = L → I pre b st ps →
      (forIn l b f).runPure st tc pc ps = .ok ((r, st'), ps') → I L r st' ps'
  | [], pre, b, st, ps, r, st', ps', hL, hI, h => by
    rw [List.forIn_nil] at h
    cases h
    simpa [← hL] using hI
  | a :: l, pre, b, st, ps, r, st', ps', hL, hI, h => by
    rw [List.forIn_cons, runPure_bind] at h
    obtain ⟨⟨⟨x, st₁⟩, ps₁⟩, hx, h⟩ := OracleWhnf.ok_of_bind h
    obtain ⟨b', rfl, hI'⟩ := hf pre a l b st ps x st₁ ps₁ hL hI hx
    exact forIn_inv I f hf l (pre ++ [a]) b' st₁ ps₁ r st' ps' (by simpa using hL) hI' h

/-- The alternatives `ctorAlts` gives: one `.ctor` per constructor, with its number of fields. -/
theorem ctorAlts_get {decls : List ConstantInfo} : ∀ {l : List Name} {alts : List CasesAltInfo},
    ctorAlts decls l = some alts → alts.length = l.length ∧ ∀ (i : Nat) (cn : Name), l[i]? = some cn →
      ∃ cv, findConst decls cn = some (.ctorInfo cv) ∧ alts[i]? = some (CasesAltInfo.ctor cn cv.numFields)
  | [], alts, h => by simp [ctorAlts] at h; subst h; simp
  | x :: l, alts, h => by
    unfold ctorAlts at h
    split at h
    · rename_i cv as hx hl
      cases h
      obtain ⟨h1, h2⟩ := ctorAlts_get hl
      refine ⟨by simp [h1], fun i cn hi => ?_⟩
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst hi
        exact ⟨cv, hx, rfl⟩
      | succ i => exact h2 i cn (by simpa using hi)
    · cases h

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P : List ConstantInfo}

/-- The constructors of an inductive of the program are distinct. -/
theorem ctors_inj (henv : ProgEnv P ζ E B) {T : Name} {iv : InductiveVal}
    (hiv : findDecl P T = some (.inductInfo iv)) {i j : Nat} {cn : Name}
    (hi : iv.ctors[i]? = some cn) (hj : iv.ctors[j]? = some cn) : i = j := by
  obtain ⟨ι, η, s, hB, -, -, hlen⟩ := henv.lookup_ind hiv
  have hil : i < ι.nctors s := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hi).1
  have hjl : j < ι.nctors s := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hj).1
  obtain ⟨cv, hcv, hfd, -, -, -, hci⟩ := SimInd.ind_ctor henv hB hiv ⟨i, hil⟩
  obtain ⟨cv', hcv', hfd', -, -, -, hcj⟩ := SimInd.ind_ctor henv hB hiv ⟨j, hjl⟩
  have e1 : cn = cv.name := Option.some.inj (hi.symm.trans hcv)
  have e2 : cn = cv'.name := Option.some.inj (hj.symm.trans hcv')
  rw [← e1] at hfd
  rw [← e2, hfd] at hfd'
  cases hfd'
  simp only at hci hcj
  omega

end

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P decls : List ConstantInfo}
  {view : EnvView} {cfg : ErasureConfig}

/-- `visitCasesOn (f + 1) iv m ∅ none d` at the pure backend, from `visitExpr` below `f` (`ih`), when
the map `m` gives each constructor of `iv` its number of fields and its alternative, and the
machine branches are not taken: a successful run registers `iv` and returns the λ□ `case` of its
λ□ inductive on `d`, whose branches erase the alternatives under their fields' binders.
Reference: the `tCase` case of `erases_erase` (`MR E/ErasureFunction.v:1228`). -/
theorem visitCasesOn_spec (hG : CoreEnv E B P decls view cfg) {f : Nat}
    (ih : ∀ j < f, ∀ e, ExprSpec E B view cfg decls j e) {iv : InductiveVal}
    (hiv : findDecl decls iv.name = some (.inductInfo iv))
    (hnm : cfg.nat = .machine → iv.name ≠ ``Nat ∧ iv.name ≠ ``Int)
    {m : Std.HashMap Name (Nat × Expr)} {alts : List Expr}
    {lps : List Name} {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    {S : Name → Prop} {st st' : ErasureState} {tc : TravCtx} {ps ps' : PureState} {d r : LBTerm}
    (hm : ∀ (i : Nat) cn, iv.ctors[i]? = some cn → ∃ cv alt,
      findDecl decls cn = some (.ctorInfo cv) ∧ alts[i]? = some alt ∧
      m[cn]? = some (cv.numFields, alt))
    (halts : ∀ alt ∈ alts, (∀ d, nameOccurs d alt = true → S d) ∧ MachineFree cfg alt ∧
      NatPlain cfg alt ∧ RecFree decls alt ∧ ∃ a', TrM E B lps Γ Δ alt a' ∧ ∃ A, E[Γ] ⊢ a' : A)
    (hctx : CtxOK E B lps Γ Δ cfg tc ps) (hsc : ScopeOK decls S)
    (hok : StateOK E B (evalEnvOf view cfg decls) st)
    (hdd : ErasesDeps E B (evalEnvOf view cfg decls) st.gdecls d)
    (hrun : (visitCasesOn (m := PureM) (f + 1) iv m ∅ none d).runPure st tc ⟨decls, view⟩ ps =
      .ok ((r, st'), ps')) :
    ∃ iid brs, IndIdOf (evalEnvOf view cfg decls) iv.name = some iid ∧
      r = .case (iid, iv.numParams) d brs ∧ brs.length = iv.ctors.length ∧
      (∀ (i : Nat) cn alt br k, iv.ctors[i]? = some cn → alts[i]? = some alt → brs[i]? = some br →
        ctorFields (evalEnvOf view cfg decls) cn = some k →
        ErasesAlt E B lps (evalEnvOf view cfg decls) Γ Δ k alt br) ∧
      ErasesDeps E B (evalEnvOf view cfg decls) st'.gdecls r ∧
      Grows E B (evalEnvOf view cfg decls) S st st' ps ps' := by
  rw [visitCasesOn, runPure_bind, StepsCases.runPure_pure, ok_bind'] at hrun
  dsimp only at hrun
  rw [runPure_read_bind] at hrun
  split at hrun
  · rename_i h1 h2
    exact ((hnm (by rw [← hctx.config]; exact h2)).1 h1).elim
  · rename_i h1 h2
    exact ((hnm (by rw [← hctx.config]; exact h2)).2 h1).elim
  rw [runPure_bind] at hrun
  obtain ⟨⟨⟨⟨indid, argmasks⟩, st₂⟩, ps₂⟩, hreg, hrun₂⟩ := OracleWhnf.ok_of_bind hrun
  clear hrun
  have hirr : tc.config.remove_irrel_constr_args = false := by
    rw [hctx.config]; exact hG.irr iv ⟨_, (findDecl_eq_some hiv).1, rfl⟩
  have hph : ∀ ci ∈ (evalEnvOf view cfg decls).decls,
      PhaseIDecl view tc.config (evalEnvOf view cfg decls).decls ci := by
    rw [hctx.config]; exact hG.phase
  obtain ⟨hok₂, hext₂, hcst₂, hid, hkm⟩ := register_inductive_ok (σ := evalEnvOf view cfg decls)
    hG.prog hG.wf hG.sub hok rfl hirr hph hG.bn hiv hreg
  have hmem₂ := register_inductive_mem (σ := evalEnvOf view cfg decls) hG.prog hG.sub rfl hirr hph
    hiv hreg
  have hps₂ : ps₂ = ps := KeepsPS.register_inductive iv _ _ _ _ _ _ hreg
  subst hps₂
  have hgr₂ : Grows E B (evalEnvOf view cfg decls) S st st₂ ps₂ ps₂ :=
    ⟨hok₂, hext₂, Nat.le_refl _, fun c kn h h' => by rw [hcst₂, h] at h'; cases h'⟩
  dsimp only at hrun₂
  rw [runPure_bind] at hrun₂
  obtain ⟨⟨⟨⟨brs, s'⟩, st₃⟩, ps₃⟩, hloop, hrun₃⟩ := OracleWhnf.ok_of_bind hrun₂
  cases hrun₃
  have hlenm := hkm.1
  have hI := forIn_inv (tc := tc) (pc := ⟨decls, view⟩) (L := iv.ctors)
    (fun pre (b : Array (List BinderName × LBTerm) × List ConstructorArgMask) st₁ ps₁ =>
      b.2 = argmasks.drop pre.length ∧ b.1.toList.length = pre.length ∧
      (∀ (i : Nat) cn alt br k, iv.ctors[i]? = some cn → alts[i]? = some alt →
        b.1.toList[i]? = some br → ctorFields (evalEnvOf view cfg decls) cn = some k →
        ErasesAlt E B lps (evalEnvOf view cfg decls) Γ Δ k alt br) ∧
      (∀ br ∈ b.1.toList, ErasesDeps E B (evalEnvOf view cfg decls) st₁.gdecls br.2) ∧
      Grows E B (evalEnvOf view cfg decls) S st₂ st₁ ps₂ ps₁) _ ?_ iv.ctors [] (#[], argmasks)
    st₂ ps₂ _ _ _ rfl ⟨rfl, rfl, fun i _ _ br _ _ _ h => by simp at h, fun _ h => by simp at h,
      .refl hok₂⟩ hloop
  · obtain ⟨-, hlen, hE, hD, hgr⟩ := hI
    refine ⟨indid, brs.toList, hid, rfl, hlen, hE, ?_, hgr₂.trans hgr⟩
    exact .case (T := iv.name) hid (StateLemmas.ErasesInd.ext hgr.ext (hok₂.inductives iv.name _ hmem₂).2.1)
      (ErasesDeps.ext (LenvExt.trans hext₂ hgr.ext) hdd) hD
  · intro pre cn rest ⟨as₁, s₁⟩ st₁ ps₁ res st₁' ps₁' hL ⟨hs, hlen, hE, hD, hgr⟩ hb
    dsimp only at hs hlen hE hD hb
    have hk : pre.length < iv.ctors.length := by rw [← hL]; simp
    have hcn : iv.ctors[pre.length]? = some cn := by rw [← hL]; simp
    obtain ⟨cv, alt, hcv, halt, hmc⟩ := hm _ _ hcn
    have hmask := hkm.2 pre.length cn cv hcn hcv
    rw [hs, List.drop_eq_getElem_cons (by rw [hlenm]; exact hk), (List.getElem?_eq_some_iff.1 hmask).2] at hb
    simp only [show ∀ (a : ConstructorArgMask) (l : List ConstructorArgMask),
      Std.Stream.next? (a :: l) = some (a, l) from fun _ _ => rfl, hmc,
      Std.HashMap.getD_empty] at hb
    rw [runPure_bind] at hb
    obtain ⟨⟨⟨br, st₄⟩, ps₄⟩, hvis, hb⟩ := OracleWhnf.ok_of_bind hb
    cases hb
    cases f with
    | zero => rw [visitAlt] at hvis; cases hvis
    | succ f =>
    obtain ⟨hoa, hma, hna, hra, a', hta, A, hA⟩ := halts alt (List.mem_of_getElem? halt)
    have ⟨hEa, hDa, hga⟩ := visitAlt_spec hG (ih f (by omega)) (hctx.mono hgr.next) hsc hoa hma hna hra hgr.inv
      hta ⟨A, hA⟩ hvis
    refine ⟨_, rfl, by simp, by simp [hlen], ?_, ?_,
      hgr.trans hga⟩
    · intro i cn' alt' br' k hi hai hbi hk'
      rw [Array.toList_push] at hbi
      rcases Nat.lt_or_ge i pre.length with hlt | hge
      · rw [List.getElem?_append_left (by omega)] at hbi
        exact hE i cn' alt' br' k hi hai hbi hk'
      · rw [List.getElem?_append_right (by omega)] at hbi
        obtain ⟨hi0, rfl⟩ := List.getElem?_eq_some_iff.1 hbi
        simp only [List.length_singleton] at hi0
        have hip : i = pre.length := by omega
        subst hip
        rw [hcn] at hi; cases hi
        rw [halt] at hai; cases hai
        have : k = cv.numFields := by
          simp only [ctorFields, evalEnvOf] at hk'
          rw [show findDecl decls cn = _ from hcv] at hk'
          cases hk'; rfl
        subst this
        simpa using hEa
    · intro br' hbr
      rw [Array.toList_push] at hbr
      rcases List.mem_append.1 hbr with hbr | hbr
      · exact ErasesDeps.ext hga.ext (hD br' hbr)
      · simp only [List.mem_singleton] at hbr
        subst hbr
        exact hDa

end

/-! ## The semantic side conditions of `Erases.cases` -/

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P : List ConstantInfo}
  {lps : List Name}
open Metalean (TypeEq)

/-- A `casesOn` that the eraser does not reduce (the oracle's level `u` of the discriminant's type
is never zero, or the inductive does not have exactly one constructor) is not `CasesReduced`: the
discriminant's type is the inductive at the spine's levels (`cases_sat_split`), whose sort is
`casesSortLevel`, so the two levels are never zero together. -/
theorem not_casesReduced {σ : EvalEnv} (henv : ProgEnv P ζ E B) (hE : EnvWF E)
    (hsub : SubEnv σ.decls P) {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
    {Δ : MLCtx ζ lps.length n} (hΓ : E[Γ] ⊢ ok) {c : Name} {iv : InductiveVal}
    {d : DefinitionVal} {us : List Level} {as : List Expr} {t T : Metalean.Expr ζ lps.length n}
    {u : Level} (hcs : σ.casesOn? c = some iv) (hd : findDecl σ.decls c = some (.defnInfo d))
    (hsat : casesArity iv ≤ as.length)
    (he : TrM E B lps Γ Δ (mkAppN (.const c us) as.toArray) t) (ht : E[Γ] ⊢ t : T)
    (hlev : ∀ m m'', as[casesMajor iv]? = some m → TrM E B lps Γ Δ m m'' →
      (∃ M, E[Γ] ⊢ m'' : M) →
      ∃ l M, TrLevel lps u = some l ∧ E[Γ] ⊢ m'' : M ∧ E[Γ] ⊢ M : .sort l)
    (hC3 : u.isNeverZero = true ∨ iv.ctors.length ≠ 1) : ¬ CasesReduced iv us := by
  rintro ⟨h1, l₀, hl₀, hz⟩
  rcases hC3 with hu | h1'
  swap
  · exact h1' h1
  obtain ⟨t₁, F, xs, -, -, ι, η, s, L, l, ps, ms, mins, is, m, m'', hm, -, hm'', hR, hlv, -,
    -⟩ := StepsCases.cases_sat_split henv hE hsub hΓ hcs hd hsat he ht
  obtain ⟨-, hps, -, -, his, hmaj⟩ := Metalean.Defeq.recr_typed hE hΓ hR
  obtain ⟨l₁, M, hTr, hmM, hMl⟩ := hlev m m'' hm hm'' ⟨_, hmaj⟩
  have hl₁ : l₁ = (E.get η).block.level{L} := by
    obtain ⟨l₂, hMI⟩ := TypeEq.sort_uniq hE hΓ (Metalean.Defeq.uniqTy hE hΓ hmM hmaj)
    have h1 := TypeEq.sort_inj hE hΓ (Metalean.Defeq.uniqTy hE hΓ hMI.left hMl)
    have h2 := TypeEq.sort_inj hE hΓ
      (Metalean.Defeq.uniqTy hE hΓ hMI.right (Metalean.Defeq.indDF hps his).left)
    rw [← h1, h2]
  have hnz := (TrLevel.isNeverZero_iff hTr).1 hu
  rw [hl₁] at hnz
  have := (TrLevel.isNeverZero_iff (hlv l₀ hl₀)).2 hnz
  rw [hz] at this
  cases this

/-- The inductive of a large-eliminating recognized `casesOn` (more universe parameters than its
inductive) is a subsingleton: a constructor node whose type is a proposition has the block's level
zero at its levels, so the block eliminates into every sort as a subsingleton
(`SortLargeElim.singleton_of_eval_zero`: one constructor, `Ctor.Eligible` fields); index variables
are Lean index fields (`IndBlock.indexVars`), of which the constructors of a recognized `casesOn`
have none (`NoIndexFields`); so ordinary fields are typed at level `0`, and recursive fields are
`Π`s into the block's sort, a proposition. Reference: `Subsingleton`
(`MR P/PCUICElimination.v:45`); `elim_only_at_universe_zero` (Lean's kernel,
`src/kernel/inductive.cpp`). -/
theorem subsingleton_large {σ : EvalEnv} (henv : ProgEnv P ζ E B) (hE : EnvWF E)
    (hsub : SubEnv σ.decls P) (hdc : DepClosed σ.decls) (hidx : NoIndexFields σ.decls)
    {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n} (hΓ : E[Γ] ⊢ ok)
    {c : Name} {ci : CasesInfo} {iv : InductiveVal} {d : DefinitionVal} {us : List Level}
    {as : List Expr} {t T : Metalean.Expr ζ lps.length n}
    (hci : casesInfo? σ.decls c = some ci) (hcs : σ.casesOn? c = some iv)
    (hd : findDecl σ.decls c = some (.defnInfo d))
    (hlp : d.levelParams.length ≠ iv.levelParams.length) (hsat : casesArity iv ≤ as.length)
    (he : TrM E B lps Γ Δ (mkAppN (.const c us) as.toArray) t) (ht : E[Γ] ⊢ t : T) :
    Subsingleton E B iv.name := by
  obtain ⟨t₁, F, xs, -, -, ι, η, s, L, l, ps, ms, mins, is, m, m'', hm, hBT, hm'', hR, -, hlv,
    -⟩ := StepsCases.cases_sat_split henv hE hsub hΓ hcs hd hsat he ht
  have hLE : (E.get η).block.LargeElim := Classical.byContradiction fun h => hlp (hlv.2 h)
  -- the block's ctors have no index variable among their fields
  obtain ⟨lps₀, Is, Cs, Rs, orders, ⟨⟨_, _, _, _, hblk⟩, -, hfd, -, hind, -⟩, hix⟩ :=
    CasesWhred.ProgEnv.blockIdx henv η
  have hT := hind _ s hBT
  have hivd := SimInd.casesOn?_ind hcs
  have hI := hfd (.inductInfo (Is s)) (by simp [IndBlock.decls, List.mem_ofFn])
  rw [CasesWhred.name_inductInfo, ← hT, SrcDefeq.findDecl_sub hsub hivd] at hI
  cases hI
  obtain ⟨-, -, -, hpI, -, hcsI, -⟩ := hblk.ind s
  have hindI : findConst σ.decls ci.indName = some (.inductInfo (Is s)) := by
    have hcs' := hcs
    simp only [EvalEnv.casesOn?, hci] at hcs'
    split at hcs'
    · cases hcs'
      assumption
    · cases hcs'
  have hnoidx : ∀ (c' : Fin (ι.nctors s)) (i : Fin (ι.nindices s))
      (f : Fin (ι.ctors s c').nfields),
      (((E.get η).block.ctors s c').targetIndices i).isVar ≠ some (ι.nparams + f.val) := by
    intro c' i f hx
    have hany := hix s c' ⟨i, f, hx⟩
    have hmem : (Cs s c').name ∈ (Is s).ctors := by
      rw [hcsI]; exact List.mem_ofFn.mpr ⟨c', rfl⟩
    obtain ⟨ci₀, hci₀⟩ := Option.isSome_iff_exists.1
      ((hdc _ (findDecl_eq_some hivd).1).2.2.1 _ rfl _ hmem)
    have hC := hfd (.ctorInfo (Cs s c')) (by
      simp only [IndBlock.decls, List.mem_append, List.mem_flatten, List.mem_ofFn]
      exact .inl (.inr ⟨_, ⟨s, rfl⟩, List.mem_ofFn.mpr ⟨c', rfl⟩⟩))
    rw [CasesWhred.name_ctorInfo, SrcDefeq.findDecl_sub hsub hci₀] at hC
    cases hC
    have hall := hidx c ci (Is s) hci hindI _ hmem _ hci₀
    rw [hpI, List.all_eq_true] at hall
    obtain ⟨x, hx, hxs⟩ := List.any_eq_true.1 hany
    have := hall x hx
    cases x <;> simp_all
  -- a constructor node that is a proof
  intro ι' η' s' hB' ℓ' n' Γ' c' ls ps' fds recFds _ hΓ' ⟨U, hU, hUp⟩
  rw [hBT] at hB'
  cases hB'
  obtain ⟨ps₁, fds₁, recFds₁, -, -, -, hind, hUI⟩ := hU.ctor_inv
  have hzero : (E.get η).block.level{ls} = .zero := by
    obtain ⟨l₂, hMI⟩ := TypeEq.sort_uniq hE hΓ' hUI
    have h1 := TypeEq.sort_inj hE hΓ' (Metalean.Defeq.uniqTy hE hΓ' hMI.left hUp)
    have h2 := TypeEq.sort_inj hE hΓ' (Metalean.Defeq.uniqTy hE hΓ' hMI.right hind.left)
    rw [← h2, h1]
  obtain ⟨h1, helig⟩ := (hLE s).singleton_of_eval_zero ls (ν := fun _ => 0)
    (by rw [hzero]; rfl) c'
  have hct := Metalean.Defeq.ctor_typed hE hU
  have hctor := (hE.entryWF η).block.ctors s c'
  refine ⟨by omega, fun f => ?_, fun f => ?_⟩
  · rcases helig.ordinary f with hz | ⟨i, hi⟩
    · have hs := hctor.ordinaryFieldExpr f hct.1 hct.2.1
      rw [hz, Metalean.Level.inst_zero] at hs
      exact ⟨_, hct.2.1 f, hs⟩
    · exact absurd hi (hnoidx c' i f)
  · have hz := helig.recursive f
    obtain ⟨v, hv⟩ := hctor.recursiveFieldExpr rfl f hΓ' hct.1 hct.2.1
    rw [Metalean.Ctor.recursiveFieldExpr_eq] at hv
    obtain ⟨hΓt, w, hindw⟩ := Metalean.Ctx.pi_isType_inv _ hΓ' hv
    obtain ⟨-, -, -, -, hsort⟩ := Metalean.Defeq.ind_inv hindw
    have hindp := hsort.conv hindw
    rw [hz, Metalean.Level.inst_zero] at hindp
    have hpi := Metalean.Ctx.pi_prop _ hΓt hindp
    rw [← Metalean.Ctor.recursiveFieldExpr_eq] at hpi
    exact ⟨_, hct.2.2 f, hpi⟩

end

/-! ## The `case` branch of `visitCases` -/

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P decls : List ConstantInfo}
  {view : EnvView} {cfg : ErasureConfig} {lps : List Name}

/-- The `case` branch of `visitCases` (`LeanToLambdaBox/Erasure.lean:870`): on a saturated spine of
a recognized `casesOn` with more universe parameters than its inductive (not the `□` branch), when
the oracle's level `u` of the discriminant's type is never zero or the inductive does not have
exactly one constructor (not the reduced branch), a successful run erases the spine to the λ□
`case` of the inductive on the erased major, with one branch per constructor (`visitCasesOn`,
`visitAlt`), applied to the erasures of the extra arguments: `Erases.cases`, whose side conditions
are `not_casesReduced` and `subsingleton_large`. The recognizer gives one alternative per
constructor and no catch-all, the constructors have no index field (`NoIndexFields`), and the
machine branches of `visitCasesOn` are not taken (`NatPlain`, `MachineFree`). Reference: the
`tCase` case of `erases_erase` (`MR E/ErasureFunction.v:1228`), rule `erases_tCase`
(`MR E/Extract.v:111`). -/
theorem casesSat_case (hG : CoreEnv E B P decls view cfg) {j : Nat}
    (ih : StepIH E B view cfg decls j) {c : Name} {ci : CasesInfo}
    (hci : casesInfo? decls c = some ci) {cd : DefinitionVal} {iv : InductiveVal}
    (hd : findDecl decls c = some (.defnInfo cd))
    (hiv : findDecl decls ci.indName = some (.inductInfo iv))
    (hlp : cd.levelParams.length ≠ iv.levelParams.length) {n : Nat}
    {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n} {S : Name → Prop}
    {us : List Level} {as : List Expr} {t : Metalean.Expr ζ lps.length n} {st : ErasureState}
    {tc : TravCtx} {ps : PureState} {r : LBTerm} {st' : ErasureState} {ps' : PureState}
    {u : Level} (hu : ∀ m, as[casesMajor iv]? = some m →
      Pure.typeLevel ⟨decls⟩ oracleFuel tc.locals m = .ok u)
    (hC3 : u.isNeverZero = true ∨ iv.ctors.length ≠ 1)
    (hctx : CtxOK E B lps Γ Δ cfg tc ps) (hsc : ScopeOK decls S)
    (hocc : ∀ d, nameOccurs d (mkAppN (.const c us) as.toArray) = true → S d)
    (hmf : MachineFree cfg (mkAppN (.const c us) as.toArray))
    (hnp : NatPlain cfg (mkAppN (.const c us) as.toArray))
    (hrf : RecFree decls (mkAppN (.const c us) as.toArray))
    (hok : StateOK E B (evalEnvOf view cfg decls) st)
    (he : TrM E B lps Γ Δ (mkAppN (.const c us) as.toArray) t) (ht : ∃ T, E[Γ] ⊢ t : T)
    (hsat : ci.arity ≤ as.length)
    (hrun : (visitCases (m := PureM) j ci as.toArray).runPure st tc ⟨decls, view⟩ ps =
      .ok ((r, st'), ps')) :
    Erases E B lps (evalEnvOf view cfg decls) Γ Δ (mkAppN (.const c us) as.toArray) r ∧
      ErasesDeps E B (evalEnvOf view cfg decls) st'.gdecls r ∧
      Grows E B (evalEnvOf view cfg decls) S st st' ps ps' := by
  obtain ⟨iv', cd', hiv', hd', hdn, hcs, har, hdp⟩ :=
    StepsCases.casesInfo?_eval (view := view) (cfg := cfg) hci
  rw [hiv] at hiv'; cases hiv'
  rw [hd] at hd'; cases hd'
  obtain ⟨alts, halts, hanp, hrange⟩ := StepsCases.casesInfo?_alts hci hiv
  obtain ⟨hlena, haltsg⟩ := ctorAlts_get halts
  have hmlt : casesMajor iv < as.length := by
    rw [har] at hsat; simp only [casesArity] at hsat; omega
  have hdisc : as.toArray[ci.discrPos]? = some (as[casesMajor iv]'hmlt) := by
    rw [hdp]; simp
  cases j with
  | zero => rw [visitCases] at hrun; cases hrun
  | succ j =>
  rw [visitCases, TravFrame.runPure_bind, StepsCases.getOrFail_run hdisc, Steps.ok_bind'] at hrun
  dsimp only at hrun
  rw [TravFrame.runPure_bind,
    StepsCases.getConst_run (pc := ⟨decls, view⟩) (show findConst decls _ = _ from hiv),
    Steps.ok_bind'] at hrun
  dsimp only at hrun
  rw [TravFrame.runPure_bind, hdn,
    StepsCases.getConst_run (pc := ⟨decls, view⟩) (show findConst decls _ = _ from hd),
    Steps.ok_bind'] at hrun
  dsimp only at hrun
  simp only [show (cd.levelParams.length == iv.levelParams.length) = false by simpa using hlp,
    Bool.false_eq_true, ↓reduceIte] at hrun
  rw [TravFrame.runPure_read_bind, TravFrame.runPure_read_bind, TravFrame.runPure_bind,
    TravFrame.runPure_liftM, TravFrame.typeLevel_run, hu _ (List.getElem?_eq_getElem _)] at hrun
  dsimp only [Except.map] at hrun
  rw [Steps.ok_bind', Steps.ok_bind'] at hrun
  dsimp only at hrun
  rw [hanp, hrange, TravFrame.runPure_bind, TravFrame.rco_forIn] at hrun
  obtain ⟨⟨⟨⟨mp, ca, s₀⟩, st₁⟩, ps₁⟩, hloop, hrun⟩ := OracleWhnf.ok_of_bind hrun
  have hLlen : (casesMajor iv + 1...casesArity iv).toList.length = alts.length := by
    rw [Nat.length_toList_rco, hlena]; simp [casesArity]
  have hI := forIn_inv (tc := tc) (pc := ⟨decls, view⟩) (L := (casesMajor iv + 1...casesArity iv).toList)
    (fun pre (b : Std.HashMap Name (Nat × Expr) × Option (Nat × Expr) × Subarray CasesAltInfo)
        st₂ ps₂ => st₂ = st ∧ ps₂ = ps ∧ b.2.1 = none ∧ b.2.2.array = alts.toArray ∧
      b.2.2.start = pre.length ∧ b.2.2.stop = alts.length ∧
      ∀ i < pre.length, ∀ cn, iv.ctors[i]? = some cn → ∃ cv a,
        findConst decls cn = some (.ctorInfo cv) ∧ as[casesMajor iv + 1 + i]? = some a ∧
        b.1[cn]? = some (cv.numFields, a)) _ ?_ _ [] _ st ps _ _ _ rfl
    ⟨rfl, rfl, rfl, by simp [Std.toStream], by simp [Std.toStream], by simp [Std.toStream],
      fun i hi => by simp at hi⟩ hloop
  swap
  · intro pre i rest ⟨mp, ca, s⟩ st₂ ps₂ res st₃ ps₃ hL ⟨rfl, rfl, hca, harr, hstart, hstop, hmap⟩ hb
    dsimp only at hca harr hstart hstop hmap hb
    have hk : pre.length < alts.length := by
      rw [← hLlen, ← hL]; simp
    have hi : i = casesMajor iv + 1 + pre.length := by
      have h1 : (casesMajor iv + 1...casesArity iv).toList[pre.length]? = some i := by
        rw [← hL]; simp
      rw [Nat.getElem?_toList_rco] at h1
      split at h1
      · cases h1; rfl
      · cases h1
    subst hi
    obtain ⟨cn, hcn⟩ : ∃ cn, iv.ctors[pre.length]? = some cn :=
      ⟨_, List.getElem?_eq_getElem (by rw [← hlena]; exact hk)⟩
    obtain ⟨cv, hcv, hacn⟩ := haltsg _ _ hcn
    have hlt : s.start < s.stop := by rw [hstart, hstop]; exact hk
    unfold Std.Stream.next? Std.instStreamSubarray at hb
    dsimp only at hb
    rw [dite_eq_left_of_eq_true (eq_true hlt)] at hb
    have hsa : s.array[s.start]'(Nat.lt_of_lt_of_le hlt s.stop_le_array_size) =
        CasesAltInfo.ctor cn cv.numFields := by
      have := List.getElem?_eq_some_iff.1 hacn
      simp only [harr, hstart, List.getElem_toArray]
      exact this.2
    simp only [hsa] at hb
    have hbd : casesMajor iv + 1 + pre.length < as.length := by
      rw [har] at hsat; simp only [casesArity] at hsat; rw [hlena] at hk; omega
    have has : as.toArray[casesMajor iv + 1 + pre.length]? =
        some (as[casesMajor iv + 1 + pre.length]'hbd) := by
      simp
    rw [TravFrame.runPure_bind, StepsCases.getOrFail_run has, Steps.ok_bind'] at hb
    cases hb
    refine ⟨_, rfl, rfl, rfl, hca, harr, by simp only [List.length_append, List.length_singleton, ← hstart]; rfl, hstop,
      fun i' hi' cn' hcn' => ?_⟩
    simp only [List.length_append, List.length_singleton] at hi'
    rw [Std.HashMap.getElem?_insert]
    rcases Nat.lt_or_ge i' pre.length with hlt' | hge
    · have hne : (cn == cn') = false := by
        rcases Bool.eq_false_or_eq_true (cn == cn') with h' | h'
        · have e := beq_iff_eq.mp h'
          subst e
          have := ctors_inj hG.prog (SrcDefeq.findDecl_sub (σ := evalEnvOf view cfg decls) hG.sub hiv) hcn hcn'
          omega
        · exact h'
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      exact hmap i' hlt' cn' hcn'
    · have : i' = pre.length := by omega
      subst this
      rw [hcn] at hcn'; cases hcn'
      exact ⟨cv, _, hcv, List.getElem?_eq_getElem hbd, by simp⟩
  obtain ⟨hst₁, hps₁, hca, -, -, -, hmap⟩ := hI
  dsimp only at hst₁ hps₁ hca hmap hrun
  rw [hst₁, hps₁, hca] at hrun
  -- no index is substituted
  have hctorc : ∀ cn ∈ iv.ctors, ∃ cv, findConst decls cn = some (.ctorInfo cv) := by
    intro cn hcn
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hcn
    obtain ⟨cv, hcv, -⟩ := haltsg _ _ hi
    exact ⟨cv, hcv⟩
  by_cases hni : (!u.isNeverZero && decide (iv.numIndices > 0)) = true
  all_goals first
    | (rw [if_pos hni, TravFrame.runPure_bind] at hrun
       obtain ⟨⟨⟨idx, st₂⟩, ps₂⟩, hloop₂, hrun⟩ := OracleWhnf.ok_of_bind hrun
       obtain ⟨rfl, hs₂, hp₂⟩ := forIn_inv (tc := tc) (pc := ⟨decls, view⟩) (L := iv.ctors)
         (fun _ (b : Std.HashMap Name (List (Option Expr))) st₂ ps₂ => b = ∅ ∧ st₂ = st ∧ ps₂ = ps)
         _ (fun pre cn rest b st₂ ps₂ res st₃ ps₃ hL ⟨hb, hs, hp⟩ hrb => by
           subst hb hs hp
           have hcn : cn ∈ iv.ctors := by rw [← hL]; simp
           obtain ⟨cv, hcv⟩ := hctorc cn hcn
           rw [TravFrame.runPure_bind, StepsCases.getConst_run (pc := ⟨decls, view⟩) hcv,
             Steps.ok_bind'] at hrb
           dsimp only at hrb
           rw [if_pos (hG.idx c ci iv hci hiv cn hcn cv hcv)] at hrb
           cases hrb
           exact ⟨_, rfl, rfl, rfl, rfl⟩) _ [] ∅ st ps _ _ _ rfl ⟨rfl, rfl, rfl⟩ hloop₂
       rw [hs₂, hp₂] at hrun)
    | rw [if_neg hni] at hrun
  all_goals
  dsimp only at hrun
  have hc2 : (!u.isNeverZero && iv.numCtors == 1) = false := by
    rw [InductiveVal.numCtors]
    rcases hC3 with h | h <;> simp [h]
  rw [if_neg (by rw [hc2]; decide), TravFrame.runPure_bind] at hrun
  obtain ⟨⟨⟨dnt, st₂⟩, ps₂⟩, hdrun, hrun⟩ := OracleWhnf.ok_of_bind hrun
  have hall : (iv.ctors.all fun x => mp.contains x) = true := by
    rw [List.all_eq_true]
    intro cn hcn
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hcn
    obtain ⟨cv, a, -, -, hma⟩ := hmap i (by rw [hLlen, hlena]; exact (List.getElem?_eq_some_iff.1 hi).1) cn hi
    simp [Std.HashMap.contains_iff_mem, Std.HashMap.mem_iff_isSome_getElem?, hma]
  rw [if_pos hall, TravFrame.runPure_bind] at hrun
  obtain ⟨⟨⟨ret, st₃⟩, ps₃⟩, hcrun, hrun⟩ := OracleWhnf.ok_of_bind hrun
  dsimp only at hcrun hrun
  cases j with
  | zero => rw [visitExpr] at hdrun; cases hdrun
  | succ f =>
  obtain ⟨T, hT⟩ := ht
  -- the arguments
  have hsp := mkAppN_toArray (.const c us) as
  have hQ : ∀ {Q : Expr → Prop}, (∀ f a, Q (.app f a) → Q f ∧ Q a) →
      Q (mkAppN (.const c us) as.toArray) → Q (.const c us) ∧ ∀ a ∈ as, Q a := fun hQ' h =>
    foldl_pred hQ' (by rw [← hsp]; exact h)
  have hoccA := (hQ (Q := fun x => ∀ d, nameOccurs d x = true → S d)
    (fun f a h => ⟨fun d hd => h d (by simp [nameOccurs, hd]),
      fun d hd => h d (by simp [nameOccurs, hd])⟩) hocc).2
  have hmfA := hQ (Q := MachineFree cfg) (fun _ _ h => h) hmf
  have hnpA := hQ (Q := NatPlain cfg) (fun _ _ h => h) hnp
  have hrfA := (hQ (Q := RecFree decls) (fun _ _ h => h) hrf).2
  have htyA := (spine_typed (StepsCases.casesOn_notSpecial (σ := evalEnvOf view cfg decls)
    hG.prog hG.sub hd) he ⟨T, hT⟩).2
  have hargs : ∀ a ∈ as, (∀ d, nameOccurs d a = true → S d) ∧ MachineFree cfg a ∧
      NatPlain cfg a ∧ RecFree decls a ∧ ∃ a', TrM E B lps Γ Δ a a' ∧ ∃ A, E[Γ] ⊢ a' : A :=
    fun a ha => ⟨hoccA a ha, hmfA.2 a ha, hnpA.2 a ha, hrfA a ha, htyA a ha⟩
  -- the discriminant
  obtain ⟨hoa, hma, hna, hra, a', hta, A, hA⟩ := hargs _ (List.getElem_mem hmlt)
  have ⟨herd, hdepd, hgrd⟩ := ih.expr (f + 1) (by omega) _ hctx hsc hoa hma hna hra hok hta
    ⟨A, hA⟩ hdrun
  -- the alternatives and the `case`
  have hname : iv.name = ci.indName := (findDecl_eq_some hiv).2
  obtain ⟨⟨T₀, hc₀, hT₀⟩, -⟩ := casesInfo?_spec hci
  have hnm : cfg.nat = .machine → iv.name ≠ ``Nat ∧ iv.name ≠ ``Int := by
    intro hm'
    refine ⟨fun h => (hnpA.1 hm').2 ?_, fun h => (hmfA.1 hm').2 ?_⟩
    · rw [hc₀, ← hT₀, ← hname, h]
    · rw [hc₀, ← hT₀, ← hname, h]
  have hk : casesMajor iv + 1 + iv.ctors.length ≤ as.length := by
    rw [har] at hsat; exact hsat
  generalize halts' : (as.drop (casesMajor iv + 1)).take iv.ctors.length = altsL
  have haltsL : ∀ (i : Nat), i < iv.ctors.length → altsL[i]? = as[casesMajor iv + 1 + i]? := by
    intro i hi
    rw [← halts', List.getElem?_take_of_lt hi, List.getElem?_drop]
  obtain ⟨iid, brs, hid, rfl, hlenb, hEb, hdepsC, hgrC⟩ := visitCasesOn_spec (alts := altsL) hG
    (fun j' hj' => ih.expr j' (by omega)) (by rw [hname]; exact hiv) hnm
    (fun i cn hcn => by
      have hil : i < iv.ctors.length := (List.getElem?_eq_some_iff.1 hcn).1
      obtain ⟨cv, a, hcv, ha, hma⟩ := hmap i (by rw [hLlen, hlena]; exact hil) cn hcn
      exact ⟨cv, a, hcv, by rw [haltsL i hil, ha], hma⟩)
    (fun alt halt => hargs alt (by
      rw [← halts'] at halt; exact List.mem_of_mem_drop (List.mem_of_mem_take halt)))
    (hctx.mono hgrd.next) hsc hgrd.inv hdepd hcrun
  -- the extra arguments
  have hsl : (as.toArray.toSubarray ci.arity).toList = as.drop ci.arity := by
    rw [Subarray.toList_eq]
    simp only [Array.array_toSubarray, Array.toList_extract, List.extract_eq_drop_take]
    simp [Nat.min_eq_left hsat]
  rw [TravFrame.subarray_forIn, hsl, TravFrame.runPure_bind] at hrun
  obtain ⟨⟨⟨ret', st₄⟩, ps₄⟩, hext, hrun⟩ := OracleWhnf.ok_of_bind hrun
  cases hrun
  obtain ⟨es, hF, rfl, hDe, hgrE⟩ := forIn_inv (tc := tc) (pc := ⟨decls, view⟩)
    (L := as.drop ci.arity)
    (fun pre (b : LBTerm) st₅ ps₅ => ∃ es, List.Forall₂
        (Erases E B lps (evalEnvOf view cfg decls) Γ Δ) pre es ∧
      b = mkApps (.case (iid, iv.numParams) dnt brs) es ∧
      (∀ e ∈ es, ErasesDeps E B (evalEnvOf view cfg decls) st₅.gdecls e) ∧
      Grows E B (evalEnvOf view cfg decls) S st₃ st₅ ps₃ ps₅) _
    (fun pre a rest b st₅ ps₅ res st₆ ps₆ hL ⟨es, hF, hb, hD, hg⟩ hrb => by
      have ha : a ∈ as := List.mem_of_mem_drop (by rw [← hL]; simp)
      rw [TravFrame.runPure_bind] at hrb
      obtain ⟨⟨⟨x, st₇⟩, ps₇⟩, hx, hrb⟩ := OracleWhnf.ok_of_bind hrb
      cases hrb
      obtain ⟨hoa, hma, hna, hra, a', hta, A, hA⟩ := hargs a ha
      have ⟨hex, hdx, hgx⟩ := ih.expr (f + 1) (by omega) _
        (hctx.mono (Nat.le_trans (Nat.le_trans hgrd.next hgrC.next) hg.next)) hsc hoa hma hna hra
        hg.inv hta ⟨A, hA⟩ hx
      refine ⟨_, rfl, es ++ [x], CasesWhred.forall₂_snoc hF hex, ?_, ?_, hg.trans hgx⟩
      · rw [hb, ← StepsCases.mkApps_append]; rfl
      · intro e he'
        rcases List.mem_append.1 he' with he' | he'
        · exact ErasesDeps.ext hgx.ext (hD e he')
        · simp only [List.mem_singleton] at he'; subst he'; exact hdx)
    _ [] _ st₃ ps₃ _ _ _ (by simp) ⟨[], .nil, rfl, ⟨fun _ h => by simp at h, Grows.refl hgrC.inv⟩⟩ hext
  dsimp only
  refine ⟨?_, StepsCases.deps_mkApps_of (ErasesDeps.ext hgrE.ext hdepsC) hDe,
    hgrd.trans (hgrC.trans hgrE)⟩
  have hsat' : casesArity iv ≤ as.length := by rw [← har]; exact hsat
  have hlev : ∀ m m'', as[casesMajor iv]? = some m → TrM E B lps Γ Δ m m'' →
      (∃ M, E[Γ] ⊢ m'' : M) →
      ∃ l M, TrLevel lps u = some l ∧ E[Γ] ⊢ m'' : M ∧ E[Γ] ⊢ M : .sort l :=
    fun m m'' hm hmt hmty => Pure.typeLevel_sound hG.prog hG.wf hG.sub hctx.wf hctx.locals
      hctx.nobv hmt hmty (hu m hm)
  have hnr := not_casesReduced (σ := evalEnvOf view cfg decls) (us := us) hG.prog hG.wf hG.sub
    hctx.wf hcs hd hsat' he hT hlev hC3
  have hss := subsingleton_large (σ := evalEnvOf view cfg decls) hG.prog hG.wf hG.sub hG.deps
    hG.idx hctx.wf hci hcs hd hlp hsat' he hT
  have has : as = as.take (casesMajor iv) ++ [as[casesMajor iv]'hmlt] ++ altsL ++
      as.drop ci.arity := by
    rw [← halts', har, casesArity]
    calc as = as.take (casesMajor iv) ++ as.drop (casesMajor iv) := (List.take_append_drop _ _).symm
      _ = as.take (casesMajor iv) ++ (as[casesMajor iv]'hmlt :: as.drop (casesMajor iv + 1)) := by
        rw [← List.drop_eq_getElem_cons hmlt]
      _ = _ := by
        rw [← List.take_append_drop iv.ctors.length (as.drop (casesMajor iv + 1)), List.drop_drop]
        simp
  have hlenA : altsL.length = iv.ctors.length := by
    rw [← halts']; simp; omega
  have key := Erases.cases (σ := evalEnvOf view cfg decls) (us := us) (lps := lps) (Γ := Γ)
    (Δ := Δ) (pre := as.take (casesMajor iv)) (maj := as[casesMajor iv]'hmlt) (alts := altsL)
    (extra := as.drop ci.arity) (brs := brs) (extra' := es) hcs hnr hss hid
    (by simp only [List.length_take]; omega) hlenA herd (by rw [hlenb, hlenA])
    (fun i cn hcn => by
      obtain ⟨cv, hcv, -⟩ := haltsg i cn hcn
      simp [ctorFields, evalEnvOf, show findDecl decls cn = _ from hcv])
    hEb hF.length_eq (fun i a a' ha ha' => by
      obtain ⟨b, hb, hab⟩ := CasesWhred.forall₂_getElem? hF ha
      rw [ha'] at hb; cases hb; exact hab)
  rw [← has] at key
  exact key

end

end StepsCasesCase

/-- The `case` branch of `visitCases` (`StepsCases.CasesCaseSpec`), by `casesSat_case`. Reference:
the `tCase` case of `erases_erase` (`MR E/ErasureFunction.v:1228`). -/
theorem StepsCases.casesCaseSpec : StepsCases.CasesCaseSpec :=
  fun hG ih hci hd hiv hlp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hu hC3 hctx hsc hocc hmf hnp hrf hok he ht
    hsat hrun =>
  StepsCasesCase.casesSat_case hG ih hci hd hiv hlp hu hC3 hctx hsc hocc hmf hnp hrf hok he ht hsat
    hrun

/-- The pure traversal is correct (`erasePure_erases_statement`): `erasePure_erases_of_case` with
the `case` branch of `visitCases` (`StepsCases.casesCaseSpec`). Reference: `erases_erase`
(`MR E/ErasureFunction.v:1228`). -/
theorem erasePure_erases : erasePure_erases_statement :=
  erasePure_erases_of_case StepsCases.casesCaseSpec

end EraseProof
