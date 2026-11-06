import EraseProof.Core.StepsCases
import EraseProof.Core.StepsCtor

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
    ?mdata ?box ?done ?alam ?intro h
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

end StepsCasesCase

end EraseProof
