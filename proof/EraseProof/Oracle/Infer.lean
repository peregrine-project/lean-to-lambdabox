import EraseProof.Oracle.Arity
import EraseProof.Oracle.InferRecr
import EraseProof.Bridge.SatTyped
import EraseProof.Source.ProofSound

/-!
# Soundness of the oracle's type inference

`Pure.inferType_sound`: a successful run of `Erasure.Pure.inferType` on a translated, typed term
returns a type that translates to a type of the term's image. The contexts are those of
`Pure.whnf_sound`: the traversal's locals (`LocalsOK`) under the bound entries of the binders the
oracle entered, whose types the oracle keeps in its list `Γo` (`OracleInfer.OracleCtx`).

The proof is a fuel induction on the translation (port of `L4 Oracle/Infer.lean`): bound and free
variables by the contexts, constants by their declared types (`ConstTyped` through
`TrM.instLevels`), applications by `Pure.whnf_sound` on the function's type with `Defeq.uniqTy`
and `TrM.inst`, binders structurally, `let` by `TrM.inst_let`. A saturating spine `c as a` is
typed through its prefix `c as` (`SatTr.typed`, `SatTr.app_defeq`), except an exactly saturated
recursor spine (`Pure.inferType_recr`).
-/

open Lean Erasure
open Metalean (Defeq TypeEq EnvWF WHRed WHRedS)

namespace EraseProof

namespace OracleInfer

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {lps : List Name}

/-- The oracle's binder types: the `i`-th, lifted over the binders entered after it, translates to
a type of the `i`-th bound entry. Reference: `type_Rel` (`MR pcuic/theories/PCUICTyping.v:199`),
the type `lift0 (S n) (decl_type decl)`; port of `L4 Oracle/Infer.lean` `OracleCtx`. -/
def OracleCtx {n : Nat} (Γ : Metalean.Ctx ζ lps.length 0 n) (Δ : MLCtx ζ lps.length n)
    (Γo : List Expr) : Prop :=
  ∀ i A, Γo[i]? = some A → ∃ t A', Δ.findB i = some t ∧
    TrM E B lps Γ Δ (A.liftLooseBVars' 0 (i + 1)) A' ∧ E[Γ] ⊢ t : A'

/-- Entering a binder of type `A` (translated to `A'`). -/
theorem OracleCtx.cons {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    {Γo : List Expr} {A : Expr} {A' : Metalean.Expr ζ lps.length n}
    (h : OracleCtx (E := E) (B := B) Γ Δ Γo) (hA : TrM E B lps Γ Δ A A') (hA' : E[Γ] ⊢ A' typ)
    (hΓ : E[Γ] ⊢ ok) :
    OracleCtx (E := E) (B := B) (Γ.snoc A') (Δ.pushLam none) (A :: Γo) := by
  have hΓ' : E[Γ.snoc A'] ⊢ ok := .snoc hΓ hA'
  intro i X hX
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hX
    subst hX
    refine ⟨.var (Fin.last n), A'.wk, rfl, TrM.weakBV hA, ?_⟩
    simpa using hΓ'.var (Fin.last n)
  | succ i =>
    simp only [List.getElem?_cons_succ] at hX
    obtain ⟨t, A₀, hf, htr, ht⟩ := h i X hX
    refine ⟨t.wk, A₀.wk, ?_, ?_, ht.wk A'⟩
    · simp [MLCtx.pushLam, MLCtx.findB, MLCtx.findB_map_wk, hf]
    · have := TrM.weakBV (A := A') htr
      rwa [InstPre.liftLooseBVars'_succ] at this

/-- Two translations of a term: the first is typed at every type of the second. -/
theorem trM_retype {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    (hE : EnvWF E) (hΓ : E[Γ] ⊢ ok) {e : Expr} {t₁ t₂ U V : Metalean.Expr ζ lps.length n}
    (h₁ : TrM E B lps Γ Δ e t₁) (h₂ : TrM E B lps Γ Δ e t₂) (ht₁ : E[Γ] ⊢ t₁ : U)
    (ht₂ : E[Γ] ⊢ t₂ : V) : E[Γ] ⊢ t₁ : V := by
  have d := DCong.defeq₂ hE (h₁.dcong h₂ (LocCong.refl Δ)) hΓ hΓ (DCong.CtxConv.refl hΓ)
    ⟨V, ht₂⟩ ht₁
  exact (Defeq.uniqTy hE hΓ d.right ht₂).conv ht₁

/-- A successful `List.mapM` in `Option` keeps the length. -/
theorem mapM_length {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {L : List β}, l.mapM f = some L → L.length = l.length
  | [], L, h => by simp at h; subst h; rfl
  | a :: l, L, h => by
    rw [List.mapM_cons] at h
    cases ha : f a <;> cases hl : l.mapM f <;> simp [ha, hl] at h
    subst h; simp [mapM_length hl]

/-- Translated levels form a translated list. -/
theorem mapM_of_trLevels {us : List Level} {k : Nat} {ls : Fin k → Metalean.Level lps.length}
    (h : TrLevels lps us k = some ls) : ∃ L, us.mapM (TrLevel lps) = some L := by
  unfold TrLevels at h
  cases hm : us.mapM (TrLevel lps) with
  | none => simp [hm] at h
  | some L => exact ⟨L, rfl⟩

/-- The levels of a saturating spine translate. -/
theorem mapM_of_satTr {n : Nat} {b : MBinding ζ} {us : List Level}
    {args : List (Metalean.Expr ζ lps.length n)} {t : Metalean.Expr ζ lps.length n}
    (h : SatTr E lps b us args t) : ∃ L, us.mapM (TrLevel lps) = some L := by
  cases h with
  | indSat _ _ _ hls => exact mapM_of_trLevels hls
  | indEta hls _ => exact mapM_of_trLevels hls
  | ctorSat _ _ _ _ _ hls => exact mapM_of_trLevels hls
  | ctorEta hls _ _ => exact mapM_of_trLevels hls
  | recrSat _ _ _ _ hRL hls =>
    obtain ⟨L, hL⟩ := mapM_of_trLevels hls
    rcases hRL with ⟨-, u, rfl, hu⟩ | ⟨-, rfl, -⟩
    · exact ⟨_, by rw [List.mapM_cons, hu, hL]; rfl⟩
    · exact ⟨L, hL⟩
  | recrEta _ hRL hls =>
    obtain ⟨L, hL⟩ := mapM_of_trLevels hls
    rcases hRL with ⟨-, u, rfl, hu⟩ | ⟨-, rfl, -⟩
    · exact ⟨_, by rw [List.mapM_cons, hu, hL]; rfl⟩
    · exact ⟨L, hL⟩
  | quotType hu => exact ⟨_, hu⟩
  | quotMk hu => exact ⟨_, hu⟩
  | quotLift hu => exact ⟨_, hu⟩
  | quotInd hu => exact ⟨_, hu⟩
  | quotEta hu _ _ => exact ⟨_, hu⟩

/-- The levels of a translated constant translate. -/
theorem levels_of_const {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    {c : Name} {us : List Level} {t : Metalean.Expr ζ lps.length n}
    (h : TrM E B lps Γ Δ (.const c us) t) : ∃ L, us.mapM (TrLevel lps) = some L := by
  generalize he : Expr.const c us = e at h
  cases h with
  | const _ hls => cases he; exact mapM_of_trLevels hls
  | special _ _ hlen _ hsat =>
    obtain ⟨rfl, rfl, rfl⟩ := SrcDefeq.spine_const he.symm
    obtain rfl := List.eq_nil_of_length_eq_zero hlen.symm
    exact mapM_of_satTr hsat
  | _ => cases he

/-- The oracle's type of a constant: its declared type at the constant's levels translates to a
type of the constant's image (`ConstTyped` through `TrM.instLevels`, weakened). Reference:
`type_Const` (`MR pcuic/theories/PCUICTyping.v:215`). -/
theorem const_type {P : List ConstantInfo} {cx : Pure.Ctx} (henv : ProgEnv P ζ E B)
    (hE : EnvWF E) (hsub : SubEnv cx.decls P) {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
    {Δ : MLCtx ζ lps.length n} (hΓ : E[Γ] ⊢ ok) {c : Name} {us : List Level} {ci : ConstantInfo}
    {t U : Metalean.Expr ζ lps.length n}
    (hci : findConst cx.decls c = some ci) (hl : us.length = ci.levelParams.length)
    (he : TrM E B lps Γ Δ (.const c us) t) (ht : E[Γ] ⊢ t : U) :
    ∃ A', TrM E B lps Γ Δ (Pure.instLevels ci.levelParams us ci.type) A' ∧ E[Γ] ⊢ t : A' := by
  have hP := OracleWhnf.findConst_sub hsub hci
  obtain ⟨hm, hn⟩ := findDecl_eq_some hP
  obtain ⟨b, -, T, t₀, hT, ht₀, hty⟩ := henv.lookup hE hP
  have hnd := henv.levelParams_nodup hm
  obtain ⟨L, hL⟩ := levels_of_const he
  have hLl : L.length = ci.levelParams.length := by
    rw [← hl]; exact mapM_length hL
  have hus : TrLevels lps us ci.levelParams.length = some (fun i => L[i.val]'(by omega)) := by
    simp only [TrLevels, hL, Option.bind_eq_bind, Option.bind_some, hLl, ↓reduceDIte]
  have hT' := TrM.instLevels hus hT
  have ht₀' := TrM.instLevels hus ht₀
  rw [Pure.instLevels, SrcProof.params_instLevel hnd hl, hn] at ht₀'
  have hty' := Defeq.instLevel (fun i => L[i.val]'(by omega)) hty
  have hw := Defeq.wkClosed (Γ := Γ) hty'
  obtain ⟨_, hTw⟩ := hw.regular
  have htr₀ := OracleWhnf.trM_closed (Δ := Δ) henv.metaOrderOK hΓ ht₀' ⟨_, hw⟩
  have hTr := OracleWhnf.trM_closed (Δ := Δ) henv.metaOrderOK hΓ hT' ⟨_, hTw⟩
  exact ⟨_, hTr, trM_retype hE hΓ he htr₀ ht hw⟩

/-- A list with one more element at the end, split at a known prefix. -/
private theorem snoc_split {α : Type} {xs ys rest : List α} {a r : α}
    (h : xs ++ [a] = ys ++ rest.concat r) : xs = ys ++ rest := by
  rw [List.concat_eq_append, ← List.append_assoc] at h
  exact (List.append_inj' h rfl).1

/-- The empty-context image of a constructor of positive arity is its η-term. -/
private theorem ctorTerm_of_nil {ι : Metalean.IndSig} {η : Metalean.Head ζ (.inductive ι)}
    {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} {order : List Nat} {us : List Level}
    {ls : Fin ι.nlevels → Metalean.Level lps.length} {t₀ : Metalean.Expr ζ lps.length 0}
    (hls : TrLevels lps us ι.nlevels = some ls)
    (hpos : 0 < ι.nparams + ((ι.ctors s c).nfields + (ι.ctors s c).nrecFields))
    (h : SatTr E lps (.ctor η s c order) us [] t₀) :
    ∃ t₁, Metalean.Frontend.ctorTerm (E.get η).block η s c ls order = .ok t₁ := by
  generalize hnil : ([] : List (Metalean.Expr ζ lps.length 0)) = args at h
  cases h with
  | ctorSat ps fs rest fds recFds hls' hfs =>
    have := congrArg List.length hnil
    simp only [List.length_append, List.length_ofFn, List.length_nil] at this
    omega
  | ctorEta hls' _ h₀ =>
    rw [hls] at hls'; cases hls'
    exact ⟨_, h₀⟩

/-- Every prefix of a saturating spine has an image, except a partial prefix of an exactly
saturated recursor spine (`hr`); a constructor's η-term exists by `hη`. -/
theorem satTr_prefix {n : Nat} {b : MBinding ζ} {us : List Level}
    (hη : ∀ {ι : Metalean.IndSig} (η : Metalean.Head ζ (.inductive ι)) (s : Fin ι.nsorts)
      (k : Fin (ι.nctors s)) (o : List Nat), b = .ctor η s k o →
        ∃ t₀ T₀ : Metalean.Expr ζ lps.length 0, SatTr E lps b us [] t₀ ∧ E[.nil] ⊢ t₀ : T₀)
    {as₁ : List (Metalean.Expr ζ lps.length n)} {a : Metalean.Expr ζ lps.length n}
    (hr : ∀ {ι : Metalean.IndSig} (η : Metalean.Head ζ (.inductive ι)) (s : Fin ι.nsorts)
      (os : List (List (List Nat))), b = .recr η s os → as₁.length < ι.recrEnd s →
        as₁.length + 1 < ι.recrEnd s)
    {t : Metalean.Expr ζ lps.length n} (h : SatTr E lps b us (as₁ ++ [a]) t) :
    ∃ t₁, SatTr E lps b us as₁ t₁ := by
  generalize hA : as₁ ++ [a] = A at h
  have hlenA := congrArg List.length hA
  simp only [List.length_append, List.length_singleton] at hlenA
  cases h with
  | indSat ps is rest hls =>
    rcases List.eq_nil_or_concat rest with rfl | ⟨rest₀, r, rfl⟩
    · simp only [List.length_append, List.length_ofFn, List.length_nil] at hlenA
      exact ⟨_, .indEta hls (by omega)⟩
    · obtain rfl := snoc_split hA
      exact ⟨_, .indSat ps is rest₀ hls⟩
  | indEta hls hlt => exact ⟨_, .indEta hls (by omega)⟩
  | ctorSat ps fs rest fds recFds hls hfs hlo hrel =>
    rcases List.eq_nil_or_concat rest with rfl | ⟨rest₀, r, rfl⟩
    · simp only [List.length_append, List.length_ofFn, List.length_nil] at hlenA
      obtain ⟨t₀, -, hS, -⟩ := hη _ _ _ _ rfl
      obtain ⟨t₁, h₀⟩ := ctorTerm_of_nil hls (by omega) hS
      exact ⟨_, .ctorEta hls (by omega) h₀⟩
    · obtain rfl := snoc_split hA
      exact ⟨_, .ctorSat ps fs rest₀ fds recFds hls hfs hlo hrel⟩
  | ctorEta hls hlt h₀ => exact ⟨_, .ctorEta hls (by omega) h₀⟩
  | recrSat mo Af rest mins hRL hls hmo hw =>
    rcases List.eq_nil_or_concat rest with rfl | ⟨rest₀, r, rfl⟩
    · simp only [List.length_append, List.length_ofFn, List.length_nil] at hlenA
      have := hr _ _ _ rfl (by omega)
      omega
    · obtain rfl := snoc_split hA
      exact ⟨_, .recrSat mo Af rest₀ mins hRL hls hmo hw⟩
  | recrEta mo hRL hls hmo hlt h₀ => exact ⟨_, .recrEta mo hRL hls hmo (by omega) h₀⟩
  | @quotType _ α r rest η u hu =>
    rcases List.eq_nil_or_concat rest with rfl | ⟨rest₀, x, rfl⟩
    · exact ⟨_, .quotEta hu (by simp [quotArity] at hlenA ⊢; omega) rfl⟩
    · obtain rfl := snoc_split hA
      exact ⟨_, .quotType hu⟩
  | @quotMk _ α r a' rest η u hu =>
    rcases List.eq_nil_or_concat rest with rfl | ⟨rest₀, x, rfl⟩
    · exact ⟨_, .quotEta hu (by simp [quotArity] at hlenA ⊢; omega) rfl⟩
    · obtain rfl := snoc_split hA
      exact ⟨_, .quotMk hu⟩
  | @quotLift _ α r β f h' a' rest η u v hu =>
    rcases List.eq_nil_or_concat rest with rfl | ⟨rest₀, x, rfl⟩
    · exact ⟨_, .quotEta hu (by simp [quotArity] at hlenA ⊢; omega) rfl⟩
    · obtain rfl := snoc_split hA
      exact ⟨_, .quotLift hu⟩
  | @quotInd _ α r β f a' rest η u hu =>
    rcases List.eq_nil_or_concat rest with rfl | ⟨rest₀, x, rfl⟩
    · exact ⟨_, .quotEta hu (by simp [quotArity] at hlenA ⊢; omega) rfl⟩
    · obtain rfl := snoc_split hA
      exact ⟨_, .quotInd hu⟩
  | quotEta hu hlt h₀ => exact ⟨_, .quotEta hu (by omega) h₀⟩

/-- A successful inference on a constant spine finds the head's declaration, at its levels. -/
theorem infer_head {cx : Pure.Ctx} {ls : List Local} {c : Name} {us : List Level} :
    ∀ (f : Nat) {Γo : List Expr} {as : List Expr} {A : Expr},
      Pure.inferType cx f ls Γo (mkAppN (.const c us) as.toArray) = .ok A →
      ∃ ci, findConst cx.decls c = some ci ∧ us.length = ci.levelParams.length
  | 0, _, _, _, h => by simp [Pure.inferType, throw, throwThe, MonadExceptOf.throw] at h
  | f + 1, Γo, as, A, h => by
    rcases List.eq_nil_or_concat as with rfl | ⟨as₀, a, rfl⟩
    · change Pure.inferType cx (f + 1) ls Γo (.const c us) = .ok A at h
      simp only [Pure.inferType] at h
      split at h
      · rename_i ci hci
        split at h
        · rename_i hl
          exact ⟨ci, hci, by simpa using hl⟩
        · simp [throw, throwThe, MonadExceptOf.throw] at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
    · rw [List.concat_eq_append, SrcDefeq.mkAppN_snoc] at h
      simp only [Pure.inferType] at h
      obtain ⟨Tg, h1, -⟩ := OracleWhnf.ok_of_bind h
      exact infer_head f h1

/-- The η-term of a saturating constant at levels `us` is typed in the empty context
(`ConstTyped` through `TrM.instLevels`). -/
theorem eta_typed {P : List ConstantInfo} {cx : Pure.Ctx} (henv : ProgEnv P ζ E B)
    (hE : EnvWF E) (hsub : SubEnv cx.decls P) {c : Name} {us : List Level} {ci : ConstantInfo}
    {b : MBinding ζ} (hB : B c = some b) (hs : b.isSpecial = true)
    (hci : findConst cx.decls c = some ci) (hl : us.length = ci.levelParams.length)
    {L : List (Metalean.Level lps.length)} (hL : us.mapM (TrLevel lps) = some L) :
    ∃ t₀ T₀ : Metalean.Expr ζ lps.length 0, SatTr E lps b us [] t₀ ∧ E[.nil] ⊢ t₀ : T₀ := by
  have hP := OracleWhnf.findConst_sub hsub hci
  obtain ⟨hm, hn⟩ := findDecl_eq_some hP
  obtain ⟨-, -, T, t₀, -, ht₀, hty⟩ := henv.lookup hE hP
  have hnd := henv.levelParams_nodup hm
  have hLl : L.length = ci.levelParams.length := by rw [← hl]; exact mapM_length hL
  have hus : TrLevels lps us ci.levelParams.length = some (fun i => L[i.val]'(by omega)) := by
    simp only [TrLevels, hL, Option.bind_eq_bind, Option.bind_some, hLl, ↓reduceDIte]
  have ht₀' := TrM.instLevels hus ht₀
  rw [Pure.instLevels, SrcProof.params_instLevel hnd hl, hn] at ht₀'
  obtain ⟨bs', hlen, -, hsat⟩ := TrM.special_inv (bs := []) hB hs ht₀'
  obtain rfl := List.eq_nil_of_length_eq_zero hlen.symm
  exact ⟨_, _, hsat, Defeq.instLevel (fun i => L[i.val]'(by omega)) hty⟩

/-- The `app` step of the oracle: when the function's image is typed at a type that the oracle's
type of the function translates to, and that type reduces to a `Π`, the instantiated codomain
translates to a type of the application. -/
theorem app_step {P : List ConstantInfo} {cx : Pure.Ctx} (henv : ProgEnv P ζ E B)
    (hE : EnvWF E) (hsub : SubEnv cx.decls P) {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
    {Δ : MLCtx ζ lps.length n} {ls : List Local} (hΓ : E[Γ] ⊢ ok)
    (hloc : LocalsOK E B lps Γ Δ ls) {f : Nat} {Tg W a : Expr}
    {tg a' Tg' U : Metalean.Expr ζ lps.length n}
    (htg : E[Γ] ⊢ tg : Tg') (hTg : TrM E B lps Γ Δ Tg Tg') (hw : Pure.whnf cx f ls Tg = .ok W)
    (ha : TrM E B lps Γ Δ a a') (happ : E[Γ] ⊢ .app tg a' : U) {x : Name} {Ad Bc : Expr}
    {bi : BinderInfo} (hW : W = .forallE x Ad Bc bi) :
    ∃ A', TrM E B lps Γ Δ (Bc.instantiate1' a) A' ∧ E[Γ] ⊢ .app tg a' : A' := by
  obtain ⟨_, hTgs⟩ := htg.regular
  obtain ⟨W', hW', dW⟩ := Pure.whnf_sound henv hE hsub hΓ hloc hTg hTgs hw
  subst hW
  generalize hx : Expr.forallE x Ad Bc bi = X at hW'
  cases hW' with
  | forallE hA hB =>
    cases hx
    rename_i A' B'
    have htg' := (TypeEq.ofDefEq dW).conv htg
    obtain ⟨A0, B0, hf0, ha0, -⟩ := happ.app_inv
    have hTy := Defeq.uniqTy hE hΓ hf0 htg'
    have ha'' := (TypeEq.forallE_inj hE hΓ hTy).1.conv ha0
    obtain ⟨_, hfa⟩ := htg'.regular
    obtain ⟨_, _, hA', hB', -⟩ := hfa.forallE_ty_inv
    obtain ⟨X', hX, dX⟩ := TrM.inst hE hΓ henv.metaOrderOK hB ha ha'' hB'
    have happ' := Defeq.appDF hA' hB' htg' ha'' (hB'.inst_congr ha'')
    exact ⟨X', hX, (TypeEq.ofDefEq dX.symm).conv happ'⟩
  | special => exact absurd hx (ne_mkAppN_const fun _ _ h => by cases h)
  | _ => cases hx

/-- The conclusion of `Pure.inferType_sound` at fuel `f`, in every oracle context over the
locals `ls`. -/
def InferOK (E : Metalean.Env ζ) (B : Binds ζ) (lps : List Name) (cx : Pure.Ctx)
    (ls : List Local) (f : Nat) : Prop :=
  ∀ {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n} {Γo : List Expr}
    {e A : Expr} {t U : Metalean.Expr ζ lps.length n},
    E[Γ] ⊢ ok → LocalsOK E B lps Γ Δ ls → OracleCtx (E := E) (B := B) Γ Δ Γo →
    TrM E B lps Γ Δ e t → E[Γ] ⊢ t : U → Pure.inferType cx f ls Γo e = .ok A →
    ∃ A', TrM E B lps Γ Δ A A' ∧ E[Γ] ⊢ t : A'

/-- The oracle on a constant. -/
theorem infer_const {P : List ConstantInfo} {cx : Pure.Ctx} (henv : ProgEnv P ζ E B)
    (hE : EnvWF E) (hsub : SubEnv cx.decls P) {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
    {Δ : MLCtx ζ lps.length n} {ls : List Local} {Γo : List Expr} (hΓ : E[Γ] ⊢ ok) {f : Nat}
    {c : Name} {us : List Level} {A : Expr} {t U : Metalean.Expr ζ lps.length n}
    (he : TrM E B lps Γ Δ (.const c us) t) (ht : E[Γ] ⊢ t : U)
    (h : Pure.inferType cx (f + 1) ls Γo (.const c us) = .ok A) :
    ∃ A', TrM E B lps Γ Δ A A' ∧ E[Γ] ⊢ t : A' := by
  simp only [Pure.inferType] at h
  split at h
  · rename_i ci hci
    split at h
    · rename_i hl
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact const_type henv hE hsub hΓ hci (by simpa using hl) he ht
    · simp [throw, throwThe, MonadExceptOf.throw] at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- The oracle on a saturating spine `c as a`: an exactly saturated recursor spine by
`Pure.inferType_recr`; otherwise through the prefix `c as` (`satTr_prefix`, `SatTr.typed`), the
induction hypothesis, `app_step` and `SatTr.app_defeq`. -/
theorem infer_special {P : List ConstantInfo} {cx : Pure.Ctx} (henv : ProgEnv P ζ E B)
    (hE : EnvWF E) (hsub : SubEnv cx.decls P) {ls : List Local} {f : Nat}
    (ih : InferOK E B lps cx ls f) {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
    {Δ : MLCtx ζ lps.length n} {Γo : List Expr} (hΓ : E[Γ] ⊢ ok)
    (hloc : LocalsOK E B lps Γ Δ ls) (hΓo : OracleCtx (E := E) (B := B) Γ Δ Γo) {c : Name}
    {us : List Level} {as : List Expr} {as' : List (Metalean.Expr ζ lps.length n)}
    {b : MBinding ζ} {A : Expr} {t U : Metalean.Expr ζ lps.length n}
    (hB : B c = some b) (hs : b.isSpecial = true) (hlen : as.length = as'.length)
    (hargs : ∀ (i : Nat) a a', as[i]? = some a → as'[i]? = some a' → TrM E B lps Γ Δ a a')
    (hsat : SatTr E lps b us as' t) (ht : E[Γ] ⊢ t : U)
    (h : Pure.inferType cx (f + 1) ls Γo (mkAppN (.const c us) as.toArray) = .ok A) :
    ∃ A', TrM E B lps Γ Δ A A' ∧ E[Γ] ⊢ t : A' := by
  have he : TrM E B lps Γ Δ (mkAppN (.const c us) as.toArray) t := .special hB hs hlen hargs hsat
  rcases List.eq_nil_or_concat as with rfl | ⟨as₀, a, rfl⟩
  · exact infer_const henv hE hsub hΓ he ht h
  rcases List.eq_nil_or_concat as' with rfl | ⟨as₀', a', rfl⟩
  · simp at hlen
  simp only [List.concat_eq_append] at hlen hsat he h hargs
  have hl0 : as₀.length = as₀'.length := by simpa using hlen
  by_cases hrx : ∃ (ι : Metalean.IndSig) (η : Metalean.Head ζ (.inductive ι)) (s : Fin ι.nsorts)
      (os : List (List (List Nat))), b = .recr η s os ∧ (as₀ ++ [a]).length = ι.recrEnd s
  · obtain ⟨ι, η, s, os, rfl, hl⟩ := hrx
    exact Pure.inferType_recr henv hE hsub hΓ hB hl he ht h
  have hr : ∀ {ι : Metalean.IndSig} (η : Metalean.Head ζ (.inductive ι)) (s : Fin ι.nsorts)
      (os : List (List (List Nat))), b = .recr η s os → as₀'.length < ι.recrEnd s →
        as₀'.length + 1 < ι.recrEnd s := by
    intro ι η s os hb hlt
    have : (as₀ ++ [a]).length ≠ ι.recrEnd s := fun hh => hrx ⟨ι, η, s, os, hb, hh⟩
    simp only [List.length_append, List.length_singleton] at this
    omega
  obtain ⟨ci, hci, hlc⟩ := infer_head (f + 1) h
  obtain ⟨L, hL⟩ := mapM_of_satTr hsat
  have hη : ∀ {ι : Metalean.IndSig} (η : Metalean.Head ζ (.inductive ι)) (s : Fin ι.nsorts)
      (k : Fin (ι.nctors s)) (o : List Nat), b = .ctor η s k o →
        ∃ t₀ T₀ : Metalean.Expr ζ lps.length 0, SatTr E lps b us [] t₀ ∧ E[.nil] ⊢ t₀ : T₀ :=
    fun _ _ _ _ _ => eta_typed henv hE hsub hB hs hci hlc hL
  obtain ⟨tg, hsg⟩ := satTr_prefix hη hr hsat
  obtain ⟨Tg₀, htg⟩ := SatTr.typed hE hΓ hη
    (fun η s os hb hlt => by simpa using hr η s os hb hlt) hsg hsat ht
  have hargs0 : ∀ (i : Nat) x x', as₀[i]? = some x → as₀'[i]? = some x' →
      TrM E B lps Γ Δ x x' := fun i x x' h1 h2 =>
    hargs i x x' (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h1).1]; exact h1)
      (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h2).1]; exact h2)
  have hg : TrM E B lps Γ Δ (mkAppN (.const c us) as₀.toArray) tg := .special hB hs hl0 hargs0 hsg
  have ha : TrM E B lps Γ Δ a a' := hargs as₀.length a a' (by simp) (by simp [hl0])
  rw [SrcDefeq.mkAppN_snoc] at h
  simp only [Pure.inferType] at h
  obtain ⟨Tg, h1, h⟩ := OracleWhnf.ok_of_bind h
  obtain ⟨W, h2, h⟩ := OracleWhnf.ok_of_bind h
  obtain ⟨Tg', hTg, htg'⟩ := ih hΓ hloc hΓo hg htg h1
  obtain ⟨U', hd⟩ := SatTr.app_defeq hE hΓ hη hr hsg hsat ht
  split at h
  · cases h
    obtain ⟨A', hA', happ⟩ := app_step henv hE hsub hΓ hloc htg' hTg h2 ha hd.left rfl
    exact ⟨A', hA', (Defeq.retype hE hΓ hd happ).right⟩
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- `TrM` of a sort is a translated sort. -/
private theorem trM_sort_inv {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
    {Δ : MLCtx ζ lps.length n} {u : Level} {w : Metalean.Expr ζ lps.length n}
    (h : TrM E B lps Γ Δ (.sort u) w) : ∃ l, TrLevel lps u = some l ∧ w = .sort l := by
  generalize hx : Expr.sort u = X at h
  cases h with
  | sort hl => cases hx; exact ⟨_, hl, rfl⟩
  | special => exact absurd hx (ne_mkAppN_const fun _ _ h => by cases h)
  | _ => cases hx

/-- The oracle's sort of a type: when its inferred type reduces to `Sort u`, the image is typed at
the translated sort. -/
theorem sort_step {P : List ConstantInfo} {cx : Pure.Ctx} (henv : ProgEnv P ζ E B)
    (hE : EnvWF E) (hsub : SubEnv cx.decls P) {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
    {Δ : MLCtx ζ lps.length n} {ls : List Local} (hΓ : E[Γ] ⊢ ok)
    (hloc : LocalsOK E B lps Γ Δ ls) {f : Nat} {S : Expr} {u : Level}
    {t S' : Metalean.Expr ζ lps.length n} (ht : E[Γ] ⊢ t : S') (hS : TrM E B lps Γ Δ S S')
    (hw : Pure.whnf cx f ls S = .ok (.sort u)) :
    ∃ l, TrLevel lps u = some l ∧ E[Γ] ⊢ t : .sort l := by
  obtain ⟨_, hSs⟩ := ht.regular
  obtain ⟨W', hW', dW⟩ := Pure.whnf_sound henv hE hsub hΓ hloc hS hSs hw
  obtain ⟨l, hl, rfl⟩ := trM_sort_inv hW'
  exact ⟨l, hl, (TypeEq.ofDefEq dW).conv ht⟩

/-- The unary Nat literal is typed at `Nat` (`ctorDF` along the chain). -/
theorem natLitM_typed {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
    (ηNat : Metalean.Head ζ (.inductive natSig)) :
    ∀ k, E[Γ] ⊢ natLitM ηNat k : .ind ηNat 0 ![] ![] ![] := by
  have hind : E[Γ] ⊢ (.ind ηNat 0 ![] ![] ![] : Metalean.Expr ζ lps.length n) :
      .sort ((E.get ηNat).block.level{![]}) :=
    .indDF (fun p => p.elim0) (fun i => i.elim0)
  intro k
  induction k with
  | zero =>
    have h := Defeq.ctorDF (η := ηNat) (s := 0) (c := 0) (ls := ![]) (ps₁ := ![]) (ps₂ := ![])
      (fds₁ := ![]) (fds₂ := ![]) (recFds₁ := ![]) (recFds₂ := ![])
      (fieldLevels := fun f => f.elim0) (recFieldLevels := fun f => f.elim0) (Γ := Γ)
      (fun p => p.elim0) (fun f => f.elim0) (fun f => f.elim0) (fun f => f.elim0)
      (fun f => f.elim0) (by convert hind using 2)
    convert h using 2 <;> rfl
  | succ k ih =>
    have hr : ((E.get ηNat).block.ctors 0 1).recursiveFieldExpr ηNat ![] ![] ![] 0 =
        (.ind ηNat 0 ![] ![] ![] : Metalean.Expr ζ lps.length n) := by
      simp only [Metalean.Ctor.recursiveFieldExpr, Metalean.RecField.instantiatedType,
        Metalean.RecField.instantiatedTelescope]
      change Metalean.Expr.ind ηNat 0 ![] _ _ = _
      congr 1
      funext i
      exact i.elim0
    have h := Defeq.ctorDF (η := ηNat) (s := 0) (c := 1) (ls := ![]) (ps₁ := ![]) (ps₂ := ![])
      (fds₁ := ![]) (fds₂ := ![]) (recFds₁ := ![natLitM ηNat k]) (recFds₂ := ![natLitM ηNat k])
      (fieldLevels := fun f => f.elim0)
      (recFieldLevels := fun _ => (E.get ηNat).block.level{![]}) (Γ := Γ)
      (fun p => p.elim0) (fun f => f.elim0)
      (fun f => by
        obtain rfl : f = 0 := Subsingleton.elim _ _
        have := hr; simp only [Metalean.Ctor.recursiveFieldExpr] at this
        rw [this]; exact ih)
      (fun f => f.elim0)
      (fun f => by obtain rfl : f = 0 := Subsingleton.elim _ _; rw [hr]; exact hind)
      (by convert hind using 2)
    convert h using 2 <;> rfl

/-- The oracle's type of a Nat literal, `Nat`, translates to a type of the literal's image. -/
theorem lit_type {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    {ηNat : Metalean.Head ζ (.inductive natSig)} (hB : B ``Nat = some (.ind ηNat 0)) (k : Nat) :
    ∃ A', TrM E B lps Γ Δ (.const ``Nat []) A' ∧ E[Γ] ⊢ natLitM ηNat k : A' := by
  obtain ⟨ls, hls⟩ : ∃ ls, TrLevels lps [] natSig.nlevels = some ls := ⟨_, rfl⟩
  obtain rfl : ls = ![] := funext fun i => i.elim0
  have hsat : SatTr E lps (.ind ηNat 0) []
      (List.ofFn (![] : Fin 0 → Metalean.Expr ζ lps.length n) ++
        List.ofFn (![] : Fin 0 → Metalean.Expr ζ lps.length n) ++ [])
      ((Metalean.Expr.ind ηNat 0 ![] ![] ![]).appList []) :=
    .indSat ![] ![] [] hls
  exact ⟨_, .special (as := []) hB rfl (by simp) (fun i a a' h => by simp at h) hsat,
    natLitM_typed ηNat k⟩

/-- `Pure.inferType_sound` in every oracle context, given the projection cases (`hproj`). Fuel
induction on the translation (port of `L4 Oracle/Infer.lean:96`). -/
theorem inferOK {P : List ConstantInfo} {cx : Pure.Ctx} (henv : ProgEnv P ζ E B)
    (hE : EnvWF E) (hsub : SubEnv cx.decls P) {ls : List Local}
    (hcl : ∀ l ∈ ls, l.type.liftLooseBVars' 0 1 = l.type ∧
      ∀ v, l.value? = some v → v.liftLooseBVars' 0 1 = v)
    (hproj : ∀ f, InferOK E B lps cx ls f → ∀ {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
      {Δ : MLCtx ζ lps.length n} {Γo : List Expr} {S : Name} {i : Nat} {e A : Expr}
      {t U : Metalean.Expr ζ lps.length n},
      E[Γ] ⊢ ok → LocalsOK E B lps Γ Δ ls → OracleCtx (E := E) (B := B) Γ Δ Γo →
      TrM E B lps Γ Δ (.proj S i e) t → E[Γ] ⊢ t : U →
      Pure.inferType cx (f + 1) ls Γo (.proj S i e) = .ok A →
      ∃ A', TrM E B lps Γ Δ A A' ∧ E[Γ] ⊢ t : A') :
    ∀ f, InferOK E B lps cx ls f
  | 0 => by
    intro _ _ _ _ _ h
    simp [Pure.inferType, throw, throwThe, MonadExceptOf.throw] at h
  | f + 1 => by
    have ih : InferOK E B lps cx ls f := inferOK henv hE hsub hcl hproj f
    rename_i n Γ Δ Γo e A t U
    intro hΓ hloc hΓo he ht h
    cases he with
    | bvar hb =>
      simp only [Pure.inferType] at h
      split at h
      · rename_i X hX
        cases h
        obtain ⟨t', A', hf, htr, ht'⟩ := hΓo _ X hX
        rw [hb] at hf; cases hf
        exact ⟨A', htr, ht'⟩
      · simp [throw, throwThe, MonadExceptOf.throw] at h
    | fvar hf =>
      simp only [Pure.inferType] at h
      split at h
      · rename_i l hl
        cases h
        have hmem := List.mem_of_find?_eq_some hl
        unfold Pure.findLocal at hl
        have hx := (fvarId_beq_iff _ _).mp (by simpa using List.find?_some hl)
        obtain ⟨A', t', hA, hF, ht', -⟩ := hloc l hmem
        rw [hx, hf] at hF; cases hF
        exact ⟨A', hA, ht'⟩
      · simp [throw, throwThe, MonadExceptOf.throw] at h
    | sort hl =>
      simp only [Pure.inferType, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨_, .sort (by simp [TrLevel, hl]), .sortDF⟩
    | const hB hls => exact infer_const henv hE hsub hΓ (.const hB hls) ht h
    | special hB hs hlen hargs hsat =>
      exact infer_special henv hE hsub ih hΓ hloc hΓo hB hs hlen hargs hsat ht h
    | app _ hg ha =>
      simp only [Pure.inferType] at h
      obtain ⟨Tg, h1, h⟩ := OracleWhnf.ok_of_bind h
      obtain ⟨W, h2, h⟩ := OracleWhnf.ok_of_bind h
      obtain ⟨A0, B0, hf0, -, -⟩ := ht.app_inv
      obtain ⟨Tg', hTg, htg'⟩ := ih hΓ hloc hΓo hg hf0 h1
      split at h
      · cases h
        exact app_step henv hE hsub hΓ hloc htg' hTg h2 ha ht rfl
      · simp [throw, throwThe, MonadExceptOf.throw] at h
    | @lam _ _ _ A₀ A' b₀ b' x bi hA hb =>
      simp only [Pure.inferType] at h
      obtain ⟨Bt, h1, h⟩ := OracleWhnf.ok_of_bind h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      obtain ⟨Bty, hb'', hT⟩ := ht.lam_inv hΓ
      obtain ⟨_, hfa⟩ := hT.right
      obtain ⟨_, _, hA', -, -⟩ := hfa.forallE_ty_inv
      have hΓ' : E[Γ.snoc A'] ⊢ ok := .snoc hΓ ⟨_, hA'⟩
      have hloc' := OracleArity.LocalsOK.weakBV A' hloc hcl
      have hΓo' := OracleCtx.cons hΓo hA ⟨_, hA'⟩ hΓ
      obtain ⟨Bt', hBt, hbB⟩ := ih hΓ' hloc' hΓo' hb hb'' h1
      obtain ⟨_, hBs⟩ := hbB.regular
      exact ⟨_, .forallE hA hBt, .lamDF hA' hBs hBs hbB hbB⟩
    | @forallE _ _ _ A₀ A' b₀ b' x bi hA hb =>
      simp only [Pure.inferType] at h
      obtain ⟨St, h1, h⟩ := OracleWhnf.ok_of_bind h
      obtain ⟨w1, h2, h⟩ := OracleWhnf.ok_of_bind h
      split at h
      · rename_i u
        obtain ⟨Sb, h3, h⟩ := OracleWhnf.ok_of_bind h
        obtain ⟨w2, h4, h⟩ := OracleWhnf.ok_of_bind h
        split at h
        · rename_i v
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          obtain ⟨l₁, l₂, hA', hb'', -⟩ := ht.forallE_ty_inv
          have hΓ' : E[Γ.snoc A'] ⊢ ok := .snoc hΓ ⟨_, hA'⟩
          have hloc' := OracleArity.LocalsOK.weakBV A' hloc hcl
          have hΓo' := OracleCtx.cons hΓo hA ⟨_, hA'⟩ hΓ
          obtain ⟨St', hSt, hAS⟩ := ih hΓ hloc hΓo hA hA' h1
          obtain ⟨u', hu', hAu⟩ := sort_step henv hE hsub hΓ hloc hAS hSt h2
          obtain ⟨Sb', hSb, hbS⟩ := ih hΓ' hloc' hΓo' hb hb'' h3
          obtain ⟨v', hv', hbv⟩ := sort_step henv hE hsub hΓ' hloc' hbS hSb h4
          exact ⟨_, .sort (by simp [TrLevel, hu', hv']), .forallEDF hAu hbv hbv⟩
        · simp [throw, throwThe, MonadExceptOf.throw] at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
    | letE _ hv hb =>
      simp only [Pure.inferType] at h
      have d1 := WHRed.defeq hE .zeta hΓ ht
      rw [Metalean.Expr.inst_wk] at d1
      obtain ⟨t₁, htr, hd₁⟩ := TrM.inst_let hE hΓ henv.metaOrderOK hb hv d1.right
      obtain ⟨A', hA', ht₁⟩ := ih hΓ hloc hΓo htr hd₁.left h
      exact ⟨A', hA', (Defeq.retype hE hΓ (hd₁.trans d1.symm) ht₁).right⟩
    | mdata he' =>
      simp only [Pure.inferType] at h
      exact ih hΓ hloc hΓo he' ht h
    | lit hB =>
      simp only [Pure.inferType, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact lit_type hB _
    | projStruct hst hi hBS hs hty =>
      exact hproj f ih hΓ hloc hΓo (.projStruct hst hi hBS hs hty) ht h
    | projProof hi0 hBS hss hcc hnr hi hns hs hty =>
      exact hproj f ih hΓ hloc hΓo (.projProof hi0 hBS hss hcc hnr hi hns hs hty) ht h


end

end OracleInfer

end EraseProof
