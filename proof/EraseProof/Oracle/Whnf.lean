import EraseProof.Bridge.Inst
import EraseProof.Bridge.Wf
import EraseProof.Bridge.Order
import EraseProof.Bridge.Unfold
import EraseProof.Bridge.Cases
import EraseProof.Metatheory.NoConf
import EraseProof.Bridge.RecWhred

/-!
# Soundness of the oracle's weak-head reduction

`Pure.whnf_sound`: a successful run of `Erasure.Pure.whnf` on a translated, well-typed term returns
a term that translates to a term definitionally equal to the input's image in Metalean. The
traversal's locals are the Lean form of the Metalean context (`LocalsOK`). β goes through
`TrM.inst`, ζ through `TrM.inst_let` and the let-bound locals, δ through `ProgEnv.lookup_def` and
`TrM.instLevels`, and the ι-rule of projections through Metalean's projection ι
(`IsStructure.projTerm_ctor_defeq`, `ML Metatheory/SubjectReduction.lean:208`) and recursor ι
(`WHRed.iota`, `ML Syntax/Reduction.lean`); a projection whose major reduces to a constructor of
another inductive, to a partial constructor or to an over-applied one is ill-typed (no-confusion
of inductive heads, `IndHead`, from Metalean's domain model, `ML Semantics/Inversion.lean:42`).
-/

open Lean Erasure
open Metalean (Defeq TypeEq EnvWF WHRed WHRedS)

namespace EraseProof

/-- The traversal's locals are the Lean form of the Metalean context: each local's free variable
denotes a term of the local's translated type; a `let` local's value translates to it.
Reference: none (DV-13). -/
def LocalsOK {ζ : Metalean.Sigs} (E : Metalean.Env ζ) (B : Binds ζ) (lps : List Name) {n : Nat}
    (Γ : Metalean.Ctx ζ lps.length 0 n) (Δ : MLCtx ζ lps.length n) (ls : List Local) : Prop :=
  ∀ l ∈ ls, ∃ A t, TrM E B lps Γ Δ l.type A ∧ Δ.findF l.fvarId = some t ∧ E[Γ] ⊢ t : A ∧
    ∀ v, l.value? = some v → TrM E B lps Γ Δ v t

namespace OracleWhnf

section Model
open Metalean CategoryTheory CoherentShape CodeAssignment Presheaf

variable {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {Δ : Ctx ζ ℓ 0 n}

/-- Two inductive types equal as types have the same head (inductive block and sort): their
interpretations in Metalean's domain model carry the same inductive code
(`ML Semantics/Domain/Constructors.lean:158` `code_eq_of_ind_eq`). Reference:
`invert_cumul_ind_ind` (`MR pcuic/theories/PCUICConversion.v:1714`). -/
theorem ind_head {ι₁ ι₂ : IndSig} {η₁ : Head ζ (.inductive ι₁)} {η₂ : Head ζ (.inductive ι₂)}
    {s₁ : Fin ι₁.nsorts} {s₂ : Fin ι₂.nsorts} {ls₁ : Fin ι₁.nlevels → Level ℓ}
    {ls₂ : Fin ι₂.nlevels → Level ℓ} {ps₁ : Fin ι₁.nparams → Expr ζ ℓ n}
    {ps₂ : Fin ι₂.nparams → Expr ζ ℓ n} {is₁ : Fin (ι₁.nindices s₁) → Expr ζ ℓ n}
    {is₂ : Fin (ι₂.nindices s₂) → Expr ζ ℓ n} (hE : EnvWF E) (hΔ : E[Δ] ⊢ ok)
    (h : E[Δ] ⊢ .ind η₁ s₁ ls₁ ps₁ is₁ ≡ .ind η₂ s₂ ls₂ ps₂ is₂ typ) :
    (⟨η₁, s₁⟩ : IndHead ζ) = ⟨η₂, s₂⟩ := by
  have ⟨_, hl⟩ := h.left
  have ⟨_, hr⟩ := h.right
  have heq := h.rawInterpret_eq hΔ hE
  rw [rawInterpret_ind_typed _ (IndTyping.ofTyping (Γ₁ := ⟨Δ, hΔ⟩) (hE.entryWF η₁).block hl)
      (hE.entryWF η₁).block,
    rawInterpret_ind_typed _ (IndTyping.ofTyping (Γ₁ := ⟨Δ, hΔ⟩) (hE.entryWF η₂).block hr)
      (hE.entryWF η₂).block,
    RawFamily.ind_value, RawFamily.ind_value] at heq
  have hcode := congrArg IndCode.toIndHead (RawValue.code_eq_of_ind_eq heq)
  simpa [IndTyping.code] using hcode

end Model

variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {lps : List Name}
  {P : List ConstantInfo}

/-- A successful bind is a successful first step followed by a successful continuation. -/
theorem ok_of_bind {α β ε : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  rcases x with e | a
  · cases h
  · exact ⟨a, rfl, h⟩

/-- The spine of an application. -/
theorem spine_app (g a : Expr) : spine (.app g a) = ((spine g).1, (spine g).2 ++ [a]) := by
  simp only [spine]

/-- The head of `spine` is the head of the application. -/
theorem spine_head : ∀ e : Expr, (spine e).1 = e.getAppFn
  | .app f _ => by rw [spine_app]; exact spine_head f
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const .. | .lam .. | .forallE .. | .letE .. | .lit _
  | .mdata .. | .proj .. => rfl

/-- The spine of a head applied to arguments. -/
theorem spine_foldl : ∀ (as : List Expr) (x : Expr),
    spine (as.foldl .app x) = ((spine x).1, (spine x).2 ++ as)
  | [], x => by simp
  | a :: as, x => by
    rw [List.foldl_cons, spine_foldl as (.app x a), spine_app]
    simp

/-- The spine of a constant applied to arguments. -/
theorem spine_const (c : Name) (us : List Level) (as : List Expr) :
    spine (mkAppN (.const c us) as.toArray) = (.const c us, as) := by
  rw [mkAppN_eq_foldl, spine_foldl]
  simp [spine]

/-- What `Erasure.Pure.iotaMinors?` checks of a recursor. -/
theorem iotaMinors?_spec {decls : List ConstantInfo} {rv : RecursorVal} {minors : List RecMinor}
    (h : Pure.iotaMinors? decls rv = some minors) :
    ∃ T iv cvs motives, rv.all = [T] ∧ findConst decls T = some (.inductInfo iv) ∧
      (iv.ctors.mapM fun c => match findConst decls c with
        | some (.ctorInfo cv) => some cv | _ => none) = some cvs ∧
      rv.name = mkRecName T ∧ rv.numIndices = 0 ∧
      recShape rv.numParams rv.numMotives rv.type (cvs.map (·.numFields)) = some (motives, minors) ∧
      ∀ mi ∈ minors, mi.ihs.map (fun h => (h.field, h.binders)) =
        (List.range' (mi.fields.length - mi.ihs.length) mi.ihs.length).map fun f => (f, []) := by
  unfold Pure.iotaMinors? at h
  split at h
  · rename_i T hall
    split at h
    · rename_i iv hT
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨cvs, hcvs, h⟩ := h
      by_cases g1 : (rv.name == mkRecName T && rv.numIndices == 0) = true
      · simp only [g1, guard, ite_true, pure] at h
        obtain ⟨_, -, ⟨motives, minors'⟩, hsh, _, hg, hm⟩ := h
        simp only [Option.some.injEq] at hm
        subst hm
        split at hg
        · rename_i hall2
          simp only [Bool.and_eq_true, beq_iff_eq] at g1
          refine ⟨T, iv, cvs, motives, hall, hT, hcvs, g1.1, g1.2, hsh, fun mi hmi => ?_⟩
          exact beq_iff_eq.mp (List.all_eq_true.mp hall2 mi hmi)
        · cases hg
      · simp [g1, guard, failure] at h
    · cases h
  · cases h

/-- `mapM` in `Option` of a mapped function. -/
theorem list_mapM_map {α β γ : Type} (g : α → Option β) (k : β → γ) :
    ∀ (l : List α), (l.mapM fun x => (g x).map k) = (l.mapM g).map (List.map k)
  | [] => rfl
  | x :: l => by
    simp only [List.mapM_cons, list_mapM_map g k l]
    cases g x <;> cases l.mapM g <;> rfl

/-- What `Erasure.Pure.iotaRhs?` reads and builds. -/
theorem iotaRhs?_spec {decls : List ConstantInfo} {r : Name} {us : List Level} {rv : RecursorVal}
    {minors : List RecMinor} {args : List Expr} {t e : Expr}
    (h : Pure.iotaRhs? decls r us rv minors args t = some e) :
    ∃ C uC cargs cv mi mk rfs, spine t = (.const C uC, cargs) ∧
      findConst decls C = some (.ctorInfo cv) ∧ rv.all = [cv.induct] ∧
      cargs.length = cv.numParams + cv.numFields ∧ minors[cv.cidx]? = some mi ∧
      ((args.take (rv.numParams + rv.numMotives + rv.numMinors)).drop
        (rv.numParams + rv.numMotives))[cv.cidx]? = some mk ∧
      (mi.ihs.mapM fun h => (cargs.drop cv.numParams)[h.field]?) = some rfs ∧
      e = mkAppN mk (cargs.drop cv.numParams ++ rfs.map fun f => mkAppN (.const r us)
        (args.take (rv.numParams + rv.numMotives + rv.numMinors) ++ [f]).toArray).toArray := by
  unfold Pure.iotaRhs? at h
  split at h
  · rename_i C uC cargs hsp
    split at h
    · rename_i cv hC
      by_cases g1 : (rv.all == [cv.induct] && cargs.length == cv.numParams + cv.numFields) = true
      · simp only [g1, guard, ite_true, pure, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨_, -, mi, hmi, mk, hmk, ihs, hihs, he⟩ := h
        rw [list_mapM_map] at hihs
        obtain ⟨rfs, hrfs, rfl⟩ := Option.map_eq_some_iff.mp hihs
        simp only [Bool.and_eq_true, beq_iff_eq] at g1
        exact ⟨C, uC, cargs, cv, mi, mk, rfs, hsp, hC, g1.1, g1.2, hmi, hmk, hrfs,
          (Option.some.inj he).symm⟩
      · simp [g1, guard, failure] at h
    · cases h
  · cases h

/-- What `Erasure.Pure.iotaApp?` checks of an application. -/
theorem iotaApp?_spec {decls : List ConstantInfo} {e : Expr} {r : Name} {us : List Level}
    {rv : RecursorVal} {minors : List RecMinor} {args : List Expr}
    (h : Pure.iotaApp? decls e = some (r, us, rv, minors, args)) :
    spine e = (.const r us, args) ∧ findConst decls r = some (.recInfo rv) ∧
      Pure.iotaMinors? decls rv = some minors ∧
      args.length = rv.numParams + rv.numMotives + rv.numMinors + 1 := by
  unfold Pure.iotaApp? at h
  split at h
  · rename_i r' us' args' hsp
    split at h
    · rename_i rv' hr
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨minors', hmin, h⟩ := h
      by_cases g : (args'.length == rv'.numParams + rv'.numMotives + rv'.numMinors + 1) = true
      · simp only [g, guard, ite_true, pure, Option.bind_eq_some_iff] at h
        obtain ⟨_, -, h⟩ := h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
        exact ⟨hsp, hr, hmin, by simpa using g⟩
      · simp [g, guard, failure] at h
    · cases h
  · cases h

/-- A successful `whnf` of an application: β on a λ head; otherwise the application of the
reduced head, or the ι-rule of a recursor of `Erasure.Pure.iotaMinors?` applied to its arity of
arguments, whose major premise reduces to a constructor application (`Erasure.Pure.iotaRhs?`). -/
theorem whnf_app_cases {cx : Pure.Ctx} {f : Nat} {ls : List Local} {g a w : Expr}
    (h : Pure.whnf cx (f + 1) ls (.app g a) = .ok w) :
    ∃ g', Pure.whnf cx f ls g = .ok g' ∧
      ((∃ n t b bi, g' = .lam n t b bi ∧ Pure.whnf cx f ls (b.instantiate1' a) = .ok w) ∨
        ((∀ n t b bi, g' ≠ .lam n t b bi) ∧
          (w = .app g' a ∨
            ∃ r us args rv minors wa e, spine (.app g' a) = (.const r us, args) ∧
              findConst cx.decls r = some (.recInfo rv) ∧ Pure.iotaMinors? cx.decls rv = some minors ∧
              args.length = rv.numParams + rv.numMotives + rv.numMinors + 1 ∧
              Pure.whnf cx f ls a = .ok wa ∧ Pure.iotaRhs? cx.decls r us rv minors args wa = some e ∧
              Pure.whnf cx f ls e = .ok w))) := by
  simp only [Pure.whnf] at h
  obtain ⟨g', h1, h2⟩ := ok_of_bind h
  refine ⟨g', h1, ?_⟩
  split at h2
  · exact .inl ⟨_, _, _, _, rfl, h2⟩
  rename_i hnl
  have refl : (pure (Expr.app g' a) : Except EraseError Expr) = .ok w → w = .app g' a :=
    fun h' => by simpa [pure, Except.pure] using h'.symm
  refine .inr ⟨fun n t b bi he => hnl n t b bi he, ?_⟩
  split at h2
  · rename_i r us rv minors args hia
    obtain ⟨wa, h3, h4⟩ := ok_of_bind h2
    split at h4
    · rename_i e he
      obtain ⟨hsp, hr, hmin, hlen⟩ := iotaApp?_spec hia
      exact .inr ⟨r, us, args, rv, minors, wa, e, hsp, hr, hmin, hlen, h3, he, h4⟩
    · exact .inl (refl h4)
  · exact .inl (refl h2)

/-- A constant of a sub-environment is the program's constant of that name. -/
theorem findConst_sub {decls : List ConstantInfo} {c : Name} {ci : ConstantInfo}
    (hsub : SubEnv decls P) (h : findConst decls c = some ci) : findDecl P c = some ci := by
  obtain ⟨hm, hn⟩ := findDecl_eq_some (l := decls) h
  have h' := hsub _ hm
  rwa [hn] at h'

/-- A name bound to a saturating binding is not a definition of the closure. -/
theorem special_not_defn {decls : List ConstantInfo} {c : Name} {b : MBinding ζ}
    (henv : ProgEnv P ζ E B) (hsub : SubEnv decls P) (hb : B c = some b)
    (hs : b.isSpecial = true) (v : DefinitionVal) : findConst decls c ≠ some (.defnInfo v) := by
  intro h
  obtain ⟨η, hB, -⟩ := henv.lookup_def (findConst_sub hsub h)
  rw [hb] at hB
  cases hB
  cases hs

/-- `whnf` returns a spine unchanged whose head constant is not a definition of the closure, and
that has fewer arguments than its arity if the head is a recursor. -/
theorem whnf_spine {cx : Pure.Ctx} {c : Name} {us : List Level}
    (hc : ∀ v, findConst cx.decls c ≠ some (.defnInfo v)) :
    ∀ {f : Nat} {ls : List Local} {e w : Expr}, e.getAppFn = .const c us →
      (∀ rv, findConst cx.decls c = some (.recInfo rv) → (spine e).2.length <
        rv.numParams + rv.numMotives + rv.numMinors + rv.numIndices + 1) →
      Pure.whnf cx f ls e = .ok w → w = e
  | 0, _, _, _, _, _, h => by simp [Pure.whnf, throw, throwThe, MonadExceptOf.throw] at h
  | f + 1, ls, .const c' us', w, hfn, _, h => by
    cases hfn
    rcases hf : findConst cx.decls c with _ | ci
    · simp only [Pure.whnf, hf] at h; simpa [pure, Except.pure] using h.symm
    · cases ci with
      | defnInfo v => exact absurd hf (hc v)
      | _ => simp only [Pure.whnf, hf] at h; simpa [pure, Except.pure] using h.symm
  | f + 1, ls, .app g a, w, hfn, hr, h => by
    obtain ⟨g', h1, h2⟩ := whnf_app_cases h
    have hg := whnf_spine hc (e := g) hfn (fun rv hrv => by
      have := hr rv hrv; rw [spine_app] at this; simp only [List.length_append,
        List.length_singleton] at this; omega) h1
    rw [hg] at h2
    rcases h2 with ⟨n, t, b, bi, rfl, -⟩ | ⟨-, rfl | ⟨r, us₂, args, rv, minors, wa, e, hsp, hrv, hmin,
      hlen, -⟩⟩
    · simp [Expr.getAppFn] at hfn
    · rfl
    · exfalso
      have h1 : (spine (.app g a)).1 = .const c us := by rw [spine_head]; exact hfn
      rw [hsp] at h1
      cases h1
      have := hr rv hrv
      rw [hsp] at this
      dsimp only at this
      obtain ⟨_, _, _, _, _, _, _, _, hni, -⟩ := iotaMinors?_spec hmin
      omega
  | _ + 1, _, .bvar _, _, hfn, _, _ | _ + 1, _, .fvar _, _, hfn, _, _
  | _ + 1, _, .mvar _, _, hfn, _, _ | _ + 1, _, .sort _, _, hfn, _, _
  | _ + 1, _, .lam .., _, hfn, _, _ | _ + 1, _, .forallE .., _, hfn, _, _
  | _ + 1, _, .letE .., _, hfn, _, _ | _ + 1, _, .lit _, _, hfn, _, _
  | _ + 1, _, .mdata .., _, hfn, _, _ | _ + 1, _, .proj .., _, hfn, _, _ => by cases hfn

open Metalean in
/-- A closed translation translates, weakened, in every context where its image is typed. -/
theorem trM_closed (hord : ∀ c {ι : IndSig} (η : Head ζ (.inductive ι)) (s : Fin ι.nsorts)
      (k : Fin (ι.nctors s)) (o : List Nat), B c = some (.ctor η s k o) →
      MetaOrderOK o (ι.ctors s k).nfields (ι.ctors s k).nrecFields)
    {n : Nat} {Γ : Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n} {e : Lean.Expr}
    {t : Expr ζ lps.length 0} (hΓ : E[Γ] ⊢ ok) (h : TrM E B lps .nil [] e t)
    (ht : ∃ T, E[Γ] ⊢ t.wkClosed : T) : TrM E B lps Γ Δ e t.wkClosed := by
  have hs : InstPre.MLCtx.Subs 0 0 (fun v => v.elim0 : Subst ζ lps.length 0 n) [] Δ :=
    ⟨fun _ _ h => (by simp [MLCtx.findB] at h), fun _ _ h => (by simp [MLCtx.findF] at h)⟩
  have hp := (InstPre.PreTr.ofTrM h).subst hs
  rw [liftLooseBVars'_zero] at hp
  have he : t.subst (fun v => v.elim0 : Subst ζ lps.length 0 n) = t.wkClosed :=
    Expr.wkClosed_subst (m := 0) t _
  rw [he] at hp
  exact InstPre.PreTr.recover hord hp (InstPre.Thin.id Γ) hΓ (by rw [Expr.rename_id]; exact ht)

variable {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}

/-- Congruence of application in the function. -/
theorem app_congr (hE : EnvWF E) (hΓ : E[Γ] ⊢ ok) {f g a F T : Metalean.Expr ζ lps.length n}
    (hd : E[Γ] ⊢ f ≡ g : F) (ht : E[Γ] ⊢ .app f a : T) : E[Γ] ⊢ .app f a ≡ .app g a : T :=
  (Metalean.Frame.app a).plug_defeq hE hΓ (fun h => Defeq.retype hE hΓ hd h) ht

/-- Congruence of a recursor in its major premise. -/
theorem recr_congr (hE : EnvWF E) (hΓ : E[Γ] ⊢ ok) {ι : Metalean.IndSig}
    {η : Metalean.Head ζ (.inductive ι)} {s : Fin ι.nsorts}
    {ls : Fin ι.nlevels → Metalean.Level lps.length} {l : Metalean.Level lps.length}
    {ps : Fin ι.nparams → Metalean.Expr ζ lps.length n}
    {ms : Fin ι.nsorts → Metalean.Expr ζ lps.length n}
    {mins : (t : Fin ι.nsorts) → Fin (ι.nctors t) → Metalean.Expr ζ lps.length n}
    {is : Fin (ι.nindices s) → Metalean.Expr ζ lps.length n} {m₁ m₂ X T : Metalean.Expr ζ lps.length n}
    (hd : E[Γ] ⊢ m₁ ≡ m₂ : X) (ht : E[Γ] ⊢ .recr η s ls l ps ms mins is m₁ : T) :
    E[Γ] ⊢ .recr η s ls l ps ms mins is m₁ ≡ .recr η s ls l ps ms mins is m₂ : T :=
  (Metalean.Frame.recr η s ls l ps ms mins is).plug_defeq hE hΓ
    (fun h => Defeq.retype hE hΓ hd h) ht

/-- A function applied to arguments and typed is typed at a Π-type. -/
theorem appList_fn_pi : ∀ {X T : Metalean.Expr ζ lps.length n} (rest : List (Metalean.Expr ζ lps.length n)),
    rest ≠ [] → E[Γ] ⊢ X.appList rest : T →
      ∃ (A : Metalean.Expr ζ lps.length n) (C : Metalean.Expr ζ lps.length (n + 1)),
        E[Γ] ⊢ X : .forallE A C := by
  intro X T rest hne ht
  induction rest using List.reverseRecOn generalizing T with
  | nil => exact absurd rfl hne
  | append_singleton rest r ih =>
    rw [TrApps.appList_append] at ht
    obtain ⟨A, C, hf, -, -⟩ := ht.app_inv
    by_cases hr : rest = []
    · subst hr
      exact ⟨A, C, hf⟩
    · exact ih hr hf

/-- A closed λ-telescope applied to fewer arguments than binders reduces to a λ. -/
theorem lam_partial : ∀ {K : Nat} (Δ : Metalean.Ctx ζ lps.length 0 K)
    (body : Metalean.Expr ζ lps.length K) (args : List (Metalean.Expr ζ lps.length n)),
    args.length < K → ∃ (A : Metalean.Expr ζ lps.length n) (b : Metalean.Expr ζ lps.length (n + 1)),
      WHRedS E ((Δ.lam body).wkClosed.appList args) (.lam A b)
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, .snoc Δ t, body, args, h => by
    by_cases hk : args.length = k
    · have h' := TrApps.eta_appList (E := E) Δ (.lam t body) args (by omega)
      rw [List.drop_of_length_le (by omega), Metalean.Expr.appList_nil] at h'
      exact ⟨_, _, h'⟩
    · exact lam_partial Δ (.lam t body) args (by omega)

/-- The shape of the translator's η-term of a constructor: a closed λ-telescope with one binder per
parameter and field. -/
theorem ctorTerm_shape {ι : Metalean.IndSig} {η : Metalean.Head ζ (.inductive ι)}
    {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} {order : List Nat}
    {ls : Fin ι.nlevels → Metalean.Level lps.length} {t₀ : Metalean.Expr ζ lps.length 0}
    (ht : Metalean.Frontend.ctorTerm (E.get η).block η s c ls order = .ok t₀) :
    ∃ (Θ : Metalean.Ctx ζ lps.length 0
        (ι.nparams + ((ι.ctors s c).nfields + (ι.ctors s c).nrecFields)))
      (body : Metalean.Expr ζ lps.length
        (ι.nparams + ((ι.ctors s c).nfields + (ι.ctors s c).nrecFields))),
      t₀ = Θ.lam body := by
  unfold Metalean.Frontend.ctorTerm at ht
  dsimp only at ht
  rcases hπ : Metalean.Frontend.orderMaps? order
        ((ι.ctors s c).nfields + (ι.ctors s c).nrecFields) with _ | ⟨π, πinv⟩
  · rw [hπ] at ht; cases ht
  rw [hπ] at ht
  dsimp only at ht
  obtain ⟨x, hx⟩ : ∃ x, Metalean.Ctx.permute? (k := (ι.ctors s c).nfields + (ι.ctors s c).nrecFields)
      (by simp [Nat.add_assoc]) π πinv (((E.get η).block.ctors s c).fieldTele η ls
        (fun p => .var p)) = x := ⟨_, rfl⟩
  rw [hx] at ht
  rcases x with _ | fields'
  · cases ht
  dsimp only at ht
  obtain ⟨y, hy⟩ : ∃ y, Fin.mapM (m := Option) (fun f : Fin (ι.ctors s c).nfields =>
      (do let j ← πinv (Fin.castAdd (ι.ctors s c).nrecFields f)
          some (Metalean.Expr.var ⟨ι.nparams + j.val, by omega⟩ : Metalean.Expr ζ lps.length
            (ι.nparams + ((ι.ctors s c).nfields + (ι.ctors s c).nrecFields))))) = y := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z, Fin.mapM (m := Option) (fun r : Fin (ι.ctors s c).nrecFields =>
      (do let j ← πinv (Fin.natAdd (ι.ctors s c).nfields r)
          some (Metalean.Expr.var ⟨ι.nparams + j.val, by omega⟩ : Metalean.Expr ζ lps.length
            (ι.nparams + ((ι.ctors s c).nfields + (ι.ctors s c).nrecFields))))) = z := ⟨_, rfl⟩
  rw [hy, hz] at ht
  rcases y with _ | fds
  · cases ht
  rcases z with _ | recFds
  · cases ht
  dsimp only at ht
  cases ht
  exact ⟨_, _, rfl⟩


/-- A typed translation of a spine of a constructor at an inductive type `η s` is a saturated
constructor node of `η s`; when the constructor has no recursive field, its `i`-th Lean field
translates to its `i`-th Metalean field. -/
theorem ctor_major {cx : Pure.Ctx} (henv : ProgEnv P ζ E B) (hE : EnvWF E)
    (hsub : SubEnv cx.decls P) (hΓ : E[Γ] ⊢ ok) {c : Name} {u : List Level} {args : List Expr}
    {cv : ConstructorVal} {ws' : Metalean.Expr ζ lps.length n} {ι : Metalean.IndSig}
    {η : Metalean.Head ζ (.inductive ι)} {s : Fin ι.nsorts}
    {ls : Fin ι.nlevels → Metalean.Level lps.length}
    {ps : Fin ι.nparams → Metalean.Expr ζ lps.length n}
    {is : Fin (ι.nindices s) → Metalean.Expr ζ lps.length n}
    (hc : findConst cx.decls c = some (.ctorInfo cv))
    (hws : TrM E B lps Γ Δ (mkAppN (.const c u) args.toArray) ws')
    (hty : E[Γ] ⊢ ws' : .ind η s ls ps is) :
    ∃ (k : Fin (ι.nctors s)) (ls₂ : Fin ι.nlevels → Metalean.Level lps.length)
      (ps₂ : Fin ι.nparams → Metalean.Expr ζ lps.length n)
      (fds : Fin (ι.ctors s k).nfields → Metalean.Expr ζ lps.length n)
      (recFds : Fin (ι.ctors s k).nrecFields → Metalean.Expr ζ lps.length n),
      ws' = .ctor η s k ls₂ ps₂ fds recFds ∧
      ((ι.ctors s k).nrecFields = 0 → ∀ (i : Nat) (hi : i < (ι.ctors s k).nfields) (a : Expr),
        args[cv.numParams + i]? = some a → TrM E B lps Γ Δ a (fds ⟨i, hi⟩)) := by
  obtain ⟨ι₂, η₂, s₂, k, order, hBc, -, hnp, -, hmo, -⟩ := henv.lookup_ctor (findConst_sub hsub hc)
  obtain ⟨bs', -, hargs, hsat⟩ := TrM.special_inv hBc rfl hws
  cases hsat with
  | ctorEta _ hlt hct =>
    obtain ⟨Θ, body, rfl⟩ := ctorTerm_shape hct
    obtain ⟨A, b, hred⟩ := lam_partial Θ body bs' hlt
    obtain ⟨_, -, hTy⟩ := (WHRedS.defeq hE hΓ hred hty).right.lam_inv hΓ
    exact (TypeEq.forallE_ne_ind hE hΓ hTy.symm).elim
  | ctorSat ps₂ fs rest fds recFds _ _ _ hperm =>
    by_cases hr : rest = []
    · subst hr
      rw [Metalean.Expr.appList_nil] at hty ⊢
      obtain ⟨_, _, _, -, -, -, -, hTy⟩ := hty.ctor_inv
      have hh := ind_head hE hΓ hTy
      cases hh
      refine ⟨k, _, ps₂, fds, recFds, rfl, fun hnr i hi a ha => hargs _ a _ ha ?_⟩
      rw [List.append_nil, hnp, List.getElem?_append_right (by simp)]
      simpa using field_of_order hnr hmo hperm hi
    · obtain ⟨A, C, hX⟩ := appList_fn_pi rest hr hty
      obtain ⟨_, _, _, -, -, -, -, hTy⟩ := hX.ctor_inv
      exact (TypeEq.forallE_ne_ind hE hΓ hTy).elim


variable {cx : Pure.Ctx} {f : Nat} {ls : List Local} {w : Expr} {T : Metalean.Expr ζ lps.length n}

/-- `whnf` of a free variable: a let-bound local unfolds to its value. -/
theorem whnf_fvar (hloc : LocalsOK E B lps Γ Δ ls) (ih : ∀ {e w : Expr} {t T : Metalean.Expr ζ lps.length n}, TrM E B lps Γ Δ e t →
      E[Γ] ⊢ t : T → Pure.whnf cx f ls e = .ok w →
      ∃ w', TrM E B lps Γ Δ w w' ∧ E[Γ] ⊢ t ≡ w' : T)
    {x : FVarId} {t : Metalean.Expr ζ lps.length n} (hf : Δ.findF x = some t)
    (ht : E[Γ] ⊢ t : T) (h : Pure.whnf cx (f + 1) ls (.fvar x) = .ok w) :
    ∃ w', TrM E B lps Γ Δ w w' ∧ E[Γ] ⊢ t ≡ w' : T := by
  simp only [Pure.whnf] at h
  split at h
  · rename_i fid nm ty v hl
    unfold Pure.findLocal at hl
    have hm := List.mem_of_find?_eq_some hl
    have hx : fid = x := (fvarId_beq_iff _ _).mp (by simpa using List.find?_some hl)
    obtain ⟨A, t', -, hF, -, hv⟩ := hloc _ hm
    simp only at hF
    rw [hx, hf] at hF
    cases hF
    exact ih (hv v rfl) ht h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨t, .fvar hf, ht⟩

/-- `whnf` of a constant: δ for a definition of the closure. -/
theorem whnf_const (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv cx.decls P)
    (hΓ : E[Γ] ⊢ ok) (ih : ∀ {e w : Expr} {t T : Metalean.Expr ζ lps.length n}, TrM E B lps Γ Δ e t →
      E[Γ] ⊢ t : T → Pure.whnf cx f ls e = .ok w →
      ∃ w', TrM E B lps Γ Δ w w' ∧ E[Γ] ⊢ t ≡ w' : T)
    {c : Name} {us : List Level} {kind : Metalean.ConstKind} {nl : Nat}
    {η : Metalean.Head ζ (.const kind nl)} {ls' : Fin nl → Metalean.Level lps.length}
    (hB : B c = some (.const η)) (hls : TrLevels lps us nl = some ls')
    (ht : E[Γ] ⊢ .const η ls' : T) (h : Pure.whnf cx (f + 1) ls (.const c us) = .ok w) :
    ∃ w', TrM E B lps Γ Δ w w' ∧ E[Γ] ⊢ .const η ls' ≡ w' : T := by
  have refl : Pure.whnf cx (f + 1) ls (.const c us) = .ok (.const c us) →
      ∃ w', TrM E B lps Γ Δ w w' ∧ E[Γ] ⊢ .const η ls' ≡ w' : T := fun h' => by
    rw [h'] at h; cases h; exact ⟨_, .const hB hls, ht⟩
  rcases hfc : findConst cx.decls c with _ | ci
  · exact refl (by simp only [Pure.whnf, hfc]; rfl)
  · cases ci with
    | defnInfo v =>
      simp only [Pure.whnf, hfc] at h
      split at h
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact ⟨_, .const hB hls, ht⟩
      · obtain ⟨η', hB', htr⟩ := henv.lookup_def (findConst_sub hsub hfc)
        rw [hB'] at hB
        simp only [Option.some.injEq, MBinding.const.injEq] at hB
        obtain ⟨rfl, rfl, hη⟩ := hB
        cases hη
        have hd := WHRed.defeq hE .delta hΓ ht
        have htr' := trM_closed (Δ := Δ) henv.metaOrderOK hΓ (TrM.instLevels hls htr)
          ⟨_, hd.right⟩
        obtain ⟨w', hw, hd'⟩ := ih htr' hd.right h
        exact ⟨w', hw, hd.trans hd'⟩
    | _ => exact refl (by simp only [Pure.whnf, hfc]; rfl)

/-- `whnf` of a spine of a saturating constant returns it, if it has fewer arguments than its arity
when the constant is a recursor. -/
theorem whnf_special (henv : ProgEnv P ζ E B) (hsub : SubEnv cx.decls P)
    {c : Name} {us : List Level} {as : List Expr} {as' : List (Metalean.Expr ζ lps.length n)}
    {b : MBinding ζ} {t : Metalean.Expr ζ lps.length n} (hB : B c = some b)
    (hs : b.isSpecial = true) (hlen : as.length = as'.length)
    (hargs : ∀ (i : Nat) a a', as[i]? = some a → as'[i]? = some a' → TrM E B lps Γ Δ a a')
    (hsat : SatTr E lps b us as' t) (ht : E[Γ] ⊢ t : T)
    (hlt : ∀ rv, findConst cx.decls c = some (.recInfo rv) →
      as.length < rv.numParams + rv.numMotives + rv.numMinors + rv.numIndices + 1)
    (h : Pure.whnf cx f ls (mkAppN (.const c us) as.toArray) = .ok w) :
    ∃ w', TrM E B lps Γ Δ w w' ∧ E[Γ] ⊢ t ≡ w' : T := by
  have hw := whnf_spine (special_not_defn henv hsub hB hs)
    (by rw [mkAppN_eq_foldl, foldl_app_getAppFn]; rfl)
    (fun rv hrv => by rw [spine_const]; exact hlt rv hrv) h
  subst hw
  exact ⟨t, .special hB hs hlen hargs hsat, ht⟩

/-- `whnf`'s ι-rule of a recursor (`Erasure.Pure.iotaRhs?`): the saturated spine reduces in Metalean,
after its major premise is replaced by the major's weak-head normal form (`recr_congr`), by ι and β
(`RecWhred.recIota_whred`) to the translation of the minor premise of the major's constructor
applied to the fields and to the induction hypotheses. -/
theorem whnf_iota (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv cx.decls P)
    (hΓ : E[Γ] ⊢ ok) (ih : ∀ {e w : Expr} {t T : Metalean.Expr ζ lps.length n}, TrM E B lps Γ Δ e t →
      E[Γ] ⊢ t : T → Pure.whnf cx f ls e = .ok w →
      ∃ w', TrM E B lps Γ Δ w w' ∧ E[Γ] ⊢ t ≡ w' : T)
    {g a : Expr} {r : Name} {us : List Level} {args : List Expr} {rv : RecursorVal}
    {minors : List RecMinor} {wa e : Expr} {t : Metalean.Expr ζ lps.length n}
    (hsp : spine (.app g a) = (.const r us, args)) (hr : findConst cx.decls r = some (.recInfo rv))
    (hmin : Pure.iotaMinors? cx.decls rv = some minors)
    (hlen : args.length = rv.numParams + rv.numMotives + rv.numMinors + 1)
    (hX : TrM E B lps Γ Δ (.app g a) t) (ht : E[Γ] ⊢ t : T)
    (hwa : Pure.whnf cx f ls a = .ok wa)
    (he : Pure.iotaRhs? cx.decls r us rv minors args wa = some e)
    (hw : Pure.whnf cx f ls e = .ok w) :
    ∃ w', TrM E B lps Γ Δ w w' ∧ E[Γ] ⊢ t ≡ w' : T := by
  obtain ⟨T₀, iv, cvs, motives, hall, hT, hcvs, hname, hni, hshape, hihs⟩ := iotaMinors?_spec hmin
  obtain ⟨C, uC, cargs, cv, mi, mk, rfs, hspw, hC, hind, hclen, hmi, hmk, hrfs, rfl⟩ :=
    iotaRhs?_spec he
  have hXe : Expr.app g a = mkAppN (.const r us) args.toArray := by
    have := CasesShape.spine_mkAppN (.app g a); rw [hsp] at this; exact this.symm
  have hargs : args = (spine g).2 ++ [a] := by rw [spine_app] at hsp; exact (Prod.mk.inj hsp).2.symm
  generalize (spine g).2 = pre at hargs
  subst hargs
  -- the recursor's Metalean node
  obtain ⟨ι, η, s, os, hBr, har⟩ := henv.lookup_recr (findConst_sub hsub hr)
  rw [hni] at har
  have hlen' : (pre ++ [a]).length = ι.recrEnd s := by omega
  have hpl : pre.length = rv.numParams + rv.numMotives + rv.numMinors := by
    simp only [List.length_append, List.length_singleton] at hlen; omega
  rw [hXe] at hX
  obtain ⟨ls', l, mo, A, mins, hA, hmo, hwc, rfl, us', hRL, hTL⟩ :=
    CasesWhred.trM_recr_inv hBr hlen' hX
  -- the major premise and its weak-head normal form
  obtain ⟨a₀, ha₀, htr₀⟩ := hA (Metalean.IndSig.RecrBinder.major (ι := ι) (s := s)).resolve
  have hlast : ((Metalean.IndSig.RecrBinder.major (ι := ι) (s := s)).resolve).val =
      ι.recrEnd s - 1 := rfl
  have hpl' : pre.length = ι.recrEnd s - 1 := by omega
  rw [hlast, ← hpl', List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at ha₀
  cases ha₀
  obtain ⟨wa', hwa', hd⟩ := ih htr₀ (recr_major ht) hwa
  have hX' := RecWhred.trM_recr_major hBr hlen' hA hmo hwc hRL hTL hwa'
  have d1 := recr_congr hE hΓ hd ht
  -- the ι-rule
  have hrn : rv.name = r := (findDecl_eq_some (l := cx.decls) hr).2
  have hcT : r = mkRecName T₀ := hrn.symm.trans hname
  have hcr : findDecl (⟨cx.decls, fun _ => false⟩ : EvalEnv).decls r = some (.recInfo rv) := hr
  have hblk : (⟨cx.decls, fun _ => false⟩ : EvalEnv).recBlock? rv = some ([iv], cvs) := by
    have hT' : findDecl cx.decls T₀ = some (.inductInfo iv) := hT
    have hcvs' : (iv.ctors.mapM (⟨cx.decls, fun _ => false⟩ : EvalEnv).ctorOf?) = some cvs := hcvs
    simp [EvalEnv.recBlock?, hall, EvalEnv.indOf?, hT', hcvs']
  have htake : (pre ++ [a]).take (rv.numParams + rv.numMotives + rv.numMinors) = pre := by
    exact List.take_left' hpl
  rw [htake] at hmk hw
  have hT₀ : cv.induct = T₀ := by
    rw [hall] at hind; exact (List.singleton_inj.mp hind).symm
  have hcv : CtorValue ⟨cx.decls, fun _ => false⟩ T₀ wa cv.cidx (cargs.drop cv.numParams) := by
    refine ⟨C, uC, cv, cargs.take cv.numParams, hC, hT₀, rfl, by simp; omega, by simp; omega, ?_⟩
    rw [List.take_append_drop]
    have := CasesShape.spine_mkAppN wa
    rw [hspw] at this
    exact this.symm
  have hpre : pre = pre.take rv.numParams ++ (pre.drop rv.numParams).take rv.numMotives ++
      pre.drop (rv.numParams + rv.numMotives) := by
    rw [← List.take_add, List.take_append_drop]
  rw [hpre] at hX' hw
  obtain ⟨a₁, fs₀, ihs₀, hmk', hfs₀, hihs₀, hred⟩ := RecWhred.recIota_whred henv hsub hcr hall hcT
    hblk hni hshape hihs (ps := pre.take rv.numParams)
    (ms := (pre.drop rv.numParams).take rv.numMotives) (mvs := pre.drop (rv.numParams + rv.numMotives))
    (by simp; omega) (by simp; omega) (by simp; omega) hcv hmi hmk hrfs hX'
  obtain ⟨t₂, htr₂, hred₂⟩ := TrM.apps hmk' (List.rel_append hfs₀ hihs₀)
  have d2 := WHRedS.defeq hE hΓ hred d1.right
  have d3 := WHRedS.defeq hE hΓ hred₂ d2.right
  obtain ⟨w', hw', d4⟩ := ih htr₂ d3.right hw
  exact ⟨w', hw', d1.trans (d2.trans (d3.trans d4))⟩

/-- `whnf` of an application of a head that is not saturating, or of a recursor spine with at least
its arity of arguments: β on a λ head, the ι-rule of a recursor (`whnf_iota`), and the translation
of the new spine otherwise (`TrM.apps`). -/
theorem whnf_app (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv cx.decls P) (hΓ : E[Γ] ⊢ ok)
    (ih : ∀ {e w : Expr} {t T : Metalean.Expr ζ lps.length n}, TrM E B lps Γ Δ e t →
      E[Γ] ⊢ t : T → Pure.whnf cx f ls e = .ok w →
      ∃ w', TrM E B lps Γ Δ w w' ∧ E[Γ] ⊢ t ≡ w' : T)
    {g a : Expr} {g' a' : Metalean.Expr ζ lps.length n} (hg : TrM E B lps Γ Δ g g')
    (ha : TrM E B lps Γ Δ a a') (ht : E[Γ] ⊢ .app g' a' : T)
    (h : Pure.whnf cx (f + 1) ls (.app g a) = .ok w) :
    ∃ w', TrM E B lps Γ Δ w w' ∧ E[Γ] ⊢ .app g' a' ≡ w' : T := by
  obtain ⟨wg, h1, h2⟩ := whnf_app_cases h
  obtain ⟨A0, B0, hf', ha', -⟩ := ht.app_inv
  obtain ⟨wg', hwg, hd⟩ := ih hg hf' h1
  have d1 := app_congr hE hΓ hd ht
  rcases h2 with ⟨nm, A, b, bi, rfl, h2⟩ | ⟨-, rfl | ⟨r, us, args, rv, minors, wa, e, hsp, hr, hmin, hlen,
    hwa, he, hw⟩⟩
  · generalize hx : Expr.lam nm A b bi = x at hwg
    cases hwg with
    | lam hA hb =>
      cases hx
      obtain ⟨B', hb', hTy⟩ := hd.right.lam_inv hΓ
      have ha'' := (TypeEq.forallE_inj hE hΓ hTy).1.conv ha'
      obtain ⟨t₁, htr, hd₁⟩ := TrM.inst hE hΓ henv.metaOrderOK hb ha ha'' hb'
      have d2 := WHRed.defeq hE .beta hΓ d1.right
      obtain ⟨w', hw, hd₂⟩ := ih htr hd₁.left h2
      exact ⟨w', hw, (d1.trans d2).trans (Defeq.retype hE hΓ (hd₁.symm.trans hd₂) d2.right)⟩
    | special => exact absurd hx (ne_mkAppN_const fun _ _ h => by cases h)
    | _ => cases hx
  · obtain ⟨t₂, htr, hred⟩ := TrM.apps hwg (List.Forall₂.cons ha .nil)
    have d3 := WHRedS.defeq hE hΓ hred d1.right
    exact ⟨t₂, htr, d1.trans d3⟩
  · obtain ⟨t₂, htr, hred⟩ := TrM.apps hwg (List.Forall₂.cons ha .nil)
    have d3 := WHRedS.defeq hE hΓ hred d1.right
    obtain ⟨w', hw', d4⟩ := whnf_iota henv hE hsub hΓ ih hsp hr hmin hlen htr d3.right hwa he hw
    exact ⟨w', hw', (d1.trans d3).trans d4⟩

/-- `whnf` of a spine of a saturating constant: a recursor spine with at least its arity of
arguments by `whnf_app` (beyond the arity) or by `whnf_iota` (at the arity), every other spine by
`whnf_special`. -/
theorem whnf_spineSpecial (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv cx.decls P)
    (hΓ : E[Γ] ⊢ ok) (ih : ∀ {e w : Expr} {t T : Metalean.Expr ζ lps.length n}, TrM E B lps Γ Δ e t →
      E[Γ] ⊢ t : T → Pure.whnf cx f ls e = .ok w →
      ∃ w', TrM E B lps Γ Δ w w' ∧ E[Γ] ⊢ t ≡ w' : T)
    {c : Name} {us : List Level} {as : List Expr} {as' : List (Metalean.Expr ζ lps.length n)}
    {b : MBinding ζ} {t : Metalean.Expr ζ lps.length n} (hB : B c = some b)
    (hs : b.isSpecial = true) (hlen : as.length = as'.length)
    (hargs : ∀ (i : Nat) a a', as[i]? = some a → as'[i]? = some a' → TrM E B lps Γ Δ a a')
    (hsat : SatTr E lps b us as' t) (ht : E[Γ] ⊢ t : T)
    (h : Pure.whnf cx (f + 1) ls (mkAppN (.const c us) as.toArray) = .ok w) :
    ∃ w', TrM E B lps Γ Δ w w' ∧ E[Γ] ⊢ t ≡ w' : T := by
  by_cases hrc : ∃ rv, findConst cx.decls c = some (.recInfo rv) ∧
      rv.numParams + rv.numMotives + rv.numMinors + rv.numIndices + 1 ≤ as.length
  swap
  · exact whnf_special henv hsub hB hs hlen hargs hsat ht
      (fun rv hrv => Nat.lt_of_not_le fun hle => hrc ⟨rv, hrv, hle⟩) h
  obtain ⟨rv, hrv, hle⟩ := hrc
  obtain ⟨ι, η, s, os, hBr, har⟩ := henv.lookup_recr (findConst_sub hsub hrv)
  have he := TrM.special hB hs hlen hargs hsat
  obtain ⟨bs, a, rfl⟩ : ∃ bs a, as = bs ++ [a] := by
    rcases as.eq_nil_or_concat with h0 | ⟨L, x, h1⟩
    · subst h0; simp at hle
    · exact ⟨L, x, by simp [h1]⟩
  have happ : mkAppN (.const c us) (bs ++ [a]).toArray = .app (mkAppN (.const c us) bs.toArray) a := by
    rw [mkAppN_eq_foldl, mkAppN_eq_foldl, List.foldl_append]; rfl
  rw [happ] at h he
  simp only [List.length_append, List.length_singleton] at hle
  by_cases hk : ι.recrEnd s ≤ bs.length
  · obtain ⟨f', a', hf, ha, rfl, -, -⟩ := RecWhred.TrM.wf_app_recr hBr hk he ht
    exact whnf_app henv hE hsub hΓ ih hf ha ht h
  obtain ⟨g', h1, h2⟩ := whnf_app_cases h
  have hg := whnf_spine (special_not_defn henv hsub hB hs)
    (by rw [mkAppN_eq_foldl, foldl_app_getAppFn]; rfl)
    (fun rv' hrv' => by rw [hrv] at hrv'; cases hrv'; rw [spine_const]; dsimp only; omega) h1
  rw [hg] at h2
  rcases h2 with ⟨_, _, _, _, hl, -⟩ | ⟨-, rfl | ⟨r, us₂, args, rv₂, minors, wa, e, hsp, hr, hmin,
    hlen₂, hwa, he', hw⟩⟩
  · have := congrArg Expr.getAppFn hl
    rw [mkAppN_eq_foldl, foldl_app_getAppFn] at this
    cases this
  · exact ⟨t, he, ht⟩
  · exact whnf_iota henv hE hsub hΓ ih hsp hr hmin hlen₂ he ht hwa he' hw

/-- `whnf` of a `let`: ζ, through the translator's inlining (`TrM.inst_let`). -/
theorem whnf_letE (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hΓ : E[Γ] ⊢ ok) (ih : ∀ {e w : Expr} {t T : Metalean.Expr ζ lps.length n}, TrM E B lps Γ Δ e t →
      E[Γ] ⊢ t : T → Pure.whnf cx f ls e = .ok w →
      ∃ w', TrM E B lps Γ Δ w w' ∧ E[Γ] ⊢ t ≡ w' : T)
    {x : Name} {T₀ v b : Expr} {nd : Bool} {T' v' b' : Metalean.Expr ζ lps.length n}
    (hv : TrM E B lps Γ Δ v v') (hb : TrM E B lps Γ ((none, .vlet v') :: Δ) b b')
    (ht : E[Γ] ⊢ .letE T' v' b'.wk : T)
    (h : Pure.whnf cx (f + 1) ls (.letE x T₀ v b nd) = .ok w) :
    ∃ w', TrM E B lps Γ Δ w w' ∧ E[Γ] ⊢ .letE T' v' b'.wk ≡ w' : T := by
  simp only [Pure.whnf] at h
  have d1 := WHRed.defeq hE .zeta hΓ ht
  rw [Metalean.Expr.inst_wk] at d1
  obtain ⟨t₁, htr, hd₁⟩ := TrM.inst_let hE hΓ henv.metaOrderOK hb hv d1.right
  obtain ⟨w', hw, hd₂⟩ := ih htr hd₁.left h
  exact ⟨w', hw, d1.trans (hd₁.symm.trans hd₂)⟩


/-- The ι-step of `whnf` on a projection: the major reduces to a spine of a constructor `c` whose
argument at `numParams + i` is `a`. -/
theorem whnf_proj_inv {S : Name} {i : Nat} {s : Expr}
    (h : Pure.whnf cx (f + 1) ls (.proj S i s) = .ok w) :
    w = .proj S i s ∨ ∃ (ws : Expr) (c : Name) (u : List Level) (args : List Expr) (cv : ConstructorVal) (a : Expr), Pure.whnf cx f ls s = .ok ws ∧
      ws = mkAppN (.const c u) args.toArray ∧ findConst cx.decls c = some (.ctorInfo cv) ∧
      args[cv.numParams + i]? = some a ∧ Pure.whnf cx f ls a = .ok w := by
  simp only [Pure.whnf] at h
  obtain ⟨ws, h1, h2⟩ := ok_of_bind h
  have hws := CasesShape.spine_mkAppN ws
  revert h2 hws
  rcases spine ws with ⟨hd, args⟩
  intro h2 hws
  simp only at h2 hws
  have refl : (pure (Expr.proj S i s) : Except EraseError Expr) = .ok w → w = .proj S i s :=
    fun h' => by simpa [pure, Except.pure] using h'.symm
  cases hd with
  | const c u =>
    simp only at h2
    split at h2
    · rename_i cv hc
      split at h2
      · rename_i a ha
        exact .inr ⟨ws, c, u, args, cv, a, h1, hws.symm, hc, ha, h2⟩
      · exact .inl (refl h2)
    · exact .inl (refl h2)
  | _ => exact .inl (refl h2)

/-- `whnf` of a projection of a structure: the ι-rule of projections. -/
theorem whnf_projStruct (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv cx.decls P)
    (hΓ : E[Γ] ⊢ ok) (ih : ∀ {e w : Expr} {t T : Metalean.Expr ζ lps.length n}, TrM E B lps Γ Δ e t →
      E[Γ] ⊢ t : T → Pure.whnf cx f ls e = .ok w →
      ∃ w', TrM E B lps Γ Δ w w' ∧ E[Γ] ⊢ t ≡ w' : T)
    {S : Name} {i : Nat} {s : Expr} {ι : Metalean.IndSig} {η : Metalean.Head ζ (.inductive ι)}
    {sₛ : Fin ι.nsorts} {c : Fin (ι.nctors sₛ)} {ls' : Fin ι.nlevels → Metalean.Level lps.length}
    {ps : Fin ι.nparams → Metalean.Expr ζ lps.length n}
    {is : Fin (ι.nindices sₛ) → Metalean.Expr ζ lps.length n} {s' : Metalean.Expr ζ lps.length n}
    (hst : (E.get η).block.IsStructure sₛ c) (hi : i < (ι.ctors sₛ c).nfields)
    (hBS : B S = some (.ind η sₛ)) (hs : TrM E B lps Γ Δ s s')
    (hty : TypedExt E Γ s' (.ind η sₛ ls' ps is))
    (ht : E[Γ] ⊢ hst.projTerm η ls' ps ⟨i, hi⟩ s' : T)
    (h : Pure.whnf cx (f + 1) ls (.proj S i s) = .ok w) :
    ∃ w', TrM E B lps Γ Δ w w' ∧ E[Γ] ⊢ hst.projTerm η ls' ps ⟨i, hi⟩ s' ≡ w' : T := by
  rcases whnf_proj_inv h with rfl | ⟨ws, c', u, args, cv, a, h1, rfl, hc, ha, h2⟩
  · exact ⟨_, .projStruct hst hi hBS hs hty, ht⟩
  have ht' := ht
  rw [hst.projTerm_eq_recr] at ht'
  obtain ⟨ws', hws', hd⟩ := ih hs (recr_major ht') h1
  obtain ⟨k, ls₂, ps₂, fds, recFds, rfl, hfield⟩ := ctor_major henv hE hsub hΓ hc hws' hd.right
  obtain rfl := hst.ctor_unique k
  have hnr : (ι.ctors sₛ k).nrecFields = 0 :=
    Nat.eq_zero_of_not_pos fun h => hst.no_recursive.false ⟨0, h⟩
  have d1 : E[Γ] ⊢ hst.projTerm η ls' ps ⟨i, hi⟩ s' ≡
      hst.projTerm η ls' ps ⟨i, hi⟩ (.ctor η sₛ k ls₂ ps₂ fds recFds) : T := by
    rw [hst.projTerm_eq_recr, hst.projTerm_eq_recr]
    exact recr_congr hE hΓ hd ht'
  have d2 := hst.projTerm_ctor_defeq ⟨i, hi⟩ hE hΓ d1.right
  obtain ⟨w', hw, d3⟩ := ih (hfield hnr i hi a ha) d2.right h2
  exact ⟨w', hw, d1.trans (d2.trans d3)⟩

/-- `whnf` of a proof projection: the ι-rule of projections, through Metalean's recursor ι. -/
theorem whnf_projProof (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv cx.decls P)
    (hΓ : E[Γ] ⊢ ok) (ih : ∀ {e w : Expr} {t T : Metalean.Expr ζ lps.length n}, TrM E B lps Γ Δ e t →
      E[Γ] ⊢ t : T → Pure.whnf cx f ls e = .ok w →
      ∃ w', TrM E B lps Γ Δ w w' ∧ E[Γ] ⊢ t ≡ w' : T)
    {S : Name} {i : Nat} {s : Expr} {ι : Metalean.IndSig} {η : Metalean.Head ζ (.inductive ι)}
    {sₛ : Fin ι.nsorts} {c : Fin (ι.nctors sₛ)} {ls' : Fin ι.nlevels → Metalean.Level lps.length}
    {ps : Fin ι.nparams → Metalean.Expr ζ lps.length n} (hi0 : ι.nindices sₛ = 0)
    {s' : Metalean.Expr ζ lps.length n} (hcc : ∀ d : Fin (ι.nctors sₛ), d = c)
    (hnr : (ι.ctors sₛ c).nrecFields = 0) (hi : i < (ι.ctors sₛ c).nfields)
    (hs : TrM E B lps Γ Δ s s')
    (ht : E[Γ] ⊢ projProofTerm E η sₛ c ls' hi0 ps i s' : T)
    (hre : ∀ w', w' = projProofTerm E η sₛ c ls' hi0 ps i s' → TrM E B lps Γ Δ (.proj S i s) w')
    (h : Pure.whnf cx (f + 1) ls (.proj S i s) = .ok w) :
    ∃ w', TrM E B lps Γ Δ w w' ∧ E[Γ] ⊢ projProofTerm E η sₛ c ls' hi0 ps i s' ≡ w' : T := by
  rcases whnf_proj_inv h with rfl | ⟨ws, c', u, args, cv, a, h1, rfl, hc, ha, h2⟩
  · exact ⟨_, hre _ rfl, ht⟩
  have ht' := ht
  rw [projProofTerm] at ht'
  obtain ⟨ws', hws', hd⟩ := ih hs (recr_major ht') h1
  obtain ⟨k, ls₂, ps₂, fds, recFds, rfl, hfield⟩ := ctor_major henv hE hsub hΓ hc hws' hd.right
  obtain rfl := hcc k
  have d1 : E[Γ] ⊢ projProofTerm E η sₛ k ls' hi0 ps i s' ≡
      projProofTerm E η sₛ k ls' hi0 ps i (.ctor η sₛ k ls₂ ps₂ fds recFds) : T := by
    rw [projProofTerm, projProofTerm]
    exact recr_congr hE hΓ hd ht'
  have d2 := WHRedS.defeq hE hΓ (projProofTerm_ctor_whredS hi0 hi hnr) d1.right
  obtain ⟨w', hw, d3⟩ := ih (hfield hnr i hi a ha) d2.right h2
  exact ⟨w', hw, d1.trans (d2.trans d3)⟩

end OracleWhnf

open OracleWhnf in
/-- A successful run of the oracle's weak-head reduction on a translated, well-typed term gives a
term whose translation is definitionally equal to the input's image: β (`TrM.inst`), ζ
(`TrM.inst_let` and the let-bound locals of `LocalsOK`), δ of every definition of the closure
(`ProgEnv.lookup_def`, `TrM.instLevels`), and the ι-rule of projections (Metalean's projection and
recursor ι); spines of saturating constants are returned unchanged. Reference: `hnf_sound`
(`MR S/PCUICSafeReduce.v:1841`); port of `L4 Oracle/Whnf.lean:316`. -/
theorem Pure.whnf_sound {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ}
    {P : List ConstantInfo} {lps : List Name} {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
    {Δ : MLCtx ζ lps.length n} {cx : Pure.Ctx} {fuel : Nat} {ls : List Local} {e w : Expr}
    {t T : Metalean.Expr ζ lps.length n}
    (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv cx.decls P)
    (hΓ : E[Γ] ⊢ ok) (hloc : LocalsOK E B lps Γ Δ ls) (he : TrM E B lps Γ Δ e t)
    (ht : E[Γ] ⊢ t : T) (h : Pure.whnf cx fuel ls e = .ok w) :
    ∃ w', TrM E B lps Γ Δ w w' ∧ E[Γ] ⊢ t ≡ w' : T := by
  induction fuel generalizing e t T w with
  | zero => simp [Pure.whnf, throw, throwThe, MonadExceptOf.throw] at h
  | succ f ih =>
    have ih' : ∀ {e w : Expr} {t T : Metalean.Expr ζ lps.length n}, TrM E B lps Γ Δ e t →
        E[Γ] ⊢ t : T → Pure.whnf cx f ls e = .ok w →
        ∃ w', TrM E B lps Γ Δ w w' ∧ E[Γ] ⊢ t ≡ w' : T := fun he ht h => ih he ht h
    cases he with
    | bvar hb =>
      simp only [Pure.whnf, pure, Except.pure, Except.ok.injEq] at h; subst h
      exact ⟨_, .bvar hb, ht⟩
    | fvar hf => exact whnf_fvar hloc ih' hf ht h
    | sort hl =>
      simp only [Pure.whnf, pure, Except.pure, Except.ok.injEq] at h; subst h
      exact ⟨_, .sort hl, ht⟩
    | const hB hls => exact whnf_const henv hE hsub hΓ ih' hB hls ht h
    | special hB hs hlen hargs hsat => exact whnf_spineSpecial henv hE hsub hΓ ih' hB hs hlen hargs hsat ht h
    | app _ hg ha => exact whnf_app henv hE hsub hΓ ih' hg ha ht h
    | lam hA hb =>
      simp only [Pure.whnf, pure, Except.pure, Except.ok.injEq] at h; subst h
      exact ⟨_, .lam hA hb, ht⟩
    | forallE hA hb =>
      simp only [Pure.whnf, pure, Except.pure, Except.ok.injEq] at h; subst h
      exact ⟨_, .forallE hA hb, ht⟩
    | letE _ hv hb => exact whnf_letE henv hE hΓ ih' hv hb ht h
    | mdata he' =>
      simp only [Pure.whnf] at h
      exact ih he' ht h
    | lit hB h₀ h₁ =>
      simp only [Pure.whnf, pure, Except.pure, Except.ok.injEq] at h; subst h
      exact ⟨_, .lit hB h₀ h₁, ht⟩
    | projStruct hst hi hBS hs hty => exact whnf_projStruct henv hE hsub hΓ ih' hst hi hBS hs hty ht h
    | projProof hi0 hBS hss hcc hnr hi hns hs hty =>
      exact whnf_projProof henv hE hsub hΓ ih' hi0 hcc hnr hi hs ht
        (fun _ hw => hw ▸ .projProof hi0 hBS hss hcc hnr hi hns hs hty) h

end EraseProof
