import EraseProof.Core.StepsCtor

/-!
# Steps of the shipping core's correctness: projections and literals

The step of `visitExpr` on a projection `proj S i b` that the oracle keeps
(`visitExpr_proj_step`): `visitProj` registers `S` (`register_inductive_spec`) and returns the λ□
projection of the erased major premise at the field index among the kept fields, which is `i`
since every field is kept (`KeepMasks`). The oracle types a projection only for an inductive of
one constructor with more than `i` fields (`proj_oracle`), so the index is `i` and `S`, which the
fragment test admits only in `Prop`, with a never-zero sort, or not eliminated
(`PhaseIDecl`), is in `Prop` or has a never-zero sort (`Erases.proj`).

The step on a literal that the oracle keeps (`visitExpr_lit_step`): under `nat := .peano` (the
marking's `litZero`, `litSucc`), `visitLiteral` erases `0` as `visitConstructor` on ``Nat.zero``
and `k + 1` as ``Nat.succ`` applied to the literal `k` (`visitConstructor_spec`,
`Erases.ctor_inv`), the constructors `0` and `1` of `Nat` (`NatCtors`, `NatShaped`):
`Erases.litZero`, `Erases.litSucc`. Machine
integers (`nat := .machine`) and string literals have no marking that the oracle keeps.

Reference: the `tProj` case of `erases_erase` (`MR E/ErasureFunction.v:1228`), rule
`erases_tProj` (`MR E/Extract.v:118`); literals: none (PCUIC has no literals). Adapted from
`ML-V Core/StepsCtor.lean:209-224, 910-1033, 1198-1303`, whose typing premises are replaced by the
marking and by the oracle's own checks.
-/

open Lean Erasure

namespace EraseProof

namespace Steps

open RegisterInd OracleRen StateLemmas Decls

/-! ## What the oracle's type of a projection reads -/

/-- `T` binds `n` `Π`s (through metadata) over an application of the constant `S`. -/
def HeadTele (S : Name) : Nat → Expr → Prop
  | 0, e => appHeadConst e = some S
  | n + 1, .forallE _ _ b _ => HeadTele S n b
  | n + 1, .mdata _ e => HeadTele S (n + 1) e
  | _ + 1, _ => False

theorem headTele_zero {S : Name} {T : Expr} : HeadTele S 0 T ↔ appHeadConst T = some S := by
  cases T <;> exact Iff.rfl

/-- The shape `blockShapeOK` checks of a constructor's type is a `HeadTele`. -/
theorem headTele_of {S : Name} {T : Expr} : ∀ {n : Nat}, piLen T = n →
    appHeadConst (piResult n T) = some S → HeadTele S n T := by
  induction T with
  | forallE _ _ b _ _ ihb =>
    intro n h1 h2
    subst h1
    exact ihb rfl (by simpa [piLen, piResult] using h2)
  | mdata _ e ih =>
    intro n h1 h2
    cases n with
    | zero =>
      have := ih h1 (by simpa [piResult] using h2)
      exact headTele_zero.2 (by simpa [appHeadConst] using headTele_zero.1 this)
    | succ m => exact ih h1 (by simpa [piResult] using h2)
  | _ =>
    intro n h1 h2
    simp only [piLen] at h1
    subst h1
    exact headTele_zero.2 (by simpa [piResult] using h2)

theorem appHeadConst_instLevels (ps : List Name) (us : List Level) :
    ∀ e : Expr, appHeadConst (Pure.instLevels ps us e) = appHeadConst e
  | .app f _ => by simp only [Pure.instLevels, appHeadConst]; exact appHeadConst_instLevels ps us f
  | .mdata _ e => by simp only [Pure.instLevels, appHeadConst]; exact appHeadConst_instLevels ps us e
  | .const .. | .sort _ | .bvar _ | .fvar _ | .mvar _ | .lit _ | .lam .. | .forallE ..
  | .letE .. | .proj .. => rfl

theorem appHeadConst_inst {S : Name} (a : Expr) :
    ∀ {e : Expr} {d : Nat}, appHeadConst e = some S → appHeadConst (e.instantiate1' a d) = some S
  | .app f _, d, h => by
    simp only [Expr.instantiate1', appHeadConst] at h ⊢; exact appHeadConst_inst a h
  | .mdata _ e, d, h => by
    simp only [Expr.instantiate1', appHeadConst] at h ⊢; exact appHeadConst_inst a h
  | .const .., _, h => h
  | .bvar _, _, h | .sort _, _, h | .fvar _, _, h | .mvar _, _, h | .lit _, _, h | .lam .., _, h
  | .forallE .., _, h | .letE .., _, h | .proj .., _, h => by simp [appHeadConst] at h

theorem HeadTele.instLevels {S : Name} (ps : List Name) (us : List Level) {T : Expr} :
    ∀ {n : Nat}, HeadTele S n T → HeadTele S n (Pure.instLevels ps us T) := by
  induction T with
  | forallE _ _ b _ _ ihb =>
    intro n h
    cases n with
    | zero => exact absurd (headTele_zero.1 h) (by simp [appHeadConst])
    | succ m => exact ihb (n := m) h
  | mdata _ e ih =>
    intro n h
    cases n with
    | zero =>
      exact headTele_zero.2 (by
        rw [appHeadConst_instLevels]; exact headTele_zero.1 h)
    | succ m => exact ih (n := m + 1) h
  | _ =>
    intro n h
    cases n with
    | zero => exact headTele_zero.2 (by rw [appHeadConst_instLevels]; exact headTele_zero.1 h)
    | succ m => exact h.elim

theorem HeadTele.inst {S : Name} (a : Expr) {T : Expr} :
    ∀ {n d : Nat}, HeadTele S n T → HeadTele S n (T.instantiate1' a d) := by
  induction T with
  | forallE _ _ b _ _ ihb =>
    intro n d h
    cases n with
    | zero => exact headTele_zero.2 (appHeadConst_inst a (headTele_zero.1 h))
    | succ m => exact ihb (n := m) h
  | mdata _ e ih =>
    intro n d h
    cases n with
    | zero => exact headTele_zero.2 (appHeadConst_inst a (headTele_zero.1 h))
    | succ m => exact ih (n := m + 1) h
  | _ =>
    intro n d h
    cases n with
    | zero => exact headTele_zero.2 (appHeadConst_inst a (headTele_zero.1 h))
    | succ m => exact h.elim

/-- `whnf` of a telescope with a leading `Π` is that `Π`. -/
theorem whnf_headTele_succ {cx : Pure.Ctx} {ls : List Local} {S : Name} {n : Nat} :
    ∀ {f : Nat} {T W : Expr}, HeadTele S (n + 1) T → Pure.whnf cx f ls T = .ok W →
      ∃ y D b bi, W = .forallE y D b bi ∧ HeadTele S n b
  | 0, _, _, _, h => absurd h throw_ne_ok
  | f + 1, .forallE y D b bi, W, hT, h => by
    simp only [Pure.whnf, pure, Except.pure, Except.ok.injEq] at h
    exact ⟨y, D, b, bi, h.symm, hT⟩
  | f + 1, .mdata _ e, W, hT, h => by
    simp only [Pure.whnf] at h
    exact whnf_headTele_succ (T := e) hT h
  | _ + 1, .bvar _, _, hT, _ | _ + 1, .fvar _, _, hT, _ | _ + 1, .mvar _, _, hT, _
  | _ + 1, .sort _, _, hT, _ | _ + 1, .const .., _, hT, _ | _ + 1, .app .., _, hT, _
  | _ + 1, .lam .., _, hT, _ | _ + 1, .letE .., _, hT, _ | _ + 1, .lit _, _, hT, _
  | _ + 1, .proj .., _, hT, _ => hT.elim

/-- The head constant of a spine whose `spine` head is a constant. -/
theorem appHeadConst_of_spine {r : Name} {us : List Level} :
    ∀ {e : Expr}, (spine e).1 = .const r us → appHeadConst e = some r
  | .app f a, h => by
    have h1 : (spine (.app f a)).1 = (spine f).1 := by
      simp only [spine]
    simp only [appHeadConst]
    exact appHeadConst_of_spine (h1 ▸ h)
  | .const .., h => by
    simp only [spine, Expr.const.injEq] at h; simp [appHeadConst, h.1]
  | .bvar _, h | .fvar _, h | .mvar _, h | .sort _, h | .lam .., h
  | .forallE .., h | .letE .., h | .lit _, h | .mdata .., h | .proj .., h => by
    simp [spine] at h

/-- `whnf` keeps an application of an inductive type: neither δ nor ι applies to it. -/
theorem whnf_headInd {cx : Pure.Ctx} {ls : List Local} {S : Name} {I : InductiveVal}
    (hS : findConst cx.decls S = some (.inductInfo I)) :
    ∀ {f : Nat} {T W : Expr}, appHeadConst T = some S → Pure.whnf cx f ls T = .ok W →
      appHeadConst W = some S
  | 0, _, _, _, h => absurd h throw_ne_ok
  | f + 1, .app g a, W, hT, h => by
    simp only [appHeadConst] at hT
    simp only [Pure.whnf] at h
    obtain ⟨g', hg', h⟩ := ok_of_bind h
    have hg'S := whnf_headInd hS hT hg'
    split at h
    · simp [appHeadConst] at hg'S
    · split at h
      · rename_i r us rv minors args hia
        have := appHeadConst_of_spine (congrArg Prod.fst (iotaApp?_spine hia))
        simp only [appHeadConst] at this
        rw [hg'S] at this
        cases this
        unfold Pure.iotaApp? at hia
        split at hia
        · rename_i r' us' args' hsp
          have := appHeadConst_of_spine (congrArg Prod.fst hsp)
          simp only [appHeadConst, hg'S, Option.some.injEq] at this
          subst this
          rw [hS] at hia
          cases hia
        · cases hia
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact hg'S
  | f + 1, .mdata _ e, W, hT, h => by
    simp only [Pure.whnf] at h
    exact whnf_headInd hS (T := e) hT h
  | f + 1, .const c us, W, hT, h => by
    simp only [appHeadConst, Option.some.injEq] at hT
    subst hT
    simp only [Pure.whnf, hS, pure, Except.pure, Except.ok.injEq] at h
    subst h
    rfl
  | _ + 1, .bvar _, _, hT, _ | _ + 1, .fvar _, _, hT, _ | _ + 1, .mvar _, _, hT, _
  | _ + 1, .sort _, _, hT, _ | _ + 1, .lam .., _, hT, _ | _ + 1, .forallE .., _, hT, _
  | _ + 1, .letE .., _, hT, _ | _ + 1, .lit _, _, hT, _ | _ + 1, .proj .., _, hT, _ => by
    simp [appHeadConst] at hT

/-- `instForalls` on a telescope of an inductive type consumes one `Π` per argument. -/
theorem instForalls_headTele {cx : Pure.Ctx} {f : Nat} {ls : List Local} {S : Name}
    {I : InductiveVal} (hS : findConst cx.decls S = some (.inductInfo I)) :
    ∀ (as : List Expr) {n : Nat} {r W : Expr}, HeadTele S n r →
      Pure.instForalls cx f ls r as = .ok W → as.length ≤ n ∧ HeadTele S (n - as.length) W
  | [], n, r, W, hr, h => by
    simp only [Pure.instForalls, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨Nat.zero_le _, by simpa using hr⟩
  | a :: as, n, r, W, hr, h => by
    simp only [Pure.instForalls] at h
    obtain ⟨w, hw, h⟩ := ok_of_bind h
    cases n with
    | zero =>
      have hw' := whnf_headInd hS (headTele_zero.1 hr) hw
      cases w with
      | forallE => simp [appHeadConst] at hw'
      | _ => exact absurd h throw_ne_ok
    | succ m =>
      obtain ⟨y, D, b, bi, rfl, hb⟩ := whnf_headTele_succ hr hw
      obtain ⟨h1, h2⟩ := instForalls_headTele hS as (HeadTele.inst a (d := 0) hb) h
      exact ⟨by simp only [List.length_cons]; omega, by simpa using h2⟩

/-- `instProjs` on a telescope of an inductive type consumes one `Π` per field. -/
theorem instProjs_headTele {cx : Pure.Ctx} {f : Nat} {ls : List Local} {S S' : Name}
    {I : InductiveVal} {s : Expr} (hS : findConst cx.decls S = some (.inductInfo I)) :
    ∀ (k j : Nat) {n : Nat} {r W : Expr}, HeadTele S n r →
      Pure.instProjs cx f ls S' s k j r = .ok W → k ≤ n ∧ HeadTele S (n - k) W
  | 0, j, n, r, W, hr, h => by
    simp only [Pure.instProjs, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨Nat.zero_le _, by simpa using hr⟩
  | k + 1, j, n, r, W, hr, h => by
    simp only [Pure.instProjs] at h
    obtain ⟨w, hw, h⟩ := ok_of_bind h
    cases n with
    | zero =>
      have hw' := whnf_headInd hS (headTele_zero.1 hr) hw
      cases w with
      | forallE => simp [appHeadConst] at hw'
      | _ => exact absurd h throw_ne_ok
    | succ m =>
      obtain ⟨y, D, b, bi, rfl, hb⟩ := whnf_headTele_succ hr hw
      obtain ⟨h1, h2⟩ := instProjs_headTele hS k (j + 1) (HeadTele.inst _ (d := 0) hb) h
      exact ⟨by omega, by simpa using h2⟩

/-- The oracle's type of a projection `proj S i s` (`Erasure.Pure.inferType`, after `inferProjType`
of Lean): `S` is an inductive of one constructor, which has more than `i` fields, when its
constructor's type binds the parameters and the fields over an application of `S`
(`blockShapeOK`): `instForalls` consumes the parameters, `instProjs` the fields before `i`, and
`whnf` does not unfold an application of `S`. Reference: `infer` on `tProj`
(`MR S/PCUICSafeRetyping.v:350`), which reads `declared_projection`. -/
theorem inferType_proj {cx : Pure.Ctx} {f : Nat} {ls : List Local} {Γ : List Expr} {S : Name}
    {i : Nat} {s T : Expr}
    (hsh : ∀ I, findConst cx.decls S = some (.inductInfo I) → ∀ cn ∈ I.ctors, ∀ cv,
      findConst cx.decls cn = some (.ctorInfo cv) → HeadTele S (I.numParams + cv.numFields) cv.type)
    (h : Pure.inferType cx (f + 1) ls Γ (.proj S i s) = .ok T) :
    ∃ I cn cv, findConst cx.decls S = some (.inductInfo I) ∧ I.ctors = [cn] ∧
      findConst cx.decls cn = some (.ctorInfo cv) ∧ i < cv.numFields := by
  simp only [Pure.inferType] at h
  obtain ⟨T₀, -, h⟩ := ok_of_bind h
  obtain ⟨W, -, h⟩ := ok_of_bind h
  split at h
  rotate_left
  · exact absurd h throw_ne_ok
  rename_i S' us args hsp
  split at h
  rotate_left
  · exact absurd h throw_ne_ok
  rename_i I R hSS hfS hfR
  split at h
  · obtain ⟨_, h1, -⟩ := ok_of_bind h
    exact absurd h1 throw_ne_ok
  split at h
  rotate_left
  · exact absurd h throw_ne_ok
  rename_i cn hct hlen
  split at h
  rotate_left
  · exact absurd h throw_ne_ok
  rename_i ci cv hci
  split at h
  rotate_left
  · obtain ⟨_, h1, -⟩ := ok_of_bind h
    exact absurd h1 throw_ne_ok
  obtain ⟨r, hr, h⟩ := ok_of_bind h
  obtain ⟨r', hr', h⟩ := ok_of_bind h
  obtain ⟨w, hw, h⟩ := ok_of_bind h
  have hT := HeadTele.instLevels (ConstantInfo.ctorInfo cv).levelParams us
    (hsh I hfS cn (by rw [hct]; exact List.mem_singleton_self _) cv hci)
  have hlen' : args.length = I.numParams + I.numIndices := by simpa using hlen
  obtain ⟨-, h2⟩ := instForalls_headTele hfS _ hT hr
  rw [List.length_take, show min I.numParams args.length = I.numParams by omega,
    Nat.add_sub_cancel_left] at h2
  obtain ⟨-, h3⟩ := instProjs_headTele hfS i 0 h2 hr'
  refine ⟨I, cn, cv, hfS, hct, hci, Nat.lt_of_not_le fun hge => ?_⟩
  rw [show cv.numFields - i = 0 by omega] at h3
  have hw' := whnf_headInd hfS (headTele_zero.1 h3) hw
  cases w with
  | forallE => simp [appHeadConst] at hw'
  | _ => exact absurd h throw_ne_ok

/-- A projection that the oracle answers on (`Erasure.Pure.isErasable` at `oracleFuel`) is typed
by `inferType_proj`. -/
theorem isErasable_proj {cx : Pure.Ctx} {ls : List Local} {S : Name} {i : Nat} {s : Expr}
    {b : Bool}
    (hsh : ∀ I, findConst cx.decls S = some (.inductInfo I) → ∀ cn ∈ I.ctors, ∀ cv,
      findConst cx.decls cn = some (.ctorInfo cv) → HeadTele S (I.numParams + cv.numFields) cv.type)
    (h : Pure.isErasable cx oracleFuel ls (.proj S i s) = .ok b) :
    ∃ I cn cv, findConst cx.decls S = some (.inductInfo I) ∧ I.ctors = [cn] ∧
      findConst cx.decls cn = some (.ctorInfo cv) ∧ i < cv.numFields := by
  unfold Pure.isErasable at h
  simp only [spine] at h
  obtain ⟨T, hT, -⟩ := ok_of_bind h
  rw [show oracleFuel = 1048575 + 1 from rfl] at hT
  exact inferType_proj hsh hT

/-! ## The projection step -/

/-- Copy of `ML-V Core/StepsCtor.lean:209`. -/
theorem count_keep_replicate :
    ∀ n, List.count ConstructorArgRelevance.keep (List.replicate n .keep) = n
  | 0 => rfl
  | n + 1 => by rw [List.replicate_succ, List.count_cons, count_keep_replicate n]; rfl

/-- The kept fields among the first `i` of a mask that keeps all `N ≥ i` fields: `i`. Copy of
`ML-V Core/StepsCtor.lean:215`. -/
theorem count_keep_slice {N i : Nat} (h : i ≤ N) :
    Array.count ConstructorArgRelevance.keep
      (Std.Slice.toArray ((Array.replicate N ConstructorArgRelevance.keep).toSubarray 0 i)) = i := by
  rw [← Subarray.toArray_eq_sliceToArray, ← Subarray.toArray_toList, ← Array.count_toList,
    Subarray.toList_eq, Array.array_toSubarray]
  simp
  rw [count_keep_replicate]
  omega

section
variable {decls : List ConstantInfo} {view : EnvView} {cfg : ErasureConfig}

/-- The constructor types of the closure have the shape `inferType_proj` reads. -/
theorem CoreEnv.projShape (hG : CoreEnv view cfg decls) (S : Name) :
    ∀ I, findConst decls S = some (.inductInfo I) → ∀ cn ∈ I.ctors, ∀ cv,
      findConst decls cn = some (.ctorInfo cv) → HeadTele S (I.numParams + cv.numFields) cv.type :=
  fun I hI cn hcn cv hcv =>
    have h := hG.ctorShape S I hI cn hcn cv hcv
    headTele_of h.1 h.2

/-- A marking of a projection that the oracle keeps marks the major premise, of an inductive of
the closure. -/
theorem MarkOf.proj_inv {ls : List Local} {S : Name} {i : Nat} {e ê : Expr}
    (h : MarkOf decls cfg ls (.proj S i e) ê) (hf : oracle decls ls (.proj S i e) = .ok false) :
    ∃ iv eM, findDecl decls S = some (.inductInfo iv) ∧ MarkOf decls cfg ls e eM ∧
      ê = .proj S i eM := by
  generalize hx : Expr.proj S i e = e' at h hf
  cases h with
  | erase h₁ => rw [h₁] at hf; cases hf
  | proj _ h₂ h₃ => cases hx; exact ⟨_, _, h₂, h₃, rfl⟩
  | app _ hne => exact absurd hx (ne_mkAppN rfl hne)
  | constApp | special => exact absurd hx (ne_mkAppN_const rfl nofun)
  | _ => cases hx

/-- The `proj` step, from `visitExpr` at the fuels up to `fuel`: a projection `proj S i b` that the
oracle keeps is of an inductive `S` of one constructor with more than `i` fields
(`isErasable_proj`); `visitProj` registers `S` (`register_inductive_spec`), keeps every field
(`KeepMasks`), so that the field index among the kept fields is `i`, and erases the major premise;
`S` is in `Prop` or has a never-zero sort, since the fragment test admits a sort that may be zero
only for a type that is not eliminated (`PhaseIDecl`), and a projection eliminates. Adapted from
`ML-V Core/StepsCtor.lean:910 stepsB_proj`, whose typing premises are replaced by the marking and
the oracle's type. Reference: the `tProj` case of `erases_erase` (`MR E/ErasureFunction.v:1228`),
rule `erases_tProj` (`MR E/Extract.v:118`). -/
theorem visitExpr_proj_step (hG : CoreEnv view cfg decls) {fuel : Nat}
    (ih : StepIH view cfg decls fuel) {s : Name} {i : Nat} {b : Expr} :
    ExprSpec view cfg decls (fuel + 1) (.proj s i b) := by
  intro ρ S ls Sc ê st tc ps r st' ps' hctx hR he hsc hocc hnp hrs hok hm hrun
  simp only [renFV] at hrun
  rw [visitExpr] at hrun
  rcases oracle_run hrun with ⟨hor, rfl, rfl, rfl⟩ | ⟨hor, hrun⟩
  · exact visitExpr_box hG.closed hR he hok hm hor
  have hor' := oracle_agree (e := .proj s i b) hG.closed hR he hor
  obtain ⟨I, bM, hiv, hbM, rfl⟩ := MarkOf.proj_inv hm hor'
  obtain ⟨I', cn, cv, hI, hct, hcn, hlt⟩ :=
    isErasable_proj (cx := ⟨decls⟩) (hG.projShape s) hor'
  obtain rfl : I' = I := by
    have h1 : findDecl decls s = some (.inductInfo I') := hI
    rw [hiv] at h1; cases h1; rfl
  have hmem : ConstantInfo.inductInfo I' ∈ decls := (findDecl_eq_some hiv).1
  cases fuel with
  | zero => rw [visitProj] at hrun; cases hrun
  | succ k =>
  rw [visitProj, runPure_bind] at hrun
  obtain ⟨⟨⟨ci, st₁⟩, ps₁⟩, hci, hrun⟩ := ok_of_bind hrun
  obtain ⟨hfc, h1, h2⟩ := getConst_run hci
  subst st₁ ps₁
  obtain rfl : ci = .inductInfo I' := by
    have h1 : findDecl decls s = some ci := hfc
    rw [hiv] at h1; cases h1; rfl
  dsimp only at hrun
  rw [runPure_bind] at hrun
  obtain ⟨⟨⟨rr, st₁⟩, ps₁⟩, hreg, hrun⟩ := ok_of_bind hrun
  obtain ⟨hok₁, hext₁, hcst₁, hiid, hind₁, hkm, hps⟩ := register_inductive_spec hG hctx hok hiv hreg
  subst ps₁
  dsimp only at hrun
  rw [runPure_bind] at hrun
  obtain ⟨⟨⟨mask, st₂⟩, ps₂⟩, hmask, hrun⟩ := ok_of_bind hrun
  obtain ⟨hmk, h1, h2⟩ := getOrFail_run hmask
  subst st₂ ps₂
  dsimp only at hrun
  rw [runPure_bind] at hrun
  obtain ⟨⟨⟨rb, st₃⟩, ps₃⟩, hb, hrun⟩ := ok_of_bind hrun
  cases hrun
  -- every field is kept
  have hmask' : mask = Array.replicate cv.numFields .keep := by
    have := hkm.2 0 cn cv (by rw [hct]; rfl) hcn
    rw [hmk] at this
    cases this; rfl
  have hcount : Array.count ConstructorArgRelevance.keep
      (Std.Slice.toArray (mask.toSubarray 0 i)) = i := by
    rw [hmask']; exact count_keep_slice (Nat.le_of_lt hlt)
  -- the major premise
  have ⟨her, hc0, hdeps, hgr⟩ := ih.expr k (Nat.le_succ k) b hctx hR he hsc
    (fun d hd => hocc d hd) hnp hrs.2 hok₁ hbM hb
  -- the sort of `S`
  have hsort : (evalEnvOf view cfg decls).propInd s = true ∨
      ∃ n u, arityShape I'.type = some (n, u) ∧ u.isNeverZero = true := by
    obtain ⟨-, -, ⟨n, u, har, hu⟩, -⟩ := hG.phase _ hmem
    rcases hu with rfl | hnz | ⟨-, hnel⟩
    · left; simp [EvalEnv.propInd, evalEnvOf, hiv, har, EvidentZero]
    · exact .inr ⟨n, u, har, hnz⟩
    · exact absurd (.inr ⟨cn, cv, hct, hcn, by omega⟩) hnel
  have hind : ErasesInd (evalEnvOf view cfg decls) st₃.gdecls s := ErasesInd.ext hgr.ext hind₁
  simp only [renFV]
  rw [hcount]
  refine ⟨.proj hiid hiv hsort her, hc0, .proj hiid hind hdeps,
    Grows.trans ⟨hok₁, hext₁, Nat.le_refl _, ?_⟩ hgr⟩
  intro c' kn h1 h2
  rw [hcst₁, h1] at h2
  cases h2

end

/-! ## The literal step -/

section
variable {decls : List ConstantInfo} {view : EnvView} {cfg : ErasureConfig}

/-- A successful run of `visitConstructor` is on a constructor of the closure. Copy of
`ML-V Core/StepsCtor.lean:1209`. -/
theorem visitConstructor_ctor {j : Nat} {c : Name} {args : Array Expr} {tc : TravCtx}
    {st st' : ErasureState} {ps ps' : PureState} {r : LBTerm}
    (h : (visitConstructor (m := PureM) (j + 1) c args).runPure st tc ⟨decls, view⟩ ps =
      .ok ((r, st'), ps')) : ∃ cv, findDecl decls c = some (.ctorInfo cv) := by
  rw [visitConstructor, runPure_bind] at h
  obtain ⟨⟨⟨ci, st₁⟩, ps₁⟩, hci, h⟩ := ok_of_bind h
  obtain ⟨hfc, -, -⟩ := getConst_run hci
  cases ci with
  | ctorInfo cv => exact ⟨cv, hfc⟩
  | _ => dsimp only at h; cases h

/-- The constructors ``Nat.zero`` and ``Nat.succ`` of the closure have no parameter and `0` and
`1` fields, of `Nat`, which is not declared in `Prop` (`NatShaped`, `NatCtors`, `CtorsListed`). -/
theorem natCtor_counts (hG : CoreEnv view cfg decls) {c : Name} {cv : ConstructorVal}
    (hc : findDecl decls c = some (.ctorInfo cv)) (hind : cv.induct = ``Nat) (hj : cv.cidx < 2) :
    cv.numParams = 0 ∧ cv.numFields = cv.cidx ∧
      (evalEnvOf view cfg decls).propInd cv.induct = false := by
  obtain ⟨iv, hiv, hpos, hnp⟩ := hG.ctors c cv hc
  rw [hind] at hiv
  obtain ⟨hnp0, hnprop, z, s, hzs, hz, hs⟩ := hG.natShaped iv hiv
  refine ⟨by omega, ?_, by rw [hind]; exact hnprop⟩
  rw [hzs] at hpos
  have hcf : ctorFields (evalEnvOf view cfg decls) c = some cv.numFields := by
    simp [ctorFields, evalEnvOf, hc]
  rcases (show cv.cidx = 0 ∨ cv.cidx = 1 by omega) with h | h <;> rw [h] at hpos ⊢ <;>
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at hpos <;>
    subst hpos
  · rw [hz] at hcf; exact (Option.some.inj hcf).symm
  · rw [hs] at hcf; exact (Option.some.inj hcf).symm

/-- A marking of a literal that the oracle keeps is the literal, under `nat := .peano`: `0`, or
`k + 1` below `peanoMaxLiteral` with a marking of `k`. -/
theorem MarkOf.lit_inv {ls : List Local} {l : Literal} {ê : Expr}
    (h : MarkOf decls cfg ls (.lit l) ê) (hf : oracle decls ls (.lit l) = .ok false) :
    ê = .lit l ∧ cfg.nat = .peano ∧ (l = .natVal 0 ∨ ∃ k, l = .natVal (k + 1) ∧
      k + 1 ≤ peanoMaxLiteral ∧ MarkOf decls cfg ls (.lit (.natVal k)) (.lit (.natVal k))) := by
  generalize hx : Expr.lit l = e' at h hf
  cases h with
  | erase h₁ => rw [h₁] at hf; cases hf
  | litZero _ hp => cases hx; exact ⟨rfl, hp, .inl rfl⟩
  | litSucc _ hp hk hm => cases hx; exact ⟨rfl, hp, .inr ⟨_, rfl, hk, hm⟩⟩
  | app _ hne => exact absurd hx (ne_mkAppN rfl hne)
  | constApp | special => exact absurd hx (ne_mkAppN_const rfl nofun)
  | _ => cases hx

/-- The `lit` step, from `visitExpr` at the fuels up to `fuel`: a literal that the oracle keeps is
marked only under `nat := .peano` (`MarkOf.lit_inv`); `visitLiteral` erases `0` as
`visitConstructor` on ``Nat.zero`` and `k + 1` as ``Nat.succ`` applied to the literal `k`, below
`peanoMaxLiteral` (`visitConstructor_spec`, `Erases.ctor_inv`); these are the constructors `0` and
`1` of `Nat`, with no parameter and `0` and `1` fields (`natCtor_counts`): `Erases.litZero`,
`Erases.litSucc`. Adapted from `ML-V Core/StepsCtor.lean:1226 stepsB_lit_of`, with `NatCtors`
and `NatShaped` for `ML-V`'s `NatCtorNames`. Reference: none (PCUIC has no literals;
`visitLiteral`, `LeanToLambdaBox/Erasure.lean:872`). -/
theorem visitExpr_lit_step (hG : CoreEnv view cfg decls) {fuel : Nat}
    (ih : StepIH view cfg decls fuel) {l : Literal} :
    ExprSpec view cfg decls (fuel + 1) (.lit l) := by
  intro ρ S ls Sc ê st tc ps r st' ps' hctx hR he hsc hocc hnp hrs hok hm hrun
  simp only [renFV] at hrun
  rw [visitExpr] at hrun
  rcases oracle_run hrun with ⟨hor, rfl, rfl, rfl⟩ | ⟨hor, hrun⟩
  · exact visitExpr_box hG.closed hR he hok hm hor
  obtain ⟨rfl, hpeano, hl⟩ := MarkOf.lit_inv hm (oracle_agree (e := .lit l) hG.closed hR he hor)
  simp only [renFV]
  have hnat : cfg.nat = .machine → ∀ c : Name, c ≠ ``Nat.zero ∧ c ≠ ``Nat.succ := fun h => by
    rw [hpeano] at h; cases h
  cases fuel with
  | zero => rw [visitLiteral] at hrun; cases hrun
  | succ f =>
  rw [visitLiteral, runPure_read_bind, hctx.config, hpeano] at hrun
  rcases hl with rfl | ⟨k, rfl, hk, hmk⟩
  · -- `0` is `Nat.zero`
    dsimp only at hrun
    rw [ite_eq_right (show ¬ (0 > peanoMaxLiteral) by omega), ite_eq_left rfl] at hrun
    cases f with
    | zero => rw [visitConstructor] at hrun; cases hrun
    | succ g =>
    obtain ⟨cv, hcv⟩ := visitConstructor_ctor hrun
    obtain ⟨hind, hcidx⟩ := hG.natCtors.1 cv hcv
    obtain ⟨hnp0, hnf0, hnprop⟩ := natCtor_counts hG hcv hind (by omega)
    have ⟨her, hc0, hdeps, hgr⟩ := visitConstructor_spec hG (fun m _ => ih.expr m (by omega))
      (ρ := ρ) (us := []) (as := []) (âs := []) hctx hsc hR (fun _ h => nomatch h) rfl
      (fun _ _ _ h => nomatch h) hcv (by simp only [List.length_nil]; omega) hnprop (hnat · _) hok
      hrun
    simp only [renFV_mkAppN, renFV, List.map_nil] at her
    obtain ⟨iid, as', hiid, rfl, hlen, -, -, -⟩ := Erases.ctor_inv hcv her
    obtain rfl : as' = [] := List.eq_nil_of_length_eq_zero hlen.symm
    rw [hind] at hiid
    rw [hcidx] at hc0 hdeps ⊢
    exact ⟨.litZero hiid, hc0, hdeps, hgr⟩
  · -- `k + 1` is `Nat.succ` applied to `k`
    dsimp only at hrun
    rw [ite_eq_right (show ¬ (k + 1 > peanoMaxLiteral) by omega), ite_eq_right (Nat.succ_ne_zero k),
      Nat.add_sub_cancel] at hrun
    cases f with
    | zero => rw [visitConstructor] at hrun; cases hrun
    | succ g =>
    obtain ⟨cv, hcv⟩ := visitConstructor_ctor hrun
    obtain ⟨hind, hcidx⟩ := hG.natCtors.2 cv hcv
    obtain ⟨hnp0, hnf1, hnprop⟩ := natCtor_counts hG hcv hind (by omega)
    have ⟨her, hc0, hdeps, hgr⟩ := visitConstructor_spec hG (fun m _ => ih.expr m (by omega))
      (ρ := ρ) (us := []) (as := [.lit (.natVal k)]) (âs := [.lit (.natVal k)]) hctx hsc hR
      (fun a ha => by
        rw [List.mem_singleton.1 ha]
        exact ⟨trivial, ⟨fun _ h => by simp [nameOccurs] at h, ⟨hpeano, trivial⟩⟩⟩)
      rfl
      (fun i a â h1 h2 => by
        cases i with
        | zero => cases h1; cases h2; exact hmk
        | succ i => simp at h1)
      hcv (by simp only [List.length_cons, List.length_nil]; omega) hnprop (hnat · _) hok hrun
    simp only [renFV_mkAppN, renFV, List.map_cons, List.map_nil] at her
    obtain ⟨iid, as', hiid, rfl, hlen, hers, -, -⟩ := Erases.ctor_inv hcv her
    obtain ⟨t, rfl⟩ := List.length_eq_one_iff.mp hlen.symm
    rw [hind] at hiid
    rw [hcidx] at hc0 hdeps ⊢
    exact ⟨.litSucc hiid (hers 0 _ _ rfl rfl), hc0, hdeps, hgr⟩

end

end Steps

end EraseProof
