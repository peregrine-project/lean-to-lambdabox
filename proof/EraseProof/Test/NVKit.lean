import EraseProof.Spec
import EraseProof.Test.Run

/-!
# Tools of the non-vacuity instances NV-3 and NV-4

con-leche's forms of Lean terms (`cl`, `cv`), and the certificates of `Spec.lean` that are
existential over con-leche's results (`CLTyped`, `CLTypedAt`, `CLErasable`, `CLProofTerm`,
`CLCert`, `CLCertProof`) from a run of con-leche's checker that succeeds (`inferOk`, `certOk`): the
kernel evaluates the run (`krfl`, `Test/Run.lean`), and the witnesses are its results. A
declaration without an `_unsafe_rec` companion has no compiled pre-definition (`preDef_none'`).
Reference: none.
-/

open Lean Erasure

namespace EraseProof.Test

/-- con-leche's form of a term (`toCL?`; the bound variable `0` if it has none). -/
def cl (e : Expr) : ConLeche.Expr := (toCL? e).getD (.bvar 0)

/-- con-leche's record of a constant's name, level parameters and type. -/
def cv (n : Name) (lps : List Name) (t : Expr) : ConLeche.ConstantVal :=
  ⟨Name.toCL n, lps.map Name.toCL, cl t⟩

/-- con-leche's full-grade inference at fuel `F` and depth `d` infers a type for `c`. -/
def inferOkCL (env : ConLeche.Env) (F d : Nat) (c : ConLeche.Expr) : Bool :=
  (ConLeche.inferTypeCore .verified false env F d c) matches .ok _

/-- con-leche's record of a declaration's name, level parameters and type. -/
def cvC (ci : ConstantInfo) : ConLeche.ConstantVal := cv ci.name ci.levelParams ci.type

/-- con-leche's inference at fuel `F` infers a type for the closed term `t`. -/
def inferOk (env : ConLeche.Env) (F : Nat) (t : Expr) : Bool :=
  match toCL? t with
  | some c => inferOkCL env F 0 c
  | none => false

/-- `CLProof` as a computation. -/
def proofOk (env : ConLeche.Env) (F d : Nat) (T : ConLeche.Expr) : Bool :=
  match ConLeche.inferTypeCore .verified false env F d T with
  | .ok S => match ConLeche.whnf .verified false env F d S with
    | .ok (.sort u) => u.isAlwaysZero
    | _ => false
  | _ => false

/-- The verdict of `CLCert` (`proof`: the proof verdict only), as a computation. -/
def verdictOk (proof : Bool) (env : ConLeche.Env) (F d : Nat) (T : ConLeche.Expr) : Bool :=
  (!proof && CLFormer env F d F T) || proofOk env F d T

/-- `CLErasable` (`proof`: `CLProofTerm`) at fuel `F`, as a computation. -/
def erasableOk (proof : Bool) (env : ConLeche.Env) (F : Nat) (t : Expr) : Bool :=
  match toCL? t with
  | some c => match ConLeche.inferTypeCore .verified false env F 0 c with
    | .ok T => verdictOk proof env F 0 T
    | _ => false
  | none => false

/-- `CLCert` (`proof`: `CLCertProof`), as a computation. -/
def certOk (proof : Bool) (env : ConLeche.Env) (Γ : List CtxBinder) (s : Expr) : Bool :=
  match toCL? (lamTele Γ s) with
  | some c => inferOkCL env ConLeche.checkFuel 0 c && match openLams 0 Γ.length c with
    | some (d, c') => match ConLeche.inferTypeCore .verified false env ConLeche.checkFuel d c' with
      | .ok T => verdictOk proof env ConLeche.checkFuel d T
      | _ => false
    | none => false
  | none => false

variable {env : ConLeche.Env} {t : Expr}

theorem inferOkCL_spec {F d : Nat} {c : ConLeche.Expr} (h : inferOkCL env F d c = true) :
    ∃ T, ConLeche.inferTypeCore .verified false env F d c = .ok T := by
  unfold inferOkCL at h
  split at h
  · exact ⟨_, ‹_›⟩
  · cases h

theorem inferOk_congr {F : Nat} {t' : Expr} (h : toCL? t = toCL? t') :
    inferOk env F t = inferOk env F t' := by
  simp only [inferOk, h]

/-- `CLTyped` from a successful inference. -/
theorem typed_of (F : Nat) (h : inferOk env F t = true) : CLTyped env t := by
  unfold inferOk at h
  split at h
  · exact (inferOkCL_spec h).elim fun T hT => ⟨_, F, T, ‹_›, hT⟩
  · cases h

/-- `CLTypedAt` from a successful inference at `checkFuel`. -/
theorem typedAt_of (h : inferOk env ConLeche.checkFuel t = true) : CLTypedAt env t := by
  unfold inferOk at h
  split at h
  · exact (inferOkCL_spec h).elim fun T hT => ⟨_, T, ‹_›, hT⟩
  · cases h

/-- `CLOk` from two successful inferences. -/
theorem ok_of {F : Nat} (h : inferOk env F t = true) (h' : inferOk env F (unmark t) = true) :
    CLOk env t :=
  ⟨typed_of F h, typed_of F h'⟩

/-- `CLOk` of a term without marks from one successful inference. -/
theorem ok_clean {F : Nat} (h : inferOk env F t = true) (hu : unmark t = t) : CLOk env t :=
  ok_of h (by rw [hu]; exact h)

theorem proof_of {F d : Nat} {T : ConLeche.Expr} (h : proofOk env F d T = true) :
    CLProof env F d T := by
  unfold proofOk at h
  split at h
  · split at h
    · exact ⟨_, _, ‹_›, ‹_›, h⟩
    · cases h
  · cases h

theorem verdict_of {p : Bool} {F d : Nat} {T : ConLeche.Expr} (h : verdictOk p env F d T = true) :
    (p = false → CLVerdict env F d T) ∧ (p = true → CLProof env F d T) := by
  unfold verdictOk at h
  cases p
  · refine ⟨fun _ => ?_, fun h => (nomatch h)⟩
    rcases Bool.or_eq_true_iff.mp h with h | h
    · exact .inl (by simpa using h)
    · exact .inr (proof_of h)
  · exact ⟨fun h => (nomatch h), fun _ => proof_of (by simpa using h)⟩

theorem erasable_spec {p : Bool} {F : Nat} (h : erasableOk p env F t = true) :
    ∃ c T, toCL? t = some c ∧ ConLeche.inferTypeCore .verified false env F 0 c = .ok T ∧
      verdictOk p env F 0 T = true := by
  unfold erasableOk at h
  split at h
  · split at h
    · exact ⟨_, _, ‹_›, ‹_›, h⟩
    · cases h
  · cases h

/-- `CLErasable` from a successful run. -/
theorem erasable_of {F : Nat} (h : erasableOk false env F t = true) : CLErasable env t :=
  (erasable_spec h).elim fun _ ⟨_, hc, hT, hv⟩ => ⟨_, F, _, hc, hT, (verdict_of hv).1 rfl⟩

/-- `CLProofTerm` from a successful run. -/
theorem proofTerm_of {F : Nat} (h : erasableOk true env F t = true) : CLProofTerm env t :=
  (erasable_spec h).elim fun _ ⟨_, hc, hT, hv⟩ => ⟨_, F, _, hc, hT, (verdict_of hv).2 rfl⟩

theorem cert_spec {p : Bool} {Γ : List CtxBinder} {s : Expr} (h : certOk p env Γ s = true) :
    ∃ c d c' T₀ T, toCL? (lamTele Γ s) = some c ∧
      ConLeche.inferTypeCore .verified false env ConLeche.checkFuel 0 c = .ok T₀ ∧
      openLams 0 Γ.length c = some (d, c') ∧
      ConLeche.inferTypeCore .verified false env ConLeche.checkFuel d c' = .ok T ∧
      verdictOk p env ConLeche.checkFuel d T = true := by
  unfold certOk at h
  split at h
  · rename_i hc
    rw [Bool.and_eq_true] at h
    obtain ⟨T₀, h₀⟩ := inferOkCL_spec h.1
    have h := h.2
    split at h
    · split at h
      · exact ⟨_, _, _, _, _, hc, h₀, ‹_›, ‹_›, h⟩
      · cases h
    · cases h
  · cases h

/-- `CLCert` from a successful run. -/
theorem cert_of {Γ : List CtxBinder} {s : Expr} (h : certOk false env Γ s = true) : CLCert env Γ s :=
  (cert_spec h).elim fun _ ⟨_, _, _, _, h1, h2, h3, h4, h5⟩ =>
    ⟨_, _, _, _, _, h1, h2, h3, h4, (verdict_of h5).1 rfl⟩

/-- `CLCertProof` from a successful run. -/
theorem certProof_of {Γ : List CtxBinder} {s : Expr} (h : certOk true env Γ s = true) :
    CLCertProof env Γ s :=
  (cert_spec h).elim fun _ ⟨_, _, _, _, h1, h2, h3, h4, h5⟩ =>
    ⟨_, _, _, _, _, h1, h2, h3, h4, (verdict_of h5).2 rfl⟩

/-- `IotaNoCertAt` as a computation. -/
def iotaOk (env : ConLeche.Env) (T : Name) (m : Expr) : Bool :=
  match m.getAppFn with
  | .const C _ => match env.find? (Name.toCL (mkRecName T)) with
    | some (.recInfo _ _ _ isK rules) => match rules.find? (·.ctor == Name.toCL C) with
      | some rl => match env.find? (Name.toCL C) with
        | some (.ctorInfo cvC _ _ ind) =>
          ConLeche.iotaNoCert env.find? isK ind (ConLeche.recFireLevelCount rl cvC.levelParams)
        | _ => false
      | none => false
    | _ => false
  | _ => false

/-- `IotaNoCertAt` from a successful run. -/
theorem iota_of {T : Name} {m : Expr} (h : iotaOk env T m = true) : IotaNoCertAt env T m := by
  unfold iotaOk at h
  split at h
  · split at h
    · split at h
      · split at h
        · exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, ‹_›, ‹_›, ‹_›, ‹_›, h⟩
        · cases h
      · cases h
    · cases h
  · cases h

/-- `FrozenFieldsCert` at fuel `F` as a computation. -/
def frozenOk (env : ConLeche.Env) (F : Nat) (T C : Name) (us : List Level) (ps : List Expr)
    (d : Expr) : Bool :=
  match env.find? (Name.toCL (mkRecName T)) with
  | some (.recInfo cvR _ rP _ rules) =>
    match rules.find? (·.ctor == Name.toCL C), env.find? (Name.toCL C), us.mapM Level.toCL,
      ps.mapM toCL?, toCL? d with
    | some rl, some (.ctorInfo cvC nP nF _), some cus, some cps, some cd =>
      ((ConLeche.iotaCertsFull (ConLeche.pureFns .verified false env F) env 0
        (cvC.type.instantiateLevelParams cvC.levelParams
          (ConLeche.recFireComparands rl nP cvR.levelParams cus cvC.levelParams cps rP).1)
        ((ConLeche.recFireComparands rl nP cvR.levelParams cus cvC.levelParams cps rP).2 ++
          (List.range nF).map fun j => .proj (Name.toCL T) j cd)) matches .ok true)
    | _, _, _, _, _ => false
  | _ => false

/-- `FrozenFieldsCert` from a successful run. -/
theorem frozen_of {F : Nat} {T C : Name} {us : List Level} {ps : List Expr} {d : Expr}
    (h : frozenOk env F T C us ps d = true) : FrozenFieldsCert env T C us ps d := by
  unfold frozenOk at h
  split at h
  · split at h
    · split at h
      · exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, F, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›⟩
      · cases h
    · cases h
  · cases h

/-- `FVarsIn (· ≠ x)` as a computation. -/
def fvarsNe (x : FVarId) : Expr → Bool
  | .fvar y => !decide (y.name = x.name)
  | .app f a => fvarsNe x f && fvarsNe x a
  | .lam _ t b _ | .forallE _ t b _ => fvarsNe x t && fvarsNe x b
  | .letE _ t v b _ => fvarsNe x t && fvarsNe x v && fvarsNe x b
  | .mdata _ e | .proj _ _ e => fvarsNe x e
  | _ => true

theorem fvarsNe_spec {x : FVarId} {e : Expr} (h : fvarsNe x e = true) : FVarsIn (· ≠ x) e := by
  induction e <;> simp_all [fvarsNe, FVarsIn]
  rintro rfl
  exact h rfl

/-- `Fresh` as a computation. -/
def freshOk (x : FVarId) (ls : List Local) (es : List Expr) : Bool :=
  ls.all (fun l => !decide (l.fvarId.name = x.name) && fvarsNe x l.type && l.value?.all (fvarsNe x)) &&
    es.all (fvarsNe x)

/-- `Fresh` from a successful run. -/
theorem fresh_of {x : FVarId} {ls : List Local} {es : List Expr} (h : freshOk x ls es = true) :
    Fresh x ls es := by
  simp only [freshOk, Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨fun l hl => ?_, fun e he => fvarsNe_spec (h.2 e he)⟩
  have := h.1 l hl
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Option.all_eq_true] at this
  exact ⟨fun e => this.1.1 (congrArg FVarId.name e), fvarsNe_spec this.1.2,
    fun v hv => fvarsNe_spec (this.2 v hv)⟩

/-- `MarkOf.lam` with the marked body `bM` given closed: its opening at `x` marks the opened body. -/
theorem mark_lam {decls : List ConstantInfo} {cfg : ErasureConfig} {ls : List Local}
    {n : Name} {A b bM : Expr} {bi : BinderInfo} {x : FVarId}
    (ho : oracle decls ls (.lam n A b bi) = .ok false) (hx : Fresh x ls [b])
    (hab : absFV x 0 (bM.instantiate1' (.fvar x)) = bM)
    (h : MarkOf decls cfg (⟨x, n, A, none⟩ :: ls) (b.instantiate1' (.fvar x))
      (bM.instantiate1' (.fvar x))) :
    MarkOf decls cfg ls (.lam n A b bi) (.lam n A bM bi) := by
  have := MarkOf.lam ho hx h
  rwa [hab] at this

/-- `register_inductive` on an inductive that is registered. -/
theorem register_found {iv : InductiveVal} {r : InductiveId × InductiveArgMasks} {st : ErasureState}
    {tc : TravCtx} {pc : PureCtx} {ps : PureState} (h : st.inductives[iv.name]? = some r) :
    (register_inductive (m := PureM) iv).runPure st tc pc ps = .ok ((r, st), ps) := by
  rw [register_inductive]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, h]
  rfl

/-- A declaration without an `_unsafe_rec` companion in the view has no compiled
pre-definition. -/
theorem preDef_none' {view : EnvView} {cfg : ErasureConfig} {ci : ConstantInfo}
    (h : view.find? (Compiler.mkUnsafeRecName ci.name) = none) : preDef? view cfg ci = none := by
  cases ci with
  | defnInfo d =>
    have h' : view.find? (Compiler.mkUnsafeRecName d.name) = none := h
    simp only [preDef?, h']
  | _ => rfl

end EraseProof.Test
