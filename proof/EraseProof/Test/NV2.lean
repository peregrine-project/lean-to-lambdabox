import EraseProof.Simulation
import EraseProof.Test.LBEval

/-!
# Non-vacuity instance NV-2 of `erases_correct`: `dbl two`

The program

    def CNat : Type 1 := ∀ α : Type, (α → α) → α → α
    def two : CNat := fun α s z => s (s z)
    def dbl (n : CNat) : CNat := let m := n; fun α s z => m α s (m α s z)
    #erase dbl two

as the newest-first declaration list `decls2` with its lean4lean model `venv2`, and the erased term
`e2` with its translation `e2'`. Every hypothesis of `erases_correct`
(`MR erasure/theories/ErasureCorrectness.v:51`) is discharged by a checked term: `henv`, `hsub`,
`hinj`, `hlc`, `he`, `her`, `hdeps`, `hblocks`, `hev`. The source evaluation takes δ (`dbl`, `two`),
β and ζ; the erasure of `dbl`'s body has `□` for the type argument `α` of `m`, and the model types
`m α` through `CNat`'s defining equation. The instance `concl` has a witness, and it is the λ
`v2' = λα. λs. λz. two' □ s (two' □ s z)`, where `two'` is `two`'s erased body (`witness`, by
determinism of λ□ evaluation), not `□`.
-/

open Lean Lean4Lean Erasure

namespace EraseProof.Test.NV2

/-! ## The source program -/

/-- `Type`. -/
def tyE : Expr := .sort (.succ .zero)

/-- `CNat`. -/
def cnE : Expr := .const `CNat []

/-- `α → α`, with `α` the loose index `0`. -/
def endoE : Expr := .forallE `x (.bvar 0) (.bvar 1) .default

/-- `∀ α : Type, (α → α) → α → α`, the value of `CNat`. -/
def cnatE : Expr :=
  .forallE `α tyE (.forallE `s endoE (.forallE `z (.bvar 1) (.bvar 2) .default) .default) .default

/-- `fun α s z => s (s z)`, the value of `two`. -/
def twoE : Expr :=
  .lam `α tyE (.lam `s endoE
    (.lam `z (.bvar 1) (.app (.bvar 1) (.app (.bvar 1) (.bvar 0))) .default) .default) .default

/-- `f α s a`, with `α`, `s` the loose indices `2`, `1`. -/
def spE (f a : Expr) : Expr := .app (.app (.app f (.bvar 2)) (.bvar 1)) a

/-- `fun α s z => f α s (f α s z)`, with `f` under the three binders. -/
def dblBodyE (f : Expr) : Expr :=
  .lam `α tyE (.lam `s endoE (.lam `z (.bvar 1) (spE f (spE f (.bvar 0))) .default) .default)
    .default

/-- `fun n => let m := n; fun α s z => m α s (m α s z)`, the value of `dbl`. -/
def dblE : Expr := .lam `n cnE (.letE `m cnE (.bvar 0) (dblBodyE (.bvar 3)) false) .default

/-- `def CNat : Type 1 := ∀ α : Type, (α → α) → α → α`. -/
def CNat_val : DefinitionVal :=
  { name := `CNat, levelParams := [], type := .sort (.succ (.succ .zero)), value := cnatE,
    hints := .abbrev, safety := .safe, all := [`CNat] }

/-- `def two : CNat := fun α s z => s (s z)`. -/
def two_val : DefinitionVal :=
  { name := `two, levelParams := [], type := cnE, value := twoE, hints := .abbrev,
    safety := .safe, all := [`two] }

/-- `def dbl : CNat → CNat := fun n => let m := n; fun α s z => m α s (m α s z)`. -/
def dbl_val : DefinitionVal :=
  { name := `dbl, levelParams := [], type := .forallE `n cnE cnE .default, value := dblE,
    hints := .abbrev, safety := .safe, all := [`dbl] }

/-- The program's declarations, newest first. -/
def decls2 : List ConstantInfo := [.defnInfo dbl_val, .defnInfo two_val, .defnInfo CNat_val]

/-- The erased term `dbl two`. -/
def e2 : Expr := .app (.const `dbl []) (.const `two [])

/-! ## Its model in lean4lean -/

/-- The image of `Type`. -/
def ty1 : VExpr := .sort (.succ .zero)

/-- The image of `Type 1`. -/
def ty2 : VExpr := .sort (.succ (.succ .zero))

/-- The image of `CNat`. -/
def vCN : VExpr := .const `CNat []

/-- The image of `α → α`. -/
def endoV : VExpr := .forallE (.bvar 0) (.bvar 1)

/-- The image of `α → α` under `s`, as the type of `z` and the result. -/
def zV : VExpr := .forallE (.bvar 1) (.bvar 2)

/-- The image of `CNat`'s value. -/
def cnatV : VExpr := .forallE ty1 (.forallE endoV zV)

/-- The image of `s (s z)`. -/
def ssz : VExpr := .app (.bvar 1) (.app (.bvar 1) (.bvar 0))

/-- The image of `two`'s value. -/
def twoV : VExpr := .lam ty1 (.lam endoV (.lam (.bvar 1) ssz))

/-- The image of `f α s a`. -/
def spV (f a : VExpr) : VExpr := .app (.app (.app f (.bvar 2)) (.bvar 1)) a

/-- The image of `dbl`'s value: the `let` is gone and `m` is `n`. -/
def dblV : VExpr := .lam vCN (.lam ty1 (.lam endoV (.lam (.bvar 1)
  (spV (.bvar 3) (spV (.bvar 3) (.bvar 0))))))

/-- The model of `CNat`. -/
def CNdef : VDefVal := { name := `CNat, uvars := 0, type := ty2, value := cnatV }

/-- The model of `two`. -/
def twodef : VDefVal := { name := `two, uvars := 0, type := vCN, value := twoV }

/-- The model of `dbl`. -/
def dbldef : VDefVal := { name := `dbl, uvars := 0, type := .forallE vCN vCN, value := dblV }

/-- The model after adding the constant `CNat`. -/
def envCN0 : VEnv :=
  { VEnv.empty with constants := fun n => if `CNat = n then some CNdef.toVConstant else none }

/-- The model after adding `CNat` with its defining equation. -/
def envCN : VEnv := envCN0.addDefEq CNdef.toDefEq

/-- The model after adding the constant `two`. -/
def envTwo0 : VEnv :=
  { envCN with
    constants := fun n => if `two = n then some twodef.toVConstant else envCN.constants n }

/-- The model after adding `two` with its defining equation. -/
def envTwo : VEnv := envTwo0.addDefEq twodef.toDefEq

/-- The model after adding the constant `dbl`. -/
def envDbl0 : VEnv :=
  { envTwo with
    constants := fun n => if `dbl = n then some dbldef.toVConstant else envTwo.constants n }

/-- The model of the program: `envDbl0` with `dbl`'s defining equation. -/
def venv2 : VEnv := envDbl0.addDefEq dbldef.toDefEq

/-- The image of `e2`. -/
def e2' : VExpr := .app (.const `dbl []) (.const `two [])

/-! ## Typing in the model -/

section
variable {env : VEnv} {Γ : List VExpr}

/-- `α → α : Sort (imax 1 1)` under `α : Type`. -/
theorem endoV_ty : env.HasType 0 (ty1 :: Γ) endoV (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .forallE (.bvar .zero) (.bvar (.succ .zero))

/-- `α → α : Sort (imax 1 1)` under `s : α → α`, `α : Type`. -/
theorem zV_ty :
    env.HasType 0 (endoV :: ty1 :: Γ) zV (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .forallE (.bvar (.succ .zero)) (.bvar (.succ (.succ .zero)))

/-- `CNat`'s value has type `Type 1` in any model. -/
theorem cnatV_ty : env.HasType 0 Γ cnatV ty2 :=
  (VEnv.IsDefEq.sortDF (l := .imax (.succ (.succ .zero)) (.imax (.imax (.succ .zero) (.succ .zero))
      (.imax (.succ .zero) (.succ .zero)))) (l' := .succ (.succ .zero))
    ⟨trivial, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩ trivial (funext fun _ => rfl)).defeq
    (.forallE (.sort trivial) (.forallE endoV_ty zV_ty))

/-- `CNat` unfolds to its value in any model holding `CNat`'s defining equation. -/
theorem cn_unfold (h : env.defeqs CNdef.toDefEq) : env.IsDefEq 0 Γ vCN cnatV ty2 :=
  .extra (ls := []) h (fun _ h => nomatch h) rfl

/-- `CNat : Type 1` in any model that declares `CNat`. -/
theorem vCN_ty (h : env.constants `CNat = some CNdef.toVConstant) : env.HasType 0 Γ vCN ty2 :=
  .const h (fun _ h => nomatch h) rfl

/-- `s z : α` under `z : α`, `s : α → α`, `α : Type`. -/
theorem sz_ty : env.HasType 0 (.bvar 1 :: endoV :: ty1 :: Γ) (.app (.bvar 1) (.bvar 0)) (.bvar 2) :=
  .app (A := .bvar 2) (B := .bvar 3) (.bvar (.succ .zero)) (.bvar .zero)

/-- `s (s z) : α` under `z : α`, `s : α → α`, `α : Type`. -/
theorem ssz_ty : env.HasType 0 (.bvar 1 :: endoV :: ty1 :: Γ) ssz (.bvar 2) :=
  .app (A := .bvar 2) (B := .bvar 3) (.bvar (.succ .zero)) sz_ty

/-- `two`'s value has type `CNat`'s value in any model. -/
theorem twoV_ty : env.HasType 0 Γ twoV cnatV :=
  .lam (.sort trivial) (.lam endoV_ty (.lam (.bvar (.succ .zero)) ssz_ty))

/-- `m : CNat`, seen as `CNat`'s value, under `z`, `s`, `α` and `n : CNat` (`m` is `n`). -/
theorem m_ty (h : env.defeqs CNdef.toDefEq) :
    env.HasType 0 (.bvar 1 :: endoV :: ty1 :: vCN :: Γ) (.bvar 3) cnatV :=
  (cn_unfold h).defeq (.bvar (.succ (.succ (.succ .zero))))

/-- `m α : (α → α) → α → α` under `z`, `s`, `α` and `n : CNat`. -/
theorem mα_ty (h : env.defeqs CNdef.toDefEq) :
    env.HasType 0 (.bvar 1 :: endoV :: ty1 :: vCN :: Γ) (.app (.bvar 3) (.bvar 2))
      (.forallE (.forallE (.bvar 2) (.bvar 3)) (.forallE (.bvar 3) (.bvar 4))) :=
  .app (A := ty1) (B := .forallE endoV zV) (m_ty h) (.bvar (.succ (.succ .zero)))

/-- `m α s : α → α` under `z`, `s`, `α` and `n : CNat`. -/
theorem mαs_ty (h : env.defeqs CNdef.toDefEq) :
    env.HasType 0 (.bvar 1 :: endoV :: ty1 :: vCN :: Γ) (.app (.app (.bvar 3) (.bvar 2)) (.bvar 1))
      (.forallE (.bvar 2) (.bvar 3)) :=
  .app (A := .forallE (.bvar 2) (.bvar 3)) (B := .forallE (.bvar 3) (.bvar 4)) (mα_ty h)
    (.bvar (.succ .zero))

/-- `m α s a : α` for `a : α`, under `z`, `s`, `α` and `n : CNat`. -/
theorem spV_ty (h : env.defeqs CNdef.toDefEq)
    (ha : env.HasType 0 (.bvar 1 :: endoV :: ty1 :: vCN :: Γ) a (.bvar 2)) :
    env.HasType 0 (.bvar 1 :: endoV :: ty1 :: vCN :: Γ) (spV (.bvar 3) a) (.bvar 2) :=
  .app (A := .bvar 2) (B := .bvar 3) (mαs_ty h) ha

/-- `dbl`'s value has type `CNat → CNat` in any model that declares `CNat` with its defining
equation: one δ-conversion for `m α`, one for the result. -/
theorem dblV_ty (hc : env.constants `CNat = some CNdef.toVConstant)
    (h : env.defeqs CNdef.toDefEq) : env.HasType 0 [] dblV (.forallE vCN vCN) :=
  .lam (vCN_ty hc) ((cn_unfold h).symm.defeq
    (.lam (.sort trivial) (.lam endoV_ty (.lam (.bvar (.succ .zero))
      (spV_ty h (spV_ty h (.bvar .zero)))))))

end

/-! ## The translation -/

section
variable {env : VEnv} {Δ : VLCtx}

/-- `Type` translates to `ty1`. -/
theorem trTy : TrS env [] Δ tyE ty1 := .sort rfl

/-- `α → α` translates to `endoV` under `α`. -/
theorem trEndo : TrS env [] ((none, .vlam ty1) :: Δ) endoE endoV :=
  .forallE ⟨_, .bvar .zero⟩ ⟨_, .bvar (.succ .zero)⟩ (.bvar rfl) (.bvar rfl)

/-- `α` translates under `s`, `α`. -/
theorem trAlpha : TrS env [] ((none, .vlam endoV) :: (none, .vlam ty1) :: Δ) (.bvar 1) (.bvar 1) :=
  .bvar rfl

/-- `CNat`'s value translates to `cnatV`. -/
theorem trCnat : TrS env [] Δ cnatE cnatV :=
  .forallE ⟨_, .sort trivial⟩ ⟨_, .forallE endoV_ty zV_ty⟩ trTy
    (.forallE ⟨_, endoV_ty⟩ ⟨_, zV_ty⟩ trEndo
      (.forallE ⟨_, .bvar (.succ .zero)⟩ ⟨_, .bvar (.succ (.succ .zero))⟩ trAlpha (.bvar rfl)))

/-- `two`'s value translates to `twoV`. -/
theorem trTwo : TrS env [] Δ twoE twoV :=
  .lam ⟨_, .sort trivial⟩ trTy (.lam ⟨_, endoV_ty⟩ trEndo (.lam ⟨_, .bvar (.succ .zero)⟩ trAlpha
    (.app (A := .bvar 2) (B := .bvar 3) (.bvar (.succ .zero)) sz_ty (.bvar rfl)
      (.app (A := .bvar 2) (B := .bvar 3) (.bvar (.succ .zero)) (.bvar .zero) (.bvar rfl)
        (.bvar rfl)))))


/-- The context of `dbl`'s body: `z`, `s`, `α`, `m := n`, `n`. -/
def ctxD : VLCtx :=
  [(none, .vlam (.bvar 1)), (none, .vlam endoV), (none, .vlam ty1), (none, .vlet vCN (.bvar 0)),
   (none, .vlam vCN)]

/-- `m α s a` translates to `n α s a'` in `dbl`'s body. -/
theorem trSp (h : env.defeqs CNdef.toDefEq) (ha : TrS env [] ctxD a a')
    (hat : env.HasType 0 [.bvar 1, endoV, ty1, vCN] a' (.bvar 2)) :
    TrS env [] ctxD (spE (.bvar 3) a) (spV (.bvar 3) a') :=
  .app (A := .bvar 2) (B := .bvar 3) (mαs_ty h) hat
    (.app (A := .forallE (.bvar 2) (.bvar 3)) (B := .forallE (.bvar 3) (.bvar 4)) (mα_ty h)
      (.bvar (.succ .zero))
      (.app (A := ty1) (B := .forallE endoV zV) (m_ty h) (.bvar (.succ (.succ .zero))) (.bvar rfl)
        (.bvar rfl))
      (.bvar rfl))
    ha

/-- `dbl`'s value translates to `dblV` in any model that declares `CNat` with its defining
equation: the `let` translates to its body with `m` bound to `n`. -/
theorem trDbl (hc : env.constants `CNat = some CNdef.toVConstant)
    (h : env.defeqs CNdef.toDefEq) : TrS env [] [] dblE dblV :=
  .lam ⟨_, vCN_ty hc⟩ (.const hc rfl rfl)
    (.letE (.bvar .zero) (.const hc rfl rfl) (.bvar rfl)
      (.lam ⟨_, .sort trivial⟩ trTy (.lam ⟨_, endoV_ty⟩ trEndo
        (.lam ⟨_, .bvar (.succ .zero)⟩ trAlpha
          (trSp h (trSp h (.bvar rfl) (.bvar .zero)) (spV_ty h (.bvar .zero)))))))

end

/-! ## `henv` and `he` -/

/-- The model of `[CNat]` is `envCN`. -/
theorem pCN : ProgEnv [.defnInfo CNat_val] envCN := by
  refine .defn (ci' := CNdef) .nil rfl ⟨⟨rfl, .sort rfl⟩, rfl, trCnat⟩ cnatV_ty ?_
  simp [VEnv.addConst, envCN0, VEnv.empty, CNat_val]
  rfl

/-- The model of `[two, CNat]` is `envTwo`: `two`'s value has type `CNat` by one δ-conversion. -/
theorem pTwo : ProgEnv [.defnInfo two_val, .defnInfo CNat_val] envTwo := by
  refine .defn (ci' := twodef) pCN rfl ⟨⟨rfl, .const rfl rfl rfl⟩, rfl, trTwo⟩
    ((cn_unfold (Or.inl rfl)).symm.defeq twoV_ty) ?_
  simp [VEnv.addConst, envCN, envCN0, envTwo0, VEnv.addDefEq, VEnv.empty, two_val]

/-- The program's model is `venv2`: the environment hypothesis of `erases_correct` on NV-2.
Reference: the hypothesis `wf_ext Σ` of `erases_correct`
(`MR erasure/theories/ErasureCorrectness.v:51`). -/
theorem henv : ProgEnv decls2 venv2 := by
  refine .defn (ci' := dbldef) pTwo rfl
    ⟨⟨rfl, .forallE ⟨_, vCN_ty rfl⟩ ⟨_, vCN_ty rfl⟩ (.const rfl rfl rfl) (.const rfl rfl rfl)⟩, rfl,
      trDbl rfl (Or.inr (Or.inl rfl))⟩
    (dblV_ty rfl (Or.inr (Or.inl rfl))) ?_
  simp [VEnv.addConst, envTwo, envTwo0, envCN, envCN0, envDbl0, VEnv.addDefEq, VEnv.empty, dbl_val]

/-- `e2` translates to `e2'` in the program's model, with both sides of the application typed:
the typing hypothesis of `erases_correct` on NV-2. Reference: the hypothesis `welltyped Σ [] t`
of `erases_correct` (`MR erasure/theories/ErasureCorrectness.v:51`). -/
theorem he : TrS venv2 [] [] e2 e2' :=
  .app (A := vCN) (B := vCN) (.const (ci := dbldef.toVConstant) rfl (fun _ h => nomatch h) rfl)
    (.const (ci := twodef.toVConstant) rfl (fun _ h => nomatch h) rfl) (.const rfl rfl rfl)
    (.const rfl rfl rfl)

/-! ## The evaluation environment and the source evaluation -/

/-- The program's view: list lookup, nothing `@[extern]`, no inline attribute. -/
def view2 : EnvView := ⟨fun n => decls2.find? (·.name == n), fun _ => false, fun _ => none⟩

/-- The program's evaluation environment under the default configuration. -/
def σ2 : EvalEnv := evalEnvOf view2 {} decls2

/-- `fun α s z => two' α s (two' α s z)`, with `two'` the value of `two`: the value of `e2`. -/
def v2 : Expr := dblBodyE twoE

/-- `e2` evaluates to `v2`: δ unfolds `dbl` and `two` to λs, β substitutes `two`'s value for
`n`, ζ substitutes it for `m`. The source-evaluation hypothesis of `erases_correct` on NV-2.
Reference: the hypothesis `Σ |-p t ⇓ v` of `erases_correct`
(`MR erasure/theories/ErasureCorrectness.v:51`). -/
theorem hev : SrcEval σ2 e2 v2 :=
  .beta (.delta rfl rfl rfl (.atom trivial)) (.delta rfl rfl rfl (.atom trivial))
    (.zeta (.atom trivial) (.atom trivial))

/-- Every declaration is the first of its name, so the evaluation environment is a
sub-environment of the program: the hypothesis `hsub` of `erases_correct` on NV-2. -/
theorem hsub : SubEnv σ2.decls decls2 := by
  intro ci h
  simp only [σ2, evalEnvOf, decls2, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> rfl

/-- The program's constants are `dbl`, `two` and `CNat`. -/
theorem mem_names {c : Name} (h : (findDecl decls2 c).isSome = true) :
    c = `dbl ∨ c = `two ∨ c = `CNat := by
  rw [findDecl, List.find?_isSome] at h
  obtain ⟨x, hx, hc⟩ := h
  simp only [decls2, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
    simp [ConstantInfo.name, ConstantInfo.toConstantVal, dbl_val, two_val, CNat_val] at hc <;>
    subst hc <;> simp

/-- The program's kernames are distinct: the hypothesis `hinj` of `erases_correct` on NV-2. -/
theorem hinj : KernameInj σ2.decls := by
  intro c₁ c₂ h₁ h₂ hk
  rcases mem_names h₁ with rfl | rfl | rfl <;> rcases mem_names h₂ with rfl | rfl | rfl <;>
    first | rfl | (revert hk; decide)

/-! ## The erased program -/

/-- `λα. λs. λz. s (s z)`: the λ□ body of `two`. -/
def twoL : LBTerm :=
  .lambda (binderNameOf `α) (.lambda (binderNameOf `s) (.lambda (binderNameOf `z)
    (.app (.bvar 1) (.app (.bvar 1) (.bvar 0)))))

/-- `f □ s a`: the erased type argument is `□`. -/
def spL (f a : LBTerm) : LBTerm := .app (.app (.app f .box) (.bvar 1)) a

/-- `λα. λs. λz. f □ s (f □ s z)`, with `f` under the three binders. -/
def dblBodyL (f : LBTerm) : LBTerm :=
  .lambda (binderNameOf `α) (.lambda (binderNameOf `s) (.lambda (binderNameOf `z)
    (spL f (spL f (.bvar 0)))))

/-- `λn. let m := n in λα. λs. λz. m □ s (m □ s z)`: the λ□ body of `dbl`. -/
def dblL : LBTerm :=
  .lambda (binderNameOf `n) (.letIn (binderNameOf `m) (.bvar 0) (dblBodyL (.bvar 3)))

/-- The λ□ environment: `two` and `dbl` with their erased bodies, as `#erase` emits them. -/
def lenv2 : GlobalDeclarations :=
  [(toKername `two, .constantDecl ⟨some twoL⟩), (toKername `dbl, .constantDecl ⟨some dblL⟩)]

/-- `dbl two`: the erasure of `e2`. -/
def t2 : LBTerm := .app (.const (toKername `dbl)) (.const (toKername `two))

/-- `λα. λs. λz. two' □ s (two' □ s z)`, with `two'` the λ□ body of `two`: the erasure of `v2`. -/
def v2' : LBTerm := dblBodyL twoL

/-- The declarations of `lenv2` are `two`'s and `dbl`'s. -/
theorem lookup2 {kn : Kername} {cb : ConstantBody} (h : lookupConst lenv2 kn = some cb) :
    cb = ⟨some twoL⟩ ∨ cb = ⟨some dblL⟩ := by
  simp only [lookupConst, lenv2, List.find?_cons, List.find?_nil] at h
  by_cases h₁ : (toKername `two == kn) = true
  · simp only [h₁] at h
    exact .inl (Option.some.inj h).symm
  · simp only [Bool.not_eq_true] at h₁
    simp only [h₁] at h
    by_cases h₂ : (toKername `dbl == kn) = true
    · simp only [h₂] at h
      exact .inr (Option.some.inj h).symm
    · simp only [Bool.not_eq_true] at h₂
      simp only [h₂] at h
      cases h

/-- `lenv2`'s bodies are closed: the hypothesis `hlc` of `erases_correct` on NV-2. -/
theorem hlc : LenvClosed lenv2 := by
  intro kn cb b h hb
  rcases lookup2 h with rfl | rfl <;> cases hb <;> exact ⟨rfl, fun _ => rfl⟩

/-- `lenv2` stores no fixpoint: the hypothesis `hblocks` of `erases_correct` on NV-2. -/
theorem hblocks : BlocksErased venv2 σ2 lenv2 := by
  intro c ci defs i _ hl
  rcases lookup2 hl with h | h <;> cases h

section
variable {Δ : VLCtx}

/-- `two`'s value erases to `twoL` in any context. -/
theorem erTwo : Erases venv2 [] σ2.isAtom (RecIn lenv2) Δ twoE twoL :=
  .lam trTy (.lam trEndo (.lam trAlpha (.app .bvar (.app .bvar .bvar))))

/-- The type variable `α` is erasable under `z`, `s`, `α`: its type is `Type`. -/
theorem erAlpha :
    ErasableS venv2 [] ((none, .vlam (.bvar 1)) :: (none, .vlam endoV) :: (none, .vlam ty1) :: Δ)
      (.bvar 2) :=
  ⟨.bvar 2, .bvar rfl, ty1, .bvar (.succ (.succ .zero)), .inl trivial⟩

/-- `f α s a` erases to `f' □ s a'` under `z`, `s`, `α`: the type argument is boxed. -/
theorem erSp
    (hf : Erases venv2 [] σ2.isAtom (RecIn lenv2)
      ((none, .vlam (.bvar 1)) :: (none, .vlam endoV) :: (none, .vlam ty1) :: Δ) f f')
    (ha : Erases venv2 [] σ2.isAtom (RecIn lenv2)
      ((none, .vlam (.bvar 1)) :: (none, .vlam endoV) :: (none, .vlam ty1) :: Δ) a a') :
    Erases venv2 [] σ2.isAtom (RecIn lenv2)
      ((none, .vlam (.bvar 1)) :: (none, .vlam endoV) :: (none, .vlam ty1) :: Δ)
      (spE f a) (spL f' a') :=
  .app (.app (.app hf (.box erAlpha)) .bvar) ha

end

/-- `dbl`'s value erases to `dblL`: the `let` is kept, the type argument of `m` is boxed. -/
theorem erDbl : Erases venv2 [] σ2.isAtom (RecIn lenv2) [] dblE dblL :=
  .lam (.const rfl rfl rfl) (.letE (.const rfl rfl rfl) (.bvar rfl) .bvar
    (.lam trTy (.lam trEndo (.lam trAlpha (erSp .bvar (erSp .bvar .bvar))))))

/-- `e2` erases to `t2`: the hypothesis `her` of `erases_correct` on NV-2. Reference: the
hypothesis `Σ;;; [] |- t ⇝ℇ t'` of `erases_correct`
(`MR erasure/theories/ErasureCorrectness.v:51`). -/
theorem her : Erases venv2 [] σ2.isAtom (RecIn lenv2) [] e2 t2 :=
  .app (.const (by decide)) (.const (by decide))

/-- `t2`'s dependencies `dbl` and `two` are erased in `lenv2`: the hypothesis `hdeps` of
`erases_correct` on NV-2. Reference: the hypothesis `erases_deps Σ Σ' t'` of `erases_correct`
(`MR erasure/theories/ErasureCorrectness.v:51`). -/
theorem hdeps : ErasesDeps venv2 σ2 lenv2 t2 :=
  .app
    (.const (ci := .defnInfo dbl_val) rfl rfl
      (Or.inr (Or.inr ⟨by decide, by decide, dblL, rfl, erDbl⟩))
      (fun _ hb => by
        cases hb
        exact .lambda (.letIn .bvar (.lambda (.lambda (.lambda
          (.app (.app (.app .bvar .box) .bvar) (.app (.app (.app .bvar .box) .bvar) .bvar))))))))
    (.const (ci := .defnInfo two_val) rfl rfl
      (Or.inr (Or.inr ⟨by decide, by decide, twoL, rfl, erTwo⟩))
      (fun _ hb => by cases hb; exact .lambda (.lambda (.lambda (.app .bvar (.app .bvar .bvar))))))

/-! ## The conclusion -/

/-- `t2` evaluates to `v2'` in `lenv2`: δ unfolds `dbl` and `two`, then β and ζ. -/
theorem lbev : LBEval defaultFlags lenv2 t2 v2' :=
  .beta (.delta rfl rfl (.atom rfl)) (.delta rfl rfl (.atom rfl)) (.zeta (.atom rfl) (.atom rfl))

/-- `v2` erases to `v2'`. -/
theorem herv : Erases venv2 [] σ2.isAtom (RecIn lenv2) [] v2 v2' :=
  .lam trTy (.lam trEndo (.lam trAlpha (erSp erTwo (erSp erTwo .bvar))))

/-- `erases_correct` on NV-2: every hypothesis is a checked term. Reference: `erases_correct`
(`MR erasure/theories/ErasureCorrectness.v:51`). -/
theorem concl : ∃ v', Erases venv2 [] σ2.isAtom (RecIn lenv2) [] v2 v' ∧
    LBEval defaultFlags lenv2 t2 v' :=
  erases_correct henv hsub hinj hlc he her hdeps hblocks hev

/-- Every witness of `concl` is `v2'`, a λ: λ□ evaluation is deterministic and `t2` evaluates to
`v2'` (`lbev`). Reference: `eval_deterministic` (`MR erasure/theories/EWcbvEval.v:1375`). -/
theorem witness {v' : LBTerm} (h : Erases venv2 [] σ2.isAtom (RecIn lenv2) [] v2 v' ∧
    LBEval defaultFlags lenv2 t2 v') : v' = v2' :=
  LBEval.deterministic h.2 lbev

end EraseProof.Test.NV2
