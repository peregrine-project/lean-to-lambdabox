import EraseProof.Simulation
import EraseProof.Test.LBEval

/-!
# Non-vacuity instance NV-1 of `erases_correct`

The program

    axiom A : Type
    def CN : Type := (A → A) → A → A
    def one : CN := fun s z => s z
    #erase one (fun a : A => a)

as the newest-first declaration list `decls0` with its lean4lean model `venv0`, and the erased term
`e0` with its translation `e0'`. Every hypothesis of `erases_correct`
(`MR erasure/theories/ErasureCorrectness.v:51`) is discharged by a checked term: `henv`, `hsub`,
`hinj`, `hlc`, `he`, `her`, `hdeps`, `hblocks`, `hev`, with the evaluation environment `σ0` of a
list view and the λ□ environment `lenv0` that `#erase` emits. The instance `concl` has a witness,
and it is the λ `v0' = λz. (λa. a) z` (`witness`, by determinism of λ□ evaluation), not `□`. The
source evaluation `hev` takes a δ, a β and three atom steps.
-/

open Lean Lean4Lean Erasure

namespace EraseProof.Test.NV1

/-! ## The source program -/

/-- `A`. -/
def tyA : Expr := .const `A []

/-- The declaration `A : Type`, without a value. -/
def A_val : AxiomVal :=
  { name := `A, levelParams := [], type := .sort (.succ .zero), isUnsafe := false }

/-- `(A → A) → A → A`, the value of `CN`. -/
def cnE : Expr :=
  .forallE `s (.forallE `x tyA tyA .default) (.forallE `z tyA tyA .default) .default

/-- `fun s z => s z`, the value of `one`. -/
def oneE : Expr :=
  .lam `s (.forallE `x tyA tyA .default) (.lam `z tyA (.app (.bvar 1) (.bvar 0)) .default) .default

/-- `def CN : Type := (A → A) → A → A`. -/
def CN_val : DefinitionVal :=
  { name := `CN, levelParams := [], type := .sort (.succ .zero), value := cnE, hints := .abbrev,
    safety := .safe, all := [`CN] }

/-- `def one : CN := fun s z => s z`. -/
def one_val : DefinitionVal :=
  { name := `one, levelParams := [], type := .const `CN [], value := oneE, hints := .abbrev,
    safety := .safe, all := [`one] }

/-- The program's declarations, newest first. -/
def decls0 : List ConstantInfo := [.defnInfo one_val, .defnInfo CN_val, .axiomInfo A_val]

/-- The erased term `one (fun a : A => a)`. -/
def e0 : Expr := .app (.const `one []) (.lam `a tyA (.bvar 0) .default)

/-! ## Its model in lean4lean -/

/-- The image of `A`. -/
def vA : VExpr := .const `A []

/-- The image of `Type`. -/
def ty1 : VExpr := .sort (.succ .zero)

/-- The image of `A → A`. -/
def vAA : VExpr := .forallE vA vA

/-- The image of `CN`'s value. -/
def cnV : VExpr := .forallE vAA vAA

/-- The image of `one`'s value. -/
def oneV : VExpr := .lam vAA (.lam vA (.app (.bvar 1) (.bvar 0)))

/-- The model of `A`. -/
def Aconst : VConstant := ⟨0, ty1⟩

/-- The model of `CN`. -/
def CNdef : VDefVal := { name := `CN, uvars := 0, type := ty1, value := cnV }

/-- The model of `one`. -/
def onedef : VDefVal := { name := `one, uvars := 0, type := .const `CN [], value := oneV }

/-- The model after adding `A`. -/
def envA : VEnv :=
  { constants := fun n => if `A = n then some Aconst else VEnv.empty.constants n,
    defeqs := VEnv.empty.defeqs }

/-- The model after adding the constant `CN`. -/
def envCN0 : VEnv :=
  { envA with constants := fun n => if `CN = n then some CNdef.toVConstant else envA.constants n }

/-- The model after adding `CN` with its defining equation. -/
def envCN : VEnv := envCN0.addDefEq CNdef.toDefEq

/-- The model after adding the constant `one`. -/
def envOne0 : VEnv :=
  { envCN with
    constants := fun n => if `one = n then some onedef.toVConstant else envCN.constants n }

/-- The model of the program: `envOne0` with `one`'s defining equation. -/
def venv0 : VEnv := envOne0.addDefEq onedef.toDefEq

/-- The image of `e0`. -/
def e0' : VExpr := .app (.const `one []) (.lam vA (.bvar 0))

/-! ## Typing in the model -/

/-- `A` is declared in `venv0`. -/
theorem venv0_A : venv0.constants `A = some Aconst := rfl

/-- `A : Type` in any model that declares `A` as `Aconst`. -/
theorem hAty {env : VEnv} (h : env.constants `A = some Aconst) {Γ : List VExpr} :
    env.HasType 0 Γ vA ty1 :=
  .const (ci := Aconst) h (fun _ h => nomatch h) rfl

/-- `A → A : Sort (imax 1 1)` in any model that declares `A` as `Aconst`. -/
theorem hAAty {env : VEnv} (h : env.constants `A = some Aconst) {Γ : List VExpr} :
    env.HasType 0 Γ vAA (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .forallE (hAty h) (hAty h)

/-- `CN`'s value has type `Type` in any model that declares `A` as `Aconst`. -/
theorem cnV_ty {env : VEnv} (h : env.constants `A = some Aconst) : env.HasType 0 [] cnV ty1 :=
  (VEnv.IsDefEq.sortDF (l := .imax (.imax (.succ .zero) (.succ .zero))
      (.imax (.succ .zero) (.succ .zero))) (l' := .succ .zero)
    ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩ trivial (funext fun _ => rfl)).defeq
    (.forallE (hAAty h) (hAAty h))

/-- `CN` unfolds to its value in any model holding `CN`'s defining equation. -/
theorem cn_unfold {env : VEnv} (h : env.defeqs CNdef.toDefEq) {Γ : List VExpr} :
    env.IsDefEq 0 Γ (.const `CN []) cnV ty1 :=
  .extra (ls := []) h (fun _ h => nomatch h) rfl

/-! ## `henv`: the program's environment -/

/-- The value of `CN` translates to `cnV` in `envA`. -/
theorem trCN : TrS envA [] [] cnE cnV := by
  have hconstA : ∀ {Δ : VLCtx}, TrS envA [] Δ tyA vA := .const rfl rfl rfl
  have hdom : ∀ {Δ : VLCtx} (n : Name), TrS envA [] Δ (.forallE n tyA tyA .default) vAA :=
    fun _ => .forallE ⟨_, hAty rfl⟩ ⟨_, hAty rfl⟩ hconstA hconstA
  exact .forallE ⟨_, hAAty rfl⟩ ⟨_, hAAty rfl⟩ (hdom `x) (hdom `z)

/-- The value of `one` translates to `oneV` in `envCN`. -/
theorem trOne : TrS envCN [] [] oneE oneV := by
  have hconstA : ∀ {Δ : VLCtx}, TrS envCN [] Δ tyA vA := .const rfl rfl rfl
  have hdom : TrS envCN [] [] (.forallE `x tyA tyA .default) vAA :=
    .forallE ⟨_, hAty rfl⟩ ⟨_, hAty rfl⟩ hconstA hconstA
  have happ : TrS envCN [] [(none, .vlam vA), (none, .vlam vAA)] (.app (.bvar 1) (.bvar 0))
      (.app (.bvar 1) (.bvar 0)) :=
    .app (A := vA) (B := vA) (.bvar (.succ .zero)) (.bvar .zero) (.bvar (A := vAA) rfl)
      (.bvar (A := vA) rfl)
  exact .lam ⟨_, hAAty rfl⟩ hdom (.lam ⟨_, hAty rfl⟩ hconstA happ)

/-- `one`'s value has type `CN` in `envCN`: one δ-conversion of `CN`. -/
theorem oneWF : onedef.WF envCN := by
  have happ : envCN.HasType 0 [vA, vAA] (.app (.bvar 1) (.bvar 0)) vA :=
    .app (A := vA) (B := vA) (.bvar (.succ .zero)) (.bvar .zero)
  exact (cn_unfold (Or.inl rfl)).symm.defeq (.lam (hAAty rfl) (.lam (hAty rfl) happ))

/-- The model of `[CN, A]` is `envCN`. -/
theorem pCN : ProgEnv [.defnInfo CN_val, .axiomInfo A_val] envCN := by
  have pA : ProgEnv [.axiomInfo A_val] envA := .«axiom» (ci' := Aconst) .nil ⟨rfl, .sort rfl⟩
    ⟨_, .sortDF trivial trivial rfl⟩ rfl
  refine .defn (ci' := CNdef) pA rfl ⟨⟨rfl, .sort rfl⟩, rfl, trCN⟩ (cnV_ty rfl) ?_
  simp [VEnv.addConst, envA, envCN0, VEnv.empty, CN_val]
  rfl

/-- The program's model is `venv0`: the environment hypothesis of the correctness theorems on
NV-1. Reference: the hypothesis `wf_ext Σ` of `erases_correct`
(`MR erasure/theories/ErasureCorrectness.v:51`). -/
theorem henv : ProgEnv decls0 venv0 := by
  refine .defn (ci' := onedef) pCN rfl ⟨⟨rfl, .const rfl rfl rfl⟩, rfl, trOne⟩ oneWF ?_
  simp [VEnv.addConst, envCN, envCN0, envA, envOne0, VEnv.addDefEq, VEnv.empty, one_val]

/-! ## `he`: the erased term -/

/-- `e0` translates to `e0'` in the program's model, with both sides of the application typed:
the typing hypothesis of the correctness theorems on NV-1. Reference: the hypothesis
`Σ ;;; [] |- t : T` of `erases_correct` (`MR erasure/theories/ErasureCorrectness.v:51`). -/
theorem he : TrS venv0 [] [] e0 e0' := by
  have hone : venv0.HasType 0 [] (.const `one []) cnV :=
    (cn_unfold (Or.inr (Or.inl rfl))).defeq
      (.const (ci := onedef.toVConstant) rfl (fun _ h => nomatch h) rfl)
  have hid : venv0.HasType 0 [] (.lam vA (.bvar 0)) vAA := .lam (hAty venv0_A) (.bvar .zero)
  exact .app (A := vAA) (B := vAA) hone hid (.const rfl rfl rfl)
    (.lam ⟨_, hAty venv0_A⟩ (.const venv0_A rfl rfl) (.bvar (A := vA) rfl))

/-! ## The evaluation environment and the source evaluation -/

/-- The program's view: list lookup, nothing `@[extern]`, no inline attribute. -/
def view0 : EnvView := ⟨fun n => decls0.find? (·.name == n), fun _ => false, fun _ => none⟩

/-- The program's evaluation environment under the default configuration. -/
def σ0 : EvalEnv := evalEnvOf view0 {} decls0

/-- `fun z => (fun a => a) z`: the value of `e0`. -/
def v0 : Expr := .lam `z tyA (.app (.lam `a tyA (.bvar 0) .default) (.bvar 0)) .default

/-- `e0` evaluates to `v0`: δ unfolds `one` to a λ, the argument is a λ, and β gives a λ. The
source-evaluation hypothesis of `erases_correct` on NV-1. Reference: the hypothesis
`Σ |-p t ⇓ v` of `erases_correct` (`MR erasure/theories/ErasureCorrectness.v:51`). -/
theorem hev : SrcEval σ0 e0 v0 :=
  .beta (.delta rfl rfl rfl (.atom trivial)) (.atom trivial) (.atom trivial)

/-- Every declaration is the first of its name, so the evaluation environment is a
sub-environment of the program: the hypothesis `hsub` of `erases_correct` on NV-1. -/
theorem hsub : SubEnv σ0.decls decls0 := by
  intro ci h
  simp only [σ0, evalEnvOf, decls0, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> rfl

/-- The program's constants are `one`, `CN` and `A`. -/
theorem mem_names {c : Name} (h : (findDecl decls0 c).isSome = true) :
    c = `one ∨ c = `CN ∨ c = `A := by
  rw [findDecl, List.find?_isSome] at h
  obtain ⟨x, hx, hc⟩ := h
  simp only [decls0, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
    simp [ConstantInfo.name, ConstantInfo.toConstantVal, one_val, CN_val, A_val] at hc <;>
    subst hc <;> simp

/-- The program's kernames are distinct: the hypothesis `hinj` of `erases_correct` on NV-1. -/
theorem hinj : KernameInj σ0.decls := by
  intro c₁ c₂ h₁ h₂ hk
  rcases mem_names h₁ with rfl | rfl | rfl <;> rcases mem_names h₂ with rfl | rfl | rfl <;>
    first | rfl | (revert hk; decide)

/-! ## The erased program -/

/-- `λs. λz. s z`: the λ□ body of `one`. -/
def oneL : LBTerm :=
  .lambda (binderNameOf `s) (.lambda (binderNameOf `z) (.app (.bvar 1) (.bvar 0)))

/-- The λ□ environment: `one` with its erased body, as `#erase` emits it. -/
def lenv0 : GlobalDeclarations := [(toKername `one, .constantDecl ⟨some oneL⟩)]

/-- `one (λa. a)`: the erasure of `e0`. -/
def t0 : LBTerm := .app (.const (toKername `one)) (.lambda (binderNameOf `a) (.bvar 0))

/-- `λz. (λa. a) z`: the erasure of `v0`. -/
def v0' : LBTerm :=
  .lambda (binderNameOf `z) (.app (.lambda (binderNameOf `a) (.bvar 0)) (.bvar 0))

/-- The only declaration of `lenv0` is `one`'s. -/
theorem lookup0 {kn : Kername} {cb : ConstantBody} (h : lookupConst lenv0 kn = some cb) :
    cb = ⟨some oneL⟩ := by
  simp only [lookupConst, lenv0, List.find?_cons, List.find?_nil] at h
  by_cases hk : (toKername `one == kn) = true
  · simp only [hk] at h
    exact (Option.some.inj h).symm
  · simp only [Bool.not_eq_true] at hk
    simp only [hk] at h
    cases h

/-- `lenv0`'s body is closed: the hypothesis `hlc` of `erases_correct` on NV-1. -/
theorem hlc : LenvClosed lenv0 := by
  intro kn cb b h hb
  cases lookup0 h
  cases hb
  exact ⟨rfl, fun _ => rfl⟩

/-- `lenv0` stores no fixpoint: the hypothesis `hblocks` of `erases_correct` on NV-1. -/
theorem hblocks : BlocksErased venv0 σ0 lenv0 := by
  intro c ci defs i _ hl
  cases lookup0 hl

/-- `A → A` translates in any context of `venv0`. -/
theorem trAA {Δ : VLCtx} : TrS venv0 [] Δ (.forallE `x tyA tyA .default) vAA :=
  .forallE ⟨_, hAty venv0_A⟩ ⟨_, hAty venv0_A⟩ (.const venv0_A rfl rfl) (.const venv0_A rfl rfl)

/-- `one`'s value erases to `oneL`. -/
theorem erOne : Erases venv0 [] σ0.isAtom (RecIn lenv0) [] oneE oneL :=
  .lam trAA (.lam (.const venv0_A rfl rfl) (.app .bvar .bvar))

/-- `e0` erases to `t0`: the hypothesis `her` of `erases_correct` on NV-1. Reference: the
hypothesis `Σ;;; [] |- t ⇝ℇ t'` of `erases_correct`
(`MR erasure/theories/ErasureCorrectness.v:51`). -/
theorem her : Erases venv0 [] σ0.isAtom (RecIn lenv0) [] e0 t0 :=
  .app (.const (by decide)) (.lam (.const venv0_A rfl rfl) .bvar)

/-- `t0`'s dependency `one` is erased in `lenv0`: the hypothesis `hdeps` of `erases_correct` on
NV-1. Reference: the hypothesis `erases_deps Σ Σ' t'` of `erases_correct`
(`MR erasure/theories/ErasureCorrectness.v:51`). -/
theorem hdeps : ErasesDeps venv0 σ0 lenv0 t0 :=
  .app (.const (ci := .defnInfo one_val) rfl rfl
      (Or.inr (Or.inr ⟨by decide, by decide, oneL, rfl, erOne⟩))
      (fun _ hb => by cases hb; exact .lambda (.lambda (.app .bvar .bvar))))
    (.lambda .bvar)

/-! ## The conclusion -/

/-- `t0` evaluates to `v0'` in `lenv0`: δ unfolds `one`, then β. -/
theorem lbev : LBEval defaultFlags lenv0 t0 v0' :=
  .beta (.delta rfl rfl (.atom rfl)) (.atom rfl) (.atom rfl)

/-- `v0` erases to `v0'`. -/
theorem herv : Erases venv0 [] σ0.isAtom (RecIn lenv0) [] v0 v0' :=
  .lam (.const venv0_A rfl rfl) (.app (.lam (.const venv0_A rfl rfl) .bvar) .bvar)

/-- `erases_correct` on NV-1: every hypothesis is a checked term. Reference: `erases_correct`
(`MR erasure/theories/ErasureCorrectness.v:51`). -/
theorem concl : ∃ v', Erases venv0 [] σ0.isAtom (RecIn lenv0) [] v0 v' ∧
    LBEval defaultFlags lenv0 t0 v' :=
  erases_correct henv hsub hinj hlc he her hdeps hblocks hev

/-- Every witness of `concl` is `v0'`, a λ: λ□ evaluation is deterministic and `t0` evaluates to
`v0'` (`lbev`). Reference: `eval_deterministic` (`MR erasure/theories/EWcbvEval.v:1375`). -/
theorem witness {v' : LBTerm} (h : Erases venv0 [] σ0.isAtom (RecIn lenv0) [] v0 v' ∧
    LBEval defaultFlags lenv0 t0 v') : v' = v0' :=
  LBEval.deterministic h.2 lbev

end EraseProof.Test.NV1
