import EraseProof.Test.NV1

/-!
# Non-vacuity instance NV-3 of `erases_correct`: `uf one`

The program of NV-1 extended with an unsafe recursive constant,

    axiom A : Type
    def CN : Type := (A → A) → A → A
    def one : CN := fun s z => s z
    unsafe def uf (n : CN) : CN := (fun (k : CN → CN) => n) (fun (y : CN) => uf y)
    #erase uf one

as the newest-first declaration list `decls3` with its lean4lean model `venv3`: NV-1's model
`venv0` with `uf` added by `ProgEnv.block` with one member. The erased term is `e3 = uf one`: the
corpus program `ufOne` (`tests/corpus/UnsafeRec.lean`) with NV-1's monomorphic `CN` in place of
the universe-polymorphic Church numerals. The λ□ environment `lenv3` and term `t3` are what
`#erase` emits: `uf` is the fixpoint `tFix [uf] 0`.

Every hypothesis of `erases_correct` (`MR erasure/theories/ErasureCorrectness.v:51`) is
discharged by a checked term: `henv`, `hsub`, `hinj`, `hlc`, `he`, `her`, `hdeps`, `hblocks`,
`hev`. The source evaluation `hev` takes `SrcEval.fixAtom` (the head `uf`) and `SrcEval.fixApp`
(one unfolding of `uf`'s body at the argument `one`); `hdeps` and `hblocks` rest on
`ErasesBlock` with one member, whose body erases the recursive call by `Erases.constRec`. `inst`
applies the theorem; `concl` exhibits its conclusion with the witness `oneL = λs. λz. s z`, reached
by `LBEval.fix` with no accumulated arguments at `defaultFlags` (guarded fixpoints), and
`witness` shows, by determinism of λ□ evaluation, that every witness of the theorem is this λ,
not `□`.
-/

open Lean Lean4Lean Erasure

namespace EraseProof.Test.NV3

open EraseProof.Test.NV1 (tyA A_val one_val oneE decls0 vA ty1 vAA Aconst CNdef onedef envA envCN
  envCN0 envOne0 venv0 hAty oneL)

/-! ## The source program -/

/-- `CN`. -/
def cnT : Expr := .const `CN []

/-- `CN → CN`, the type of `uf`. -/
def cnArr : Expr := .forallE `n cnT cnT .default

/-- `(fun (k : CN → CN) => n) (fun (y : CN) => uf y)`, with `n` the loose index `0`. -/
def ufBody : Expr :=
  .app (.lam `k cnArr (.bvar 1) .default) (.lam `y cnT (.app (.const `uf []) (.bvar 0)) .default)

/-- `fun n => (fun k => n) (fun y => uf y)`, the value of `uf`. -/
def ufE : Expr := .lam `n cnT ufBody .default

/-- The unsafe definition `uf : CN → CN`, recursive through its own name. -/
def uf_val : DefinitionVal :=
  { name := `uf, levelParams := [], type := cnArr, value := ufE, hints := .«opaque»,
    safety := .«unsafe», all := [`uf] }

/-- The program's declarations, newest first. -/
def decls3 : List ConstantInfo := .defnInfo uf_val :: decls0

/-- The erased term `uf one`. -/
def e3 : Expr := .app (.const `uf []) (.const `one [])

/-! ## Its model in lean4lean -/

/-- The image of `CN`. -/
def cnC : VExpr := .const `CN []

/-- The image of `CN → CN`. -/
def cnArrV : VExpr := .forallE cnC cnC

/-- The image of `uf`'s value. -/
def ufV : VExpr :=
  .lam cnC (.app (.lam cnArrV (.bvar 1)) (.lam cnC (.app (.const `uf []) (.bvar 0))))

/-- The model of `uf`. -/
def ufdef : VDefVal := { name := `uf, uvars := 0, type := cnArrV, value := ufV }

/-- The model after adding the constant `uf`. -/
def envUf0 : VEnv :=
  { venv0 with
    constants := fun n => if `uf = n then some ufdef.toVConstant else venv0.constants n }

/-- The model of the program: `envUf0` with `uf`'s defining equation. -/
def venv3 : VEnv := envUf0.addDefEqs [ufdef]

/-- The image of `e3`. -/
def e3' : VExpr := .app (.const `uf []) (.const `one [])

/-! ## Typing in the model -/

/-- `CN : Type` in any model that declares `CN` as `CNdef`. -/
theorem cnC_ty {env : VEnv} (h : env.constants `CN = some CNdef.toVConstant) {Γ : List VExpr} :
    env.HasType 0 Γ cnC ty1 :=
  .const (ci := CNdef.toVConstant) h (fun _ h => nomatch h) rfl

/-- `CN → CN : Sort (imax 1 1)` in any model that declares `CN` as `CNdef`. -/
theorem cnArr_ty {env : VEnv} (h : env.constants `CN = some CNdef.toVConstant) {Γ : List VExpr} :
    env.HasType 0 Γ cnArrV (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .forallE (cnC_ty h) (cnC_ty h)

/-- `uf : CN → CN` in any model that declares `uf` as `ufdef`. -/
theorem uf_ty {env : VEnv} (h : env.constants `uf = some ufdef.toVConstant) {Γ : List VExpr} :
    env.HasType 0 Γ (.const `uf []) cnArrV :=
  .const (ci := ufdef.toVConstant) h (fun _ h => nomatch h) rfl

/-- `one : CN` in any model that declares `one` as `onedef`. -/
theorem one_ty {env : VEnv} (h : env.constants `one = some onedef.toVConstant) {Γ : List VExpr} :
    env.HasType 0 Γ (.const `one []) cnC :=
  .const (ci := onedef.toVConstant) h (fun _ h => nomatch h) rfl

/-- `CN` is declared in `envUf0`. -/
theorem envUf0_CN : envUf0.constants `CN = some CNdef.toVConstant := rfl

/-- `uf` is declared in `envUf0`. -/
theorem envUf0_uf : envUf0.constants `uf = some ufdef.toVConstant := rfl

/-- `CN` is declared in `venv3`. -/
theorem venv3_CN : venv3.constants `CN = some CNdef.toVConstant := rfl

/-- `uf` is declared in `venv3`. -/
theorem venv3_uf : venv3.constants `uf = some ufdef.toVConstant := rfl

/-- `one` is declared in `venv3`. -/
theorem venv3_one : venv3.constants `one = some onedef.toVConstant := rfl

/-- `A` is declared in `venv3`. -/
theorem venv3_A : venv3.constants `A = some Aconst := rfl

/-- `fun (k : CN → CN) => n : (CN → CN) → CN` under `n : CN`. -/
theorem kfun_ty {env : VEnv} (h : env.constants `CN = some CNdef.toVConstant) :
    env.HasType 0 [cnC] (.lam cnArrV (.bvar 1)) (.forallE cnArrV cnC) :=
  .lam (cnArr_ty h) (.bvar (.succ .zero))

/-- `fun (y : CN) => uf y : CN → CN` under `n : CN`. -/
theorem yfun_ty {env : VEnv} (h : env.constants `CN = some CNdef.toVConstant)
    (hu : env.constants `uf = some ufdef.toVConstant) :
    env.HasType 0 [cnC] (.lam cnC (.app (.const `uf []) (.bvar 0))) cnArrV :=
  .lam (cnC_ty h) (.app (uf_ty hu) (.bvar .zero))

/-- `uf`'s value has type `CN → CN` in any model that declares `CN` and `uf`. -/
theorem ufV_ty {env : VEnv} (h : env.constants `CN = some CNdef.toVConstant)
    (hu : env.constants `uf = some ufdef.toVConstant) : env.HasType 0 [] ufV cnArrV :=
  .lam (cnC_ty h) (.app (kfun_ty h) (yfun_ty h hu))

/-- `CN` translates to `cnC` in any context. -/
theorem trCNc {env : VEnv} (h : env.constants `CN = some CNdef.toVConstant) {Δ : VLCtx} :
    TrS env [] Δ cnT cnC := .const h rfl rfl

/-- `CN → CN` translates to `cnArrV` in any context. -/
theorem trCnArr {env : VEnv} (h : env.constants `CN = some CNdef.toVConstant) {Δ : VLCtx} :
    TrS env [] Δ cnArr cnArrV :=
  .forallE ⟨_, cnC_ty h⟩ ⟨_, cnC_ty h⟩ (trCNc h) (trCNc h)

/-- `uf`'s value translates to `ufV` in any model that declares `CN` and `uf`. -/
theorem trUfE {env : VEnv} (h : env.constants `CN = some CNdef.toVConstant)
    (hu : env.constants `uf = some ufdef.toVConstant) : TrS env [] [] ufE ufV :=
  .lam ⟨_, cnC_ty h⟩ (trCNc h)
    (.app (kfun_ty h) (yfun_ty h hu)
      (.lam ⟨_, cnArr_ty h⟩ (trCnArr h) (.bvar (A := cnC) rfl))
      (.lam ⟨_, cnC_ty h⟩ (trCNc h) (.app (uf_ty hu) (.bvar .zero) (.const hu rfl rfl)
        (.bvar (A := cnC) rfl))))

/-! ## `henv`: the program's environment -/

/-- Adding the block `[uf]` to `venv0` gives `envUf0`. -/
theorem addUf : venv0.addConsts [ufdef] = some envUf0 := by
  simp [VEnv.addConsts, VEnv.addConst, venv0, envOne0, envCN, envCN0, envA, VEnv.addDefEq,
    VEnv.empty, ufdef, envUf0]

/-- The program's model is `venv3`: NV-1's `ProgEnv` with the one-member block `[uf]`, whose value
is typed in the model that already declares `uf`. Reference: the hypothesis `wf_ext Σ` of
`erases_correct` (`MR erasure/theories/ErasureCorrectness.v:51`). -/
theorem henv : ProgEnv decls3 venv3 :=
  .block (vs := [uf_val]) (cis' := [ufdef]) NV1.henv (by simp [uf_val]) (by simp [uf_val])
    (.cons ⟨⟨rfl, trCnArr rfl⟩, rfl, trUfE envUf0_CN envUf0_uf⟩ .nil)
    (by intro ci h; simp at h; subst h; exact ⟨_, cnArr_ty rfl⟩) addUf
    (by intro ci h; simp at h; subst h; exact ufV_ty envUf0_CN envUf0_uf)

/-! ## `he`: the erased term -/

/-- `e3` translates to `e3'` in the program's model, with both sides of the application typed.
Reference: the hypothesis `Σ ;;; [] |- t : T` of `erases_correct`
(`MR erasure/theories/ErasureCorrectness.v:51`). -/
theorem he : TrS venv3 [] [] e3 e3' :=
  .app (uf_ty venv3_uf) (one_ty venv3_one) (.const venv3_uf rfl rfl) (.const venv3_one rfl rfl)

/-! ## The evaluation environment -/

/-- The program's view: list lookup, nothing `@[extern]`, no inline attribute. -/
def view3 : EnvView := ⟨fun n => decls3.find? (·.name == n), fun _ => false, fun _ => none⟩

/-- The program's evaluation environment under the default configuration. -/
def σ3 : EvalEnv := evalEnvOf view3 {} decls3

/-- Every declaration is the first of its name, so the evaluation environment is a
sub-environment of the program: the hypothesis `hsub` of `erases_correct` on NV-3. -/
theorem hsub : SubEnv σ3.decls decls3 := by
  intro ci h
  simp only [σ3, evalEnvOf, decls3, decls0, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> rfl

/-- The program's constants are `uf`, `one`, `CN` and `A`. -/
theorem mem_names {c : Name} (h : (findDecl decls3 c).isSome = true) :
    c = `uf ∨ c = `one ∨ c = `CN ∨ c = `A := by
  rw [findDecl, List.find?_isSome] at h
  obtain ⟨x, hx, hc⟩ := h
  simp only [decls3, decls0, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
    simp [ConstantInfo.name, ConstantInfo.toConstantVal, uf_val, one_val, NV1.CN_val, A_val] at hc <;>
    subst hc <;> simp

/-- The program's kernames are distinct: the hypothesis `hinj` of `erases_correct` on NV-3. -/
theorem hinj : KernameInj σ3.decls := by
  intro c₁ c₂ h₁ h₂ hk
  rcases mem_names h₁ with rfl | rfl | rfl | rfl <;> rcases mem_names h₂ with rfl | rfl | rfl | rfl <;>
    first | rfl | (revert hk; decide)

/-- `uf` is not an atom. -/
theorem atom_uf : σ3.isAtom `uf = false := by decide

/-- `one` is not an atom. -/
theorem atom_one : σ3.isAtom `one = false := by decide

/-- `uf` is recursive: its value mentions `uf`. -/
theorem rec_uf : RecursiveDecl (.defnInfo uf_val) = true := by decide

/-- `one` is not recursive. -/
theorem rec_one : RecursiveDecl (.defnInfo one_val) = false := by decide

/-- `uf` unfolds to its value. -/
theorem unfold_uf : σ3.unfold? `uf = some (.defnInfo uf_val, ufE) := rfl

/-- `one` unfolds to its value. -/
theorem unfold_one : σ3.unfold? `one = some (.defnInfo one_val, oneE) := rfl

/-- `uf`'s declaration in the evaluation environment. -/
theorem find_uf : findDecl σ3.decls `uf = some (.defnInfo uf_val) := rfl

/-- `one`'s declaration in the evaluation environment. -/
theorem find_one : findDecl σ3.decls `one = some (.defnInfo one_val) := rfl

/-- The source evaluation of `uf one`: `fixAtom` evaluates the head `uf` to itself, and `fixApp`
unfolds `uf` once at the argument `one` (a δ to its λ value); two β steps reach `one`'s value. The
source-evaluation hypothesis of `erases_correct` on NV-3. Reference: the hypothesis `Σ |-p t ⇓ v`
of `erases_correct` (`MR erasure/theories/ErasureCorrectness.v:51`), with `eval_fix`
(`MR pcuic/theories/PCUICWcbvEval.v:273`). -/
theorem hev : SrcEval σ3 e3 oneE :=
  .fixApp (.fixAtom unfold_uf rec_uf rfl) unfold_uf rec_uf
    (.delta unfold_one rec_one rfl (.atom trivial))
    (.beta (.atom trivial) (.atom trivial) (.beta (.atom trivial) (.atom trivial) (.atom trivial)))

/-! ## The erased program -/

/-- `λn. (λk. n) (λy. #uf y)`: the λ□ body of `uf`'s fixpoint, the recursive call `#uf` the
fixpoint variable `tRel 2`. -/
def ufL : LBTerm :=
  .lambda (binderNameOf `n)
    (.app (.lambda (binderNameOf `k) (.bvar 1))
      (.lambda (binderNameOf `y) (.app (.bvar 2) (.bvar 0))))

/-- The one-member block `[uf]`. -/
def defs3 : List (@FixDef LBTerm) := [{ name := fixDefName `uf, body := ufL }]

/-- The λ□ environment: `one` with its erased body and `uf` as the fixpoint of its block, as
`#erase` emits it. -/
def lenv3 : GlobalDeclarations :=
  [(toKername `one, .constantDecl ⟨some oneL⟩), (toKername `uf, .constantDecl ⟨some (.fix defs3 0)⟩)]

/-- `uf one`: the erasure of `e3`. -/
def t3 : LBTerm := .app (.const (toKername `uf)) (.const (toKername `one))

/-- `ufL` with the fixpoint substituted for its variable: the body `cunfold_fix defs3 0` gives. -/
def ufL' : LBTerm :=
  .lambda (binderNameOf `n)
    (.app (.lambda (binderNameOf `k) (.bvar 1))
      (.lambda (binderNameOf `y) (.app (.fix defs3 0) (.bvar 0))))

/-- Substituting the block's fixpoints into `ufL` gives `ufL'`. -/
theorem substl_ufL : substl (fixSubst defs3) ufL = ufL' := rfl

/-- `cunfold_fix defs3 0` unfolds to `ufL'` with principal argument `0`. -/
theorem cunfold : cunfoldFix defs3 0 = some (0, ufL') := rfl

/-- `uf`'s λ□ declaration. -/
theorem look_uf : lookupConst lenv3 (toKername `uf) = some ⟨some (.fix defs3 0)⟩ := rfl

/-- `one`'s λ□ declaration. -/
theorem look_one : lookupConst lenv3 (toKername `one) = some ⟨some oneL⟩ := rfl

/-- `CN` has no λ□ declaration. -/
theorem look_CN : lookupConst lenv3 (toKername `CN) = none := by decide

/-- `A` has no λ□ declaration. -/
theorem look_A : lookupConst lenv3 (toKername `A) = none := by decide

/-- `uf` is stored as a fixpoint of `lenv3`. -/
theorem recIn_uf : RecIn lenv3 `uf (.fix defs3 0) := ⟨defs3, 0, rfl, look_uf⟩

/-! ## The relation -/

/-- `one`'s value erases to `oneL`, the witness of NV-3. -/
theorem herv : Erases venv3 [] σ3.isAtom (RecIn lenv3) [] oneE oneL :=
  .lam (.forallE ⟨_, hAty venv3_A⟩ ⟨_, hAty venv3_A⟩ (.const venv3_A rfl rfl)
      (.const venv3_A rfl rfl))
    (.lam (.const venv3_A rfl rfl) (.app .bvar .bvar))

/-- `uf`'s value erases to `cunfold_fix defs3 0`'s body, the recursive call by `Erases.constRec`. -/
theorem erUf : Erases venv3 [] σ3.isAtom (RecIn lenv3) [] ufE ufL' :=
  .lam (trCNc venv3_CN)
    (.app (.lam (trCnArr venv3_CN) .bvar)
      (.lam (trCNc venv3_CN) (.app (.constRec atom_uf recIn_uf) .bvar)))

/-- The block `[uf]` is erased to `defs3`. -/
theorem block_uf : ErasesBlock venv3 σ3 lenv3 [`uf] defs3 := by
  refine ⟨rfl, fun j n hn => ?_⟩
  match j, hn with
  | 0, hn =>
    cases hn
    exact ⟨_, _, _, find_uf, rfl, rfl, rfl, rfl, substl_ufL ▸ erUf, look_uf⟩

/-- `uf`'s λ□ declaration erases it: the fixpoint of its block. -/
theorem decl_uf : ErasesDecl venv3 σ3 lenv3 (.defnInfo uf_val) ⟨some (.fix defs3 0)⟩ :=
  .inr (.inl ⟨by decide, rec_uf, defs3, 0, rfl, rfl, block_uf⟩)

/-- `one`'s λ□ declaration erases it. -/
theorem decl_one : ErasesDecl venv3 σ3 lenv3 (.defnInfo one_val) ⟨some oneL⟩ :=
  .inr (.inr ⟨by decide, rec_one, oneL, rfl, herv⟩)

/-- The fixpoint's bodies have their dependencies erased. -/
theorem deps_defs : ∀ d ∈ defs3, ErasesDeps venv3 σ3 lenv3 d.body := by
  intro d hd
  simp only [defs3, List.mem_cons, List.not_mem_nil, or_false] at hd
  subst hd
  exact .lambda (.app (.lambda .bvar) (.lambda (.app .bvar .bvar)))

/-- `e3` erases to `t3`: the hypothesis `her` of `erases_correct` on NV-3. Reference: the
hypothesis `Σ;;; [] |- t ⇝ℇ t'` of `erases_correct`
(`MR erasure/theories/ErasureCorrectness.v:51`). -/
theorem her : Erases venv3 [] σ3.isAtom (RecIn lenv3) [] e3 t3 :=
  .app (.const atom_uf) (.const atom_one)

/-- `t3`'s dependencies `uf` and `one` are erased in `lenv3`: the hypothesis `hdeps` of
`erases_correct` on NV-3. Reference: the hypothesis `erases_deps Σ Σ' t'` of `erases_correct`
(`MR erasure/theories/ErasureCorrectness.v:51`). -/
theorem hdeps : ErasesDeps venv3 σ3 lenv3 t3 :=
  .app (.const find_uf look_uf decl_uf (fun b hb => by cases hb; exact .fix deps_defs))
    (.const find_one look_one decl_one
      (fun b hb => by cases hb; exact .lambda (.lambda (.app .bvar .bvar))))

/-- The fixpoint stored for `uf` is its block's erasure: the hypothesis `hblocks` of
`erases_correct` on NV-3. -/
theorem hblocks : BlocksErased venv3 σ3 lenv3 := by
  intro c ci ds i hfd hl
  have hs : (findDecl decls3 c).isSome = true := by
    have h := hfd
    simp only [σ3, evalEnvOf] at h
    rw [h]
    rfl
  rcases mem_names hs with rfl | rfl | rfl | rfl
  · rw [find_uf] at hfd
    cases hfd
    rw [look_uf] at hl
    cases hl
    exact ⟨decl_uf, deps_defs⟩
  · rw [look_one] at hl
    cases hl
  · rw [look_CN] at hl
    cases hl
  · rw [look_A] at hl
    cases hl

/-- The declarations of `lenv3` are `one`'s and `uf`'s. -/
theorem look_cases {kn : Kername} {cb : ConstantBody} (h : lookupConst lenv3 kn = some cb) :
    cb = ⟨some oneL⟩ ∨ cb = ⟨some (.fix defs3 0)⟩ := by
  unfold lookupConst at h
  simp only [lenv3, List.find?_cons, List.find?_nil] at h
  cases h1 : (toKername `one == kn) <;> cases h2 : (toKername `uf == kn) <;> simp [h1, h2] at h <;>
    subst h <;> simp

/-- `lenv3`'s bodies are closed: the hypothesis `hlc` of `erases_correct` on NV-3. -/
theorem hlc : LenvClosed lenv3 := by
  intro kn cb b hl hb
  rcases look_cases hl with rfl | rfl <;> cases hb <;> exact ⟨rfl, fun _ => rfl⟩

/-! ## The instance and its conclusion -/

/-- `t3` evaluates to `oneL` in `lenv3`: δ gives `uf`'s fixpoint, `LBEval.fix` with no accumulated
arguments unfolds it at `one`'s body, then two β steps. Reference: `eval_fix`
(`MR erasure/theories/EWcbvEval.v:171`). -/
theorem lbev : LBEval defaultFlags lenv3 t3 oneL :=
  .fix (argsv := []) rfl (.delta look_uf rfl (.atom rfl)) (.delta look_one rfl (.atom rfl)) cunfold
    (.beta (.atom rfl) (.atom rfl) (.beta (.atom rfl) (.atom rfl) (.atom rfl)))

/-- `erases_correct` on NV-3: every hypothesis is a checked term. Reference: `erases_correct`
(`MR erasure/theories/ErasureCorrectness.v:51`). -/
theorem inst : ∃ v', Erases venv3 [] σ3.isAtom (RecIn lenv3) [] oneE v' ∧
    LBEval defaultFlags lenv3 t3 v' :=
  erases_correct henv hsub hinj hlc he her hdeps hblocks hev

/-- The conclusion of `erases_correct` on NV-3 holds with the non-`□` witness `oneL`. -/
theorem concl : Erases venv3 [] σ3.isAtom (RecIn lenv3) [] oneE oneL ∧
    LBEval defaultFlags lenv3 t3 oneL :=
  ⟨herv, lbev⟩

/-- Every witness of `erases_correct` on NV-3 is `oneL`, a λ: λ□ evaluation is deterministic and
`t3` evaluates to `oneL` (`lbev`). Reference: `eval_deterministic`
(`MR erasure/theories/EWcbvEval.v:1375`). -/
theorem witness {v' : LBTerm} (h : Erases venv3 [] σ3.isAtom (RecIn lenv3) [] oneE v' ∧
    LBEval defaultFlags lenv3 t3 v') : v' = oneL :=
  LBEval.deterministic h.2 lbev

end EraseProof.Test.NV3
