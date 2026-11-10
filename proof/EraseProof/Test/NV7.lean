import EraseProof.Simulation
import EraseProof.Source.Restrict
import EraseProof.Test.LBEval

/-!
# Non-vacuity instance NV-7: a proof at a universe-polymorphic proposition

The program `(fun (h : P.{0}) (x : A) => x) hp` over the environment `A : Type`,
`P.{v} : Sort v`, `hp : P.{0}` (all axioms). The proof `hp` is an atom: its type `P.{0}` is an
evident proposition at its declaration's own (empty) level parameters, although `P`'s sort
depends on a level parameter. The program evaluates by β to `fun x : A => x`, with `hp` evaluated
as an atom (`constAtom`); the shipping oracle boxes `hp` (`oracle_hp`); the erasure
`(λh. λx. x) □` evaluates in λ□ to `λx. x`.

Every hypothesis of `EraseProof.erases_correct` is discharged by a checked term: the program's
model `henv` (with the universe-polymorphic `P`), `hsub`, `hinj`, `hlc`, `he`, `her`, `hdeps`,
`hblocks`, `hev`. `inst` applies the theorem; `concl` exhibits its conclusion with the non-`□`
witness `λx. x`, which `witness` shows is the only one. Reference: `erases_correct`
(`MR erasure/theories/ErasureCorrectness.v:51`).
-/

open Lean Lean4Lean Erasure

namespace EraseProof.Test.NV7

/-! ## The environment -/

/-- `axiom A : Type`. -/
def A_val : AxiomVal :=
  { name := `A, levelParams := [], type := .sort (.succ .zero), isUnsafe := false }
/-- `axiom P.{v} : Sort v`. -/
def P_val : AxiomVal :=
  { name := `P, levelParams := [`v], type := .sort (.param `v), isUnsafe := false }
/-- `axiom hp : P.{0}`. -/
def hp_val : AxiomVal :=
  { name := `hp, levelParams := [], type := .const `P [.zero], isUnsafe := false }
/-- The environment, newest first. -/
def decls : List ConstantInfo := [.axiomInfo hp_val, .axiomInfo P_val, .axiomInfo A_val]
/-- Nothing is `@[extern]`. -/
def view : EnvView := ⟨fun n => decls.find? (·.name == n), fun _ => false, fun _ => none⟩
/-- The evaluation environment. -/
def σ : EvalEnv := evalEnvOf view {} decls
/-- The oracle's context. -/
def cx : Pure.Ctx := ⟨decls⟩

/-- The proof `hp` is an atom: its type `P.{0}` is an evident proposition. -/
theorem atom_hp : σ.isAtom `hp = true := by decide

/-- The shipping oracle answers "erasable" on the proof `hp`. -/
theorem oracle_hp : (Pure.isErasable cx oracleFuel [] (.const `hp [])).toOption = some true := by
  decide

/-! ## Its model in lean4lean -/

/-- The image of `A`. -/
def vA : VExpr := .const `A []
/-- The image of `Type`. -/
def ty1 : VExpr := .sort (.succ .zero)
/-- The image of `P.{0}`. -/
def vP0 : VExpr := .const `P [.zero]
/-- The model of `A`. -/
def AC : VConstant := ⟨0, ty1⟩
/-- The model of `P`: one level parameter, type `Sort u₀`. -/
def PC : VConstant := ⟨1, .sort (.param 0)⟩
/-- The model of `hp`. -/
def hpC : VConstant := ⟨0, vP0⟩

/-- The model after adding `A`. -/
def env1 : VEnv := { VEnv.empty with constants := fun n => if `A = n then some AC else none }
/-- The model after adding `P`. -/
def env2 : VEnv :=
  { env1 with constants := fun n => if `P = n then some PC else env1.constants n }
/-- The model of the environment: `env2` with `hp`. -/
def env3 : VEnv :=
  { env2 with constants := fun n => if `hp = n then some hpC else env2.constants n }

/-- `A` is declared in `env3`. -/
theorem e3A : env3.constants `A = some AC := rfl
/-- `P` is declared in `env3`. -/
theorem e3P : env3.constants `P = some PC := rfl
/-- `hp` is declared in `env3`. -/
theorem e3hp : env3.constants `hp = some hpC := rfl

/-- `P.{0} : Prop` in any model that declares `P` as `PC`. -/
theorem hP0ty {env : VEnv} (h : env.constants `P = some PC) {Γ} :
    env.HasType 0 Γ vP0 (.sort .zero) :=
  VEnv.HasType.const (ci := PC) (ls := [.zero]) h (by simp [VLevel.WF]) rfl

/-- `A : Type` in `env3`. -/
theorem hAty {Γ} : env3.HasType 0 Γ vA ty1 :=
  VEnv.HasType.const (ci := AC) e3A (fun _ h => nomatch h) rfl
/-- `hp : P.{0}` in `env3`. -/
theorem hhpty {Γ} : env3.HasType 0 Γ (.const `hp []) vP0 :=
  VEnv.HasType.const (ci := hpC) e3hp (fun _ h => nomatch h) rfl

/-- The environment's model is `env3`. Reference: the hypothesis `wf_ext Σ` of `erases_correct`
(`MR erasure/theories/ErasureCorrectness.v:51`). -/
theorem henv : ProgEnv decls env3 :=
  .«axiom» (ci' := hpC)
    (.«axiom» (ci' := PC)
      (.«axiom» (ci' := AC) .nil ⟨rfl, .sort rfl⟩ ⟨_, .sortDF trivial trivial rfl⟩ rfl)
      ⟨rfl, .sort rfl⟩ ⟨_, .sortDF (by decide) (by decide) rfl⟩ rfl)
    ⟨rfl, .const rfl rfl rfl⟩ ⟨_, hP0ty rfl⟩ rfl

/-- Every declaration is the first of its name. Reference: `extends_decls` (the closure `Σ'` of
`MR E/ErasureFunction.v:1602 erase_global_deps` is a sub-environment), DV-3. -/
theorem hsub : SubEnv σ.decls decls := by
  intro ci h
  simp only [σ, evalEnvOf, decls, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> rfl

/-- The names declared in the environment are `hp`, `P`, `A`. -/
theorem mem_names {c} (h : (findDecl decls c).isSome = true) : c = `hp ∨ c = `P ∨ c = `A := by
  rw [findDecl, List.find?_isSome] at h
  obtain ⟨x, hx, hc⟩ := h
  simp only [decls, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
    simp [ConstantInfo.name, ConstantInfo.toConstantVal, A_val, P_val, hp_val] at hc <;>
    subst hc <;> simp

/-- The kernames of the environment's constants are distinct. Reference: none (DV-14;
`MR E/Extract.v:324 erases_deps_tConst` shares the kername of source and target). -/
theorem hinj : KernameInj σ.decls := by
  intro c₁ c₂ h₁ h₂ hk
  rcases mem_names h₁ with rfl | rfl | rfl <;> rcases mem_names h₂ with rfl | rfl | rfl <;>
    first | rfl | (revert hk; decide)

/-- The empty λ□ environment is closed. Reference: `closed_env` (`MR E/EGlobalEnv.v:181`). -/
theorem hlc : LenvClosed [] := by
  intro kn cb b h
  simp [lookupConst] at h

/-- The empty λ□ environment stores no fixpoint. Reference: the part of
`MR E/EDeps.v:594 globals_erased_with_deps` that `erases_deps` cannot carry (DV-7). -/
theorem hblocks : BlocksErased env3 σ [] := by
  intro c ci defs i _ hl
  simp [lookupConst] at hl

/-! ## The program -/

/-- `fun x : A => x`, the value. -/
def v : Expr := .lam `x (.const `A []) (.bvar 0) .default

/-- `fun (h : P.{0}) (x : A) => x`. -/
def fE : Expr := .lam `h (.const `P [.zero]) v .default

/-- The erased term `(fun (h : P.{0}) (x : A) => x) hp`. -/
def e : Expr := .app fE (.const `hp [])

/-- The image of `fE` in the model. -/
def fV : VExpr := .lam vP0 (.lam vA (.bvar 0))

/-- The image of `e` in the model. -/
def e' : VExpr := .app fV (.const `hp [])

/-- The erasure of `e`: `(λh. λx. x) □`. -/
def t : LBTerm := .app (.lambda (binderNameOf `h) (.lambda (binderNameOf `x) (.bvar 0))) .box

/-- The erasure of `v`: `λx. x`. -/
def t' : LBTerm := .lambda (binderNameOf `x) (.bvar 0)

/-! ## The hypotheses on the program -/

/-- `e` evaluates to `v`: β, with the proof `hp` an atom value (`constAtom`). Reference: the
hypothesis `Σ ⊢ t ⇓ v` of `erases_correct` (`MR erasure/theories/ErasureCorrectness.v:51`). -/
theorem hev : SrcEval σ e v :=
  .beta (.atom trivial) (.constAtom (ci := .axiomInfo hp_val) rfl atom_hp) (.atom trivial)

/-- `fV : P.{0} → A → A` in `env3`. -/
theorem fV_ty : env3.HasType 0 [] fV (.forallE vP0 (.forallE vA vA)) :=
  VEnv.HasType.lam (u := .zero) (hP0ty e3P) (VEnv.HasType.lam (u := .succ .zero) hAty (.bvar .zero))

/-- `e` translates to `e'`, with both sides of the application typed. Reference: the hypothesis
`Σ ;;; [] |- t : T` of `erases_correct` (`MR erasure/theories/ErasureCorrectness.v:51`). -/
theorem he : TrS env3 [] [] e e' :=
  .app (A := vP0) (B := .forallE vA vA) fV_ty hhpty
    (.lam ⟨_, hP0ty e3P⟩ (.const e3P rfl rfl)
      (.lam ⟨_, hAty⟩ (.const e3A rfl rfl) (.bvar (A := vA) rfl)))
    (.const e3hp rfl rfl)

/-- `e` erases to `t`: the proof `hp` erases to `□` (it is erasable, its type `P.{0}` being a
proposition). Reference: the hypothesis `Σ ;;; [] |- t ⇝ℇ t'` of `erases_correct`
(`MR erasure/theories/ErasureCorrectness.v:51`). -/
theorem her : Erases env3 [] σ.isAtom (RecIn []) [] e t :=
  .app (.lam (.const e3P rfl rfl) (.lam (.const e3A rfl rfl) .bvar))
    (.box ⟨_, .const e3hp rfl rfl, vP0, hhpty, .inr ⟨.zero, hP0ty e3P, VLevel.equiv_def'.2 rfl⟩⟩)

/-- `t` has no dependency. Reference: the hypothesis `erases_deps Σ Σ' t'` of `erases_correct`
(`MR erasure/theories/ErasureCorrectness.v:51`). -/
theorem hdeps : ErasesDeps env3 σ [] t := .app (.lambda (.lambda .bvar)) .box

/-! ## The instance and its conclusion -/

/-- `EraseProof.erases_correct` on NV-7, every hypothesis a checked term. -/
theorem inst : ∃ t'', Erases env3 [] σ.isAtom (RecIn []) [] v t'' ∧
    LBEval defaultFlags [] t t'' :=
  erases_correct henv hsub hinj hlc he her hdeps hblocks hev

/-- The conclusion of `erases_correct` on NV-7 holds with the non-`□` witness `λx. x`. -/
theorem concl : Erases env3 [] σ.isAtom (RecIn []) [] v t' ∧ LBEval defaultFlags [] t t' :=
  ⟨.lam (.const e3A rfl rfl) .bvar, .beta (.atom rfl) (.atom rfl) (.atom rfl)⟩

/-- Every witness of `erases_correct` on NV-7 is `λx. x` (λ□ evaluation is deterministic). -/
theorem witness {t'' : LBTerm} (h : Erases env3 [] σ.isAtom (RecIn []) [] v t'' ∧
    LBEval defaultFlags [] t t'') : t'' = t' :=
  LBEval.deterministic h.2 concl.2

end EraseProof.Test.NV7
