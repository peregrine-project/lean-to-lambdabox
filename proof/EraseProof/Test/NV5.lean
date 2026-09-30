import EraseProof.Simulation
import EraseProof.Test.LBEval
import EraseProof.Test.Oracle

/-!
# Non-vacuity instance NV-5: a type former as an argument

The program `(fun (α : Type) (x : α) => x) A` over the environment `D1` (`A : Type`, `P : Prop`,
`hP : P`, `F : Type → Type`, all axioms; `EraseProof.Test.D1`, in `Test/Oracle.lean`). It
evaluates by β to `fun x : A => x`, with the type former `A` evaluated as an atom (`constAtom`);
its erasure `(λα. λx. x) □` evaluates in λ□ to `λx. x`.

Every hypothesis of `EraseProof.erases_correct` is discharged by a checked term: the program's
model `D1.henv`, the sub-environment `D1.hsub`, the kername injectivity `D1.hinj`, the closedness
of the empty λ□ environment `D1.hlc`, the translation `he`, the erasure `her`, its dependencies
`hdeps`, the stored blocks `D1.hblocks`, and the source evaluation `hev`. `inst` applies the
theorem; `concl` exhibits its conclusion with the non-`□` witness `λx. x`, and `witness` shows, by
`EraseProof.Test.LBEval.deterministic`, that every witness of the theorem is this one.
Reference: `erases_correct` (`MR erasure/theories/ErasureCorrectness.v:51`).
-/

open Lean Lean4Lean Erasure

namespace EraseProof.Test

/-! ## `D1`: the hypotheses on the environment

The facts of `D1` that `erases_correct` takes besides `D1.henv` and `D1.hsub`, with the empty λ□
environment `[]` of the instances NV-5 and NV-6. -/

namespace D1

/-- The names declared in `D1` are `F`, `hP`, `P`, `A`. -/
theorem mem_names {c} (h : (findDecl decls c).isSome = true) :
    c = `F ∨ c = `hP ∨ c = `P ∨ c = `A := by
  rw [findDecl, List.find?_isSome] at h
  obtain ⟨x, hx, hc⟩ := h
  simp only [decls, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
    simp [ConstantInfo.name, ConstantInfo.toConstantVal, A_val, P_val, hP_val, F_val] at hc <;>
    subst hc <;> simp

/-- The kernames of `D1`'s constants are distinct: the injectivity hypothesis of
`erases_correct`, which `collectDeps`'s collision check provides. Reference: none (DV-14;
`MR E/Extract.v:324 erases_deps_tConst` shares the kername of source and target). -/
theorem hinj : KernameInj σ.decls := by
  intro c₁ c₂ h₁ h₂ hk
  rcases mem_names h₁ with rfl | rfl | rfl | rfl <;>
    rcases mem_names h₂ with rfl | rfl | rfl | rfl <;>
    first | rfl | (revert hk; decide)

/-- The empty λ□ environment is closed. Reference: `closed_env` (`MR E/EGlobalEnv.v:181`), the
hypothesis of `erases_correct` on the λ□ environment. -/
theorem hlc : LenvClosed [] := by
  intro kn cb b h
  simp [lookupConst] at h

/-- The empty λ□ environment stores no fixpoint. Reference: the part of
`MR E/EDeps.v:594 globals_erased_with_deps` that `erases_deps` cannot carry (DV-7). -/
theorem hblocks : BlocksErased env4 σ [] := by
  intro c ci defs i _ hl
  simp [lookupConst] at hl

end D1

namespace NV5

/-! ## The program -/

/-- `fun (α : Type) (x : α) => x`. -/
def idE : Expr := .lam `α (.sort (.succ .zero)) (.lam `x (.bvar 0) (.bvar 0) .default) .default

/-- The erased term `(fun (α : Type) (x : α) => x) A`. -/
def e : Expr := .app idE (.const `A [])

/-- Its value `fun x : A => x`. -/
def v : Expr := .lam `x (.const `A []) (.bvar 0) .default

/-- The image of `idE` in the model. -/
def idV : VExpr := .lam D1.ty1 (.lam (.bvar 0) (.bvar 0))

/-- The image of `e` in the model. -/
def e' : VExpr := .app idV D1.vA

/-- The erasure of `e`: `(λα. λx. x) □`. -/
def t : LBTerm := .app (.lambda (binderNameOf `α) (.lambda (binderNameOf `x) (.bvar 0))) .box

/-- The erasure of `v`: `λx. x`. -/
def t' : LBTerm := .lambda (binderNameOf `x) (.bvar 0)

/-! ## The hypotheses -/

/-- `e` evaluates to `v`: β, with `A` an atom value (`constAtom`). Reference: the hypothesis
`Σ ⊢ t ⇓ v` of `erases_correct` (`MR erasure/theories/ErasureCorrectness.v:51`). -/
theorem hev : SrcEval D1.σ e v :=
  .beta (.atom trivial) (.constAtom (ci := .axiomInfo D1.A_val) rfl D1.atom_A rfl) (.atom trivial)

/-- `idV : Π (α : Type), α → α` in `D1.env4`. -/
theorem idV_ty : D1.env4.HasType 0 [] idV (.forallE D1.ty1 (.forallE (.bvar 0) (.bvar 1))) :=
  VEnv.HasType.lam (u := .succ (.succ .zero)) (.sortDF trivial trivial rfl)
    (VEnv.HasType.lam (u := .succ .zero) (.bvar .zero) (.bvar .zero))

/-- `e` translates to `e'`, with both sides of the application typed. Reference: the hypothesis
`Σ ;;; [] |- t : T` of `erases_correct` (`MR erasure/theories/ErasureCorrectness.v:51`). -/
theorem he : TrS D1.env4 [] [] e e' :=
  .app (A := D1.ty1) (B := .forallE (.bvar 0) (.bvar 1)) idV_ty D1.hAty
    (.lam ⟨_, .sortDF trivial trivial rfl⟩ (.sort rfl)
      (.lam ⟨_, .bvar .zero⟩ (.bvar (A := D1.ty1) rfl) (.bvar (A := .bvar 1) rfl)))
    (.const D1.e4A rfl rfl)

/-- `e` erases to `t`: the type former `A` erases to `□` (it is erasable, its type `Type` being an
arity; the same fact as `EraseProof.Test.Oracle.sound_A`, here by a direct typing). Reference: the
hypothesis `Σ ;;; [] |- t ⇝ℇ t'` of `erases_correct`
(`MR erasure/theories/ErasureCorrectness.v:51`). -/
theorem her : Erases D1.env4 [] D1.σ.isAtom (RecIn []) [] e t :=
  .app (.lam (.sort rfl) (.lam (.bvar (A := D1.ty1) rfl) .bvar))
    (.box ⟨D1.vA, .const D1.e4A rfl rfl, D1.ty1, D1.hAty, .inl trivial⟩)

/-- `t` has no dependency. Reference: the hypothesis `erases_deps Σ Σ' t'` of `erases_correct`
(`MR erasure/theories/ErasureCorrectness.v:51`). -/
theorem hdeps : ErasesDeps D1.env4 D1.σ [] t := .app (.lambda (.lambda .bvar)) .box

/-! ## The instance and its conclusion -/

/-- `EraseProof.erases_correct` on NV-5, every hypothesis a checked term. -/
theorem inst : ∃ t'', Erases D1.env4 [] D1.σ.isAtom (RecIn []) [] v t'' ∧
    LBEval defaultFlags [] t t'' :=
  erases_correct D1.henv D1.hsub D1.hinj D1.hlc he her hdeps D1.hblocks hev

/-- The conclusion of `erases_correct` on NV-5 holds with the non-`□` witness `λx. x`. -/
theorem concl : Erases D1.env4 [] D1.σ.isAtom (RecIn []) [] v t' ∧
    LBEval defaultFlags [] t t' :=
  ⟨.lam (.const D1.e4A rfl rfl) .bvar, .beta (.atom rfl) (.atom rfl) (.atom rfl)⟩

/-- Every witness of `erases_correct` on NV-5 is `λx. x` (λ□ evaluation is deterministic). -/
theorem witness {t'' : LBTerm} (h : Erases D1.env4 [] D1.σ.isAtom (RecIn []) [] v t'' ∧
    LBEval defaultFlags [] t t'') : t'' = t' :=
  LBEval.deterministic h.2 concl.2

end NV5

end EraseProof.Test
