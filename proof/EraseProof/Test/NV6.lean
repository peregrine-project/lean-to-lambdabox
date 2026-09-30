import EraseProof.Test.NV5

/-!
# Non-vacuity instance NV-6: a proof as an argument

The program `(fun (h : P) (y : Type) => y) hP` over the environment `D1` (`A : Type`, `P : Prop`,
`hP : P`, `F : Type → Type`, all axioms; `EraseProof.Test.D1`, in `Test/Oracle.lean`). It
evaluates by β to `fun y : Type => y`, with the proof axiom `hP` evaluated as an atom
(`constAtom`: its type is an evident proposition); its erasure `(λh. λy. y) □` evaluates in λ□ to
`λy. y`.

Every hypothesis of `EraseProof.erases_correct` is discharged by a checked term: `D1.henv`,
`D1.hsub`, `D1.hinj`, `D1.hlc`, `D1.hblocks` (`Test/NV5.lean`), and this program's `he`, `her`,
`hdeps`, `hev`. `inst` applies the theorem; `concl` exhibits its conclusion with the non-`□`
witness `λy. y`, which `witness` shows is the only one. `hP_not_const` shows that the atom `hP`
erases only to `□`. Reference: `erases_correct` (`MR erasure/theories/ErasureCorrectness.v:51`).
-/

open Lean Lean4Lean Erasure

namespace EraseProof.Test.NV6

/-! ## The program -/

/-- `fun (h : P) (y : Type) => y`. -/
def kE : Expr := .lam `h (.const `P []) (.lam `y (.sort (.succ .zero)) (.bvar 0) .default) .default

/-- The erased term `(fun (h : P) (y : Type) => y) hP`. -/
def e : Expr := .app kE (.const `hP [])

/-- Its value `fun y : Type => y`. -/
def v : Expr := .lam `y (.sort (.succ .zero)) (.bvar 0) .default

/-- The image of `kE` in the model. -/
def kV : VExpr := .lam D1.vP (.lam D1.ty1 (.bvar 0))

/-- The image of `e` in the model. -/
def e' : VExpr := .app kV (.const `hP [])

/-- The erasure of `e`: `(λh. λy. y) □`. -/
def t : LBTerm := .app (.lambda (binderNameOf `h) (.lambda (binderNameOf `y) (.bvar 0))) .box

/-- The erasure of `v`: `λy. y`. -/
def t' : LBTerm := .lambda (binderNameOf `y) (.bvar 0)

/-! ## The hypotheses -/

/-- `e` evaluates to `v`: β, with the proof `hP` an atom value (`constAtom`). Reference: the
hypothesis `Σ ⊢ t ⇓ v` of `erases_correct` (`MR erasure/theories/ErasureCorrectness.v:51`). -/
theorem hev : SrcEval D1.σ e v :=
  .beta (.atom trivial) (.constAtom (ci := .axiomInfo D1.hP_val) rfl D1.atom_hP rfl) (.atom trivial)

/-- `kV : P → Type → Type` in `D1.env4`. -/
theorem kV_ty : D1.env4.HasType 0 [] kV (.forallE D1.vP (.forallE D1.ty1 D1.ty1)) :=
  VEnv.HasType.lam (u := .zero) D1.hPty
    (VEnv.HasType.lam (u := .succ (.succ .zero)) (.sortDF trivial trivial rfl) (.bvar .zero))

/-- `e` translates to `e'`, with both sides of the application typed. Reference: the hypothesis
`Σ ;;; [] |- t : T` of `erases_correct` (`MR erasure/theories/ErasureCorrectness.v:51`). -/
theorem he : TrS D1.env4 [] [] e e' :=
  .app (A := D1.vP) (B := .forallE D1.ty1 D1.ty1) kV_ty D1.hhPty
    (.lam ⟨_, D1.hPty⟩ (.const D1.e4P rfl rfl)
      (.lam ⟨_, .sortDF trivial trivial rfl⟩ (.sort rfl) (.bvar (A := D1.ty1) rfl)))
    (.const D1.e4hP rfl rfl)

/-- `e` erases to `t`: the proof `hP` erases to `□` (it is erasable, its type `P` being a
proposition; the same fact as `EraseProof.Test.Oracle.sound_hP`, here by a direct typing).
Reference: the hypothesis `Σ ;;; [] |- t ⇝ℇ t'` of `erases_correct`
(`MR erasure/theories/ErasureCorrectness.v:51`). -/
theorem her : Erases D1.env4 [] D1.σ.isAtom (RecIn []) [] e t :=
  .app (.lam (.const D1.e4P rfl rfl) (.lam (.sort rfl) .bvar))
    (.box ⟨_, .const D1.e4hP rfl rfl, D1.vP, D1.hhPty,
      .inr ⟨.zero, D1.hPty, VLevel.equiv_def'.2 rfl⟩⟩)

/-- `t` has no dependency. Reference: the hypothesis `erases_deps Σ Σ' t'` of `erases_correct`
(`MR erasure/theories/ErasureCorrectness.v:51`). -/
theorem hdeps : ErasesDeps D1.env4 D1.σ [] t := .app (.lambda (.lambda .bvar)) .box

/-! ## The instance and its conclusion -/

/-- `EraseProof.erases_correct` on NV-6, every hypothesis a checked term. -/
theorem inst : ∃ t'', Erases D1.env4 [] D1.σ.isAtom (RecIn []) [] v t'' ∧
    LBEval defaultFlags [] t t'' :=
  erases_correct D1.henv D1.hsub D1.hinj D1.hlc he her hdeps D1.hblocks hev

/-- The conclusion of `erases_correct` on NV-6 holds with the non-`□` witness `λy. y`. -/
theorem concl : Erases D1.env4 [] D1.σ.isAtom (RecIn []) [] v t' ∧
    LBEval defaultFlags [] t t' :=
  ⟨.lam (.sort rfl) .bvar, .beta (.atom rfl) (.atom rfl) (.atom rfl)⟩

/-- Every witness of `erases_correct` on NV-6 is `λy. y` (λ□ evaluation is deterministic). -/
theorem witness {t'' : LBTerm} (h : Erases D1.env4 [] D1.σ.isAtom (RecIn []) [] v t'' ∧
    LBEval defaultFlags [] t t'') : t'' = t' :=
  LBEval.deterministic h.2 concl.2

/-- The atom `hP` erases only to `□`: neither `Erases.const` nor `Erases.constRec` applies to it
(DV-11). -/
theorem hP_not_const {t'' : LBTerm} (h : Erases D1.env4 [] D1.σ.isAtom (RecIn []) []
    (.const `hP []) t'') : t'' = .box := by
  cases h with
  | const hac => simp [D1.atom_hP] at hac
  | constRec hac _ => simp [D1.atom_hP] at hac
  | box _ => rfl

end EraseProof.Test.NV6
