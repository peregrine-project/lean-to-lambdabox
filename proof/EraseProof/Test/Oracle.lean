import EraseProof.Oracle
import EraseProof.Source.Restrict

/-!
# The oracle: the register test of its δ policy (DV-18) and soundness instances

Tests, off the path of the final theorem. `Oracle.irreducibleAlias`, which `doc/DIVERGENCES.md`
DV-18 cites, runs the shipping oracle `Erasure.Pure.isErasable` at `Erasure.oracleFuel` on the
formal environment `IrrAlias` and is checked by `decide`. `Oracle.sound_A` and `Oracle.sound_hP`
are instances of `EraseProof.Pure.isErasable_sound` on the environment `D1` (`A : Type`,
`P : Prop`, `hP : P`, `F : Type → Type`): every hypothesis is discharged by a checked term (the
model `D1.henv`, `D1.hsub`, the translation of the term, and the oracle's answer by `decide`), and
the conclusion is the erasability of the type former `A` and of the proof `hP`.
-/

open Lean Lean4Lean Erasure

namespace EraseProof.Test

/-! ## Environment of the register test `irreducibleAlias` (DV-18)

Newest first: `a : A`, `fI : Endo`, `Endo : Type := A → A`, `hR : R`, `R : IProp`,
`IProp : Type := Prop`, `A : Type`: the formal counterpart of the corpus programs whose aliases
`IProp` and `Endo` are `@[irreducible]` in Lean. The attribute has no counterpart in the model, and
the oracle does not read it. -/

namespace IrrAlias
/-- `Type`. -/
def ty1E : Expr := .sort (.succ .zero)
/-- `A`. -/
def AE : Expr := .const `A []
/-- `axiom A : Type`. -/
def A_val : AxiomVal := { name := `A, levelParams := [], type := ty1E, isUnsafe := false }
/-- `def IProp : Type := Prop`. -/
def IProp_val : DefinitionVal :=
  { name := `IProp, levelParams := [], type := ty1E, value := .sort .zero, hints := .abbrev,
    safety := .safe, all := [`IProp] }
/-- `axiom R : IProp`. -/
def R_val : AxiomVal := { name := `R, levelParams := [], type := .const `IProp [], isUnsafe := false }
/-- `axiom hR : R`. -/
def hR_val : AxiomVal := { name := `hR, levelParams := [], type := .const `R [], isUnsafe := false }
/-- `def Endo : Type := A → A`. -/
def Endo_val : DefinitionVal :=
  { name := `Endo, levelParams := [], type := ty1E, value := .forallE `x AE AE .default,
    hints := .abbrev, safety := .safe, all := [`Endo] }
/-- `axiom fI : Endo`. -/
def fI_val : AxiomVal := { name := `fI, levelParams := [], type := .const `Endo [], isUnsafe := false }
/-- `axiom a : A`. -/
def a_val : AxiomVal := { name := `a, levelParams := [], type := AE, isUnsafe := false }
/-- The environment, newest first. -/
def decls : List ConstantInfo :=
  [.axiomInfo a_val, .axiomInfo fI_val, .defnInfo Endo_val, .axiomInfo hR_val, .axiomInfo R_val,
   .defnInfo IProp_val, .axiomInfo A_val]
/-- The oracle's context. -/
def cx : Pure.Ctx := ⟨decls⟩
/-- `fun (_ : R) (x : A) => x`: its type is a Π whose domain's sort is behind `IProp`. -/
def guardE : Expr := .lam `h (.const `R []) (.lam `x AE (.bvar 0) .default) .default
/-- `fI a`: the head's type is `Endo`, an alias of a Π. -/
def appE : Expr := .app (.const `fI []) (.const `a [])
/-- `R`. -/
def RE : Expr := .const `R []
/-- `hR`. -/
def hRE : Expr := .const `hR []
end IrrAlias

namespace Oracle

/-- Register test (DV-18): every reduction of the oracle uses the kernel's δ, as those of
`is_erasableb` do. Through the aliases `IProp` and `Endo`, `@[irreducible]` in the corpus programs,
it types `fun (_ : R) (x : A) => x` and `fI a` (keep), which `Meta`'s type inference at default
transparency fails to type, and it boxes `R` and the proof `hR` of `R : IProp`, which `Meta` keeps
(SHIPPING-CHANGES R-14, on the `Meta` path only). Reference: `MR E/ErasureFunction.v:894
is_erasableb`, whose reductions unfold every constant with a body (`MR S/PCUICSafeReduce.v:1839
hnf` at `MR P/PCUICNormal.v:26 RedFlags.default`), DV-18. -/
theorem irreducibleAlias :
    (Pure.isErasable IrrAlias.cx oracleFuel [] IrrAlias.guardE).toOption = some false ∧
    (Pure.isErasable IrrAlias.cx oracleFuel [] IrrAlias.appE).toOption = some false ∧
    (Pure.isErasable IrrAlias.cx oracleFuel [] IrrAlias.RE).toOption = some true ∧
    (Pure.isErasable IrrAlias.cx oracleFuel [] IrrAlias.hRE).toOption = some true := by
  decide

end Oracle

/-! ## The environment `D1`

Newest first: `F : Type → Type`, `hP : P`, `P : Prop`, `A : Type`, all axioms, with its model in
lean4lean. -/

namespace D1
/-- `axiom A : Type`. -/
def A_val : AxiomVal :=
  { name := `A, levelParams := [], type := .sort (.succ .zero), isUnsafe := false }
/-- `axiom P : Prop`. -/
def P_val : AxiomVal := { name := `P, levelParams := [], type := .sort .zero, isUnsafe := false }
/-- `axiom hP : P`. -/
def hP_val : AxiomVal := { name := `hP, levelParams := [], type := .const `P [], isUnsafe := false }
/-- `axiom F : Type → Type`. -/
def F_val : AxiomVal :=
  { name := `F, levelParams := [],
    type := .forallE `x (.sort (.succ .zero)) (.sort (.succ .zero)) .default, isUnsafe := false }
/-- The environment, newest first. -/
def decls : List ConstantInfo :=
  [.axiomInfo F_val, .axiomInfo hP_val, .axiomInfo P_val, .axiomInfo A_val]
/-- Nothing is `@[extern]`. -/
def view : EnvView :=
  ⟨fun n => decls.find? (·.name == n), fun _ => false, fun _ => none⟩
/-- The evaluation environment. -/
def σ : EvalEnv := evalEnvOf view {} decls
/-- The oracle's context. -/
def cx : Pure.Ctx := ⟨decls⟩

/-- The type former `A` is an atom. -/
theorem atom_A : σ.isAtom `A = true := by decide
/-- The proof `hP` is an atom: its type `P` is an evident proposition. -/
theorem atom_hP : σ.isAtom `hP = true := by decide
/-- The type former `F` is an atom. -/
theorem atom_F : σ.isAtom `F = true := by decide
/-- The type former `P` is an atom. -/
theorem atom_P : σ.isAtom `P = true := by decide

/-- The image of `A`. -/
def vA : VExpr := .const `A []
/-- The image of `P`. -/
def vP : VExpr := .const `P []
/-- The image of `Type`. -/
def ty1 : VExpr := .sort (.succ .zero)
/-- The model of `A`. -/
def AC : VConstant := ⟨0, ty1⟩
/-- The model of `P`. -/
def PC : VConstant := ⟨0, .sort .zero⟩
/-- The model of `hP`. -/
def hPC : VConstant := ⟨0, vP⟩
/-- The model of `F`. -/
def FC : VConstant := ⟨0, .forallE ty1 ty1⟩

/-- The model after adding `A`. -/
def env1 : VEnv := { VEnv.empty with constants := fun n => if `A = n then some AC else none }
/-- The model after adding `P`. -/
def env2 : VEnv :=
  { env1 with constants := fun n => if `P = n then some PC else env1.constants n }
/-- The model after adding `hP`. -/
def env3 : VEnv :=
  { env2 with constants := fun n => if `hP = n then some hPC else env2.constants n }
/-- The model of the environment: `env3` with `F`. -/
def env4 : VEnv :=
  { env3 with constants := fun n => if `F = n then some FC else env3.constants n }

/-- `A` is declared in `env4`. -/
theorem e4A : env4.constants `A = some AC := rfl
/-- `P` is declared in `env4`. -/
theorem e4P : env4.constants `P = some PC := rfl
/-- `hP` is declared in `env4`. -/
theorem e4hP : env4.constants `hP = some hPC := rfl

/-- `P : Prop` in `env2`, the model to which `hP` is added. -/
theorem hPty2 {Γ} : env2.HasType 0 Γ vP (.sort .zero) :=
  VEnv.HasType.const (ci := PC) rfl (fun _ h => nomatch h) rfl

/-- The environment's model is `env4`. Reference: the hypothesis `wf_ext Σ` of `is_erasableP`
(`MR erasure/theories/ErasureFunction.v:915`). -/
theorem henv : ProgEnv decls env4 :=
  .«axiom» (ci' := FC)
    (.«axiom» (ci' := hPC)
      (.«axiom» (ci' := PC)
        (.«axiom» (ci' := AC) .nil ⟨rfl, .sort rfl⟩ ⟨_, .sortDF trivial trivial rfl⟩ rfl)
        ⟨rfl, .sort rfl⟩ ⟨_, .sortDF trivial trivial rfl⟩ rfl)
      ⟨rfl, .const rfl rfl rfl⟩ ⟨_, hPty2⟩ rfl)
    ⟨rfl, .forallE ⟨_, .sortDF trivial trivial rfl⟩ ⟨_, .sortDF trivial trivial rfl⟩
      (.sort rfl) (.sort rfl)⟩
    ⟨_, .forallE (.sortDF trivial trivial rfl) (.sortDF trivial trivial rfl)⟩ rfl

/-- Every declaration is the first of its name: the oracle's declarations (`cx.decls`) and the
evaluation environment's (`σ.decls`) are `decls` itself. -/
theorem hsub : SubEnv decls decls := by
  intro ci h
  simp only [decls, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> rfl

/-- `A : Type` in `env4`. -/
theorem hAty {Γ} : env4.HasType 0 Γ vA ty1 :=
  VEnv.HasType.const (ci := AC) e4A (fun _ h => nomatch h) rfl
/-- `P : Prop` in `env4`. -/
theorem hPty {Γ} : env4.HasType 0 Γ vP (.sort .zero) :=
  VEnv.HasType.const (ci := PC) e4P (fun _ h => nomatch h) rfl
/-- `hP : P` in `env4`. -/
theorem hhPty {Γ} : env4.HasType 0 Γ (.const `hP []) vP :=
  VEnv.HasType.const (ci := hPC) e4hP (fun _ h => nomatch h) rfl
end D1

namespace Oracle

/-- An oracle run whose `toOption` is `some a` succeeded with `a`. -/
theorem ok_of_toOption {ε α} {x : Except ε α} {a : α} (h : x.toOption = some a) : x = .ok a := by
  cases x <;> simp_all [Except.toOption]

/-- The oracle answers "erasable" on the type former `A`. -/
theorem oracle_A : (Pure.isErasable D1.cx oracleFuel [] (.const `A [])).toOption = some true := by
  decide

/-- The oracle answers "erasable" on the proof `hP`. -/
theorem oracle_hP :
    (Pure.isErasable D1.cx oracleFuel [] (.const `hP [])).toOption = some true := by
  decide

/-- Instance of `EraseProof.Pure.isErasable_sound` on the type former `A` of `D1`, with no locals:
every hypothesis is a checked term, and the conclusion is that `A` is erasable (its type `Type`
is an arity). Reference: `is_erasableP` (`MR erasure/theories/ErasureFunction.v:915`). -/
theorem sound_A : ErasableS D1.env4 [] [] (.const `A []) :=
  Pure.isErasable_sound (cx := D1.cx) (fuel := oracleFuel) D1.henv D1.hsub .nil
    (.const D1.e4A rfl rfl) (ok_of_toOption oracle_A)

/-- Instance of `EraseProof.Pure.isErasable_sound` on the proof `hP` of `D1`, with no locals: every
hypothesis is a checked term, and the conclusion is that `hP` is erasable (its type `P` is a
proposition). Reference: `is_erasableP` (`MR erasure/theories/ErasureFunction.v:915`). -/
theorem sound_hP : ErasableS D1.env4 [] [] (.const `hP []) :=
  Pure.isErasable_sound (cx := D1.cx) (fuel := oracleFuel) D1.henv D1.hsub .nil
    (.const D1.e4hP rfl rfl) (ok_of_toOption oracle_hP)

end Oracle

end EraseProof.Test
