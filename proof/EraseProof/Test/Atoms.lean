import EraseProof.Atoms
import EraseProof.Source.Restrict
import LeanToLambdaBox.Erasure.Pure

/-!
# Register tests of the atom class (DV-11)

Tests, off the path of the final theorem, that `doc/DIVERGENCES.md` DV-11 cites. Each runs the
shipping oracle `Erasure.Pure.isErasable` at `Erasure.oracleFuel` and the atom test
`EvalEnv.isAtom` on a formal environment, and is checked by `decide`:
- `defHead_kept`: a proof whose proposition is headed by a definition that unfolds to a Π is kept
  on an ill-typed spine, so such a proof is not an atom;
- `levelDependent_kept`: a proof whose propositionality depends on its own level parameter is kept
  at the parameter and erased at `0`, so it is not an atom.
-/

open Lean Lean4Lean Erasure

namespace EraseProof.Test

namespace Atoms

/-! ## Register test `defHead_kept` (DV-11)

Environment, newest first: `hq : Q`, `Q : Prop := ∀ P : Prop, P → P`, `a : A`, `A : Type`.
Program: `hq A a`, a spine of `hq` that is not well typed (`A` is not a proposition). -/

namespace DefHead
/-- `Prop`. -/
def ty0E : Expr := .sort .zero
/-- `Type`. -/
def ty1E : Expr := .sort (.succ .zero)
/-- `A`. -/
def AE : Expr := .const `A []
/-- `axiom A : Type`. -/
def A_val : AxiomVal := { name := `A, levelParams := [], type := ty1E, isUnsafe := false }
/-- `axiom a : A`. -/
def a_val : AxiomVal := { name := `a, levelParams := [], type := AE, isUnsafe := false }
/-- `def Q : Prop := ∀ P : Prop, P → P`. -/
def Q_val : DefinitionVal :=
  { name := `Q, levelParams := [], type := ty0E,
    value := .forallE `P ty0E (.forallE `h (.bvar 0) (.bvar 1) .default) .default,
    hints := .abbrev, safety := .safe, all := [`Q] }
/-- `axiom hq : Q`. -/
def hq_val : AxiomVal := { name := `hq, levelParams := [], type := .const `Q [], isUnsafe := false }
/-- The environment, newest first. -/
def decls : List ConstantInfo :=
  [.axiomInfo hq_val, .defnInfo Q_val, .axiomInfo a_val, .axiomInfo A_val]
/-- Nothing is `@[extern]`. -/
def view : EnvView := ⟨fun n => decls.find? (·.name == n), fun _ => false, fun _ => none⟩
/-- The evaluation environment. -/
def σ : EvalEnv := evalEnvOf view {} decls
/-- The oracle's context. -/
def cx : Pure.Ctx := ⟨decls⟩
/-- `hq A a`: a proof whose proposition is headed by a definition, applied through that
definition's Π to arguments of the wrong types. -/
def e0 : Expr := .app (.app (.const `hq []) AE) (.const `a [])
end DefHead

/-- Register test (DV-11): on the spine `hq A a` of a proof `hq` whose proposition is headed by a
definition that unfolds to a Π, the oracle answers "keep", so a proof whose type is headed by a
definition is not an atom (`Pure.isErasable_atom` holds on every spine of an atom). Reference: none
(DV-11; the head of a propositional constructor's type is an inductive, which never δ-reduces). -/
theorem defHead_kept :
    (Pure.isErasable DefHead.cx oracleFuel [] DefHead.e0).toOption = some false ∧
    DefHead.σ.isAtom `hq = false := by
  decide

/-! ## Register test `levelDependent_kept` (DV-11)

Environment, newest first: `hq.{v} : P.{v}`, `P.{v} : Sort v`. -/

namespace LevelDep
/-- `axiom P.{v} : Sort v`. -/
def P_val : AxiomVal :=
  { name := `P, levelParams := [`v], type := .sort (.param `v), isUnsafe := false }
/-- `axiom hq.{v} : P.{v}`. -/
def hq_val : AxiomVal :=
  { name := `hq, levelParams := [`v], type := .const `P [.param `v], isUnsafe := false }
/-- The environment, newest first. -/
def decls : List ConstantInfo := [.axiomInfo hq_val, .axiomInfo P_val]
/-- Nothing is `@[extern]`. -/
def view : EnvView := ⟨fun n => decls.find? (·.name == n), fun _ => false, fun _ => none⟩
/-- The evaluation environment. -/
def σ : EvalEnv := evalEnvOf view {} decls
/-- The oracle's context. -/
def cx : Pure.Ctx := ⟨decls⟩
end LevelDep

/-- Register test (DV-11): a proof whose propositionality depends on its own level parameters is
kept at the level parameter (`hq.{v}`, as a universe-polymorphic body is erased once, at its
parameters) and boxed at `0` (`hq.{0}`); so atomhood cannot depend on the occurrence, and under
the design's class `hq` is not an atom. Reference: `erases_subst_instance_decl`
(`MR E/ErasureProperties.v:412`), which occurrence-dependent atoms would break (DV-11). -/
theorem levelDependent_kept :
    (Pure.isErasable LevelDep.cx oracleFuel [] (.const `hq [.param `v])).toOption = some false ∧
    (Pure.isErasable LevelDep.cx oracleFuel [] (.const `hq [.zero])).toOption = some true ∧
    LevelDep.σ.isAtom `hq = false := by
  decide

end Atoms

end EraseProof.Test
