import EraseProof.Test.NV1Data

/-!
# NV-P and NV-K: the programs

    @Eq.casesOn.{1,1} B B.t (fun _ _ => B → B) B.t (@Eq.refl.{1} B B.t) (fun y => y)     -- NV-P
    theorem hEq : B.t = B.t := rfl
    @Eq.casesOn.{1,1} B B.t (fun _ _ => B → B) B.t hEq (fun y => y)                    -- NV-K

`B` is NV-1's `inductive B | f | t`. A recognized `casesOn` on the `Prop` inductive `Eq`, on a
constructor (NV-P) and on a lemma (NV-K); both evaluate to `fun y => y`. The declarations as Lean
v4.35.0-rc2 generates them, newest first: `NVP.P = [Eq.casesOn, Eq.rec, Eq.refl, Eq, B.rec, B.f,
B.t, B]`, `NVK.P = [hEq] ++ NVP.P`; the views read them as lists, with no attributes; the default
configuration. Non-vacuity instances of the final theorem, whose hypotheses `hfrag` and `hrun`
(`MR E/ErasureFunctionProperties.v:657 erase_correct`) `Test/NVPRun.lean` discharges.
-/

open Lean Erasure

namespace EraseProof.Test.NVP

open EraseProof.Test.NV1 (tB cF cT B_ind Bf_ctor Bt_ctor B_rec)

/-- The anonymous binder name Lean uses in `Eq`'s declarations. -/
def an : Name := .mkNum (.mkStr (.mkStr (.mkStr (.mkStr .anonymous "a") "_@") "_internal") "_hyg") 0

def u1 : Level := .param `u_1
def lu : Level := .param `u
def eqC (α a b : Expr) : Expr := mkAppN (.const `Eq [u1]) #[α, a, b]
def reflC (α a : Expr) : Expr := mkAppN (.const `Eq.refl [u1]) #[α, a]

def Eq_ind : InductiveVal :=
  { name := `Eq, levelParams := [`u_1],
    type := .forallE `α (.sort u1) (.forallE an (.bvar 0) (.forallE an (.bvar 1) (.sort .zero) .default)
      .default) .implicit,
    numParams := 2, numIndices := 1, all := [`Eq], ctors := [`Eq.refl], numNested := 0,
    isRec := false, isUnsafe := false, isReflexive := false }

def Eq_refl : ConstructorVal :=
  { name := `Eq.refl, levelParams := [`u_1],
    type := .forallE `α (.sort u1) (.forallE `a (.bvar 0) (eqC (.bvar 1) (.bvar 0) (.bvar 0)) .default)
      .implicit,
    induct := `Eq, cidx := 0, numParams := 2, numFields := 0, isUnsafe := false }

/-- `(a_1 : α) → a = a_1 → Sort u` under `α a`. -/
def eqMotTy : Expr :=
  .forallE an (.bvar 1) (.forallE `t (eqC (.bvar 2) (.bvar 1) (.bvar 0)) (.sort lu) .default) .default

def eqRecTy : Expr :=
  .forallE `α (.sort u1) (.forallE an (.bvar 0) (.forallE `motive eqMotTy
    (.forallE `refl (.app (.app (.bvar 0) (.bvar 1)) (reflC (.bvar 2) (.bvar 1)))
      (.forallE an (.bvar 3) (.forallE `t (eqC (.bvar 4) (.bvar 3) (.bvar 0))
        (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)) .default) .implicit) .default) .implicit)
    .implicit) .implicit

def eqRecRhs : Expr :=
  .lam `α (.sort u1) (.lam an (.bvar 0) (.lam `motive eqMotTy
    (.lam `refl (.app (.app (.bvar 0) (.bvar 1)) (reflC (.bvar 2) (.bvar 1))) (.bvar 0) .default)
    .default) .default) .implicit

def Eq_rec : RecursorVal :=
  { name := `Eq.rec, levelParams := [`u, `u_1], type := eqRecTy, all := [`Eq], numParams := 2,
    numIndices := 1, numMotives := 1, numMinors := 1,
    rules := [{ ctor := `Eq.refl, nfields := 0, rhs := eqRecRhs }], k := true, isUnsafe := false }

def eqCasesOnTy : Expr :=
  .forallE `α (.sort u1) (.forallE an (.bvar 0) (.forallE `motive eqMotTy
    (.forallE an (.bvar 2) (.forallE `t (eqC (.bvar 3) (.bvar 2) (.bvar 0))
      (.forallE `refl (.app (.app (.bvar 2) (.bvar 3)) (reflC (.bvar 4) (.bvar 3)))
        (.app (.app (.bvar 3) (.bvar 2)) (.bvar 1)) .default) .default) .implicit) .implicit)
    .implicit) .implicit

def eqCasesOnVal : Expr :=
  .lam `α (.sort u1) (.lam an (.bvar 0) (.lam `motive eqMotTy
    (.lam an (.bvar 2) (.lam `t (eqC (.bvar 3) (.bvar 2) (.bvar 0))
      (.lam `refl (.app (.app (.bvar 2) (.bvar 3)) (reflC (.bvar 4) (.bvar 3)))
        (mkAppN (.const `Eq.rec [lu, u1]) #[.bvar 5, .bvar 4, .bvar 3, .bvar 0, .bvar 2, .bvar 1])
        .default) .default) .implicit) .implicit) .implicit) .implicit

def Eq_casesOn : DefinitionVal :=
  { name := `Eq.casesOn, levelParams := [`u, `u_1], type := eqCasesOnTy, value := eqCasesOnVal,
    hints := .abbrev, safety := .safe, all := [`Eq.casesOn] }

/-- NV-P's program, newest first. -/
def P : List ConstantInfo :=
  [.defnInfo Eq_casesOn, .recInfo Eq_rec, .ctorInfo Eq_refl, .inductInfo Eq_ind,
    .recInfo B_rec, .ctorInfo Bf_ctor, .ctorInfo Bt_ctor, .inductInfo B_ind]

def l1 : Level := .succ .zero
def tBB : Expr := .forallE `y tB tB .default
/-- The motive `fun x h => B → B`. -/
def motE : Expr := .lam `x tB (.lam `h (mkAppN (.const `Eq [l1]) #[tB, cT, .bvar 0]) tBB .default) .default
/-- The alternative `fun y => y`. -/
def idB : Expr := .lam `y tB (.bvar 0) .default

/-- NV-P's term. -/
def e : Expr :=
  mkAppN (.const `Eq.casesOn [l1, l1])
    #[tB, cT, motE, cT, mkAppN (.const `Eq.refl [l1]) #[tB, cT], idB]
/-- NV-P's view: `P` as a list, no attributes. -/
def view : EnvView where
  find? := findConst P
  isExtern _ := false
  inlineAttr? _ := none
  implementedBy? _ := none

/-- The default configuration. -/
def cfg : ErasureConfig := {}

end EraseProof.Test.NVP

namespace EraseProof.Test.NVK

open EraseProof.Test.NV1 (tB cT)
open EraseProof.Test.NVP (l1 motE idB)

/-- `@Eq.{1} B B.t B.t` -/
def hEqTy : Expr := mkAppN (.const `Eq [l1]) #[tB, cT, cT]

/-- `theorem hEq : B.t = B.t := rfl` -/
def hEq_thm : TheoremVal :=
  { name := `hEq, levelParams := [], type := hEqTy, value := mkAppN (.const `rfl [l1]) #[tB, cT],
    all := [`hEq] }

/-- NV-K's program, newest first. -/
def P : List ConstantInfo := .thmInfo hEq_thm :: NVP.P

/-- NV-K's term. -/
def e : Expr :=
  mkAppN (.const `Eq.casesOn [l1, l1]) #[tB, cT, motE, cT, .const `hEq [], idB]

/-- NV-K's view: `P` as a list, no attributes. -/
def view : EnvView where
  find? := findConst P
  isExtern _ := false
  inlineAttr? _ := none
  implementedBy? _ := none

end EraseProof.Test.NVK
