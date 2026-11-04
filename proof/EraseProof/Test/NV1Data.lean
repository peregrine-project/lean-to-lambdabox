import LeanToLambdaBox

/-!
# NV-1: the program

    inductive B | f | t
    def B.neg (b : B) : B := B.casesOn (motive := fun _ => B) b B.t B.f
    #erase B.neg B.f            -- evaluates to B.t

The declarations as Lean v4.35.0-rc2 generates them (`tools/NVEmit.lean` checks them against the
elaborator's), newest first: `P = [B.neg, B.casesOn, B.rec, B.f, B.t, B]`; the term `e`; the view
`#erase` reads (`P` as a list, no `@[extern]`, inline or `implemented_by` attributes); the default
configuration. The first non-vacuity instance of the final theorem, whose hypotheses `hfrag` and
`hrun` (`MR E/ErasureFunctionProperties.v:657 erase_correct`) `Test/NV1Run.lean` discharges.
-/

open Lean Erasure

namespace EraseProof.Test.NV1

def tB : Expr := .const `B []
def cF : Expr := .const `B.f []
def cT : Expr := .const `B.t []
/-- `(t : B) → Sort u` -/
def motTy : Expr := .forallE `t tB (.sort (.param `u)) .default

def B_ind : InductiveVal :=
  { name := `B, levelParams := [], type := .sort (.succ .zero), numParams := 0, numIndices := 0,
    all := [`B], ctors := [`B.f, `B.t], numNested := 0, isRec := false, isUnsafe := false,
    isReflexive := false }

def Bf_ctor : ConstructorVal :=
  { name := `B.f, levelParams := [], type := tB, induct := `B, cidx := 0, numParams := 0,
    numFields := 0, isUnsafe := false }

def Bt_ctor : ConstructorVal :=
  { name := `B.t, levelParams := [], type := tB, induct := `B, cidx := 1, numParams := 0,
    numFields := 0, isUnsafe := false }

/-- `{motive : B → Sort u} → (f : motive B.f) → (t : motive B.t) → (t : B) → motive t` -/
def recTy : Expr :=
  .forallE `motive motTy
    (.forallE `f (.app (.bvar 0) cF)
      (.forallE `t (.app (.bvar 1) cT)
        (.forallE `t tB (.app (.bvar 3) (.bvar 0)) .default) .default) .default) .implicit

def recRhs (i : Nat) : Expr :=
  .lam `motive motTy
    (.lam `f (.app (.bvar 0) cF) (.lam `t (.app (.bvar 1) cT) (.bvar i) .default) .default) .default

def B_rec : RecursorVal :=
  { name := `B.rec, levelParams := [`u], type := recTy, all := [`B], numParams := 0,
    numIndices := 0, numMotives := 1, numMinors := 2,
    rules := [{ ctor := `B.f, nfields := 0, rhs := recRhs 1 },
              { ctor := `B.t, nfields := 0, rhs := recRhs 0 }],
    k := false, isUnsafe := false }

/-- `{motive : B → Sort u} → (t : B) → motive B.f → motive B.t → motive t` -/
def casesOnTy : Expr :=
  .forallE `motive motTy
    (.forallE `t tB
      (.forallE `f (.app (.bvar 1) cF)
        (.forallE `t (.app (.bvar 2) cT) (.app (.bvar 3) (.bvar 2)) .default) .default) .default)
    .implicit

/-- `fun {motive} t f t_1 => @B.rec motive f t_1 t` -/
def casesOnVal : Expr :=
  .lam `motive motTy
    (.lam `t tB
      (.lam `f (.app (.bvar 1) cF)
        (.lam `t (.app (.bvar 2) cT)
          (.app (.app (.app (.app (.const `B.rec [.param `u]) (.bvar 3)) (.bvar 1)) (.bvar 0))
            (.bvar 2)) .default) .default) .default) .implicit

def B_casesOn : DefinitionVal :=
  { name := `B.casesOn, levelParams := [`u], type := casesOnTy, value := casesOnVal,
    hints := .abbrev, safety := .safe, all := [`B.casesOn] }

def negTy : Expr := .forallE `b tB tB .default

/-- `fun b => @B.casesOn.{1} (fun x => B) b B.t B.f` -/
def negVal : Expr :=
  .lam `b tB
    (.app (.app (.app (.app (.const `B.casesOn [.succ .zero]) (.lam `x tB tB .default))
      (.bvar 0)) cT) cF) .default

def neg_def : DefinitionVal :=
  { name := `B.neg, levelParams := [], type := negTy, value := negVal, hints := .regular 1,
    safety := .safe, all := [`B.neg] }

/-- The program, newest first. -/
def P : List ConstantInfo :=
  [.defnInfo neg_def, .defnInfo B_casesOn, .recInfo B_rec, .ctorInfo Bf_ctor, .ctorInfo Bt_ctor,
    .inductInfo B_ind]

/-- The erased term `B.neg B.f`. -/
def e : Expr := .app (.const `B.neg []) cF

/-- The view `#erase` reads: `P` as a list, no `@[extern]`, inline or `implemented_by` attributes. -/
def view : EnvView where
  find? := Erasure.findConst P
  isExtern _ := false
  inlineAttr? _ := none
  implementedBy? _ := none

/-- The default configuration (`#erase` without options). -/
def cfg : ErasureConfig := {}

end EraseProof.Test.NV1
