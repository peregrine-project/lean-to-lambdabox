import EraseProof.Test.NV1Data

/-!
# NV-5: the program

    inductive B | f | t                                   -- NV-1's
    structure W.{u} (Y : Sort u) : Sort (max 1 u) where (fst : B) (snd : Y)
    def wrap.{u} (Y : Sort u) (f : B → Y) : W.{u} Y := ⟨B.t, f B.t⟩
    #erase let p : W.{2} Type := wrap.{2} Type (fun _ => B); p.1      -- evaluates to B.t

`p.1` is the projection `.proj W 0 p`. `wrap`'s value is marked at its own level `u`, where
`f B.t : Y` is not erased; at `u := 2` its arguments are a type and a type former, both erased, so
the instantiated value applies an erased function (λ□ `□ B.t`). The declarations as Lean v4.35.0
has them (`tools/NVEmit.lean` checks them against the kernel's), newest first; the term `e`; the
view (`P` as a list, no attributes); the default configuration; the closure `D` of `e`. A
non-vacuity instance of the final theorem through `let`, a projection of a structure value and an
erased function applied; `Test/NV5Premises.lean` discharges its hypotheses.
-/

open Lean Erasure

namespace EraseProof.Test.NV5

open EraseProof.Test.NV1 (tB cT B_ind Bf_ctor Bt_ctor B_rec)

def l1 : Level := .succ .zero
def l2 : Level := .succ l1
def lu : Level := .param `u
def u1 : Level := .param `u_1

/-! ## `W` -/

def tW (u : Level) (Y : Expr) : Expr := .app (.const `W [u]) Y
def mkW (u : Level) (Y a b : Expr) : Expr := mkAppN (.const `W.mk [u]) #[Y, a, b]

def W_ind : InductiveVal :=
  { name := `W, levelParams := [`u], type := .forallE `Y (.sort lu) (.sort (.max l1 lu)) .default,
    numParams := 1, numIndices := 0, all := [`W], ctors := [`W.mk], numNested := 0,
    isRec := false, isUnsafe := false, isReflexive := false }
/-- `{Y : Sort u} → (fst : B) → (snd : Y) → W Y` -/
def mkTy : Expr :=
  .forallE `Y (.sort lu) (.forallE `fst tB (.forallE `snd (.bvar 1) (tW lu (.bvar 2)) .default) .default)
    .implicit
def W_mk : ConstructorVal :=
  { name := `W.mk, levelParams := [`u], type := mkTy, induct := `W, cidx := 0, numParams := 1,
    numFields := 2, isUnsafe := false }
def wMotTy : Expr := .forallE `t (tW lu (.bvar 0)) (.sort u1) .default
def wMinTy : Expr :=
  .forallE `fst tB (.forallE `snd (.bvar 2) (.app (.bvar 2) (mkW lu (.bvar 3) (.bvar 1) (.bvar 0))) .default)
    .default
def W_rec : RecursorVal :=
  { name := `W.rec, levelParams := [`u_1, `u],
    type := .forallE `Y (.sort lu) (.forallE `motive wMotTy (.forallE `mk wMinTy
      (.forallE `t (tW lu (.bvar 2)) (.app (.bvar 2) (.bvar 0)) .default) .default) .implicit) .implicit,
    all := [`W], numParams := 1, numIndices := 0, numMotives := 1, numMinors := 1,
    rules := [{ ctor := `W.mk, nfields := 2, rhs := .lam `Y (.sort lu) (.lam `motive wMotTy (.lam `mk wMinTy
      (.lam `fst tB (.lam `snd (.bvar 3) (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0)) .default) .default)
      .default) .default) .default }],
    k := false, isUnsafe := false }

/-! ## `wrap` -/

/-- `B → Y`, under `Y` -/
def fTy : Expr := .forallE `x tB (.bvar 1) .default
def wrapVal : Expr :=
  .lam `Y (.sort lu) (.lam `f fTy (mkW lu (.bvar 1) cT (.app (.bvar 0) cT)) .default) .default
def wrap_def : DefinitionVal :=
  { name := `wrap, levelParams := [`u],
    type := .forallE `Y (.sort lu) (.forallE `f fTy (tW lu (.bvar 1)) .default) .default,
    value := wrapVal, hints := .regular 1, safety := .safe, all := [`wrap] }

/-- The program, newest first. -/
def P : List ConstantInfo :=
  [.defnInfo wrap_def, .recInfo W_rec, .ctorInfo W_mk, .inductInfo W_ind, .recInfo B_rec,
    .ctorInfo Bf_ctor, .ctorInfo Bt_ctor, .inductInfo B_ind]

/-! ## The term -/

/-- `Type` -/
def tyT : Expr := .sort l1
/-- `fun _ : B => B` -/
def famF : Expr := .lam `x tB tB .default
def valOf (Y f : Expr) : Expr := mkAppN (.const `wrap [l2]) #[Y, f]
def letOf (v : Expr) : Expr := .letE `p (tW l2 tyT) v (.proj `W 0 (.bvar 0)) false

/-- The erased term. -/
def e : Expr := letOf (valOf tyT famF)

def view : EnvView where
  find? := findConst P
  isExtern _ := false
  inlineAttr? _ := none
  implementedBy? _ := none

def cfg : ErasureConfig := {}

/-- The closure of `e`, in the order the fragment test returns it. -/
def D : List ConstantInfo :=
  [.defnInfo wrap_def, .ctorInfo Bt_ctor, .ctorInfo Bf_ctor, .inductInfo B_ind, .ctorInfo W_mk,
    .recInfo W_rec, .inductInfo W_ind]

end EraseProof.Test.NV5
