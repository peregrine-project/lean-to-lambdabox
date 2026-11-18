import EraseProof.Test.NV1Data

/-!
# NV-2: the program

    inductive B | f | t                                  -- NV-1's
    inductive Box (α : Type) | mk (val : α) : Box α
    #erase @B.casesOn.{1} (fun _ => Box B) B.t (@Box.mk B B.t)
      ((fun (k : (α : Type) → α → Box α) => k B B.f) @Box.mk)     -- evaluates to Box.mk B B.f

The declarations as Lean v4.35.0 generates them (`tools/NVEmit.lean` checks them against the elaborator's): `P`, the
term `e` (a mark in each `casesOn` minor, one under the source λ `k`, and the under-applied
constructor `@Box.mk`, which the eraser η-expands, its η-variable `α` erased), the view `#erase`
reads, the default configuration and the closure `D` of `e`. The motive is constant with the plain
sort `Box B : Type`, so that every con-leche run is ι-free and compares no levels.
`Test/NV2Premises.lean` discharges the hypotheses of the final theorem on it.
-/

open Lean Erasure EraseProof.Test EraseProof.Test.NV1

namespace EraseProof.Test.NV2

def l1 : Level := .succ .zero
def tBox (a : Expr) : Expr := .app (.const `Box []) a
def cMk : Expr := .const `Box.mk []

def Box_ind : InductiveVal :=
  { name := `Box, levelParams := [], type := .forallE `α (.sort l1) (.sort l1) .default,
    numParams := 1, numIndices := 0, all := [`Box], ctors := [`Box.mk], numNested := 0,
    isRec := false, isUnsafe := false, isReflexive := false }

/-- `{α : Type} → (val : α) → Box α` -/
def mkTy : Expr := .forallE `α (.sort l1) (.forallE `val (.bvar 0) (tBox (.bvar 1)) .default) .implicit

def Boxmk_ctor : ConstructorVal :=
  { name := `Box.mk, levelParams := [], type := mkTy, induct := `Box, cidx := 0, numParams := 1,
    numFields := 1, isUnsafe := false }

def bmotTy : Expr := .forallE `t (tBox (.bvar 0)) (.sort (.param `u)) .default
def bminTy : Expr :=
  .forallE `val (.bvar 1) (.app (.bvar 1) (.app (.app cMk (.bvar 2)) (.bvar 0))) .default

def boxRecTy : Expr :=
  .forallE `α (.sort l1) (.forallE `motive bmotTy (.forallE `mk bminTy
    (.forallE `t (tBox (.bvar 2)) (.app (.bvar 2) (.bvar 0)) .default) .default) .implicit) .implicit

def boxRecRhs : Expr :=
  .lam `α (.sort l1) (.lam `motive bmotTy (.lam `mk bminTy
    (.lam `val (.bvar 2) (.app (.bvar 1) (.bvar 0)) .default) .default) .default) .default

def Box_rec : RecursorVal :=
  { name := `Box.rec, levelParams := [`u], type := boxRecTy, all := [`Box], numParams := 1,
    numIndices := 0, numMotives := 1, numMinors := 1,
    rules := [{ ctor := `Box.mk, nfields := 1, rhs := boxRecRhs }], k := false, isUnsafe := false }

def P : List ConstantInfo :=
  [.recInfo Box_rec, .ctorInfo Boxmk_ctor, .inductInfo Box_ind, .defnInfo B_casesOn, .recInfo B_rec,
    .ctorInfo Bf_ctor, .ctorInfo Bt_ctor, .inductInfo B_ind]

/-- `(α : Type) → α → Box α` -/
def kTy : Expr := .forallE `α (.sort l1) (.forallE `a (.bvar 0) (tBox (.bvar 1)) .default) .default
/-- `fun _ => Box B` -/
def motB : Expr := .lam `x tB (tBox tB) .default
/-- the minor of `B.f`: `Box.mk B B.t` -/
def alt1 : Expr := .app (.app cMk tB) cT
/-- `fun (k : (α : Type) → α → Box α) => k B B.f` -/
def lamK : Expr := .lam `k kTy (.app (.app (.bvar 0) tB) cF) .default
/-- the minor of `B.t`: `(fun k => k B B.f) @Box.mk` -/
def alt2 : Expr := .app lamK cMk
def cases4 : List Expr := [motB, cT, alt1, alt2]
def e : Expr := mkAppN (.const `B.casesOn [l1]) cases4.toArray

def view : EnvView where
  find? := Erasure.findConst P
  isExtern _ := false
  inlineAttr? _ := none
  implementedBy? _ := none
def cfg : ErasureConfig := {}

def D : List ConstantInfo :=
  [.ctorInfo Boxmk_ctor, .recInfo Box_rec, .inductInfo Box_ind, .ctorInfo Bt_ctor, .ctorInfo Bf_ctor,
    .inductInfo B_ind, .recInfo B_rec, .defnInfo B_casesOn]

end EraseProof.Test.NV2
