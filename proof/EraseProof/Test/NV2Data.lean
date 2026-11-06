import EraseProof.Test.NV1Data

/-!
# NV-2: the program

    inductive B | f | t
    inductive T : Prop | i
    inductive W | n | s (b : B) (h : T)
    #erase W.casesOn (motive := fun _ => B) (W.s B.t T.i) B.f (fun b h => b)   -- evaluates to B.t

`B` is NV-1's `inductive B | f | t`. `W` has a constructor with fields, one of them a proof of the
`Prop` inductive `T`; the `casesOn` has two alternatives, the second binding both fields. The
declarations as Lean v4.35.0-rc2 generates them (`tools/NVEmit.lean` checks them against the
elaborator's), newest first: `P = [W.casesOn, W.rec, W.n, W.s, W, T.rec, T.i, T, B.rec, B.f, B.t,
B]`; the term `e`; the view `#erase` reads (`P` as a list, no attributes); the default
configuration. A non-vacuity instance of the final theorem (`MR E/ErasureFunctionProperties.v:657
erase_correct`): `Test/NV2Run.lean` discharges the hypotheses `hfrag` and `hrun`,
`Test/NV2Model.lean` `henv`, `hwf`, `he` and `hty`, and `Test/NV2Final.lean` the others and applies
the final theorem.
-/

open Lean Erasure

namespace EraseProof.Test.NV2

open EraseProof.Test.NV1 (tB cF cT B_ind Bf_ctor Bt_ctor B_rec)

def tT : Expr := .const `T []
def cI : Expr := .const `T.i []
def tW : Expr := .const `W []
def cN : Expr := .const `W.n []
def cS : Expr := .const `W.s []

/-! ## `inductive T : Prop | i` -/

def T_ind : InductiveVal :=
  { name := `T, levelParams := [], type := .sort .zero, numParams := 0, numIndices := 0,
    all := [`T], ctors := [`T.i], numNested := 0, isRec := false, isUnsafe := false,
    isReflexive := false }

def Ti_ctor : ConstructorVal :=
  { name := `T.i, levelParams := [], type := tT, induct := `T, cidx := 0, numParams := 0,
    numFields := 0, isUnsafe := false }

/-- `(t : T) → Sort u` -/
def motTyT : Expr := .forallE `t tT (.sort (.param `u)) .default

/-- `{motive : T → Sort u} → (i : motive T.i) → (t : T) → motive t` -/
def recTyT : Expr :=
  .forallE `motive motTyT
    (.forallE `i (.app (.bvar 0) cI) (.forallE `t tT (.app (.bvar 2) (.bvar 0)) .default) .default)
    .implicit

/-- `T.rec`'s rule for `T.i`: `fun motive i => i`. -/
def recRhsT : Expr := .lam `motive motTyT (.lam `i (.app (.bvar 0) cI) (.bvar 0) .default) .default

def T_rec : RecursorVal :=
  { name := `T.rec, levelParams := [`u], type := recTyT, all := [`T], numParams := 0,
    numIndices := 0, numMotives := 1, numMinors := 1,
    rules := [{ ctor := `T.i, nfields := 0, rhs := recRhsT }],
    k := true, isUnsafe := false }

/-! ## `inductive W | n | s (b : B) (h : T)` -/

def W_ind : InductiveVal :=
  { name := `W, levelParams := [], type := .sort (.succ .zero), numParams := 0, numIndices := 0,
    all := [`W], ctors := [`W.n, `W.s], numNested := 0, isRec := false, isUnsafe := false,
    isReflexive := false }

def Wn_ctor : ConstructorVal :=
  { name := `W.n, levelParams := [], type := tW, induct := `W, cidx := 0, numParams := 0,
    numFields := 0, isUnsafe := false }

/-- `(b : B) → (h : T) → W` -/
def sTy : Expr := .forallE `b tB (.forallE `h tT tW .default) .default

def Ws_ctor : ConstructorVal :=
  { name := `W.s, levelParams := [], type := sTy, induct := `W, cidx := 1, numParams := 0,
    numFields := 2, isUnsafe := false }

/-- `(t : W) → Sort u` -/
def motTyW : Expr := .forallE `t tW (.sort (.param `u)) .default

/-- `(b : B) → (h : T) → motive (W.s b h)`, the motive `k` binders out. -/
def minSTy (k : Nat) : Expr :=
  .forallE `b tB (.forallE `h tT (.app (.bvar (k + 2)) (.app (.app cS (.bvar 1)) (.bvar 0)))
    .default) .default

/-- `{motive : W → Sort u} → (n : motive W.n) → (s : (b : B) → (h : T) → motive (W.s b h)) →
(t : W) → motive t` -/
def recTyW : Expr :=
  .forallE `motive motTyW
    (.forallE `n (.app (.bvar 0) cN)
      (.forallE `s (minSTy 1) (.forallE `t tW (.app (.bvar 3) (.bvar 0)) .default) .default)
      .default) .implicit

/-- The recursor rule's right-hand side `fun motive n s => body`. -/
def recRhsW (body : Expr) : Expr :=
  .lam `motive motTyW (.lam `n (.app (.bvar 0) cN) (.lam `s (minSTy 1) body .default) .default)
    .default

def W_rec : RecursorVal :=
  { name := `W.rec, levelParams := [`u], type := recTyW, all := [`W], numParams := 0,
    numIndices := 0, numMotives := 1, numMinors := 2,
    rules := [{ ctor := `W.n, nfields := 0, rhs := recRhsW (.bvar 1) },
              { ctor := `W.s, nfields := 2, rhs := recRhsW (.lam `b tB (.lam `h tT
                  (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0)) .default) .default) }],
    k := false, isUnsafe := false }

/-- `{motive : W → Sort u} → (t : W) → motive W.n → ((b : B) → (h : T) → motive (W.s b h)) →
motive t` -/
def casesOnTyW : Expr :=
  .forallE `motive motTyW
    (.forallE `t tW
      (.forallE `n (.app (.bvar 1) cN)
        (.forallE `s (minSTy 2) (.app (.bvar 3) (.bvar 2)) .default) .default) .default)
    .implicit

/-- `fun {motive} t n s => @W.rec motive n (fun b h => s b h) t` -/
def casesOnValW : Expr :=
  .lam `motive motTyW
    (.lam `t tW
      (.lam `n (.app (.bvar 1) cN)
        (.lam `s (minSTy 2)
          (.app (.app (.app (.app (.const `W.rec [.param `u]) (.bvar 3)) (.bvar 1))
            (.lam `b tB (.lam `h tT (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0)) .default) .default))
            (.bvar 2)) .default) .default) .default) .implicit

def W_casesOn : DefinitionVal :=
  { name := `W.casesOn, levelParams := [`u], type := casesOnTyW, value := casesOnValW,
    hints := .abbrev, safety := .safe, all := [`W.casesOn] }

/-- The program, newest first. -/
def P : List ConstantInfo :=
  [.defnInfo W_casesOn, .recInfo W_rec, .ctorInfo Wn_ctor, .ctorInfo Ws_ctor, .inductInfo W_ind,
    .recInfo T_rec, .ctorInfo Ti_ctor, .inductInfo T_ind,
    .recInfo B_rec, .ctorInfo Bf_ctor, .ctorInfo Bt_ctor, .inductInfo B_ind]

/-- The motive `fun x => B`. -/
def motB : Expr := .lam `x tW tB .default
/-- The major `W.s B.t T.i`. -/
def mj : Expr := .app (.app cS cT) cI
/-- The second alternative `fun b h => b`. -/
def altS : Expr := .lam `b tB (.lam `h tT (.bvar 1) .default) .default

/-- The erased term `W.casesOn (motive := fun _ => B) (W.s B.t T.i) B.f (fun b h => b)`. -/
def e : Expr :=
  .app (.app (.app (.app (.const `W.casesOn [.succ .zero]) motB) mj) cF) altS

/-- The view `#erase` reads: `P` as a list, no `@[extern]`, inline or `implemented_by` attributes. -/
def view : EnvView where
  find? := findConst P
  isExtern _ := false
  inlineAttr? _ := none
  implementedBy? _ := none

/-- The default configuration (`#erase` without options). -/
def cfg : ErasureConfig := {}

end EraseProof.Test.NV2
