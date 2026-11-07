import EraseProof.Test.NV1Data

/-!
# NV-R: the program

    inductive B | f | t
    inductive N | z | s (n : N)
    #erase @N.rec.{1} (fun _ => B) B.t (fun _ (ih : B) => ih) (N.s N.z)   -- evaluates to B.t

`B` is NV-1's `inductive B | f | t`. `N` is a recursive inductive: the field of `N.s` is of type
`N`, so the minor premise of `N.s` receives an induction hypothesis, and the recursor's ι on
`N.s N.z` evaluates the recursor once more on `N.z`. The declarations as Lean v4.35.0-rc2
generates them (`tools/NVEmit.lean` checks them against the kernel's), newest first:
`P = [N.rec, N.z, N.s, N, B.rec, B.f, B.t, B]`; the term `e`; the view `#erase` reads (`P` as a
list, no attributes); the default configuration. A non-vacuity instance of the final theorem
(`MR E/ErasureFunctionProperties.v:657 erase_correct`) through the recursor rules (DV-30):
`Test/NVRRun.lean` discharges the hypotheses `hfrag` and `hrun`, `Test/NVRModel.lean` `henv`,
`hwf`, `he` and `hty`, and `Test/NVRFinal.lean` the others and applies the final theorem.
-/

open Lean Erasure

namespace EraseProof.Test.NVR

open EraseProof.Test.NV1 (tB cT B_ind Bf_ctor Bt_ctor B_rec)

def tN : Expr := .const `N []
def cZ : Expr := .const `N.z []
def cS : Expr := .const `N.s []

/-! ## `inductive N | z | s (n : N)` -/

def N_ind : InductiveVal :=
  { name := `N, levelParams := [], type := .sort (.succ .zero), numParams := 0, numIndices := 0,
    all := [`N], ctors := [`N.z, `N.s], numNested := 0, isRec := true, isUnsafe := false,
    isReflexive := false }

def Nz_ctor : ConstructorVal :=
  { name := `N.z, levelParams := [], type := tN, induct := `N, cidx := 0, numParams := 0,
    numFields := 0, isUnsafe := false }

/-- `(n : N) → N` -/
def sTy : Expr := .forallE `n tN tN .default

def Ns_ctor : ConstructorVal :=
  { name := `N.s, levelParams := [], type := sTy, induct := `N, cidx := 1, numParams := 0,
    numFields := 1, isUnsafe := false }

/-- `(t : N) → Sort u` -/
def motTy : Expr := .forallE `t tN (.sort (.param `u)) .default

/-- `(n : N) → (n_ih : motive n) → motive (N.s n)`, the motive one binder out. -/
def minSTy : Expr :=
  .forallE `n tN (.forallE `n_ih (.app (.bvar 2) (.bvar 0)) (.app (.bvar 3) (.app cS (.bvar 1)))
    .default) .default

/-- `{motive : N → Sort u} → (z : motive N.z) → (s : (n : N) → motive n → motive (N.s n)) →
(t : N) → motive t` -/
def recTy : Expr :=
  .forallE `motive motTy
    (.forallE `z (.app (.bvar 0) cZ)
      (.forallE `s minSTy (.forallE `t tN (.app (.bvar 3) (.bvar 0)) .default) .default)
      .default) .implicit

/-- The recursor rule's right-hand side `fun motive z s => body`. -/
def recRhs (body : Expr) : Expr :=
  .lam `motive motTy (.lam `z (.app (.bvar 0) cZ) (.lam `s minSTy body .default) .default) .default

def N_rec : RecursorVal :=
  { name := `N.rec, levelParams := [`u], type := recTy, all := [`N], numParams := 0,
    numIndices := 0, numMotives := 1, numMinors := 2,
    rules := [{ ctor := `N.z, nfields := 0, rhs := recRhs (.bvar 1) },
              { ctor := `N.s, nfields := 1, rhs := recRhs (.lam `n tN
                  (.app (.app (.bvar 1) (.bvar 0))
                    (mkAppN (.const `N.rec [.param `u]) #[.bvar 3, .bvar 2, .bvar 1, .bvar 0]))
                  .default) }],
    k := false, isUnsafe := false }

/-- The program, newest first. -/
def P : List ConstantInfo :=
  [.recInfo N_rec, .ctorInfo Nz_ctor, .ctorInfo Ns_ctor, .inductInfo N_ind,
    .recInfo B_rec, .ctorInfo Bf_ctor, .ctorInfo Bt_ctor, .inductInfo B_ind]

/-- The motive `fun x => B`. -/
def motB : Expr := .lam `x tN tB .default
/-- The minor premise of `N.s`, `fun n (ih : B) => ih`. -/
def minS : Expr := .lam `n tN (.lam `ih tB (.bvar 0) .default) .default
/-- The major `N.s N.z`. -/
def mj : Expr := .app cS cZ

/-- The erased term `@N.rec.{1} (fun _ => B) B.t (fun _ (ih : B) => ih) (N.s N.z)`. -/
def e : Expr := mkAppN (.const `N.rec [.succ .zero]) #[motB, cT, minS, mj]

/-- The view `#erase` reads: `P` as a list, no `@[extern]`, inline or `implemented_by` attributes. -/
def view : EnvView where
  find? := findConst P
  isExtern _ := false
  inlineAttr? _ := none
  implementedBy? _ := none

/-- The default configuration (`#erase` without options). -/
def cfg : ErasureConfig := {}

end EraseProof.Test.NVR
