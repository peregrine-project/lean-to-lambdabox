import EraseProof.Test.NV1Data

/-!
# NV-L: the program

    inductive B | f | t
    #erase @Nat.rec.{1} (fun _ => B) B.t (fun _ (ih : B) => ih) 2 config {nat := .peano}
      -- evaluates to B.t

`B` is NV-1's `inductive B | f | t`; `Nat` is `Init`'s. The major premise is the Nat literal `2`:
the recursor's ι reads it as ``Nat.succ`` applied to the literal `1` (`natLitCtor`), as Lean's
kernel does, so the induction hypothesis is the recursor on `1`, read as ``Nat.succ`` applied to
`0`, whose hypothesis is the recursor on `0`, read as ``Nat.zero``. Under `nat := .peano` the
eraser emits the literal as λ□'s constructor chain of `Nat`. The declarations as Lean v4.35.0
has them (`tools/NVEmit.lean` checks them against the environment's), newest first:
`P = [Nat.rec, Nat.zero, Nat.succ, Nat, B.rec, B.f, B.t, B]`; the term `e`; the view `#erase`
reads (`P` as a list, no attributes); the configuration `nat := .peano`. A non-vacuity instance of
the final theorem (`MR E/ErasureFunctionProperties.v:657 erase_correct`) through the recursor rule
on a literal major (DV-30): `Test/NVLRun.lean` discharges the hypotheses `hfrag` and `hrun`,
`Test/NVLModel.lean` `henv`, `hwf`, `he` and `hty`, and `Test/NVLFinal.lean` the others and
applies the final theorem.
-/

open Lean Erasure

namespace EraseProof.Test.NVL

open EraseProof.Test.NV1 (tB cT B_ind Bf_ctor Bt_ctor B_rec)

def tN : Expr := .const `Nat []
def cZ : Expr := .const `Nat.zero []
def cS : Expr := .const `Nat.succ []

/-! ## `Nat`: `inductive Nat | zero | succ (n : Nat)` -/

def Nat_ind : InductiveVal :=
  { name := `Nat, levelParams := [], type := .sort (.succ .zero), numParams := 0, numIndices := 0,
    all := [`Nat], ctors := [`Nat.zero, `Nat.succ], numNested := 0, isRec := true,
    isUnsafe := false, isReflexive := false }

def Zero_ctor : ConstructorVal :=
  { name := `Nat.zero, levelParams := [], type := tN, induct := `Nat, cidx := 0, numParams := 0,
    numFields := 0, isUnsafe := false }

/-- `(n : Nat) → Nat` -/
def sTy : Expr := .forallE `n tN tN .default

def Succ_ctor : ConstructorVal :=
  { name := `Nat.succ, levelParams := [], type := sTy, induct := `Nat, cidx := 1, numParams := 0,
    numFields := 1, isUnsafe := false }

/-- `(t : Nat) → Sort u` -/
def motTy : Expr := .forallE `t tN (.sort (.param `u)) .default

/-- `(n : Nat) → (n_ih : motive n) → motive (Nat.succ n)`, the motive one binder out. -/
def minSTy : Expr :=
  .forallE `n tN (.forallE `n_ih (.app (.bvar 2) (.bvar 0)) (.app (.bvar 3) (.app cS (.bvar 1)))
    .default) .default

/-- `{motive : Nat → Sort u} → (zero : motive Nat.zero) →
(succ : (n : Nat) → motive n → motive (Nat.succ n)) →
(t : Nat) → motive t` -/
def recTy : Expr :=
  .forallE `motive motTy
    (.forallE `zero (.app (.bvar 0) cZ)
      (.forallE `succ minSTy (.forallE `t tN (.app (.bvar 3) (.bvar 0)) .default) .default)
      .default) .implicit

/-- The recursor rule's right-hand side `fun motive zero succ => body`. -/
def recRhs (body : Expr) : Expr :=
  .lam `motive motTy (.lam `zero (.app (.bvar 0) cZ) (.lam `succ minSTy body .default) .default)
    .default

def Nat_rec : RecursorVal :=
  { name := `Nat.rec, levelParams := [`u], type := recTy, all := [`Nat], numParams := 0,
    numIndices := 0, numMotives := 1, numMinors := 2,
    rules := [{ ctor := `Nat.zero, nfields := 0, rhs := recRhs (.bvar 1) },
              { ctor := `Nat.succ, nfields := 1, rhs := recRhs (.lam `n tN
                  (.app (.app (.bvar 1) (.bvar 0))
                    (mkAppN (.const `Nat.rec [.param `u]) #[.bvar 3, .bvar 2, .bvar 1, .bvar 0]))
                  .default) }],
    k := false, isUnsafe := false }

/-- The program, newest first. -/
def P : List ConstantInfo :=
  [.recInfo Nat_rec, .ctorInfo Zero_ctor, .ctorInfo Succ_ctor, .inductInfo Nat_ind,
    .recInfo B_rec, .ctorInfo Bf_ctor, .ctorInfo Bt_ctor, .inductInfo B_ind]

/-- The motive `fun x => B`. -/
def motB : Expr := .lam `x tN tB .default
/-- The minor premise of `Nat.succ`, `fun n (ih : B) => ih`. -/
def minS : Expr := .lam `n tN (.lam `ih tB (.bvar 0) .default) .default
/-- The major, the literal `2`. -/
def mj : Expr := .lit (.natVal 2)

/-- The erased term `@Nat.rec.{1} (fun _ => B) B.t (fun _ (ih : B) => ih) 2`. -/
def e : Expr := mkAppN (.const `Nat.rec [.succ .zero]) #[motB, cT, minS, mj]

/-- The view `#erase` reads: `P` as a list, no `@[extern]`, inline or `implemented_by` attributes. -/
def view : EnvView where
  find? := findConst P
  isExtern _ := false
  inlineAttr? _ := none
  implementedBy? _ := none

/-- The configuration `nat := .peano`. -/
def cfg : ErasureConfig := { nat := .peano }

end EraseProof.Test.NVL
