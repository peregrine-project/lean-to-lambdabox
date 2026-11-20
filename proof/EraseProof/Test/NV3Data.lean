import LeanToLambdaBox

/-!
# NV-3: the program

    #erase @Nat.rec.{1} (fun _ => Nat) z (fun n (ih : Nat) => ih) 1
      config {nat := .peano, structural := .kernel}                     -- evaluates to 0
    z := @Nat.casesOn.{1} (fun _ => Nat) 0 (@Nat.casesOn.{1} (fun _ => Nat) 1 0 (fun n => n))
           (fun n => n)

`Nat` is `Init`'s. The recursor's ι on the literal major `1` reads it as `Nat.succ 0`
(`natLitCtor`), whose induction hypothesis is the recursor on `0`, read as `Nat.zero`; the minor
premise `z` is a `casesOn` on the literal `0` whose alternative is a `casesOn` on the literal `1`.
The recursion is a direct `Nat.rec`, which the eraser erases the same way under either
`structural` setting (only a definition with a `brecOn` reads it). The declarations as Lean
v4.35.0 has them (`tools/NVEmit.lean` checks them against the environment's), newest first: `P = [Nat.casesOn, Nat.rec, Nat.succ, Nat.zero, Nat]`; the term `e`;
the view `#erase` reads (`P` as a list, no attributes); the configuration; the closure `D` of `e`.
A non-vacuity instance of the final theorem through the recursor rule and the literal `casesOn`
rules; `Test/NV3Premises.lean` discharges its hypotheses.
-/

open Lean Erasure

namespace EraseProof.Test.NV3

def l1 : Level := .succ .zero
def lu : Level := .param `u
def tN : Expr := .const `Nat []
def cZ : Expr := .const `Nat.zero []
def cS : Expr := .const `Nat.succ []
def lit (k : Nat) : Expr := .lit (.natVal k)

def Nat_ind : InductiveVal :=
  { name := `Nat, levelParams := [], type := .sort l1, numParams := 0, numIndices := 0,
    all := [`Nat], ctors := [`Nat.zero, `Nat.succ], numNested := 0, isRec := true,
    isUnsafe := false, isReflexive := false }

def Zero_ctor : ConstructorVal :=
  { name := `Nat.zero, levelParams := [], type := tN, induct := `Nat, cidx := 0, numParams := 0,
    numFields := 0, isUnsafe := false }

def Succ_ctor : ConstructorVal :=
  { name := `Nat.succ, levelParams := [], type := .forallE `n tN tN .default, induct := `Nat,
    cidx := 1, numParams := 0, numFields := 1, isUnsafe := false }

/-- `(t : Nat) → Sort u` -/
def motTy : Expr := .forallE `t tN (.sort lu) .default

/-- `(n : Nat) → motive n → motive (Nat.succ n)`, the motive one binder out -/
def minSTy : Expr :=
  .forallE `n tN (.forallE `n_ih (.app (.bvar 2) (.bvar 0)) (.app (.bvar 3) (.app cS (.bvar 1)))
    .default) .default

def recTy : Expr :=
  .forallE `motive motTy (.forallE `zero (.app (.bvar 0) cZ)
    (.forallE `succ minSTy (.forallE `t tN (.app (.bvar 3) (.bvar 0)) .default) .default) .default)
    .implicit

def recRhs (body : Expr) : Expr :=
  .lam `motive motTy (.lam `zero (.app (.bvar 0) cZ) (.lam `succ minSTy body .default) .default)
    .default

def Nat_rec : RecursorVal :=
  { name := `Nat.rec, levelParams := [`u], type := recTy, all := [`Nat], numParams := 0,
    numIndices := 0, numMotives := 1, numMinors := 2,
    rules := [{ ctor := `Nat.zero, nfields := 0, rhs := recRhs (.bvar 1) },
              { ctor := `Nat.succ, nfields := 1, rhs := recRhs (.lam `n tN
                  (.app (.app (.bvar 1) (.bvar 0))
                    (mkAppN (.const `Nat.rec [lu]) #[.bvar 3, .bvar 2, .bvar 1, .bvar 0])) .default) }],
    k := false, isUnsafe := false }

/-- `(n : Nat) → motive (Nat.succ n)`, the motive three binders out -/
def caseSTy : Expr := .forallE `n tN (.app (.bvar 3) (.app cS (.bvar 0))) .default

def casesOnTy : Expr :=
  .forallE `motive motTy (.forallE `t tN (.forallE `zero (.app (.bvar 1) cZ)
    (.forallE `succ caseSTy (.app (.bvar 3) (.bvar 2)) .default) .default) .default) .implicit

/-- `fun {motive} t zero succ => @Nat.rec motive zero (fun n n_ih => succ n) t` -/
def casesOnVal : Expr :=
  .lam `motive motTy (.lam `t tN (.lam `zero (.app (.bvar 1) cZ) (.lam `succ caseSTy
    (mkAppN (.const `Nat.rec [lu]) #[.bvar 3, .bvar 1,
      .lam `n tN (.lam `n_ih (.app (.bvar 4) (.bvar 0)) (.app (.bvar 2) (.bvar 1)) .default) .default,
      .bvar 2]) .default) .default) .default) .implicit

def Nat_casesOn : DefinitionVal :=
  { name := `Nat.casesOn, levelParams := [`u], type := casesOnTy, value := casesOnVal,
    hints := .abbrev, safety := .safe, all := [`Nat.casesOn] }

/-- The program, newest first. -/
def P : List ConstantInfo :=
  [.defnInfo Nat_casesOn, .recInfo Nat_rec, .ctorInfo Succ_ctor, .ctorInfo Zero_ctor,
    .inductInfo Nat_ind]

/-- `fun _ => Nat` -/
def motN : Expr := .lam `x tN tN .default
/-- `fun n => n` -/
def idN : Expr := .lam `n tN (.bvar 0) .default
/-- `@Nat.casesOn.{1} (fun _ => Nat) k a (fun n => n)` -/
def cas (k : Nat) (a : Expr) : Expr := mkAppN (.const `Nat.casesOn [l1]) #[motN, lit k, a, idN]
/-- the minor premise of `Nat.zero` -/
def z : Expr := cas 0 (cas 1 (lit 0))
/-- the minor premise of `Nat.succ`, `fun n (ih : Nat) => ih` -/
def minS : Expr := .lam `n tN (.lam `ih tN (.bvar 0) .default) .default

/-- The erased term. -/
def e : Expr := mkAppN (.const `Nat.rec [l1]) #[motN, z, minS, lit 1]

def view : EnvView where
  find? := findConst P
  isExtern _ := false
  inlineAttr? _ := none
  implementedBy? _ := none

/-- `nat := .peano`, `structural := .kernel` -/
def cfg : ErasureConfig := { nat := .peano, structural := .kernel }

/-- The closure of `e`, in the order the fragment test returns it. -/
def D : List ConstantInfo :=
  [.defnInfo Nat_casesOn, .ctorInfo Succ_ctor, .ctorInfo Zero_ctor, .inductInfo Nat_ind,
    .recInfo Nat_rec]

end EraseProof.Test.NV3
