import EraseProof.Test.NVPData

/-!
# NV-Q: the program

    inductive B | f | t
    axiom R : (B → B) → (B → B) → Prop
    axiom hR : ∀ a b : B → B, R a b → (fun x => x) a = (fun x => x) b
    #erase @Quot.lift.{1,1} (B → B) R (B → B) (fun x => x) hR (@Quot.mk.{1} (B → B) R (fun y => y)) B.t
                                                     -- evaluates to B.t

`B` is NV-1's `inductive B | f | t`; `Eq` and the four quotient constants are `Init`'s. The quotient
ι reduces the spine to `(fun x => x) (fun y => y)`, whose value `fun y => y` applied to `B.t` gives
`B.t`; `Quot.lift` is applied beyond its arity. The declarations as
Lean v4.35.0-rc2 has them (`tools/NVEmit.lean` checks them against the kernel's), newest first:
`P = [hR, R, Quot.ind, Quot.lift, Quot.mk, Quot] ++ NVP.P`; the view reads them as a list, with no
attributes; the default configuration. A non-vacuity instance of the final theorem
(`MR E/ErasureFunctionProperties.v:657 erase_correct`) through the quotient rules (DV-29):
`Test/NVQRun.lean` discharges the hypotheses `hfrag` and `hrun`, `Test/NVQModel.lean` `henv`,
`hwf`, `he` and `hty`, and `Test/NVQFinal.lean` the others and applies the final theorem.
-/

open Lean Erasure

namespace EraseProof.Test.NVQ

open EraseProof.Test.NV1 (tB cT)
open EraseProof.Test.NVP (l1)

def lu : Level := .param `u
def lv : Level := .param `v

/-- `α → α → Prop`, with `α` the variable `i`. -/
def relTy (i : Nat) : Expr :=
  .forallE `a (.bvar i) (.forallE `a (.bvar (i + 1)) (.sort .zero) .default) .default

/-- `@Quot.{u} α r`. -/
def quotC (α r : Expr) : Expr := .app (.app (.const `Quot [lu]) α) r

def Quot_val : QuotVal :=
  { name := `Quot, levelParams := [`u], kind := .type,
    type := .forallE `α (.sort lu) (.forallE `r (relTy 0) (.sort lu) .default) .implicit }

def QuotMk_val : QuotVal :=
  { name := `Quot.mk, levelParams := [`u], kind := .ctor,
    type := .forallE `α (.sort lu) (.forallE `r (relTy 0)
      (.forallE `a (.bvar 1) (quotC (.bvar 2) (.bvar 1)) .default) .default) .implicit }

/-- `∀ a b, r a b → f a = f b` under `α r β f`. -/
def compatTy : Expr :=
  .forallE `a (.bvar 3) (.forallE `b (.bvar 4) (.forallE `a (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))
    (mkAppN (.const `Eq [lv]) #[.bvar 4, .app (.bvar 3) (.bvar 2), .app (.bvar 3) (.bvar 1)])
    .default) .default) .default

def QuotLift_val : QuotVal :=
  { name := `Quot.lift, levelParams := [`u, `v], kind := .lift,
    type := .forallE `α (.sort lu) (.forallE `r (relTy 0) (.forallE `β (.sort lv)
      (.forallE `f (.forallE `a (.bvar 2) (.bvar 1) .default)
        (.forallE `a compatTy (.forallE `a (quotC (.bvar 4) (.bvar 3)) (.bvar 3) .default) .default)
        .default) .implicit) .implicit) .implicit }

def QuotInd_val : QuotVal :=
  { name := `Quot.ind, levelParams := [`u], kind := .ind,
    type := .forallE `α (.sort lu) (.forallE `r (relTy 0)
      (.forallE `β (.forallE `a (quotC (.bvar 1) (.bvar 0)) (.sort .zero) .default)
        (.forallE `mk (.forallE `a (.bvar 2)
          (.app (.bvar 1) (mkAppN (.const `Quot.mk [lu]) #[.bvar 3, .bvar 2, .bvar 0])) .default)
          (.forallE `q (quotC (.bvar 3) (.bvar 2)) (.app (.bvar 2) (.bvar 0)) .default) .default)
        .implicit) .implicit) .implicit }

/-- The quotient constants, in the order `ProgEnv.quot` lists them. -/
def qs : List QuotVal := [Quot_val, QuotMk_val, QuotLift_val, QuotInd_val]

/-- `B → B` -/
def tBB : Expr := .forallE `x tB tB .default
/-- `fun x => x : (B → B) → B → B` -/
def idF : Expr := .lam `x tBB (.bvar 0) .default
/-- `fun y => y : B → B` -/
def idB : Expr := .lam `y tB (.bvar 0) .default
def cR : Expr := .const `R []

def R_ax : AxiomVal :=
  { name := `R, levelParams := [], type := .forallE `a tBB (.forallE `a tBB (.sort .zero) .default)
      .default, isUnsafe := false }

/-- `∀ a b : B → B, R a b → (fun x => x) a = (fun x => x) b` -/
def hRTy : Expr :=
  .forallE `a tBB (.forallE `b tBB (.forallE `h (.app (.app cR (.bvar 1)) (.bvar 0))
    (mkAppN (.const `Eq [l1]) #[tBB, .app idF (.bvar 2), .app idF (.bvar 1)]) .default) .default)
    .default

def hR_ax : AxiomVal := { name := `hR, levelParams := [], type := hRTy, isUnsafe := false }

/-- NV-Q's program, newest first. -/
def P : List ConstantInfo :=
  [.axiomInfo hR_ax, .axiomInfo R_ax] ++ qs.reverse.map .quotInfo ++ NVP.P

/-- `@Quot.mk.{1} (B → B) R (fun y => y)` -/
def qm : Expr := mkAppN (.const `Quot.mk [l1]) #[tBB, cR, idB]

/-- NV-Q's term. -/
def e : Expr := mkAppN (.const `Quot.lift [l1, l1]) #[tBB, cR, tBB, idF, .const `hR [], qm, cT]

/-- NV-Q's view: `P` as a list, no attributes. -/
def view : EnvView where
  find? := findConst P
  isExtern _ := false
  inlineAttr? _ := none
  implementedBy? _ := none

/-- The default configuration. -/
def cfg : ErasureConfig := {}

end EraseProof.Test.NVQ
