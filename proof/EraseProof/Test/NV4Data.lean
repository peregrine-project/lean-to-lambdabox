import EraseProof.Test.NV1Data

/-!
# NV-4: the program

    inductive B | f | t                                   -- NV-1's
    inductive P : Prop | mk : (False → P) → P
    #erase @Quot.lift.{1,1} B r B (fun x => x) (fun a b (h : r a b) => h) (@Quot.mk.{1} B r
      (@Eq.casesOn.{1,1} B B.t (fun _ _ => B) B.t (@Eq.refl.{1} B B.t)
        (@P.casesOn.{1} (fun _ => B) (P.mk fun h => @False.rec.{0} (fun _ => P) h) (fun _ => B.t))))
    -- with r := fun a b : B => a = b; evaluates to B.t

`Eq`, `False` and the quotient constants are `Init`'s. The quotient's element is a `casesOn` on the
proof `Eq.refl B B.t` (no field), whose alternative is a `casesOn` on a proof of `P` (one field,
a proof); the eraser reduces both (`P` is recursive, so `P.casesOn` is built from `P.rec`, which
the recognizer reads). The declarations as Lean v4.35.0 has them (`tools/NVEmit.lean` checks
them against the kernel's), newest first; the term `e`; the view (`P` as a list, no attributes);
the default configuration; the closure `D` of `e`. A non-vacuity instance of the final theorem
through the quotient rules and the reduced `casesOn` rule; `Test/NV4Premises.lean` discharges its
hypotheses.
-/

open Lean Erasure

namespace EraseProof.Test.NV4

open EraseProof.Test.NV1 (tB cT B_ind Bf_ctor Bt_ctor B_rec)

def l1 : Level := .succ .zero
def lu : Level := .param `u
def u1 : Level := .param `u_1

/-! ## `Eq` -/

/-- The anonymous binder name of `Eq`'s declarations. -/
def an : Name := .mkNum (.mkStr (.mkStr (.mkStr (.mkStr .anonymous "a") "_@") "_internal") "_hyg") 0
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
def eqReflTy : Expr := .app (.app (.bvar 2) (.bvar 3)) (reflC (.bvar 4) (.bvar 3))
def eqCasesOnTy : Expr :=
  .forallE `α (.sort u1) (.forallE an (.bvar 0) (.forallE `motive eqMotTy
    (.forallE an (.bvar 2) (.forallE `t (eqC (.bvar 3) (.bvar 2) (.bvar 0))
      (.forallE `refl eqReflTy (.app (.app (.bvar 3) (.bvar 2)) (.bvar 1)) .default) .default)
      .implicit) .implicit) .implicit) .implicit
def eqCasesOnVal : Expr :=
  .lam `α (.sort u1) (.lam an (.bvar 0) (.lam `motive eqMotTy
    (.lam an (.bvar 2) (.lam `t (eqC (.bvar 3) (.bvar 2) (.bvar 0)) (.lam `refl eqReflTy
      (mkAppN (.const `Eq.rec [lu, u1]) #[.bvar 5, .bvar 4, .bvar 3, .bvar 0, .bvar 2, .bvar 1])
      .default) .default) .implicit) .implicit) .implicit) .implicit
def Eq_casesOn : DefinitionVal :=
  { name := `Eq.casesOn, levelParams := [`u, `u_1], type := eqCasesOnTy, value := eqCasesOnVal,
    hints := .abbrev, safety := .safe, all := [`Eq.casesOn] }

/-! ## The quotient -/

/-- `α → α → Prop`, `α` the variable `i` -/
def relTy (i : Nat) : Expr :=
  .forallE `a (.bvar i) (.forallE `a (.bvar (i + 1)) (.sort .zero) .default) .default
def quotC (α r : Expr) : Expr := .app (.app (.const `Quot [lu]) α) r
def Quot_val : QuotVal :=
  { name := `Quot, levelParams := [`u], kind := .type,
    type := .forallE `α (.sort lu) (.forallE `r (relTy 0) (.sort lu) .default) .implicit }
def QuotMk_val : QuotVal :=
  { name := `Quot.mk, levelParams := [`u], kind := .ctor,
    type := .forallE `α (.sort lu) (.forallE `r (relTy 0)
      (.forallE `a (.bvar 1) (quotC (.bvar 2) (.bvar 1)) .default) .default) .implicit }
def compatTy : Expr :=
  .forallE `a (.bvar 3) (.forallE `b (.bvar 4) (.forallE `a (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))
    (mkAppN (.const `Eq [.param `v]) #[.bvar 4, .app (.bvar 3) (.bvar 2), .app (.bvar 3) (.bvar 1)])
    .default) .default) .default
def QuotLift_val : QuotVal :=
  { name := `Quot.lift, levelParams := [`u, `v], kind := .lift,
    type := .forallE `α (.sort lu) (.forallE `r (relTy 0) (.forallE `β (.sort (.param `v))
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

/-! ## `False` and `P` -/

def tF : Expr := .const `False []
def tP : Expr := .const `P []
def False_ind : InductiveVal :=
  { name := `False, levelParams := [], type := .sort .zero, numParams := 0, numIndices := 0,
    all := [`False], ctors := [], numNested := 0, isRec := false, isUnsafe := false,
    isReflexive := false }
def False_rec : RecursorVal :=
  { name := `False.rec, levelParams := [`u], type := .forallE `motive (.forallE `t tF (.sort lu) .default)
      (.forallE `t tF (.app (.bvar 1) (.bvar 0)) .default) .default,
    all := [`False], numParams := 0, numIndices := 0, numMotives := 1, numMinors := 0, rules := [],
    k := false, isUnsafe := false }

/-- `False → P` -/
def fP : Expr := .forallE `x tF tP .default
def P_ind : InductiveVal :=
  { name := `P, levelParams := [], type := .sort .zero, numParams := 0, numIndices := 0,
    all := [`P], ctors := [`P.mk], numNested := 0, isRec := true, isUnsafe := false,
    isReflexive := true }
def P_mk : ConstructorVal :=
  { name := `P.mk, levelParams := [], type := .forallE `a fP tP .default, induct := `P, cidx := 0,
    numParams := 0, numFields := 1, isUnsafe := false }
def pMotTy : Expr := .forallE `t tP (.sort lu) .default
/-- `(a : False → P) → ((x : False) → motive (a x)) → motive (P.mk a)` -/
def pMinTy : Expr :=
  .forallE `a fP (.forallE `a_ih (.forallE `x tF (.app (.bvar 2) (.app (.bvar 1) (.bvar 0))) .default)
    (.app (.bvar 2) (.app (.const `P.mk []) (.bvar 1))) .default) .default
def P_rec : RecursorVal :=
  { name := `P.rec, levelParams := [`u],
    type := .forallE `motive pMotTy (.forallE `mk pMinTy (.forallE `t tP (.app (.bvar 2) (.bvar 0))
      .default) .default) .implicit,
    all := [`P], numParams := 0, numIndices := 0, numMotives := 1, numMinors := 1,
    rules := [{ ctor := `P.mk, nfields := 1, rhs := .lam `motive pMotTy (.lam `mk pMinTy (.lam `a fP
      (.app (.app (.bvar 1) (.bvar 0)) (.lam `x tF (mkAppN (.const `P.rec [lu])
        #[.bvar 3, .bvar 2, .app (.bvar 1) (.bvar 0)]) .default)) .default) .default) .default }],
    k := false, isUnsafe := false }
/-- `(a : False → P) → motive (P.mk a)` -/
def pAltTy : Expr := .forallE `a fP (.app (.bvar 2) (.app (.const `P.mk []) (.bvar 0))) .default
def pCasesOnVal : Expr :=
  .lam `motive pMotTy (.lam `t tP (.lam `mk pAltTy (mkAppN (.const `P.rec [lu]) #[.bvar 2,
    .lam `a fP (.lam `a_ih (.forallE `x tF (.app (.bvar 4) (.app (.bvar 1) (.bvar 0))) .default)
      (.app (.bvar 2) (.bvar 1)) .default) .default, .bvar 1]) .default) .default) .implicit
def P_casesOn : DefinitionVal :=
  { name := `P.casesOn, levelParams := [`u],
    type := .forallE `motive pMotTy (.forallE `t tP (.forallE `mk pAltTy (.app (.bvar 2) (.bvar 1))
      .default) .default) .implicit,
    value := pCasesOnVal, hints := .abbrev, safety := .safe, all := [`P.casesOn] }

/-- The program, newest first. -/
def P : List ConstantInfo :=
  [.defnInfo P_casesOn, .recInfo P_rec, .ctorInfo P_mk, .inductInfo P_ind, .recInfo False_rec,
    .inductInfo False_ind, .defnInfo Eq_casesOn, .quotInfo QuotInd_val, .quotInfo QuotLift_val,
    .quotInfo QuotMk_val, .quotInfo Quot_val, .recInfo Eq_rec, .ctorInfo Eq_refl, .inductInfo Eq_ind,
    .recInfo B_rec, .ctorInfo Bf_ctor, .ctorInfo Bt_ctor, .inductInfo B_ind]

/-! ## The term -/

def eqB (a b : Expr) : Expr := mkAppN (.const `Eq [l1]) #[tB, a, b]
/-- `fun a b : B => a = b` -/
def cR : Expr := .lam `a tB (.lam `b tB (eqB (.bvar 1) (.bvar 0)) .default) .default
/-- `fun x => x : B → B` -/
def idF : Expr := .lam `x tB (.bvar 0) .default
/-- `fun a b (h : r a b) => h` -/
def hL : Expr := .lam `a tB (.lam `b tB (.lam `h (.app (.app cR (.bvar 1)) (.bvar 0)) (.bvar 0) .default)
  .default) .default
/-- `P.mk fun h => False.rec (fun _ => P) h` -/
def dP : Expr :=
  .app (.const `P.mk []) (.lam `h tF (mkAppN (.const `False.rec [.zero]) #[.lam `x tF tP .default, .bvar 0])
    .default)
def motP : Expr := .lam `x tP tB .default
def altP : Expr := .lam `a fP cT .default
def frzPOf (d : Expr) : Expr := mkAppN (.const `P.casesOn [l1]) #[motP, d, altP]
def reflB : Expr := mkAppN (.const `Eq.refl [l1]) #[tB, cT]
def motE : Expr := .lam `x tB (.lam `h (eqB cT (.bvar 0)) tB .default) .default
def frzOf (d a : Expr) : Expr := mkAppN (.const `Eq.casesOn [l1, l1]) #[tB, cT, motE, cT, d, a]
def qmOf (a : Expr) : Expr := mkAppN (.const `Quot.mk [l1]) #[tB, cR, a]
def liftOf (q : Expr) : Expr := mkAppN (.const `Quot.lift [l1, l1]) #[tB, cR, tB, idF, hL, q]

/-- The erased term. -/
def e : Expr := liftOf (qmOf (frzOf reflB (frzPOf dP)))

def view : EnvView where
  find? := findConst P
  isExtern _ := false
  inlineAttr? _ := none
  implementedBy? _ := none

def cfg : ErasureConfig := {}

end EraseProof.Test.NV4
