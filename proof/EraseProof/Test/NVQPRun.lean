import EraseProof.Test.NVQPData
import EraseProof.Test.NVSRun

/-!
# NV-QP through the entry point of `#erase`

The hypotheses `hfrag` and `hrun` of the final theorem (`MR E/ErasureFunctionProperties.v:657
erase_correct`) on NV-QP (`Test/NVQPData.lean`). `hcollect` computes the fragment test's closure `D`
by kernel evaluation: it holds the definitions the term reaches and their types' constants (the
theorem `orU._proof_1` with its type only), the quotient constants `Quot.mk`, `Quot.lift` and
`Quot`, `Eq` (from `Quot.lift`'s type), `Prod` and `B` with their recursors. `p0` and `inl0` are
the program `#erase` emits and the constants it marks for inlining.
-/

open Lean Erasure EraseProof.Test

namespace EraseProof.Test.NVQP

open EraseProof.Test.NV1 (tB cT B_ind Bf_ctor Bt_ctor B_rec B_casesOn iidB masksB bodyB stB)
open EraseProof.Test.NVP (Eq_ind Eq_refl Eq_rec)
open EraseProof.Test.NVQ (Quot_val QuotMk_val QuotLift_val)

/-- The closure of `e`, in the order the fragment test returns it. -/
def D : List ConstantInfo :=
  [.quotInfo QuotMk_val, .thmInfo resp_thm, .recInfo B_rec, .defnInfo B_casesOn,
    .defnInfo orB_match_1, .defnInfo orB_def, .quotInfo QuotLift_val, .defnInfo Prod_fst,
    .defnInfo Prod_snd, .ctorInfo Eq_refl, .recInfo Eq_rec, .inductInfo Eq_ind, .defnInfo swapR_def,
    .ctorInfo Prod_mk, .recInfo Prod_rec, .inductInfo Prod_ind, .quotInfo Quot_val, .defnInfo orU_def,
    .ctorInfo Bt_ctor, .ctorInfo Bf_ctor, .inductInfo B_ind, .defnInfo useTF_def]

/-- The fragment test accepts `e` and returns the closure `D`, by kernel evaluation. Reference: the
environment `Σ'` of `erase_global_deps` (`MR E/ErasureFunction.v:1602`). -/
theorem hcollect : collectDeps view cfg e = .ok D := rfl

/-- The pure backend's context over the closure. -/
def pc : PureCtx := ⟨D, view⟩

/-! ## The emitted program -/

/-- The λ□ inductive of `Prod`, the argument masks of `Prod.mk` (both fields kept), and its body (a
structure: one projection per kept field). -/
def iidPr : InductiveId := ⟨mutualBlockKername [`Prod], 0⟩
def masksPr : InductiveArgMasks := [#[.keep, .keep]]
def bodyPr : OneInductiveBody :=
  { name := toString `Prod, propositional := false, ctors := [⟨toString `Prod.mk, 2⟩],
    projs := [⟨"0"⟩, ⟨"1"⟩] }

/-- The projection `i` of `Prod`. -/
def projPr (i : Nat) : ProjectionInfo := { indType := iidPr, paramCount := 2, fieldIdx := i }

/-- `B.f`, `B.t` and `Prod.mk` in λ□. -/
def fL : LBTerm := .construct iidB 0 []
def tL : LBTerm := .construct iidB 1 []
def mkL : LBTerm := .construct iidPr 0 []

/-- `Prod.mk □ □ a b` in λ□. -/
def pairL (a b : LBTerm) : LBTerm := .app (.app (.app (.app mkL .box) .box) a) b

/-- The erasure of `orU (Quot.mk swapR (Prod.mk a b))`: `orU (Prod.mk □ □ a b)`. -/
def useL (a b : LBTerm) : LBTerm := .app (.const (toKername `orU)) (pairL a b)

/-- `fun self => self.i` under two erased type binders: `Prod.fst` and `Prod.snd` in λ□. -/
def projVL (i : Nat) : LBTerm :=
  .lambda .anon (.lambda .anon (.lambda (binderNameOf `self) (.proj (projPr i) (.bvar 0))))

/-- `c □ □ x` for the projection function `c`. -/
def projAppL (c : Name) (x : LBTerm) : LBTerm := .app (.app (.app (.const (toKername c)) .box) .box) x

/-- `fun a => (fun p => orB p.1 p.2) a`: `orU`, η-expanded to the arity of `Quot.lift`. -/
def orUVL : LBTerm :=
  .lambda (binderNameOf `a) (.app (.lambda (binderNameOf `p)
    (.app (.app (.const (toKername `orB)) (projAppL `Prod.fst (.bvar 0)))
      (projAppL `Prod.snd (.bvar 0)))) (.bvar 0))

/-- `fun x y => orB.match_1 □ x y (fun b => b) (fun _ => B.t)` -/
def orBVL : LBTerm :=
  .lambda (binderNameOf (hyg 7)) (.lambda (binderNameOf (hyg 8))
    (.app (.app (.app (.app (.app (.const (toKername `orB.match_1)) .box) (.bvar 1)) (.bvar 0))
      (.lambda (binderNameOf `b) (.bvar 0))) (.lambda (binderNameOf (hyg 42)) tL)))

/-- `fun motive x y h_1 h_2 => match x with | B.f => h_1 y | B.t => h_2 y` -/
def matchVL : LBTerm :=
  .lambda (binderNameOf `motive) (.lambda (binderNameOf (hyg2 7 26))
    (.lambda (binderNameOf (hyg2 8 29)) (.lambda (binderNameOf `h_1) (.lambda (binderNameOf `h_2)
      (.case (iidB, 0) (.bvar 3) [([], .app (.bvar 1) (.bvar 2)), ([], .app (.bvar 0) (.bvar 2))])))))

/-- The constants `#erase` marks for inlining: the matcher. -/
def inl0 : List Kername := [toKername `orB.match_1]

/-- The λ□ environment `#erase` emits for `useTF` and `useFT` below the term's own constant. -/
def lenv0 : List (Kername × GlobalDecl) :=
  [(toKername `orU, .constantDecl ⟨some orUVL⟩),
    (toKername `Prod.snd, .constantDecl ⟨some (projVL 1)⟩),
    (toKername `Prod.fst, .constantDecl ⟨some (projVL 0)⟩),
    (mutualBlockKername [`Prod], .inductiveDecl ⟨.finite, 2, [bodyPr]⟩),
    (toKername `orB, .constantDecl ⟨some orBVL⟩),
    (toKername `orB.match_1, .constantDecl ⟨some matchVL⟩),
    (mutualBlockKername [`B], .inductiveDecl ⟨.finite, 0, [bodyB]⟩)]

/-- The program `#erase` emits for NV-QP. -/
def p0 : Program :=
  .untyped ((toKername `useTF, .constantDecl ⟨some (useL tL fL)⟩) :: lenv0)
    (some (.const (toKername `useTF)))

/-- The program `#erase` emits for the second term `useFT`. -/
def pFT : Program :=
  .untyped ((toKername `useFT, .constantDecl ⟨some (useL fL tL)⟩) :: lenv0)
    (some (.const (toKername `useFT)))

end EraseProof.Test.NVQP
