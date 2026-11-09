import EraseProof.Test.NVSData
import EraseProof.Test.NVLData

/-!
# NV-A: the program

    #erase Nat.add 2 3 config {extern := .preferLogical, structural := .kernel, nat := .peano}
      -- evaluates to 5

`Nat`, `Nat.add`, `OfNat` and `instOfNatNat` are `Init`'s. `Nat.add` is `@[extern "lean_nat_add"]`:
under the default `extern := .preferAxiom` the eraser emits it as an axiom, under
`.preferLogical` it erases its kernel definition. That definition is by structural recursion on
the second argument (`Lean.Elab.Structural`): `Nat.add x y` is `Nat.brecOn` on `y` at the motive
`fun _ => Nat → Nat`, applied to `x`, with the body `Nat.add._f`, which matches with
`Nat.add.match_1` (a `Nat.casesOn` on the second of its two discriminants) and reads the recursive
call as the first projection of the table `Nat.below`, a function of the first argument. The
literals `2` and `3` elaborate to `@OfNat.ofNat Nat 2 (instOfNatNat 2)`, the `Nat` of their type
annotated with the borrow annotation of `Nat.add`'s binders (`mdata`). The declarations as Lean
v4.35.0 has them (`tools/NVEmit.lean` checks them, the term `e` and the program `#erase` emits
against the environment's), newest first:
`P = [instOfNatNat, OfNat.ofNat, OfNat.rec, OfNat.mk, OfNat, Nat.add, Nat.add._f, Nat.add.match_1,
Nat.brecOn, Nat.brecOn.go, Nat.below, Nat.casesOn, Nat.rec, Nat.zero, Nat.succ, Nat, PProd.rec,
PProd.mk, PProd, PUnit.rec, PUnit.unit, PUnit]` (the dependency closure of the term); the term `e`;
the view `#erase` reads (`P` and the compiled companion `Nat.add._unsafe_rec`, which the fragment
test admits only under `structural := .kernel`; `@[extern]` on `Nat.add`; no inline or
`implemented_by` attribute); the configuration. A non-vacuity instance of the final theorem
(`MR E/ErasureFunctionProperties.v:657 erase_correct`) on `Init`'s arithmetic: `Test/NVARun.lean`
discharges the hypotheses `hfrag` and `hrun`, `Test/NVAModel.lean` `henv`, `hwf`, `he` and `hty`,
and `Test/NVAFinal.lean` the others and applies the final theorem.
-/

open Lean Erasure

namespace EraseProof.Test.NVA

open EraseProof.Test.NVL (tN cZ cS Nat_ind Zero_ctor Succ_ctor Nat_rec motTy)
open EraseProof.Test.NVS (uu u1 l1 m1u tPU cPU tPP cPP PUnit_ind PUnit_unit PUnit_rec PProd_ind
  PProd_mk PProd_rec)

/-! ## Binder names -/

/-- `x._@.Init.Prelude.k._hygCtx._hyg.j`, a hygienic binder name of `Init.Prelude`. -/
def hygP (x : String) (k j : Nat) : Name :=
  .num (.str (.str (.num (.str (.str (.str (.str .anonymous x) "_@") "Init") "Prelude") k)
    "_hygCtx") "_hyg") j

/-- `x._@.Init.Prelude.2314059840._hygCtx.i.Init.Prelude.2314059840._hygCtx._hyg.j`, the names
of `Nat.add.match_1`'s discriminants. -/
def hygM (i j : Nat) : Name :=
  .num (.str (.str (.num (.str (.str (.num (.str (.num (.str (.str (.str (.str .anonymous "x")
    "_@") "Init") "Prelude") 2314059840) "_hygCtx") i) "Init") "Prelude") 2314059840) "_hygCtx")
    "_hyg") j

/-- The binder names of `Nat.add` and its auxiliary definitions. -/
def x13 : Name := hygP "x" 2314059840 13
def x14 : Name := hygP "x" 2314059840 14
def x61 : Name := hygP "x" 2314059840 61
def n58 : Name := hygP "n" 2314059840 58
def x32 : Name := hygM 13 32
def x35 : Name := hygM 14 35
/-- The name of `OfNat`'s second parameter. -/
def xo : Name := hygP "x" 1822880135 3
/-- The binder name of `Nat.add`'s type, `a._@._internal._hyg.0`. -/
def aI : Name := .num (.str (.str (.str (.str .anonymous "a") "_@") "_internal") "_hyg") 0

/-! ## `Nat.casesOn`, `Nat.below`, `Nat.brecOn.go`, `Nat.brecOn` -/

/-- `{motive : Nat → Sort u} → (t : Nat) → motive Nat.zero → ((n : Nat) → motive (Nat.succ n)) →
motive t` -/
def casesOnTy : Expr :=
  .forallE `motive motTy (.forallE `t tN (.forallE `zero (.app (.bvar 1) cZ)
    (.forallE `succ (.forallE `n tN (.app (.bvar 3) (.app cS (.bvar 0))) .default)
      (.app (.bvar 3) (.bvar 2)) .default) .default) .default) .implicit

/-- `fun {motive} t zero succ => @Nat.rec motive zero (fun n n_ih => succ n) t` -/
def casesOnVal : Expr :=
  .lam `motive motTy (.lam `t tN (.lam `zero (.app (.bvar 1) cZ)
    (.lam `succ (.forallE `n tN (.app (.bvar 3) (.app cS (.bvar 0))) .default)
      (.app (.app (.app (.app (.const `Nat.rec [uu]) (.bvar 3)) (.bvar 1))
        (.lam `n tN (.lam `n_ih (.app (.bvar 4) (.bvar 0)) (.app (.bvar 2) (.bvar 1)) .default)
          .default)) (.bvar 2)) .default) .default) .default) .implicit

def Nat_casesOn : DefinitionVal :=
  { name := `Nat.casesOn, levelParams := [`u], type := casesOnTy, value := casesOnVal,
    hints := .abbrev, safety := .safe, all := [`Nat.casesOn] }

/-- `Nat.below.{l}` -/
def below (l : Level) : Expr := .const `Nat.below [l]

/-- `{motive : Nat → Sort u} → Nat → Sort (max 1 u)` -/
def belowTy : Expr := .forallE `motive motTy (.forallE `t tN (.sort m1u) .default) .implicit

/-- `fun {motive} t => @Nat.rec.{max 1 u + 1} (fun t => Sort (max 1 u)) PUnit
(fun n n_ih => PProd (motive n) n_ih) t` -/
def belowVal : Expr :=
  .lam `motive motTy (.lam `t tN
    (.app (.app (.app (.app (.const `Nat.rec [.succ m1u]) (.lam `t tN (.sort m1u) .default))
      (tPU m1u))
      (.lam `n tN (.lam `n_ih (.sort m1u) (.app (.app (tPP uu m1u) (.app (.bvar 3) (.bvar 1)))
        (.bvar 0)) .default) .default)) (.bvar 0)) .default) .implicit

def Nat_below : DefinitionVal :=
  { name := `Nat.below, levelParams := [`u], type := belowTy, value := belowVal, hints := .abbrev,
    safety := .safe, all := [`Nat.below] }

/-- `(t : Nat) → Nat.below motive t → motive t`, under `motive t`. -/
def F1Ty : Expr :=
  .forallE `t tN (.forallE `f (.app (.app (below uu) (.bvar 2)) (.bvar 0)) (.app (.bvar 3) (.bvar 1))
    .default) .default

/-- `PProd (motive t) (Nat.below motive t)`, `motive` and `t` the variables `mo` and `t`. -/
def pairTy (mo t : Nat) : Expr :=
  .app (.app (tPP uu m1u) (.app (.bvar mo) (.bvar t))) (.app (.app (below uu) (.bvar mo)) (.bvar t))

/-- `{motive : Nat → Sort u} → (t : Nat) → (F_1 : (t : Nat) → Nat.below motive t → motive t) →
PProd (motive t) (Nat.below motive t)` -/
def goTy : Expr :=
  .forallE `motive motTy (.forallE `t tN (.forallE `F_1 F1Ty (pairTy 2 1) .default) .default)
    .implicit

/-- `fun {motive} t F_1 => @Nat.rec.{max 1 u} (fun t => PProd (motive t) (Nat.below motive t))
⟨F_1 Nat.zero PUnit.unit, PUnit.unit⟩ (fun n n_ih => ⟨F_1 (Nat.succ n) n_ih, n_ih⟩) t` -/
def goVal : Expr :=
  .lam `motive motTy (.lam `t tN (.lam `F_1 F1Ty
    (.app (.app (.app (.app (.const `Nat.rec [m1u]) (.lam `t tN (pairTy 3 0) .default))
      (.app (.app (.app (.app (cPP uu m1u) (.app (.bvar 2) cZ)) (tPU m1u))
        (.app (.app (.bvar 0) cZ) (cPU m1u))) (cPU m1u)))
      (.lam `n tN (.lam `n_ih (pairTy 3 0)
        (.app (.app (.app (.app (cPP uu m1u) (.app (.bvar 4) (.app cS (.bvar 1)))) (pairTy 4 1))
          (.app (.app (.bvar 2) (.app cS (.bvar 1))) (.bvar 0))) (.bvar 0)) .default) .default))
      (.bvar 1)) .default) .default) .implicit

def Nat_brecOn_go : DefinitionVal :=
  { name := `Nat.brecOn.go, levelParams := [`u], type := goTy, value := goVal, hints := .abbrev,
    safety := .safe, all := [`Nat.brecOn.go] }

/-- `{motive : Nat → Sort u} → (t : Nat) → (F_1 : (t : Nat) → Nat.below motive t → motive t) →
motive t` -/
def brecOnTy : Expr :=
  .forallE `motive motTy (.forallE `t tN (.forallE `F_1 F1Ty (.app (.bvar 2) (.bvar 1)) .default)
    .default) .implicit

/-- `fun {motive} t F_1 => (Nat.brecOn.go motive t F_1).1` -/
def brecOnVal : Expr :=
  .lam `motive motTy (.lam `t tN (.lam `F_1 F1Ty
    (.proj `PProd 0 (.app (.app (.app (.const `Nat.brecOn.go [uu]) (.bvar 2)) (.bvar 1)) (.bvar 0)))
    .default) .default) .implicit

def Nat_brecOn : DefinitionVal :=
  { name := `Nat.brecOn, levelParams := [`u], type := brecOnTy, value := brecOnVal,
    hints := .abbrev, safety := .safe, all := [`Nat.brecOn] }

/-! ## `Nat.add.match_1`, `Nat.add._f`, `Nat.add` -/

/-- `(x y : Nat) → Sort u_1` -/
def mMotTy : Expr := .forallE x32 tN (.forallE x35 tN (.sort u1) .default) .default

/-- `(a : Nat) → motive a Nat.zero`, the motive the variable `k`. -/
def h1Ty (k : Nat) : Expr := .forallE `a tN (.app (.app (.bvar (k + 1)) (.bvar 0)) cZ) .default

/-- `(a b : Nat) → motive a (Nat.succ b)`, the motive the variable `k`. -/
def h2Ty (k : Nat) : Expr :=
  .forallE `a tN (.forallE `b tN (.app (.app (.bvar (k + 2)) (.bvar 1)) (.app cS (.bvar 0)))
    .default) .default

/-- `(motive : Nat → Nat → Sort u_1) → (x y : Nat) → ((a : Nat) → motive a Nat.zero) →
((a b : Nat) → motive a (Nat.succ b)) → motive x y` -/
def matchTy : Expr :=
  .forallE `motive mMotTy (.forallE x32 tN (.forallE x35 tN
    (.forallE `h_1 (h1Ty 2) (.forallE `h_2 (h2Ty 3)
      (.app (.app (.bvar 4) (.bvar 3)) (.bvar 2)) .default) .default) .default) .default) .default

/-- `fun motive x y h_1 h_2 => Nat.casesOn (fun z => motive x z) y (h_1 x) (fun n => h_2 x n)` -/
def matchVal : Expr :=
  .lam `motive mMotTy (.lam x32 tN (.lam x35 tN
    (.lam `h_1 (h1Ty 2) (.lam `h_2 (h2Ty 3)
      (.app (.app (.app (.app (.const `Nat.casesOn [u1])
          (.lam `x tN (.app (.app (.bvar 5) (.bvar 4)) (.bvar 0)) .default)) (.bvar 2))
        (.app (.bvar 1) (.bvar 3)))
        (.lam n58 tN (.app (.app (.bvar 1) (.bvar 4)) (.bvar 0)) .default))
      .default) .default) .default) .default) .default

def match_def : DefinitionVal :=
  { name := `Nat.add.match_1, levelParams := [`u_1], type := matchTy, value := matchVal,
    hints := .abbrev, safety := .safe, all := [`Nat.add.match_1] }

/-- `Nat → Nat`, with the binder name of `Nat.add`'s first argument. -/
def nn : Expr := .forallE x13 tN tN .default

/-- The motive `fun y => Nat → Nat` of `Nat.add`'s structural recursion. -/
def motA : Expr := .lam x14 tN nn .default

/-- `Nat.below.{1} (fun y => Nat → Nat) a` -/
def belowA (a : Expr) : Expr := .app (.app (below l1) motA) a

/-- `(y : Nat) → Nat.below (fun y => Nat → Nat) y → Nat → Nat` -/
def fTy : Expr := .forallE x14 tN (.forallE `f (belowA (.bvar 0)) nn .default) .default

/-- The motive `fun x y => Nat.below (fun y => Nat → Nat) y → Nat` of `Nat.add._f`'s match. -/
def motF : Expr :=
  .lam x32 tN (.lam x35 tN (.forallE x61 (belowA (.bvar 0)) tN .default) .default) .default

/-- The alternatives of `Nat.add._f`'s match: `fun a x => a` and `fun a b x => Nat.succ (x.1 a)`. -/
def h1F : Expr := .lam `a tN (.lam x61 (belowA cZ) (.bvar 1) .default) .default
def h2F : Expr :=
  .lam `a tN (.lam `b tN (.lam x61 (belowA (.app cS (.bvar 0)))
    (.app cS (.app (.proj `PProd 0 (.bvar 0)) (.bvar 2))) .default) .default) .default

/-- `fun y f x => Nat.add.match_1 motF x y h1F h2F f` -/
def fVal : Expr :=
  .lam x14 tN (.lam `f (belowA (.bvar 0)) (.lam x13 tN
    (.app (.app (.app (.app (.app (.app (.const `Nat.add.match_1 [l1]) motF) (.bvar 0)) (.bvar 2))
      h1F) h2F) (.bvar 1)) .default) .default) .default

def add_f : DefinitionVal :=
  { name := `Nat.add._f, levelParams := [], type := fTy, value := fVal, hints := .abbrev,
    safety := .safe, all := [`Nat.add._f] }

/-- The borrow annotation `@&` on `Nat.add`'s binders, as the elaborator records it. -/
def borrowed : MData := { entries := [(`borrowed, .ofBool true)] }

/-- `Nat` annotated as borrowed. -/
def tNb : Expr := .mdata borrowed tN

/-- `(@& Nat) → (@& Nat) → Nat` -/
def addTy : Expr := .forallE aI tNb (.forallE aI tNb tN .default) .default

/-- `fun x y => Nat.brecOn (fun y => Nat → Nat) y Nat.add._f x` -/
def addVal : Expr :=
  .lam x13 tN (.lam x14 tN
    (.app (.app (.app (.app (.const `Nat.brecOn [l1]) motA) (.bvar 0)) (.const `Nat.add._f []))
      (.bvar 1)) .default) .default

def add_def : DefinitionVal :=
  { name := `Nat.add, levelParams := [], type := addTy, value := addVal, hints := .regular 1,
    safety := .safe, all := [`Nat.add] }

/-- `fun x y => Nat.add.match_1 (fun x y => Nat) x y (fun a => a)
(fun a b => Nat.succ (Nat.add._unsafe_rec a b))` -/
def addUnsafeRecVal : Expr :=
  .lam x13 tN (.lam x14 tN
    (.app (.app (.app (.app (.app (.const `Nat.add.match_1 [l1])
        (.lam x32 tN (.lam x35 tN tN .default) .default)) (.bvar 1)) (.bvar 0))
      (.lam `a tN (.bvar 0) .default))
      (.lam `a tN (.lam `b tN
        (.app cS (.app (.app (.const `Nat.add._unsafe_rec []) (.bvar 1)) (.bvar 0))) .default)
        .default)) .default) .default

/-- `Nat.add._unsafe_rec`, the compiled companion of `Nat.add`: the recursive definition before its
compilation to `Nat.brecOn`, `partial`, outside `P` (the program's dependency closure does not
reach it). -/
def add_unsafe_rec : DefinitionVal :=
  { name := `Nat.add._unsafe_rec, levelParams := [], type := addTy, value := addUnsafeRecVal,
    hints := .«opaque», safety := .partial, all := [`Nat.add._unsafe_rec] }

/-! ## `class OfNat (α : Type u) (_ : Nat) where ofNat : α` (`Init.Prelude`) and `instOfNatNat` -/

def lv : Level := .param `u
/-- `Type u` -/
def tyU : Expr := .sort (.succ lv)
def tOf (l : Level) : Expr := .const `OfNat [l]
def cOf (l : Level) : Expr := .const `OfNat.mk [l]

def OfNat_ind : InductiveVal :=
  { name := `OfNat, levelParams := [`u], type := .forallE `α tyU (.forallE xo tN tyU .default) .default,
    numParams := 2, numIndices := 0, all := [`OfNat], ctors := [`OfNat.mk], numNested := 0,
    isRec := false, isUnsafe := false, isReflexive := false }

def OfNat_mk : ConstructorVal :=
  { name := `OfNat.mk, levelParams := [`u],
    type := .forallE `α tyU (.forallE xo tN (.forallE `ofNat (.bvar 1)
      (.app (.app (tOf lv) (.bvar 2)) (.bvar 1)) .default) .implicit) .implicit,
    induct := `OfNat, cidx := 0, numParams := 2, numFields := 1, isUnsafe := false }

/-- `(t : OfNat α x) → Sort u_1`, under `α x`. -/
def ofMotTy : Expr := .forallE `t (.app (.app (tOf lv) (.bvar 1)) (.bvar 0)) (.sort u1) .default

/-- `(ofNat : α) → motive ⟨ofNat⟩`, under `α x motive`. -/
def ofMinTy : Expr :=
  .forallE `ofNat (.bvar 2) (.app (.bvar 1) (.app (.app (.app (cOf lv) (.bvar 3)) (.bvar 2)) (.bvar 0)))
    .default

/-- The rule's right-hand side `fun α x motive mk ofNat => mk ofNat`. -/
def ofRhs : Expr :=
  .lam `α tyU (.lam xo tN (.lam `motive ofMotTy (.lam `mk ofMinTy
    (.lam `ofNat (.bvar 3) (.app (.bvar 1) (.bvar 0)) .default) .default) .default) .default) .default

def OfNat_rec : RecursorVal :=
  { name := `OfNat.rec, levelParams := [`u_1, `u],
    type := .forallE `α tyU (.forallE xo tN (.forallE `motive ofMotTy (.forallE `mk ofMinTy
      (.forallE `t (.app (.app (tOf lv) (.bvar 3)) (.bvar 2)) (.app (.bvar 2) (.bvar 0)) .default)
      .default) .implicit) .implicit) .implicit,
    all := [`OfNat], numParams := 2, numIndices := 0, numMotives := 1, numMinors := 1,
    rules := [{ ctor := `OfNat.mk, nfields := 1, rhs := ofRhs }],
    k := false, isUnsafe := false }

/-- `{α : Type u} → (x : Nat) → [self : OfNat α x] → α` -/
def ofNatTy : Expr :=
  .forallE `α tyU (.forallE xo tN (.forallE `self (.app (.app (tOf lv) (.bvar 1)) (.bvar 0))
    (.bvar 2) .instImplicit) .default) .implicit

/-- `fun α x self => self.1` -/
def ofNatVal : Expr :=
  .lam `α tyU (.lam xo tN (.lam `self (.app (.app (tOf lv) (.bvar 1)) (.bvar 0))
    (.proj `OfNat 0 (.bvar 0)) .instImplicit) .default) .default

def ofNat_def : DefinitionVal :=
  { name := `OfNat.ofNat, levelParams := [`u], type := ofNatTy, value := ofNatVal,
    hints := .abbrev, safety := .safe, all := [`OfNat.ofNat] }

/-- `(n : Nat) → OfNat Nat n` -/
def instTy : Expr := .forallE `n tN (.app (.app (tOf .zero) tN) (.bvar 0)) .default

/-- `fun n => OfNat.mk Nat n n` -/
def instVal : Expr :=
  .lam `n tN (.app (.app (.app (cOf .zero) tN) (.bvar 0)) (.bvar 0)) .default

def inst_def : DefinitionVal :=
  { name := `instOfNatNat, levelParams := [], type := instTy, value := instVal,
    hints := .regular 1, safety := .safe, all := [`instOfNatNat] }

/-- The program, newest first. -/
def P : List ConstantInfo :=
  [.defnInfo inst_def, .defnInfo ofNat_def, .recInfo OfNat_rec, .ctorInfo OfNat_mk,
    .inductInfo OfNat_ind, .defnInfo add_def, .defnInfo add_f, .defnInfo match_def,
    .defnInfo Nat_brecOn, .defnInfo Nat_brecOn_go, .defnInfo Nat_below, .defnInfo Nat_casesOn,
    .recInfo Nat_rec, .ctorInfo Zero_ctor, .ctorInfo Succ_ctor, .inductInfo Nat_ind,
    .recInfo PProd_rec, .ctorInfo PProd_mk, .inductInfo PProd_ind,
    .recInfo PUnit_rec, .ctorInfo PUnit_unit, .inductInfo PUnit_ind]

/-- The Nat literal `k`. -/
def lit (k : Nat) : Expr := .lit (.natVal k)

/-- `instOfNatNat k` -/
def instK (k : Nat) : Expr := .app (.const `instOfNatNat []) (lit k)

/-- The numeral `k` as the elaborator writes it at the borrowed type: `@OfNat.ofNat.{0} Nat k
(instOfNatNat k)`. -/
def numK (k : Nat) : Expr := .app (.app (.app (.const `OfNat.ofNat [.zero]) tNb) (lit k)) (instK k)

/-- The erased term `Nat.add 2 3`, as `#erase` elaborates it. -/
def e : Expr := .app (.app (.const `Nat.add []) (numK 2)) (numK 3)

/-- The declarations the view holds: `P` and `Nat.add._unsafe_rec`. -/
def PV : List ConstantInfo := P ++ [.defnInfo add_unsafe_rec]

/-- The view `#erase` reads: the list `PV`, `@[extern]` on `Nat.add`, no inline or
`implemented_by` attribute, as in the environment that elaborates the program. -/
def view : EnvView where
  find? := findConst PV
  isExtern n := n == `Nat.add
  inlineAttr? _ := none
  implementedBy? _ := none

/-- The configuration `extern := .preferLogical, structural := .kernel, nat := .peano`. -/
def cfg : ErasureConfig := { extern := .preferLogical, structural := .kernel, nat := .peano }

/- `e` is the term `#erase` elaborates from `Nat.add 2 3`: `elabTerm` without an expected type,
then the synthetic metavariables and their instantiation, as `LeanToLambdaBox/Erasure/Command.lean`
does. -/
run_elab do
  let t ← Elab.Term.elabTerm (← `(Nat.add 2 3)) none
  Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let t ← instantiateMVars t
  unless t.equal e do throwError "`Nat.add 2 3` elaborates to {t}, not to NV-A's term"

end EraseProof.Test.NVA
