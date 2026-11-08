import EraseProof.Test.NVQData

/-!
# NV-QP: the program

    inductive B | f | t
    def orB : B → B → B
      | .f, b => b
      | .t, _ => .t
    def swapR (p q : B × B) : Prop := q = (p.2, p.1)
    theorem orB_comm (a b : B) : orB a b = orB b a := by cases a <;> cases b <;> rfl
    def orU : Quot swapR → B :=
      Quot.lift (fun p => orB p.1 p.2) (fun p q h => by subst h; exact orB_comm p.1 p.2)
    def useTF : B := orU (Quot.mk swapR (B.t, B.f))
    def useFT : B := orU (Quot.mk swapR (B.f, B.t))
    #erase useTF                                              -- evaluates to B.t

The program of the regression test `tests/regress/quotient_pair.lean`, outside its namespace: a
quotient whose relation identifies distinct values. `Quot swapR` is the type of unordered pairs of
`B`: `(B.t, B.f)` and `(B.f, B.t)` are distinct and have one class. `orU` lifts `orB`, which matches
on `B` (`orB.match_1`, a `B.casesOn`), through both projections of `Prod` along the respect proof,
which the elaborator abstracts as the theorem `orU._proof_1` (by `Eq.ndrec` along `Eq.symm h` from
`orB_comm`). `B` is NV-1's, `Eq` and its recursor NV-P's, the quotient constants NV-Q's; `Prod`, its
projections `Prod.fst` and `Prod.snd` (whose values are primitive projections) are `Init`'s.

The declarations as Lean v4.35.0-rc2 generates them (`tools/NVEmit.lean` elaborates the program, with
`Prod B B` for `B × B`, `Eq a b` for `a = b` and term proofs, and checks them against the
environment's), newest first:
`P = [useFT, useTF, orU, orU._proof_1, swapR, orB, orB.match_1, B.casesOn, Prod.snd, Prod.fst,
Prod.rec, Prod.mk, Prod] ++ NVQ`'s quotient constants `++ NVP.P`. `P` is the closure of the terms
through what the eraser reads: the value of the theorem `orU._proof_1` is not read, and the
constants it alone names (`orB_comm`, `Eq.ndrec`, `Eq.symm`) are not in `P`. The view reads `P` as
a list, with `@[inline]` on the matcher `orB.match_1`; the default configuration. The terms: `e`,
the constant `useTF`, and `eFT`, the constant `useFT`, the same function on the other
representative of the class.
-/

open Lean Erasure

namespace EraseProof.Test.NVQP

open EraseProof.Test.NV1 (tB cF cT)
open EraseProof.Test.NVP (an l1)

/-- A hygienic binder name of the elaborated definitions, `x._@.834910558._hygCtx._hyg.k`
(macro scopes of the elaboration that `tools/NVEmit.lean` runs). -/
def hyg (k : Nat) : Name :=
  .mkNum (.mkStr (.mkStr (.mkNum (.mkStr (.mkStr .anonymous "x") "_@") 834910558) "_hygCtx") "_hyg") k

/-- The hygienic name `x._@.834910558._hygCtx.c.834910558._hygCtx._hyg.k` of the matcher's
discriminants. -/
def hyg2 (c k : Nat) : Name :=
  .mkNum (.mkStr (.mkStr (.mkNum (.mkNum (.mkStr (.mkNum (.mkStr (.mkStr .anonymous "x") "_@")
    834910558) "_hygCtx") c) 834910558) "_hygCtx") "_hyg") k

def uu : Level := .param `u
def uv : Level := .param `v
def u1 : Level := .param `u_1

/-! ## `Prod.{u, v} (α : Type u) (β : Type v) : Type (max u v)` (`Init.Prelude`) -/

/-- `@Prod.{u, v} α β` -/
def prodC (α β : Expr) : Expr := .app (.app (.const `Prod [uu, uv]) α) β
/-- `@Prod.mk.{u, v} α β` -/
def mkC (α β : Expr) : Expr := .app (.app (.const `Prod.mk [uu, uv]) α) β

def Prod_ind : InductiveVal :=
  { name := `Prod, levelParams := [`u, `v],
    type := .forallE `α (.sort (.succ uu)) (.forallE `β (.sort (.succ uv))
      (.sort (.max (.succ uu) (.succ uv))) .default) .default,
    numParams := 2, numIndices := 0, all := [`Prod], ctors := [`Prod.mk], numNested := 0,
    isRec := false, isUnsafe := false, isReflexive := false }

def Prod_mk : ConstructorVal :=
  { name := `Prod.mk, levelParams := [`u, `v],
    type := .forallE `α (.sort (.succ uu)) (.forallE `β (.sort (.succ uv)) (.forallE `fst (.bvar 1)
      (.forallE `snd (.bvar 1) (prodC (.bvar 3) (.bvar 2)) .default) .default) .implicit) .implicit,
    induct := `Prod, cidx := 0, numParams := 2, numFields := 2, isUnsafe := false }

/-- `(t : Prod α β) → Sort u_1`, under `α β`. -/
def prMotTy : Expr := .forallE `t (prodC (.bvar 1) (.bvar 0)) (.sort u1) .default

/-- `(fst : α) → (snd : β) → motive (Prod.mk fst snd)`, under `α β motive`. -/
def prMinTy : Expr :=
  .forallE `fst (.bvar 2) (.forallE `snd (.bvar 2)
    (.app (.bvar 2) (.app (.app (mkC (.bvar 4) (.bvar 3)) (.bvar 1)) (.bvar 0))) .default) .default

/-- The rule's right-hand side `fun α β motive mk fst snd => mk fst snd`. -/
def prRhs : Expr :=
  .lam `α (.sort (.succ uu)) (.lam `β (.sort (.succ uv)) (.lam `motive prMotTy (.lam `mk prMinTy
    (.lam `fst (.bvar 3) (.lam `snd (.bvar 3) (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0)) .default)
      .default) .default) .default) .default) .default

def Prod_rec : RecursorVal :=
  { name := `Prod.rec, levelParams := [`u_1, `u, `v],
    type := .forallE `α (.sort (.succ uu)) (.forallE `β (.sort (.succ uv)) (.forallE `motive prMotTy
      (.forallE `mk prMinTy (.forallE `t (prodC (.bvar 3) (.bvar 2)) (.app (.bvar 2) (.bvar 0))
        .default) .default) .implicit) .implicit) .implicit,
    all := [`Prod], numParams := 2, numIndices := 0, numMotives := 1, numMinors := 1,
    rules := [{ ctor := `Prod.mk, nfields := 2, rhs := prRhs }], k := false, isUnsafe := false }

/-- `{α : Type u} → {β : Type v} → Prod α β → R`, with `R` under `α β self`. -/
def projTy (R : Expr) : Expr :=
  .forallE `α (.sort (.succ uu)) (.forallE `β (.sort (.succ uv))
    (.forallE `self (prodC (.bvar 1) (.bvar 0)) R .default) .implicit) .implicit

/-- `fun α β self => self.i` -/
def projVal (i : Nat) : Expr :=
  .lam `α (.sort (.succ uu)) (.lam `β (.sort (.succ uv))
    (.lam `self (prodC (.bvar 1) (.bvar 0)) (.proj `Prod i (.bvar 0)) .default) .default) .default

def Prod_fst : DefinitionVal :=
  { name := `Prod.fst, levelParams := [`u, `v], type := projTy (.bvar 2), value := projVal 0,
    hints := .abbrev, safety := .safe, all := [`Prod.fst] }

def Prod_snd : DefinitionVal :=
  { name := `Prod.snd, levelParams := [`u, `v], type := projTy (.bvar 1), value := projVal 1,
    hints := .abbrev, safety := .safe, all := [`Prod.snd] }

/-! ## The program -/

/-- `Prod.{0,0} B B` -/
def tP : Expr := .app (.app (.const `Prod [.zero, .zero]) tB) tB
/-- `Prod.fst.{0,0} B B x` and `Prod.snd.{0,0} B B x` -/
def fstB (x : Expr) : Expr := .app (.app (.app (.const `Prod.fst [.zero, .zero]) tB) tB) x
def sndB (x : Expr) : Expr := .app (.app (.app (.const `Prod.snd [.zero, .zero]) tB) tB) x
/-- `Prod.mk.{0,0} B B a b` -/
def pairB (a b : Expr) : Expr := .app (.app (.app (.app (.const `Prod.mk [.zero, .zero]) tB) tB) a) b
/-- `orB a b` -/
def orBC (a b : Expr) : Expr := .app (.app (.const `orB []) a) b
/-- `Eq.{1} B a b` -/
def eqB (a b : Expr) : Expr := .app (.app (.app (.const `Eq [l1]) tB) a) b

/-- `(x : B) → (y : B) → Sort u_1`, the matcher's motive type. -/
def motMTy : Expr := .forallE (hyg2 7 26) tB (.forallE (hyg2 8 29) tB (.sort u1) .default) .default

/-- `(motive : B → B → Sort u_1) → (x y : B) → ((b : B) → motive B.f b) →
((y : B) → motive B.t y) → motive x y` -/
def matchTy : Expr :=
  .forallE `motive motMTy (.forallE (hyg2 7 26) tB (.forallE (hyg2 8 29) tB
    (.forallE `h_1 (.forallE `b tB (.app (.app (.bvar 3) cF) (.bvar 0)) .default)
      (.forallE `h_2 (.forallE (hyg 42) tB (.app (.app (.bvar 4) cT) (.bvar 0)) .default)
        (.app (.app (.bvar 4) (.bvar 3)) (.bvar 2)) .default) .default) .default) .default) .default

/-- `fun motive x y h_1 h_2 => B.casesOn (fun x => motive x y) x (h_1 y) (h_2 y)` -/
def matchVal : Expr :=
  .lam `motive motMTy (.lam (hyg2 7 26) tB (.lam (hyg2 8 29) tB
    (.lam `h_1 (.forallE `b tB (.app (.app (.bvar 3) cF) (.bvar 0)) .default)
      (.lam `h_2 (.forallE (hyg 42) tB (.app (.app (.bvar 4) cT) (.bvar 0)) .default)
        (.app (.app (.app (.app (.const `B.casesOn [u1])
          (.lam `x tB (.app (.app (.bvar 5) (.bvar 0)) (.bvar 3)) .default)) (.bvar 3))
          (.app (.bvar 1) (.bvar 2))) (.app (.bvar 0) (.bvar 2))) .default) .default) .default)
      .default) .default

def orB_match_1 : DefinitionVal :=
  { name := `orB.match_1, levelParams := [`u_1], type := matchTy, value := matchVal,
    hints := .abbrev, safety := .safe, all := [`orB.match_1] }

/-- `B → B → B` -/
def orBTy : Expr := .forallE an tB (.forallE an tB tB .default) .default

/-- `fun x y => orB.match_1 (fun x y => B) x y (fun b => b) (fun _ => B.t)` -/
def orBVal : Expr :=
  .lam (hyg 7) tB (.lam (hyg 8) tB
    (.app (.app (.app (.app (.app (.const `orB.match_1 [l1])
      (.lam (hyg2 7 26) tB (.lam (hyg2 8 29) tB tB .default) .default)) (.bvar 1)) (.bvar 0))
      (.lam `b tB (.bvar 0) .default)) (.lam (hyg 42) tB cT .default)) .default) .default

def orB_def : DefinitionVal :=
  { name := `orB, levelParams := [], type := orBTy, value := orBVal, hints := .regular 1,
    safety := .safe, all := [`orB] }

/-- `Prod B B → Prod B B → Prop` -/
def swapRTy : Expr := .forallE `p tP (.forallE `q tP (.sort .zero) .default) .default

/-- `fun p q => Eq q (Prod.mk p.2 p.1)` -/
def swapRVal : Expr :=
  .lam `p tP (.lam `q tP (.app (.app (.app (.const `Eq [l1]) tP) (.bvar 0))
    (pairB (sndB (.bvar 1)) (fstB (.bvar 1)))) .default) .default

def swapR_def : DefinitionVal :=
  { name := `swapR, levelParams := [], type := swapRTy, value := swapRVal, hints := .regular 1,
    safety := .safe, all := [`swapR] }

/-- `∀ p q, swapR p q → orB p.1 p.2 = orB q.1 q.2` -/
def respTy : Expr :=
  .forallE `p tP (.forallE `q tP (.forallE `h (.app (.app (.const `swapR []) (.bvar 1)) (.bvar 0))
    (eqB (orBC (fstB (.bvar 2)) (sndB (.bvar 2))) (orBC (fstB (.bvar 1)) (sndB (.bvar 1))))
    .default) .default) .default

/-- `fun p q h => @Eq.ndrec (Prod B B) (p.2, p.1) (fun q => orB p.1 p.2 = orB q.1 q.2)
(orB_comm p.1 p.2) q (Eq.symm h)` -/
def respVal : Expr :=
  .lam `p tP (.lam `q tP (.lam `h (.app (.app (.const `swapR []) (.bvar 1)) (.bvar 0))
    (mkAppN (.const `Eq.ndrec [.zero, l1]) #[tP, pairB (sndB (.bvar 2)) (fstB (.bvar 2)),
      .lam `q tP (eqB (orBC (fstB (.bvar 3)) (sndB (.bvar 3))) (orBC (fstB (.bvar 0)) (sndB (.bvar 0))))
        .default,
      .app (.app (.const `orB_comm []) (fstB (.bvar 2))) (sndB (.bvar 2)), .bvar 1,
      mkAppN (.const `Eq.symm [l1]) #[tP, .bvar 1, pairB (sndB (.bvar 2)) (fstB (.bvar 2)), .bvar 0]])
    .default) .default) .default

/-- The respect proof of `orU`, abstracted by the elaborator. -/
def resp_thm : TheoremVal :=
  { name := `orU._proof_1, levelParams := [], type := respTy, value := respVal,
    all := [`orU._proof_1] }

/-- `Quot.{1} (Prod B B) swapR` -/
def tQ : Expr := .app (.app (.const `Quot [l1]) tP) (.const `swapR [])

/-- `fun p => orB p.1 p.2` -/
def liftF : Expr := .lam `p tP (orBC (fstB (.bvar 0)) (sndB (.bvar 0))) .default

/-- `@Quot.lift.{1,1} (Prod B B) swapR B (fun p => orB p.1 p.2) orU._proof_1` -/
def orUVal : Expr :=
  mkAppN (.const `Quot.lift [l1, l1]) #[tP, .const `swapR [], tB, liftF, .const `orU._proof_1 []]

def orU_def : DefinitionVal :=
  { name := `orU, levelParams := [], type := .forallE an tQ tB .default, value := orUVal,
    hints := .regular 2, safety := .safe, all := [`orU] }

/-- `orU (@Quot.mk.{1} (Prod B B) swapR (Prod.mk a b))` -/
def useVal (a b : Expr) : Expr :=
  .app (.const `orU []) (mkAppN (.const `Quot.mk [l1]) #[tP, .const `swapR [], pairB a b])

def useTF_def : DefinitionVal :=
  { name := `useTF, levelParams := [], type := tB, value := useVal cT cF, hints := .regular 3,
    safety := .safe, all := [`useTF] }

def useFT_def : DefinitionVal :=
  { name := `useFT, levelParams := [], type := tB, value := useVal cF cT, hints := .regular 3,
    safety := .safe, all := [`useFT] }

/-- NV-QP's program, newest first. -/
def P : List ConstantInfo :=
  [.defnInfo useFT_def, .defnInfo useTF_def, .defnInfo orU_def, .thmInfo resp_thm,
    .defnInfo swapR_def, .defnInfo orB_def, .defnInfo orB_match_1, .defnInfo NV1.B_casesOn,
    .defnInfo Prod_snd, .defnInfo Prod_fst, .recInfo Prod_rec, .ctorInfo Prod_mk,
    .inductInfo Prod_ind] ++ NVQ.qs.reverse.map .quotInfo ++ NVP.P

/-- NV-QP's term: `useTF`, `orU` on the class of `(B.t, B.f)`. -/
def e : Expr := .const `useTF []

/-- The second term: `useFT`, `orU` on the class of `(B.f, B.t)`. -/
def eFT : Expr := .const `useFT []

/-- NV-QP's view: `P` as a list, `@[inline]` on the matcher `orB.match_1`, as in the environment
that elaborates the program. -/
def view : EnvView where
  find? := findConst P
  isExtern _ := false
  inlineAttr? n := if n == `orB.match_1 then some .inline else none
  implementedBy? _ := none

/-- The default configuration. -/
def cfg : ErasureConfig := {}

end EraseProof.Test.NVQP
