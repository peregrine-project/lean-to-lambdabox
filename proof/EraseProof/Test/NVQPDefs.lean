import EraseProof.Test.NVQPBlocks
import EraseProof.Test.NVQModel
import EraseProof.Test.NVSFuns

/-!
# NV-QP: the Metalean definitions

The Metalean forms of `orB.match_1`, `orB`, `swapR`, the statement of `orU._proof_1`, `orU`,
`useTF` and `useFT` (`Test/NVQPData.lean`) and the typing of their values at their types, in any
well-formed environment whose heads hold the blocks of `B`, `Prod` and `Eq`, the quotient entry and
the earlier constants (the hypotheses on the heads' types). `orU`'s value is the η-term of
`Quot.lift` applied to five arguments, the last the respect proof `orU._proof_1`, whose statement
`∀ p q, swapR p q → orB p.1 p.2 = orB q.1 q.2` is β-convertible to the compatibility type of the
lifted function `fun p => orB p.1 p.2` (`respTyM_defeq`). For `Test/NVQPModel.lean`.
-/

open Lean Metalean

namespace EraseProof.Test.NVQP

open EraseProof.Test.NV1 (bSig bBlock mB mF mT mMot indB_typed ctorB_typed typed_of_eq var_of_get
  app_typed const_typed fin0_eq lu casesOnTyM)
open EraseProof.Test.NVS (ppSig mPP mPPmk defeq_rw beta_defeq app_typed' one)
open EraseProof.Test.NVP (eqA eqA_typed l1M mB_typed mT_typed typed_of_eq')

/-- A family of terms closed under renaming is typed in every context if it is in the empty one. -/
theorem typed_wk {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {f g : (n : Nat) → Expr ζ ℓ n}
    (hf : ∀ {m k : Nat} (ρ : Ren m k), (f m).rename ρ = f k)
    (hg : ∀ {m k : Nat} (ρ : Ren m k), (g m).rename ρ = g k) (h : E[.nil] ⊢ f 0 : g 0) {n : Nat}
    {Γ : Ctx ζ ℓ 0 n} : E[Γ] ⊢ f n : g n := by
  have h' := Defeq.wkClosed (Γ := Γ) h
  rwa [Expr.wkClosed_of_rename hf, Expr.wkClosed_of_rename hg] at h'

/-- `max 1 1 = 1`. -/
theorem prLevel_zero : (prLevel .zero .zero : Level 0) = l1M := Level.ext fun ν => by simp

section Terms
variable {ζ : Sigs} (ηB : Head ζ (.inductive bSig)) (ηP : Head ζ (.inductive ppSig))
  (ηE : Head ζ (.inductive Eq.sig)) (ηQ : Head ζ .quot) (ηF ηS : Head ζ (.const .def 2))
  (ηC ηM : Head ζ (.const .def 1)) (ηO ηW ηU : Head ζ (.const .def 0))
  (ηH : Head ζ (.const .«opaque» 0)) {n : Nat}

/-- `Prod.{0,0} B B` -/
def tPM : Expr ζ 0 n := mPP ηP .zero .zero (mB ηB) (mB ηB)
/-- `@Prod.fst.{0,0} B B`, `@Prod.snd.{0,0} B B` -/
def fstBB : Expr ζ 0 n := .app (.app (.const ηF ![.zero, .zero]) (mB ηB)) (mB ηB)
def sndBB : Expr ζ 0 n := .app (.app (.const ηS ![.zero, .zero]) (mB ηB)) (mB ηB)
/-- `x.1`, `x.2` through `Prod.fst` and `Prod.snd` -/
def fstM (x : Expr ζ 0 n) : Expr ζ 0 n := .app (fstBB ηB ηF) x
def sndM (x : Expr ζ 0 n) : Expr ζ 0 n := .app (sndBB ηB ηS) x
/-- `orB a b` -/
def orBM (a b : Expr ζ 0 n) : Expr ζ 0 n := .app (.app (.const ηO Fin.elim0) a) b
/-- `Prod.mk.{0,0} B B a b` -/
def pairM (a b : Expr ζ 0 n) : Expr ζ 0 n := mPPmk ηP .zero .zero (mB ηB) (mB ηB) a b
/-- `swapR` -/
def swapM : Expr ζ 0 n := .const ηW Fin.elim0
/-- `Quot.{1} (Prod B B) swapR` -/
def quotTM : Expr ζ 0 n := .quot ηQ l1M (tPM ηB ηP) (swapM ηW)

/-- `B → B → Sort u_1` -/
def motMM : Expr ζ 1 n := .forallE (mB ηB) (.forallE (mB ηB) (.sort lu))

/-- `orB.match_1`'s type `(motive : B → B → Sort u_1) → (x y : B) → ((b : B) → motive B.f b) →
((y : B) → motive B.t y) → motive x y`. -/
def omTyM : Expr ζ 1 0 :=
  .forallE (motMM ηB) (.forallE (mB ηB) (.forallE (mB ηB)
    (.forallE (.forallE (mB ηB) (.app (.app #0 (mF ηB)) #3))
      (.forallE (.forallE (mB ηB) (.app (.app #0 (mT ηB)) #4)) (.app (.app #0 #1) #2)))))

/-- `fun motive x y h_1 h_2 => B.casesOn (fun x => motive x y) x (h_1 y) (h_2 y)` -/
def omValM : Expr ζ 1 0 :=
  .lam (motMM ηB) (.lam (mB ηB) (.lam (mB ηB)
    (.lam (.forallE (mB ηB) (.app (.app #0 (mF ηB)) #3))
      (.lam (.forallE (mB ηB) (.app (.app #0 (mT ηB)) #4))
        (.app (.app (.app (.app (.const ηC ![lu]) (.lam (mB ηB) (.app (.app #0 #5) #2))) #1)
          (.app #3 #2)) (.app #4 #2))))))

/-- `B → B → B` -/
def orBTyM : Expr ζ 0 0 := .forallE (mB ηB) (.forallE (mB ηB) (mB ηB))

/-- `fun x y => B` -/
def motBM : Expr ζ 0 n := .lam (mB ηB) (.lam (mB ηB) (mB ηB))

/-- `fun x y => orB.match_1 (fun x y => B) x y (fun b => b) (fun _ => B.t)` -/
def orBValM : Expr ζ 0 0 :=
  .lam (mB ηB) (.lam (mB ηB) (.app (.app (.app (.app (.app (.const ηM ![l1M]) (motBM ηB)) #0) #1)
    (.lam (mB ηB) #2)) (.lam (mB ηB) (mT ηB))))

/-- `Prod B B → Prod B B → Prop` -/
def swapTyM : Expr ζ 0 0 := .forallE (tPM ηB ηP) (.forallE (tPM ηB ηP) .prop)

/-- `fun p q => q = (p.2, p.1)` -/
def swapValM : Expr ζ 0 0 :=
  .lam (tPM ηB ηP) (.lam (tPM ηB ηP) (eqA ηE l1M (tPM ηB ηP) #1
    (pairM ηB ηP (sndM ηB ηS #0) (fstM ηB ηF #0))))

/-- `∀ p q, swapR p q → orB p.1 p.2 = orB q.1 q.2` -/
def respTyM : Expr ζ 0 0 :=
  .forallE (tPM ηB ηP) (.forallE (tPM ηB ηP) (.forallE (.app (.app (swapM ηW) #0) #1)
    (eqA ηE l1M (mB ηB) (orBM ηO (fstM ηB ηF #0) (sndM ηB ηS #0))
      (orBM ηO (fstM ηB ηF #1) (sndM ηB ηS #1)))))

/-- `fun p => orB p.1 p.2` -/
def liftFM : Expr ζ 0 0 := .lam (tPM ηB ηP) (orBM ηO (fstM ηB ηF #0) (sndM ηB ηS #0))

/-- The binders of `Quot.lift`'s η-term at the levels `u`, `v`. -/
def ΔLM {ℓ : Nat} (u v : Level ℓ) : Ctx ζ ℓ 0 6 :=
  #t[.sort u, Quot.relType #0, .sort v, .forallE #0 #2, Quot.compatType ηE v #0 #1 #2 #3,
    .quot ηQ u #0 #1]

/-- `Quot.lift.{1,1}`'s η-term. -/
def liftEtaM : Expr ζ 0 0 := (ΔLM ηE ηQ l1M l1M).lam (.quotLift ηQ l1M l1M #0 #1 #2 #3 #4 #5)

/-- `Quot (Prod B B) swapR → B` -/
def orUTyM : Expr ζ 0 0 := .forallE (quotTM ηB ηP ηQ ηW) (mB ηB)

/-- `@Quot.lift (Prod B B) swapR B (fun p => orB p.1 p.2) orU._proof_1`, the η-term of
`Quot.lift` applied to five arguments. -/
def orUValM : Expr ζ 0 0 :=
  .app (.app (.app (.app (.app (liftEtaM ηE ηQ) (tPM ηB ηP)) (swapM ηW)) (mB ηB))
    (liftFM ηB ηP ηF ηS ηO)) (.const ηH Fin.elim0)

/-- `orU (Quot.mk swapR (a, b))` -/
def useValM (a b : Expr ζ 0 0) : Expr ζ 0 0 :=
  .app (.const ηU Fin.elim0) (.quotMk ηQ l1M (tPM ηB ηP) (swapM ηW) (pairM ηB ηP a b))

end Terms

/-- Compute substitutions, renamings, weakenings and level instantiations on NV-QP's terms. -/
syntax (name := _qsx) "qsx" ("[" ident,* "]")? (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| qsx $[$loc]?) => `(tactic| qsx [Ctx.get] $[$loc]?)
  | `(tactic| qsx [$ts,*] $[$loc]?) => `(tactic| rsx [$[$ts:ident],*, mB, mF, mT, mMot, tPM, fstBB,
      sndBB, fstM, sndM, orBM, pairM, swapM, quotTM, motMM, motBM, Quot.compatType, Quot.relType,
      Quot.eqApp, eqA, prFstTyM, prSndTyM, ΓPr, Ctx.pi, Tele.foldr, casesOnTyM] $[$loc]?)

section Typed
variable {ζ : Sigs} {E : Env ζ} {ηB : Head ζ (.inductive bSig)} {ηP : Head ζ (.inductive ppSig)}
  {ηE : Head ζ (.inductive Eq.sig)} {ηQ : Head ζ .quot} {ηF ηS : Head ζ (.const .def 2)}
  {ηC ηM : Head ζ (.const .def 1)} {ηO ηW ηU : Head ζ (.const .def 0)}
  {ηH : Head ζ (.const .«opaque» 0)}
  (hE : EnvWF E) (hb : (E.get ηB).block = bBlock) (hp : (E.get ηP).block = prBlock)

include hb in
theorem mFT {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} : E[Γ] ⊢ mF ηB : mB ηB := ctorB_typed hb
include hb in
theorem mTT {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} : E[Γ] ⊢ mT ηB : mB ηB := ctorB_typed hb

include hb hp in
theorem tPM_typed {n : Nat} {Γ : Ctx ζ 0 0 n} : E[Γ] ⊢ tPM ηB ηP : .sort l1M :=
  typed_of_eq' (mPr_typed hp (mB_typed hb) (mB_typed hb)) prLevel_zero

include hb hp in
theorem pairM_typed {n : Nat} {Γ : Ctx ζ 0 0 n} {a b : Expr ζ 0 n} (ha : E[Γ] ⊢ a : mB ηB)
    (hb' : E[Γ] ⊢ b : mB ηB) : E[Γ] ⊢ pairM ηB ηP a b : tPM ηB ηP :=
  mPrmk_typed hp (mB_typed hb) (mB_typed hb) ha hb'

include hE hb in
theorem fstBB_typed (hft : (E.get ηF).constType = prFstTyM ηP) {n : Nat} {Γ : Ctx ζ 0 0 n} :
    E[Γ] ⊢ fstBB ηB ηF : .forallE (tPM ηB ηP) (mB ηB) := by
  refine typed_wk (f := fun n => fstBB ηB ηF (n := n))
    (g := fun n => .forallE (tPM ηB ηP) (mB ηB)) (fun ρ => by qsx) (fun ρ => by qsx) ?_
  have h0 : E[(.nil : Ctx ζ 0 0 0)] ⊢ .const ηF ![.zero, .zero] :
      .forallE (.sort (.succ .zero)) (.forallE (.sort (.succ .zero))
        (.forallE (mPP ηP .zero .zero #0 #1) #0)) :=
    const_typed hE ηF _ (by rw [hft]; qsx)
  have h1 := app_typed h0 (mB_typed hb)
  qsx at h1
  have h2 := app_typed h1 (mB_typed hb)
  exact typed_of_eq h2 (by qsx)

include hE hb in
theorem sndBB_typed (hst : (E.get ηS).constType = prSndTyM ηP) {n : Nat} {Γ : Ctx ζ 0 0 n} :
    E[Γ] ⊢ sndBB ηB ηS : .forallE (tPM ηB ηP) (mB ηB) := by
  refine typed_wk (f := fun n => sndBB ηB ηS (n := n))
    (g := fun n => .forallE (tPM ηB ηP) (mB ηB)) (fun ρ => by qsx) (fun ρ => by qsx) ?_
  have h0 : E[(.nil : Ctx ζ 0 0 0)] ⊢ .const ηS ![.zero, .zero] :
      .forallE (.sort (.succ .zero)) (.forallE (.sort (.succ .zero))
        (.forallE (mPP ηP .zero .zero #0 #1) #1)) :=
    const_typed hE ηS _ (by rw [hst]; qsx)
  have h1 := app_typed h0 (mB_typed hb)
  qsx at h1
  have h2 := app_typed h1 (mB_typed hb)
  exact typed_of_eq h2 (by qsx)

include hE hb in
theorem fstM_typed (hft : (E.get ηF).constType = prFstTyM ηP) {n : Nat} {Γ : Ctx ζ 0 0 n}
    {x : Expr ζ 0 n} (hx : E[Γ] ⊢ x : tPM ηB ηP) : E[Γ] ⊢ fstM ηB ηF x : mB ηB :=
  typed_of_eq (app_typed (fstBB_typed hE hb hft) hx) (by qsx)

include hE hb in
theorem sndM_typed (hst : (E.get ηS).constType = prSndTyM ηP) {n : Nat} {Γ : Ctx ζ 0 0 n}
    {x : Expr ζ 0 n} (hx : E[Γ] ⊢ x : tPM ηB ηP) : E[Γ] ⊢ sndM ηB ηS x : mB ηB :=
  typed_of_eq (app_typed (sndBB_typed hE hb hst) hx) (by qsx)

include hE in
theorem orBC_typed (hot : (E.get ηO).constType = orBTyM ηB) {n : Nat} {Γ : Ctx ζ 0 0 n} :
    E[Γ] ⊢ .const ηO Fin.elim0 : .forallE (mB ηB) (.forallE (mB ηB) (mB ηB)) :=
  typed_wk (f := fun _ => .const ηO Fin.elim0)
    (g := fun _ => .forallE (mB ηB) (.forallE (mB ηB) (mB ηB))) (fun ρ => by qsx)
    (fun ρ => by qsx) (const_typed hE ηO _ (by rw [hot]; qsx [orBTyM]))

include hE in
theorem orBM_typed (hot : (E.get ηO).constType = orBTyM ηB) {n : Nat} {Γ : Ctx ζ 0 0 n}
    {a b : Expr ζ 0 n} (ha : E[Γ] ⊢ a : mB ηB) (hb' : E[Γ] ⊢ b : mB ηB) :
    E[Γ] ⊢ orBM ηO a b : mB ηB := by
  have h1 := typed_of_eq (app_typed (orBC_typed hE hot) ha) (T' := .forallE (mB ηB) (mB ηB))
    (by qsx)
  exact typed_of_eq (app_typed h1 hb') (by qsx)

include hE in
theorem swapC_typed (hwt : (E.get ηW).constType = swapTyM ηB ηP) {n : Nat} {Γ : Ctx ζ 0 0 n} :
    E[Γ] ⊢ swapM ηW : .forallE (tPM ηB ηP) (.forallE (tPM ηB ηP) .prop) :=
  typed_wk (f := fun _ => swapM ηW) (g := fun _ => .forallE (tPM ηB ηP) (.forallE (tPM ηB ηP) .prop))
    (fun ρ => by qsx) (fun ρ => by qsx) (const_typed hE ηW _ (by rw [hwt]; qsx [swapTyM]))

include hE in
theorem swapApp_typed (hwt : (E.get ηW).constType = swapTyM ηB ηP) {n : Nat} {Γ : Ctx ζ 0 0 n}
    {x y : Expr ζ 0 n} (hx : E[Γ] ⊢ x : tPM ηB ηP) (hy : E[Γ] ⊢ y : tPM ηB ηP) :
    E[Γ] ⊢ .app (.app (swapM ηW) x) y : .prop := by
  have h1 := typed_of_eq (app_typed (swapC_typed hE hwt) hx) (T' := .forallE (tPM ηB ηP) .prop)
    (by qsx)
  exact typed_of_eq (app_typed h1 hy) (by qsx)

/-! ### `orB.match_1` -/

/-- `orB.match_1`'s binder context `motive x y h_1 h_2`. -/
def ΓOM (ηB : Head ζ (.inductive bSig)) : Ctx ζ 1 0 5 :=
  #t[motMM ηB, mB ηB, mB ηB, .forallE (mB ηB) (.app (.app #0 (mF ηB)) #3),
    .forallE (mB ηB) (.app (.app #0 (mT ηB)) #4)]

/-- `motive a b : Sort u_1` -/
theorem appMot2_typed {n : Nat} {Γ : Ctx ζ 1 0 n} {m a b : Expr ζ 1 n}
    (hm : E[Γ] ⊢ m : motMM ηB) (ha : E[Γ] ⊢ a : mB ηB) (hb' : E[Γ] ⊢ b : mB ηB) :
    E[Γ] ⊢ .app (.app m a) b : .sort lu := by
  have h1 := typed_of_eq (app_typed hm ha) (T' := .forallE (mB ηB) (.sort lu)) (by qsx)
  exact typed_of_eq (app_typed h1 hb') (by qsx)

include hE hb in
theorem omValM_typed (hct : (E.get ηC).constType = casesOnTyM ηB) :
    E[.nil] ⊢ omValM ηB ηC : omTyM ηB := by
  have hBt : ∀ {n : Nat} {Γ : Ctx ζ 1 0 n}, E[Γ] ⊢ mB ηB : .sort (.succ .zero) := fun {_ _} =>
    indB_typed hb
  have hmot : ∀ {n : Nat} {Γ : Ctx ζ 1 0 n}, E[Γ] ⊢ motMM ηB : _ := fun {_ _} =>
    .forallEDF hBt (.forallEDF hBt .sortDF .sortDF) (.forallEDF hBt .sortDF .sortDF)
  have h1 : E[(#t[motMM ηB] : Ctx ζ 1 0 1)] ⊢ ok := .snoc .nil ⟨_, hmot⟩
  have h2 : E[(#t[motMM ηB, mB ηB] : Ctx ζ 1 0 2)] ⊢ ok := .snoc h1 ⟨_, hBt⟩
  have h3 : E[(#t[motMM ηB, mB ηB, mB ηB] : Ctx ζ 1 0 3)] ⊢ ok := .snoc h2 ⟨_, hBt⟩
  have h3b : E[(#t[motMM ηB, mB ηB, mB ηB, mB ηB] : Ctx ζ 1 0 4)] ⊢ ok := .snoc h3 ⟨_, hBt⟩
  have hf3 := appMot2_typed (var_of_get h3b ⟨0, by decide⟩ (by qsx)) (mFT hb)
    (var_of_get h3b ⟨3, by decide⟩ (by qsx))
  have h4 : E[(#t[motMM ηB, mB ηB, mB ηB, .forallE (mB ηB) (.app (.app #0 (mF ηB)) #3)] :
      Ctx ζ 1 0 4)] ⊢ ok := .snoc h3 ⟨_, .forallEDF hBt hf3 hf3⟩
  have h4b : E[(#t[motMM ηB, mB ηB, mB ηB, .forallE (mB ηB) (.app (.app #0 (mF ηB)) #3), mB ηB] :
      Ctx ζ 1 0 5)] ⊢ ok := .snoc h4 ⟨_, hBt⟩
  have ht4 := appMot2_typed (var_of_get h4b ⟨0, by decide⟩ (by qsx)) (mTT hb)
    (var_of_get h4b ⟨4, by decide⟩ (by qsx))
  have hΓ : E[ΓOM ηB] ⊢ ok := .snoc h4 ⟨_, .forallEDF hBt ht4 ht4⟩
  have hm : E[ΓOM ηB] ⊢ #0 : motMM ηB := var_of_get hΓ ⟨0, by decide⟩ (by qsx [ΓOM])
  have hx : E[ΓOM ηB] ⊢ #1 : mB ηB := var_of_get hΓ ⟨1, by decide⟩ (by qsx [ΓOM])
  have hy : E[ΓOM ηB] ⊢ #2 : mB ηB := var_of_get hΓ ⟨2, by decide⟩ (by qsx [ΓOM])
  have hh1 : E[ΓOM ηB] ⊢ #3 : .forallE (mB ηB) (.app (.app #0 (mF ηB)) #5) :=
    var_of_get hΓ ⟨3, by decide⟩ (by qsx [ΓOM])
  have hh2 : E[ΓOM ηB] ⊢ #4 : .forallE (mB ηB) (.app (.app #0 (mT ηB)) #5) :=
    var_of_get hΓ ⟨4, by decide⟩ (by qsx [ΓOM])
  -- the motive `fun x => motive x y`
  have h6 : E[(ΓOM ηB).snoc (mB ηB)] ⊢ ok := .snoc hΓ ⟨_, hBt⟩
  have hbody : E[(ΓOM ηB).snoc (mB ηB)] ⊢ .app (.app #0 #5) #2 : .sort lu :=
    appMot2_typed (var_of_get (T := motMM ηB) h6 ⟨0, by decide⟩ (by qsx [ΓOM]))
      (var_of_get (T := mB ηB) h6 ⟨5, by decide⟩ (by qsx [ΓOM]))
      (var_of_get (T := mB ηB) h6 ⟨2, by decide⟩ (by qsx [ΓOM]))
  have hMo : E[ΓOM ηB] ⊢ .lam (mB ηB) (.app (.app #0 #5) #2) : .forallE (mB ηB) (.sort lu) :=
    .lamDF hBt .sortDF .sortDF hbody hbody
  have hβ : ∀ {a : Expr ζ 1 5}, E[ΓOM ηB] ⊢ a : mB ηB →
      E[ΓOM ηB] ⊢ .app (.lam (mB ηB) (.app (.app #0 #5) #2)) a ≡ .app (.app #0 a) #2 :
        .sort lu := fun ha =>
    defeq_rw (beta_defeq hBt .sortDF hbody ha) rfl (by qsx) (by qsx)
  -- `B.casesOn (fun x => motive x y) x (h_1 y) (h_2 y)`
  have h0 : E[ΓOM ηB] ⊢ .const ηC ![lu] : (E.get ηC).constType{![lu]}.wkClosed :=
    const_typed hE ηC ![lu] rfl
  rw [hct] at h0
  qsx at h0
  have hc1 := app_typed' h0 hMo (by qsx)
  qsx at hc1
  have hc2 := app_typed' hc1 hx (by qsx)
  qsx at hc2
  have hz := typed_of_eq (app_typed hh1 hy) (T' := .app (.app #0 (mF ηB)) #2) (by qsx)
  have hc3 := app_typed' hc2 (.defeqDF (hβ (mFT hb)).symm hz) (by qsx)
  qsx at hc3
  have ht := typed_of_eq (app_typed hh2 hy) (T' := .app (.app #0 (mT ηB)) #2) (by qsx)
  have hc4 := app_typed' hc3 (.defeqDF (hβ (mTT hb)).symm ht) (by qsx)
  qsx at hc4
  have hres := Defeq.defeqDF (hβ hx) (typed_of_eq hc4 (by qsx))
  exact typed_of_eq (Ctx.lam_congr (Γ := .nil) (Δ := ΓOM ηB) hΓ hres) (by qsx [ΓOM, omTyM])

/-! ### `orB` -/

include hb in
/-- `(fun x y => B) a b ≡ B` -/
theorem motBM_beta {n : Nat} {Γ : Ctx ζ 0 0 n} {a b : Expr ζ 0 n} (ha : E[Γ] ⊢ a : mB ηB)
    (hb' : E[Γ] ⊢ b : mB ηB) : E[Γ] ⊢ .app (.app (motBM ηB) a) b ≡ mB ηB : .sort l1M := by
  have hBt : ∀ {n : Nat} {Γ : Ctx ζ 0 0 n}, E[Γ] ⊢ mB ηB : .sort l1M := fun {_ _} => mB_typed hb
  have hin : ∀ {n : Nat} {Γ : Ctx ζ 0 0 n}, E[Γ] ⊢ .lam (mB ηB) (mB ηB) :
      .forallE (mB ηB) (.sort l1M) := fun {_ _} => .lamDF hBt .sortDF .sortDF hBt hBt
  have h1 : E[Γ] ⊢ .app (motBM ηB) a ≡ .lam (mB ηB) (mB ηB) : .forallE (mB ηB) (.sort l1M) :=
    defeq_rw (beta_defeq hBt (.forallEDF hBt .sortDF .sortDF) hin ha) rfl (by qsx) (by qsx)
  have h2 : E[Γ] ⊢ .app (.app (motBM ηB) a) b ≡ .app (.lam (mB ηB) (mB ηB)) b : .sort l1M :=
    defeq_rw (.appDF hBt .sortDF h1 hb' .sortDF) rfl rfl (by qsx)
  have h3 : E[Γ] ⊢ .app (.lam (mB ηB) (mB ηB)) b ≡ mB ηB : .sort l1M :=
    defeq_rw (beta_defeq hBt .sortDF hBt hb') rfl (by qsx) (by qsx)
  exact h2.trans h3

include hE hb in
theorem orBValM_typed (hmt : (E.get ηM).constType = omTyM ηB) :
    E[.nil] ⊢ orBValM ηB ηM : orBTyM ηB := by
  have hBt : ∀ {n : Nat} {Γ : Ctx ζ 0 0 n}, E[Γ] ⊢ mB ηB : .sort l1M := fun {_ _} => mB_typed hb
  have h1 : E[(#t[mB ηB] : Ctx ζ 0 0 1)] ⊢ ok := .snoc .nil ⟨_, hBt⟩
  have hΓ : E[(#t[mB ηB, mB ηB] : Ctx ζ 0 0 2)] ⊢ ok := .snoc h1 ⟨_, hBt⟩
  have hx : E[(#t[mB ηB, mB ηB] : Ctx ζ 0 0 2)] ⊢ #0 : mB ηB := var_of_get hΓ ⟨0, by decide⟩ (by qsx)
  have hy : E[(#t[mB ηB, mB ηB] : Ctx ζ 0 0 2)] ⊢ #1 : mB ηB := var_of_get hΓ ⟨1, by decide⟩ (by qsx)
  have hin : ∀ {n : Nat} {Γ : Ctx ζ 0 0 n}, E[Γ] ⊢ .lam (mB ηB) (mB ηB) :
      .forallE (mB ηB) (.sort l1M) := fun {_ _} => .lamDF hBt .sortDF .sortDF hBt hBt
  have hMot : E[(#t[mB ηB, mB ηB] : Ctx ζ 0 0 2)] ⊢ motBM ηB :
      .forallE (mB ηB) (.forallE (mB ηB) (.sort l1M)) :=
    .lamDF hBt (.forallEDF hBt .sortDF .sortDF) (.forallEDF hBt .sortDF .sortDF) hin hin
  have h0 : E[(#t[mB ηB, mB ηB] : Ctx ζ 0 0 2)] ⊢ .const ηM ![l1M] :
      (E.get ηM).constType{![l1M]}.wkClosed := const_typed hE ηM ![l1M] rfl
  rw [hmt] at h0
  qsx [omTyM] at h0
  have hc1 := app_typed' h0 hMot (by qsx)
  qsx at hc1
  have hc2 := app_typed' hc1 hx (by qsx)
  qsx at hc2
  have hc3 := app_typed' hc2 hy (by qsx)
  qsx at hc3
  have h3 : E[(#t[mB ηB, mB ηB, mB ηB] : Ctx ζ 0 0 3)] ⊢ ok := .snoc hΓ ⟨_, hBt⟩
  have hv : E[(#t[mB ηB, mB ηB, mB ηB] : Ctx ζ 0 0 3)] ⊢ #2 : mB ηB :=
    var_of_get h3 ⟨2, by decide⟩ (by qsx)
  have hβf := motBM_beta hb (mFT hb) hv
  have hβt := motBM_beta hb (mTT hb) hv
  have ha4 : E[(#t[mB ηB, mB ηB] : Ctx ζ 0 0 2)] ⊢ .lam (mB ηB) #2 :
      .forallE (mB ηB) (.app (.app (motBM ηB) (mF ηB)) #2) :=
    .lamDF hBt hβf.left hβf.left (.defeqDF hβf.symm hv) (.defeqDF hβf.symm hv)
  have hc4 := app_typed' hc3 ha4 (by qsx)
  qsx at hc4
  have ha5 : E[(#t[mB ηB, mB ηB] : Ctx ζ 0 0 2)] ⊢ .lam (mB ηB) (mT ηB) :
      .forallE (mB ηB) (.app (.app (motBM ηB) (mT ηB)) #2) :=
    .lamDF hBt hβt.left hβt.left (.defeqDF hβt.symm (mTT hb))
      (.defeqDF hβt.symm (mTT hb))
  have hc5 := app_typed' hc4 ha5 (by qsx)
  qsx at hc5
  have hres := Defeq.defeqDF (motBM_beta hb hx hy) (typed_of_eq hc5 (by qsx))
  exact typed_of_eq (Ctx.lam_congr (Γ := .nil) (Δ := #t[mB ηB, mB ηB]) hΓ hres) (by qsx [orBTyM])

/-! ### `swapR`, the statement of `orU._proof_1` and the lifted function -/

/-- `Eq` congruence in both sides. -/
theorem eqA_defeq (hq : (E.get ηE).block = Eq.block) {n : Nat} {Γ : Ctx ζ 0 0 n} {l : Level 0}
    {α a₁ a₂ b₁ b₂ : Expr ζ 0 n} (hα : E[Γ] ⊢ α : .sort l) (ha : E[Γ] ⊢ a₁ ≡ a₂ : α)
    (hb' : E[Γ] ⊢ b₁ ≡ b₂ : α) : E[Γ] ⊢ eqA ηE l α a₁ b₁ ≡ eqA ηE l α a₂ b₂ : .prop := by
  have h := Defeq.indDF (E := E) (Γ := Γ) (η := ηE) (s := 0)
    (ls := ![l]) (ps₁ := ![α, a₁]) (ps₂ := ![α, a₂]) (is₁ := ![b₁]) (is₂ := ![b₂])
    (fun
      | ⟨0, _⟩ => by simpa! [hq, Inductive.paramType] using hα
      | ⟨1, _⟩ => by simpa! [hq, Inductive.paramType] using ha)
    (fun
      | ⟨0, _⟩ => by simpa! [hq, Inductive.indexType, Ctx.proj] using hb')
  rw [hq] at h
  simpa [Quot.eqApp] using h

/-- `swapR`'s and `orU._proof_1`'s binder contexts. -/
def ΓP2 (ηB : Head ζ (.inductive bSig)) (ηP : Head ζ (.inductive ppSig)) : Ctx ζ 0 0 2 :=
  #t[tPM ηB ηP, tPM ηB ηP]
def ΓP3 (ηB : Head ζ (.inductive bSig)) (ηP : Head ζ (.inductive ppSig))
    (ηW : Head ζ (.const .def 0)) : Ctx ζ 0 0 3 :=
  (ΓP2 ηB ηP).snoc (.app (.app (swapM ηW) #0) #1)

include hb hp in
theorem ΓP2_wf : E[ΓP2 ηB ηP] ⊢ ok :=
  .snoc (.snoc .nil ⟨_, tPM_typed hb hp⟩) ⟨_, tPM_typed hb hp⟩

include hE hb hp in
theorem ΓP3_wf (hwt : (E.get ηW).constType = swapTyM ηB ηP) : E[ΓP3 ηB ηP ηW] ⊢ ok :=
  .snoc (ΓP2_wf hb hp) ⟨_, swapApp_typed hE hwt
    (var_of_get (ΓP2_wf hb hp) ⟨0, by decide⟩ (by qsx [ΓP2]))
    (var_of_get (ΓP2_wf hb hp) ⟨1, by decide⟩ (by qsx [ΓP2]))⟩

variable (hq : (E.get ηE).block = Eq.block) (hft : (E.get ηF).constType = prFstTyM ηP)
  (hst : (E.get ηS).constType = prSndTyM ηP)

include hE hb hp hq hft hst in
theorem swapValM_typed : E[.nil] ⊢ swapValM ηB ηP ηE ηF ηS : swapTyM ηB ηP := by
  have hΓ := ΓP2_wf hb hp (E := E)
  have hp0 : E[ΓP2 ηB ηP] ⊢ #0 : tPM ηB ηP := var_of_get hΓ ⟨0, by decide⟩ (by qsx [ΓP2])
  have hp1 : E[ΓP2 ηB ηP] ⊢ #1 : tPM ηB ηP := var_of_get hΓ ⟨1, by decide⟩ (by qsx [ΓP2])
  have hbody := eqA_typed hq (tPM_typed hb hp) hp1
    (pairM_typed hb hp (sndM_typed hE hb hst hp0) (fstM_typed hE hb hft hp0))
  exact typed_of_eq (Ctx.lam_congr (Γ := .nil) (Δ := ΓP2 ηB ηP) hΓ hbody)
    (by qsx [ΓP2, swapTyM])

variable (hot : (E.get ηO).constType = orBTyM ηB) (hwt : (E.get ηW).constType = swapTyM ηB ηP)

include hE hb hft hst hot in
/-- `orB x.1 x.2 : B` -/
theorem orBfs_typed {n : Nat} {Γ : Ctx ζ 0 0 n} {x : Expr ζ 0 n} (hx : E[Γ] ⊢ x : tPM ηB ηP) :
    E[Γ] ⊢ orBM ηO (fstM ηB ηF x) (sndM ηB ηS x) : mB ηB :=
  orBM_typed hE hot (fstM_typed hE hb hft hx) (sndM_typed hE hb hst hx)

include hE hb hp hq hft hst hot hwt in
theorem respTyM_typed : E[.nil] ⊢ respTyM ηB ηP ηE ηF ηS ηO ηW : .prop := by
  have hΓ := ΓP3_wf hE hb hp hwt
  have hp0 : E[ΓP3 ηB ηP ηW] ⊢ #0 : tPM ηB ηP := var_of_get hΓ ⟨0, by decide⟩ (by qsx [ΓP3, ΓP2])
  have hp1 : E[ΓP3 ηB ηP ηW] ⊢ #1 : tPM ηB ηP := var_of_get hΓ ⟨1, by decide⟩ (by qsx [ΓP3, ΓP2])
  have hbody := eqA_typed hq (mB_typed hb) (orBfs_typed hE hb hft hst hot hp0)
    (orBfs_typed hE hb hft hst hot hp1)
  have hΓ2 := ΓP2_wf hb hp (E := E)
  have hsw : E[ΓP2 ηB ηP] ⊢ .app (.app (swapM ηW) #0) #1 : .prop :=
    swapApp_typed hE hwt (var_of_get hΓ2 ⟨0, by decide⟩ (by qsx [ΓP2]))
      (var_of_get hΓ2 ⟨1, by decide⟩ (by qsx [ΓP2]))
  have h3 : E[ΓP2 ηB ηP] ⊢ .forallE (.app (.app (swapM ηW) #0) #1) _ : _ :=
    .forallEDF hsw hbody hbody
  have h2 : E[(#t[tPM ηB ηP] : Ctx ζ 0 0 1)] ⊢ .forallE (tPM ηB ηP) _ : _ :=
    .forallEDF (tPM_typed hb hp) h3 h3
  have h1 := Defeq.forallEDF (Γ := .nil) (tPM_typed hb hp) h2 h2
  exact typed_of_eq' h1 (Level.ext fun ν => by simp [Nat.imax])

include hE hb hp hft hst hot in
theorem liftFM_typed : E[.nil] ⊢ liftFM ηB ηP ηF ηS ηO : .forallE (tPM ηB ηP) (mB ηB) := by
  have hΓ : E[(#t[tPM ηB ηP] : Ctx ζ 0 0 1)] ⊢ ok := .snoc .nil ⟨_, tPM_typed hb hp⟩
  have hbody := orBfs_typed hE hb hft hst hot (var_of_get hΓ ⟨0, by decide⟩ (T := tPM ηB ηP)
    (by qsx))
  exact .lamDF (tPM_typed hb hp) (mB_typed hb) (mB_typed hb) hbody hbody

/-- The lifted function under the binders of the compatibility type. -/
def liftF3 (ηB : Head ζ (.inductive bSig)) (ηP : Head ζ (.inductive ppSig))
    (ηF ηS : Head ζ (.const .def 2)) (ηO : Head ζ (.const .def 0)) : Expr ζ 0 3 :=
  .lam (tPM ηB ηP) (orBM ηO (fstM ηB ηF #3) (sndM ηB ηS #3))

/-- The compatibility type of the lifted function, computed. -/
def compatM (ηB : Head ζ (.inductive bSig)) (ηP : Head ζ (.inductive ppSig))
    (ηE : Head ζ (.inductive Eq.sig)) (ηF ηS : Head ζ (.const .def 2))
    (ηO ηW : Head ζ (.const .def 0)) : Expr ζ 0 0 :=
  .forallE (tPM ηB ηP) (.forallE (tPM ηB ηP) (.forallE (.app (.app (swapM ηW) #0) #1)
    (eqA ηE l1M (mB ηB) (.app (liftF3 ηB ηP ηF ηS ηO) #0) (.app (liftF3 ηB ηP ηF ηS ηO) #1))))

theorem compatM_eq {ηB : Head ζ (.inductive bSig)} {ηP : Head ζ (.inductive ppSig)}
    {ηE : Head ζ (.inductive Eq.sig)} {ηF ηS : Head ζ (.const .def 2)}
    {ηO ηW : Head ζ (.const .def 0)} :
    compatM ηB ηP ηE ηF ηS ηO ηW =
      Quot.compatType ηE l1M (tPM ηB ηP) (swapM ηW) (mB ηB) (liftFM ηB ηP ηF ηS ηO) := by
  qsx [compatM, liftF3, liftFM]

include hE hb hp hq hft hst hot hwt in
/-- `orU._proof_1`'s statement is β-convertible to the compatibility type of
`fun p => orB p.1 p.2`. -/
theorem respTyM_defeq :
    E[.nil] ⊢ respTyM ηB ηP ηE ηF ηS ηO ηW ≡ compatM ηB ηP ηE ηF ηS ηO ηW :
      .sort (.imax l1M (.imax l1M (.imax .zero .zero))) := by
  have hΓ := ΓP3_wf hE hb hp hwt
  have hp0 : E[ΓP3 ηB ηP ηW] ⊢ #0 : tPM ηB ηP := var_of_get hΓ ⟨0, by decide⟩ (by qsx [ΓP3, ΓP2])
  have hp1 : E[ΓP3 ηB ηP ηW] ⊢ #1 : tPM ηB ηP := var_of_get hΓ ⟨1, by decide⟩ (by qsx [ΓP3, ΓP2])
  have h4 : E[(ΓP3 ηB ηP ηW).snoc (tPM ηB ηP)] ⊢ ok := .snoc hΓ ⟨_, tPM_typed hb hp⟩
  have hb4 := orBfs_typed hE hb hft hst hot (var_of_get h4 ⟨3, by decide⟩ (T := tPM ηB ηP)
    (by qsx [ΓP3, ΓP2]))
  have hβ : ∀ {x : Expr ζ 0 3}, E[ΓP3 ηB ηP ηW] ⊢ x : tPM ηB ηP →
      E[ΓP3 ηB ηP ηW] ⊢ orBM ηO (fstM ηB ηF x) (sndM ηB ηS x) ≡
        .app (liftF3 ηB ηP ηF ηS ηO) x : mB ηB := fun hx =>
    (defeq_rw (beta_defeq (tPM_typed hb hp) (mB_typed hb) hb4 hx) rfl (by qsx [liftF3])
      (by qsx)).symm
  have hd := eqA_defeq hq (mB_typed hb) (hβ hp0) (hβ hp1) (ηE := ηE) (l := l1M)
  have hΓ2 := ΓP2_wf hb hp (E := E)
  have hsw : E[ΓP2 ηB ηP] ⊢ .app (.app (swapM ηW) #0) #1 : .prop :=
    swapApp_typed hE hwt (var_of_get hΓ2 ⟨0, by decide⟩ (by qsx [ΓP2]))
      (var_of_get hΓ2 ⟨1, by decide⟩ (by qsx [ΓP2]))
  have h3 : E[ΓP2 ηB ηP] ⊢ .forallE (.app (.app (swapM ηW) #0) #1) _ ≡
      .forallE (.app (.app (swapM ηW) #0) #1) _ : _ := .forallEDF hsw hd hd
  have h2 : E[(#t[tPM ηB ηP] : Ctx ζ 0 0 1)] ⊢ .forallE (tPM ηB ηP) _ ≡ .forallE (tPM ηB ηP) _ :
      _ := .forallEDF (tPM_typed hb hp) h3 h3
  exact Defeq.forallEDF (Γ := .nil) (tPM_typed hb hp) h2 h2

include hE hb hp hq hft hst hot hwt in
/-- The respect proof at the compatibility type of the lifted function. -/
theorem resp_typed (hht : (E.get ηH).constType = respTyM ηB ηP ηE ηF ηS ηO ηW) :
    E[.nil] ⊢ .const ηH Fin.elim0 :
      Quot.compatType ηE l1M (tPM ηB ηP) (swapM ηW) (mB ηB) (liftFM ηB ηP ηF ηS ηO) := by
  have h0 : E[(.nil : Ctx ζ 0 0 0)] ⊢ .const ηH Fin.elim0 : respTyM ηB ηP ηE ηF ηS ηO ηW :=
    const_typed hE ηH _ (by rw [hht]; qsx [respTyM])
  rw [← compatM_eq]
  exact .defeqDF (respTyM_defeq hE hb hp hq hft hst hot hwt) h0

/-! ### `orU`, `useTF`, `useFT` -/

theorem ΔLM_wf {ℓ : Nat} {u v : Level ℓ} (hq' : (E.get ηE).block = Eq.block) :
    E[ΔLM ηE ηQ u v] ⊢ ok := by
  have h1 : E[(#t[.sort u] : Ctx ζ ℓ 0 1)] ⊢ ok := .snoc .nil ⟨_, .sortDF⟩
  have h2 : E[(#t[.sort u, Quot.relType #0] : Ctx ζ ℓ 0 2)] ⊢ ok :=
    .snoc h1 ⟨_, Quot.relType_congr (var_of_get h1 ⟨0, by decide⟩ (by eqsimp))⟩
  have h3 : E[(#t[.sort u, Quot.relType #0, .sort v] : Ctx ζ ℓ 0 3)] ⊢ ok :=
    .snoc h2 ⟨_, .sortDF⟩
  have h3' : E[(#t[.sort u, Quot.relType #0, .sort v, #0] : Ctx ζ ℓ 0 4)] ⊢ ok :=
    .snoc h3 ⟨_, var_of_get h3 ⟨0, by decide⟩ (by eqsimp)⟩
  have hf3 : E[(#t[.sort u, Quot.relType #0, .sort v] : Ctx ζ ℓ 0 3)] ⊢
      .forallE #0 #2 : .sort (.imax u v) :=
    .forallEDF (var_of_get h3 ⟨0, by decide⟩ (by eqsimp)) (var_of_get h3' ⟨2, by decide⟩ (by eqsimp))
      (var_of_get h3' ⟨2, by decide⟩ (by eqsimp))
  have h4 : E[(#t[.sort u, Quot.relType #0, .sort v, .forallE #0 #2] : Ctx ζ ℓ 0 4)] ⊢ ok :=
    .snoc h3 ⟨_, hf3⟩
  have h5 : E[(#t[.sort u, Quot.relType #0, .sort v, .forallE #0 #2,
      Quot.compatType ηE v #0 #1 #2 #3] : Ctx ζ ℓ 0 5)] ⊢ ok :=
    .snoc h4 (Quot.compatType_isType hq' (var_of_get h4 ⟨0, by decide⟩ (by eqsimp))
      (var_of_get h4 ⟨1, by decide⟩ (by eqsimp)) (var_of_get h4 ⟨2, by decide⟩ (by eqsimp))
      (var_of_get h4 ⟨3, by decide⟩ (by eqsimp)))
  exact .snoc h5 ⟨_, .quotDF (var_of_get h5 ⟨0, by decide⟩ (by eqsimp))
    (var_of_get h5 ⟨1, by decide⟩ (by eqsimp))⟩

/-- `Quot.lift`'s η-term at the levels `u`, `v`. -/
theorem liftEta_typed {ℓ : Nat} {u v : Level ℓ} (hq' : (E.get ηE).block = Eq.block)
    (heq : (E.get ηQ).eqHead = ηE) :
    E[.nil] ⊢ (ΔLM ηE ηQ u v).lam (.quotLift ηQ u v #0 #1 #2 #3 #4 #5) :
      (ΔLM ηE ηQ u v).pi #2 := by
  have hΓ := ΔLM_wf (ηQ := ηQ) (u := u) (v := v) hq'
  have hh : E[ΔLM ηE ηQ u v] ⊢ #4 : Quot.compatType (E.get ηQ).eqHead v #0 #1 #2 #3 := by
    rw [heq]; exact var_of_get hΓ ⟨4, by decide⟩ (by eqsimp [ΔLM])
  exact Ctx.lam_congr (Γ := .nil) (Δ := ΔLM ηE ηQ u v) hΓ
    (.quotLiftDF (var_of_get hΓ ⟨0, by decide⟩ (by eqsimp [ΔLM]))
      (var_of_get hΓ ⟨1, by decide⟩ (by eqsimp [ΔLM])) (var_of_get hΓ ⟨2, by decide⟩ (by eqsimp [ΔLM]))
      (var_of_get hΓ ⟨3, by decide⟩ (by eqsimp [ΔLM])) hh
      (var_of_get hΓ ⟨5, by decide⟩ (by eqsimp [ΔLM])))

include hE hb hp hq hft hst hot hwt in
theorem orUValM_typed (heq : (E.get ηQ).eqHead = ηE)
    (hht : (E.get ηH).constType = respTyM ηB ηP ηE ηF ηS ηO ηW) :
    E[.nil] ⊢ orUValM ηB ηP ηE ηQ ηF ηS ηO ηW ηH : orUTyM ηB ηP ηQ ηW := by
  have h0 := liftEta_typed (ηQ := ηQ) (u := l1M) (v := l1M) hq heq
  qsx [ΔLM] at h0
  have h1 := app_typed' h0 (tPM_typed hb hp) (by qsx)
  qsx at h1
  have h2 := app_typed' h1 (swapC_typed hE hwt) (by qsx)
  qsx at h2
  have h3 := app_typed' h2 (mB_typed hb) (by qsx)
  qsx at h3
  have h4 := app_typed' h3 (liftFM_typed hE hb hp hft hst hot) (by qsx)
  qsx at h4
  have h5 := app_typed' h4 (resp_typed hE hb hp hq hft hst hot hwt hht) (by qsx [liftFM])
  exact typed_of_eq h5 (by qsx [orUTyM])

include hE hb hp hwt in
theorem useValM_typed (hut : (E.get ηU).constType = orUTyM ηB ηP ηQ ηW) {a b : Expr ζ 0 0}
    (ha : E[.nil] ⊢ a : mB ηB) (hb' : E[.nil] ⊢ b : mB ηB) :
    E[.nil] ⊢ useValM ηB ηP ηQ ηW ηU a b : mB ηB := by
  have h0 : E[(.nil : Ctx ζ 0 0 0)] ⊢ .const ηU Fin.elim0 : orUTyM ηB ηP ηQ ηW :=
    const_typed hE ηU _ (by rw [hut]; qsx [orUTyM])
  have hq : E[(.nil : Ctx ζ 0 0 0)] ⊢ .quotMk ηQ l1M (tPM ηB ηP) (swapM ηW) (pairM ηB ηP a b) :
      quotTM ηB ηP ηQ ηW :=
    .quotMkDF (tPM_typed hb hp) (typed_of_eq (swapC_typed hE hwt) (by qsx))
      (pairM_typed hb hp ha hb')
  exact typed_of_eq (app_typed h0 hq) (by qsx)

end Typed

end EraseProof.Test.NVQP
