import EraseProof.Test.NVQPDefs

/-!
# NV-QP: a Metalean proof of the respect statement

Metalean loads the theorem `orU._proof_1` as an opaque constant, whose entry asks for an
inhabitant of its statement `∀ p q, swapR p q → orB p.1 p.2 = orB q.1 q.2` (`respTyM`). The
inhabitant `respPrfM` follows the elaborated proof: it transports, along `Eq`'s recursor on
`h : swapR p q` (by δ, `q = (p.2, p.1)`), the commutativity of `orB` at `p.1 p.2` (`commM`, two
nested recursors of `B` into `Prop`, whose off-diagonal cases rest on `orB B.f B.t ≡ B.t` and
`orB B.t B.f ≡ B.t`, by weak-head reduction through `orB`, its matcher and `B.casesOn`) to the
pair `(p.2, p.1)`, whose projections reduce to `p.2` and `p.1`. For `Test/NVQPModel.lean`.
-/

open Lean Metalean

namespace EraseProof.Test.NVQP

open EraseProof.Test.NV1 (bSig bBlock mB mF mT indB_typed ctorB_typed typed_of_eq var_of_get
  app_typed const_typed fin0_eq lu casesOnTyM casesOnValM minsC recAllowedB)
open EraseProof.Test.NVS (ppSig mPP mPPmk defeq_rw beta_defeq app_typed' whredS_step)
open EraseProof.Test.NVP (eqA eqA_typed reflA reflA_typed l1M mB_typed mT_typed typed_of_eq')

/-- A family of definitional equalities closed under renaming holds in every context if it holds
in the empty one. -/
theorem defeq_wk {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {f f' g : (n : Nat) → Expr ζ ℓ n}
    (hf : ∀ {m k : Nat} (ρ : Ren m k), (f m).rename ρ = f k)
    (hf' : ∀ {m k : Nat} (ρ : Ren m k), (f' m).rename ρ = f' k)
    (hg : ∀ {m k : Nat} (ρ : Ren m k), (g m).rename ρ = g k) (h : E[.nil] ⊢ f 0 ≡ f' 0 : g 0)
    {n : Nat} {Γ : Ctx ζ ℓ 0 n} : E[Γ] ⊢ f n ≡ f' n : g n := by
  have h' := Defeq.wkClosed (Γ := Γ) h
  rwa [Expr.wkClosed_of_rename hf, Expr.wkClosed_of_rename hf',
    Expr.wkClosed_of_rename hg] at h'

section Red
variable {ζ : Sigs} {E : Env ζ} {ηB : Head ζ (.inductive bSig)} {ηC ηM : Head ζ (.const .def 1)}
  {ηO : Head ζ (.const .def 0)}
  (hE : EnvWF E) (hb : (E.get ηB).block = bBlock)
  (hcv : (E.get ηC).defValue = casesOnValM ηB) (hmv : (E.get ηM).defValue = omValM ηB ηC)
  (hot : (E.get ηO).constType = orBTyM ηB) (hov : (E.get ηO).defValue = orBValM ηB ηM)

include hE hb hcv hmv hot hov in
/-- `orB B.f B.t ≡ B.t`: δ of `orB`, β, δ of the matcher, β, δ of `B.casesOn`, β, ι, β. -/
theorem orB_ft0 : E[.nil] ⊢ orBM ηO (mF ηB) (mT ηB) ≡ mT ηB : mB ηB := by
  have h1 : E ⊢ orBM ηO (mF ηB) (mT ηB : Expr ζ 0 0) ⤳*
      .app (.app (Expr.wkClosed (n := 0)
        ((E.get ηO).defValue{(Fin.elim0 : Fin 0 → Level 0)} : Expr ζ 0 0)) (mF ηB)) (mT ηB) :=
    .single (.frame (K := .app _) (.frame (K := .app _) .delta))
  rw [hov] at h1; qsx [orBValM] at h1
  have h2 := whredS_step h1 (.frame (K := .app _) .beta); qsx at h2
  have h3 := whredS_step h2 .beta; qsx at h3
  have h4 := whredS_step h3 (.frame (K := .app _) (.frame (K := .app _) (.frame (K := .app _)
    (.frame (K := .app _) (.frame (K := .app _) .delta)))))
  rw [hmv] at h4; qsx [omValM] at h4
  have h5 := whredS_step h4 (.frame (K := .app _) (.frame (K := .app _) (.frame (K := .app _)
    (.frame (K := .app _) .beta)))); qsx at h5
  have h6 := whredS_step h5 (.frame (K := .app _) (.frame (K := .app _) (.frame (K := .app _)
    .beta))); qsx at h6
  have h7 := whredS_step h6 (.frame (K := .app _) (.frame (K := .app _) .beta)); qsx at h7
  have h8 := whredS_step h7 (.frame (K := .app _) .beta); qsx at h8
  have h9 := whredS_step h8 .beta; qsx at h9
  have h10 := whredS_step h9 (.frame (K := .app _) (.frame (K := .app _) (.frame (K := .app _)
    (.frame (K := .app _) .delta))))
  rw [hcv] at h10; qsx [casesOnValM, minsC] at h10
  have h11 := whredS_step h10 (.frame (K := .app _) (.frame (K := .app _) (.frame (K := .app _)
    .beta))); qsx at h11
  have h12 := whredS_step h11 (.frame (K := .app _) (.frame (K := .app _) .beta)); qsx at h12
  have h13 := whredS_step h12 (.frame (K := .app _) .beta); qsx at h13
  have h14 := whredS_step h13 .beta; qsx at h14
  have h15 := whredS_step h14 .iota; rw [hb] at h15; qsx at h15
  have h16 := whredS_step h15 .beta; qsx at h16
  exact defeq_rw (WHRedS.defeq hE .nil h16 (orBM_typed hE hot (mFT hb) (mTT hb))) rfl (by qsx) rfl

include hE hb hcv hmv hot hov in
/-- `orB B.t B.f ≡ B.t`, by the same steps. -/
theorem orB_tf0 : E[.nil] ⊢ orBM ηO (mT ηB) (mF ηB) ≡ mT ηB : mB ηB := by
  have h1 : E ⊢ orBM ηO (mT ηB) (mF ηB : Expr ζ 0 0) ⤳*
      .app (.app (Expr.wkClosed (n := 0)
        ((E.get ηO).defValue{(Fin.elim0 : Fin 0 → Level 0)} : Expr ζ 0 0)) (mT ηB)) (mF ηB) :=
    .single (.frame (K := .app _) (.frame (K := .app _) .delta))
  rw [hov] at h1; qsx [orBValM] at h1
  have h2 := whredS_step h1 (.frame (K := .app _) .beta); qsx at h2
  have h3 := whredS_step h2 .beta; qsx at h3
  have h4 := whredS_step h3 (.frame (K := .app _) (.frame (K := .app _) (.frame (K := .app _)
    (.frame (K := .app _) (.frame (K := .app _) .delta)))))
  rw [hmv] at h4; qsx [omValM] at h4
  have h5 := whredS_step h4 (.frame (K := .app _) (.frame (K := .app _) (.frame (K := .app _)
    (.frame (K := .app _) .beta)))); qsx at h5
  have h6 := whredS_step h5 (.frame (K := .app _) (.frame (K := .app _) (.frame (K := .app _)
    .beta))); qsx at h6
  have h7 := whredS_step h6 (.frame (K := .app _) (.frame (K := .app _) .beta)); qsx at h7
  have h8 := whredS_step h7 (.frame (K := .app _) .beta); qsx at h8
  have h9 := whredS_step h8 .beta; qsx at h9
  have h10 := whredS_step h9 (.frame (K := .app _) (.frame (K := .app _) (.frame (K := .app _)
    (.frame (K := .app _) .delta))))
  rw [hcv] at h10; qsx [casesOnValM, minsC] at h10
  have h11 := whredS_step h10 (.frame (K := .app _) (.frame (K := .app _) (.frame (K := .app _)
    .beta))); qsx at h11
  have h12 := whredS_step h11 (.frame (K := .app _) (.frame (K := .app _) .beta)); qsx at h12
  have h13 := whredS_step h12 (.frame (K := .app _) .beta); qsx at h13
  have h14 := whredS_step h13 .beta; qsx at h14
  have h15 := whredS_step h14 .iota; rw [hb] at h15; qsx at h15
  have h16 := whredS_step h15 .beta; qsx at h16
  exact defeq_rw (WHRedS.defeq hE .nil h16 (orBM_typed hE hot (mTT hb) (mFT hb))) rfl (by qsx) rfl

include hE hb hcv hmv hot hov in
theorem orB_ft {n : Nat} {Γ : Ctx ζ 0 0 n} : E[Γ] ⊢ orBM ηO (mF ηB) (mT ηB) ≡ mT ηB : mB ηB :=
  defeq_wk (f := fun _ => orBM ηO (mF ηB) (mT ηB)) (f' := fun _ => mT ηB) (g := fun _ => mB ηB)
    (fun ρ => by qsx) (fun ρ => by qsx) (fun ρ => by qsx) (orB_ft0 hE hb hcv hmv hot hov)

include hE hb hcv hmv hot hov in
theorem orB_tf {n : Nat} {Γ : Ctx ζ 0 0 n} : E[Γ] ⊢ orBM ηO (mT ηB) (mF ηB) ≡ mT ηB : mB ηB :=
  defeq_wk (f := fun _ => orBM ηO (mT ηB) (mF ηB)) (f' := fun _ => mT ηB) (g := fun _ => mB ηB)
    (fun ρ => by qsx) (fun ρ => by qsx) (fun ρ => by qsx) (orB_tf0 hE hb hcv hmv hot hov)

/-! ## `orB` is commutative -/

/-- `orB a b = orB b a` -/
abbrev commEq (ηB : Head ζ (.inductive bSig)) (ηE : Head ζ (.inductive Eq.sig))
    (ηO : Head ζ (.const .def 0)) {n : Nat} (a b : Expr ζ 0 n) : Expr ζ 0 n :=
  eqA ηE l1M (mB ηB) (orBM ηO a b) (orBM ηO b a)

/-- `∀ a b : B, orB a b = orB b a` -/
def commTyM (ηB : Head ζ (.inductive bSig)) (ηE : Head ζ (.inductive Eq.sig))
    (ηO : Head ζ (.const .def 0)) : Expr ζ 0 0 :=
  .forallE (mB ηB) (.forallE (mB ηB) (commEq ηB ηE ηO #0 #1))

/-- The inner motive `fun b' => orB c b' = orB b' c` under `a b`. -/
def comm2 (ηB : Head ζ (.inductive bSig)) (ηE : Head ζ (.inductive Eq.sig))
    (ηO : Head ζ (.const .def 0)) (c : Expr ζ 0 3) : Expr ζ 0 2 :=
  .lam (mB ηB) (commEq ηB ηE ηO c #2)

/-- The inner minors on `B.f`: `rfl`, and `rfl : B.t = B.t` for `orB B.f B.t = orB B.t B.f`. -/
def minsF (ηB : Head ζ (.inductive bSig)) (ηE : Head ζ (.inductive Eq.sig))
    (ηO : Head ζ (.const .def 0)) : (t : Fin 1) → Fin (bSig.nctors t) → Expr ζ 0 2 :=
  fun _ k => if k.val = 0 then reflA ηE l1M (mB ηB) (orBM ηO (mF ηB) (mF ηB))
    else reflA ηE l1M (mB ηB) (mT ηB)

/-- The inner minors on `B.t`. -/
def minsT (ηB : Head ζ (.inductive bSig)) (ηE : Head ζ (.inductive Eq.sig))
    (ηO : Head ζ (.const .def 0)) : (t : Fin 1) → Fin (bSig.nctors t) → Expr ζ 0 2 :=
  fun _ k => if k.val = 0 then reflA ηE l1M (mB ηB) (mT ηB)
    else reflA ηE l1M (mB ηB) (orBM ηO (mT ηB) (mT ηB))

/-- The outer motive `fun a' => orB a' b = orB b a'` under `a b`. -/
def commA (ηB : Head ζ (.inductive bSig)) (ηE : Head ζ (.inductive Eq.sig))
    (ηO : Head ζ (.const .def 0)) : Expr ζ 0 2 :=
  .lam (mB ηB) (commEq ηB ηE ηO #2 #1)

/-- The outer minors: the case analysis on `b`. -/
def minsA (ηB : Head ζ (.inductive bSig)) (ηE : Head ζ (.inductive Eq.sig))
    (ηO : Head ζ (.const .def 0)) : (t : Fin 1) → Fin (bSig.nctors t) → Expr ζ 0 2 :=
  fun _ k => if k.val = 0 then
      .recr ηB 0 Fin.elim0 .zero Fin.elim0 (fun _ => comm2 ηB ηE ηO (mF ηB)) (minsF ηB ηE ηO)
        Fin.elim0 #1
    else .recr ηB 0 Fin.elim0 .zero Fin.elim0 (fun _ => comm2 ηB ηE ηO (mT ηB)) (minsT ηB ηE ηO)
        Fin.elim0 #1

/-- `fun a b => B.rec (B.rec rfl rfl b) (B.rec rfl rfl b) a`: `orB` is commutative. -/
def commM (ηB : Head ζ (.inductive bSig)) (ηE : Head ζ (.inductive Eq.sig))
    (ηO : Head ζ (.const .def 0)) : Expr ζ 0 0 :=
  .lam (mB ηB) (.lam (mB ηB) (.recr ηB 0 Fin.elim0 .zero Fin.elim0 (fun _ => commA ηB ηE ηO)
    (minsA ηB ηE ηO) Fin.elim0 #0))

include hb in
/-- β on a motive `fun x : B => body` into `Prop`. -/
theorem lamB_beta {n : Nat} {Γ : Ctx ζ 0 0 n} {body : Expr ζ 0 (n + 1)} {a : Expr ζ 0 n}
    (hbody : E[Γ.snoc (mB ηB)] ⊢ body : .prop) (ha : E[Γ] ⊢ a : mB ηB) :
    E[Γ] ⊢ .app (.lam (mB ηB) body) a ≡ body.inst a : .prop :=
  defeq_rw (beta_defeq (mB_typed hb) .sortDF hbody ha) rfl rfl (by qsx)

include hb in
/-- A recursor of `B` into `Prop`. -/
theorem recB_typed {n : Nat} {Γ : Ctx ζ 0 0 n} {M maj : Expr ζ 0 n}
    {mins : (t : Fin 1) → Fin (bSig.nctors t) → Expr ζ 0 n}
    (hM : E[Γ] ⊢ M : .forallE (mB ηB) .prop)
    (hmins : ∀ k : Fin 2, E[Γ] ⊢ mins 0 k : .app M (.ctor ηB 0 k Fin.elim0 Fin.elim0 Fin.elim0
      Fin.elim0))
    (hmaj : E[Γ] ⊢ maj : mB ηB) :
    E[Γ] ⊢ .recr ηB 0 Fin.elim0 .zero Fin.elim0 (fun _ => M) mins Fin.elim0 maj : .app M maj := by
  have h := Defeq.recrDF (E := E) (Γ := Γ) (η := ηB) (s := 0) (ls := Fin.elim0) (l := .zero)
    (ps₁ := Fin.elim0) (ps₂ := Fin.elim0) (ms₁ := fun _ => M) (ms₂ := fun _ => M)
    (mins₁ := mins) (mins₂ := mins) (is₁ := Fin.elim0) (is₂ := Fin.elim0)
    (maj₁ := maj) (maj₂ := maj) (recAllowedB hb) (fun p => Fin.elim0 p) ?_ ?_
    (fun i => Fin.elim0 i) hmaj ?_
  · exact typed_of_eq h (by qsx [Inductive.motiveResult])
  · intro s; fin_cases s; rw [hb]; exact typed_of_eq hM (by qsx [Inductive.motiveType,
      Inductive.motiveTele, Inductive.indexTele])
  · intro s c; fin_cases s; fin_cases c <;> rw [hb]
    · exact typed_of_eq (hmins 0) (by qsx [Inductive.caseFnType, Inductive.caseTele,
        Inductive.caseType, Inductive.motiveResult, Ctor.fieldTele, Ctor.ordinaryFieldTele,
        Ctor.ordinaryFieldTeleAux, Ctor.recursiveFieldTeleAux, Ctor.ihTele, CtorSig.caseParams,
        CtorSig.caseOrdinary, CtorSig.caseRecursive])
    · exact typed_of_eq (hmins 1) (by qsx [Inductive.caseFnType, Inductive.caseTele,
        Inductive.caseType, Inductive.motiveResult, Ctor.fieldTele, Ctor.ordinaryFieldTele,
        Ctor.ordinaryFieldTeleAux, Ctor.recursiveFieldTeleAux, Ctor.ihTele, CtorSig.caseParams,
        CtorSig.caseOrdinary, CtorSig.caseRecursive])
  · exact typed_of_eq (app_typed hM hmaj) (by qsx [Inductive.motiveResult])

include hb in
theorem lamB_beta' {n : Nat} {Γ : Ctx ζ 0 0 n} {body : Expr ζ 0 (n + 1)} {a r : Expr ζ 0 n}
    (hbody : E[Γ.snoc (mB ηB)] ⊢ body : .prop) (ha : E[Γ] ⊢ a : mB ηB) (hr : body.inst a = r) :
    E[Γ] ⊢ .app (.lam (mB ηB) body) a ≡ r : .prop :=
  hr ▸ lamB_beta hb hbody ha

variable {ηE : Head ζ (.inductive Eq.sig)} (hq : (E.get ηE).block = Eq.block)

include hE hb hq hot in
theorem commEq_typed {n : Nat} {Γ : Ctx ζ 0 0 n} {a b : Expr ζ 0 n} (ha : E[Γ] ⊢ a : mB ηB)
    (hb' : E[Γ] ⊢ b : mB ηB) : E[Γ] ⊢ commEq ηB ηE ηO a b : .prop :=
  eqA_typed hq (mB_typed hb) (orBM_typed hE hot ha hb') (orBM_typed hE hot hb' ha)

include hE hb hq hcv hmv hot hov in
theorem commM_typed : E[.nil] ⊢ commM ηB ηE ηO : commTyM ηB ηE ηO := by
  have hBt : ∀ {n : Nat} {Γ : Ctx ζ 0 0 n}, E[Γ] ⊢ mB ηB : .sort l1M := fun {_ _} => mB_typed hb
  have h1 : E[(#t[mB ηB] : Ctx ζ 0 0 1)] ⊢ ok := .snoc .nil ⟨_, hBt⟩
  have hΓ : E[(#t[mB ηB, mB ηB] : Ctx ζ 0 0 2)] ⊢ ok := .snoc h1 ⟨_, hBt⟩
  have h3 : E[(#t[mB ηB, mB ηB] : Ctx ζ 0 0 2).snoc (mB ηB)] ⊢ ok := .snoc hΓ ⟨_, hBt⟩
  have ha : E[(#t[mB ηB, mB ηB] : Ctx ζ 0 0 2)] ⊢ #0 : mB ηB := var_of_get hΓ ⟨0, by decide⟩ (by qsx)
  have hbv : E[(#t[mB ηB, mB ηB] : Ctx ζ 0 0 2)] ⊢ #1 : mB ηB :=
    var_of_get hΓ ⟨1, by decide⟩ (by qsx)
  have hv2 : E[(#t[mB ηB, mB ηB] : Ctx ζ 0 0 2).snoc (mB ηB)] ⊢ #2 : mB ηB :=
    var_of_get h3 ⟨2, by decide⟩ (by qsx)
  have hv1 : E[(#t[mB ηB, mB ηB] : Ctx ζ 0 0 2).snoc (mB ηB)] ⊢ #1 : mB ηB :=
    var_of_get h3 ⟨1, by decide⟩ (by qsx)
  -- the inner case analyses
  have hbF := commEq_typed hE hb hot hq (ηE := ηE) (mFT hb) hv2
  have hbT := commEq_typed hE hb hot hq (ηE := ηE) (mTT hb) hv2
  have hMF : E[(#t[mB ηB, mB ηB] : Ctx ζ 0 0 2)] ⊢ comm2 ηB ηE ηO (mF ηB) :
      .forallE (mB ηB) .prop := .lamDF hBt .sortDF .sortDF hbF hbF
  have hMT : E[(#t[mB ηB, mB ηB] : Ctx ζ 0 0 2)] ⊢ comm2 ηB ηE ηO (mT ηB) :
      .forallE (mB ηB) .prop := .lamDF hBt .sortDF .sortDF hbT hbT
  have hdFT : E[(#t[mB ηB, mB ηB] : Ctx ζ 0 0 2)] ⊢ eqA ηE l1M (mB ηB) (mT ηB) (mT ηB) ≡
      commEq ηB ηE ηO (mF ηB) (mT ηB) : .prop :=
    eqA_defeq hq hBt (orB_ft hE hb hcv hmv hot hov).symm (orB_tf hE hb hcv hmv hot hov).symm
  have hdTF : E[(#t[mB ηB, mB ηB] : Ctx ζ 0 0 2)] ⊢ eqA ηE l1M (mB ηB) (mT ηB) (mT ηB) ≡
      commEq ηB ηE ηO (mT ηB) (mF ηB) : .prop :=
    eqA_defeq hq hBt (orB_tf hE hb hcv hmv hot hov).symm (orB_ft hE hb hcv hmv hot hov).symm
  have hinF := recB_typed hb (maj := #1) (mins := minsF ηB ηE ηO) hMF (fun k => by
    fin_cases k
    · exact .defeqDF (lamB_beta' hb hbF (mFT hb)
        (r := commEq ηB ηE ηO (mF ηB) (mF ηB)) (by qsx)).symm
        (reflA_typed hq hBt (orBM_typed hE hot (mFT hb) (mFT hb)))
    · exact .defeqDF (hdFT.trans (lamB_beta' hb hbF (mTT hb) (by qsx)).symm)
        (reflA_typed hq hBt (mTT hb))) hbv
  have hinT := recB_typed hb (maj := #1) (mins := minsT ηB ηE ηO) hMT (fun k => by
    fin_cases k
    · exact .defeqDF (hdTF.trans (lamB_beta' hb hbT (mFT hb) (by qsx)).symm)
        (reflA_typed hq hBt (mTT hb))
    · exact .defeqDF (lamB_beta' hb hbT (mTT hb)
        (r := commEq ηB ηE ηO (mT ηB) (mT ηB)) (by qsx)).symm
        (reflA_typed hq hBt (orBM_typed hE hot (mTT hb) (mTT hb)))) hbv
  -- the outer case analysis
  have hbA := commEq_typed hE hb hot hq (ηE := ηE) hv2 hv1
  have hMA : E[(#t[mB ηB, mB ηB] : Ctx ζ 0 0 2)] ⊢ commA ηB ηE ηO : .forallE (mB ηB) .prop :=
    .lamDF hBt .sortDF .sortDF hbA hbA
  have hout := recB_typed hb (maj := #0) (mins := minsA ηB ηE ηO) hMA (fun k => by
    fin_cases k
    · exact .defeqDF ((lamB_beta' hb hbF hbv (r := commEq ηB ηE ηO (mF ηB) #1) (by qsx)).trans
        (lamB_beta' hb hbA (mFT hb) (by qsx)).symm) hinF
    · exact .defeqDF ((lamB_beta' hb hbT hbv (r := commEq ηB ηE ηO (mT ηB) #1) (by qsx)).trans
        (lamB_beta' hb hbA (mTT hb) (by qsx)).symm) hinT) ha
  have hres := Defeq.defeqDF (lamB_beta' hb hbA ha (r := commEq ηB ηE ηO #0 #1) (by qsx)) hout
  exact typed_of_eq (Ctx.lam_congr (Γ := .nil) (Δ := #t[mB ηB, mB ηB]) hΓ hres) (by qsx [commTyM])

end Red

/-! ## The respect statement -/

/-- Compute the parameter, motive, minor and index types of `Eq`'s block. -/
syntax (name := _eqty) "eqty" : tactic
macro_rules
  | `(tactic| eqty) => `(tactic| first
    | (eqsimp; done)
    | (qsx [Eq.block, Eq.ctorDecl, Inductive.paramType, Inductive.indexType, Inductive.motiveType,
        Inductive.motiveTele, Inductive.indexTele, Inductive.caseFnType, Inductive.caseTele,
        Inductive.caseType, Inductive.motiveResult, Ctx.proj, Ctor.targetIndex, Ctor.fieldTele,
        CtorSig.caseParams, reflA, Ctx.substN, Subst.liftN, Expr.wkN]; done))

/-- A context extended by a type is well formed. -/
theorem ctx_snoc {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} {t : Expr ζ ℓ n} {l : Level ℓ}
    (h : E[Γ] ⊢ ok) (ht : E[Γ] ⊢ t : .sort l) : E[Γ.snoc t] ⊢ ok := .snoc h ⟨_, ht⟩

section Prf
variable {ζ : Sigs} {E : Env ζ} {ηB : Head ζ (.inductive bSig)} {ηP : Head ζ (.inductive ppSig)}
  {ηE : Head ζ (.inductive Eq.sig)} {ηC ηM : Head ζ (.const .def 1)}
  {ηF ηS : Head ζ (.const .def 2)} {ηO ηW : Head ζ (.const .def 0)}
  (hE : EnvWF E) (hb : (E.get ηB).block = bBlock) (hp : (E.get ηP).block = prBlock)
  (hq : (E.get ηE).block = Eq.block)
  (hcv : (E.get ηC).defValue = casesOnValM ηB) (hmv : (E.get ηM).defValue = omValM ηB ηC)
  (hot : (E.get ηO).constType = orBTyM ηB) (hov : (E.get ηO).defValue = orBValM ηB ηM)
  (hft : (E.get ηF).constType = prFstTyM ηP) (hfv : (E.get ηF).defValue = prFstValM ηP)
  (hst : (E.get ηS).constType = prSndTyM ηP) (hsv : (E.get ηS).defValue = prSndValM ηP)
  (hwt : (E.get ηW).constType = swapTyM ηB ηP)
  (hwv : (E.get ηW).defValue = swapValM ηB ηP ηE ηF ηS)

/-- `p.2` and `p.1` under `p q h`. -/
abbrev sp (ηB : Head ζ (.inductive bSig)) (ηS : Head ζ (.const .def 2)) : Expr ζ 0 3 :=
  sndM ηB ηS #0
abbrev fp (ηB : Head ζ (.inductive bSig)) (ηF : Head ζ (.const .def 2)) : Expr ζ 0 3 :=
  fstM ηB ηF #0

include hE hb hp hft hfv hst hwt in
/-- `(p.2, p.1).1 ≡ p.2`: δ of `Prod.fst`, three β, ι, two β. -/
theorem fst_pair :
    E[ΓP3 ηB ηP ηW] ⊢ fstM ηB ηF (pairM ηB ηP (sp ηB ηS) (fp ηB ηF)) ≡ sp ηB ηS : mB ηB := by
  have hΓ := ΓP3_wf hE hb hp hwt
  have hp0 : E[ΓP3 ηB ηP ηW] ⊢ #0 : tPM ηB ηP := var_of_get hΓ ⟨0, by decide⟩ (by qsx [ΓP3, ΓP2])
  have h1 : E ⊢ fstM ηB ηF (pairM ηB ηP (sp ηB ηS) (fp ηB ηF)) ⤳*
      .app (.app (.app (Expr.wkClosed (n := 3)
        ((E.get ηF).defValue{(![.zero, .zero] : Fin 2 → Level 0)} : Expr ζ 0 0)) (mB ηB)) (mB ηB))
        (pairM ηB ηP (sp ηB ηS) (fp ηB ηF)) :=
    .single (.frame (K := .app _) (.frame (K := .app _) (.frame (K := .app _) .delta)))
  rw [hfv] at h1; qsx [prFstValM, prFstM] at h1
  have h2 := whredS_step h1 (.frame (K := .app _) (.frame (K := .app _) .beta)); qsx at h2
  have h3 := whredS_step h2 (.frame (K := .app _) .beta); qsx at h3
  have h4 := whredS_step h3 .beta; qsx at h4
  have h5 := whredS_step h4 .iota; rw [hp] at h5; qsx at h5
  have h6 := whredS_step h5 (.frame (K := .app _) .beta); qsx at h6
  have h7 := whredS_step h6 .beta; qsx at h7
  exact defeq_rw (WHRedS.defeq hE hΓ h7 (fstM_typed hE hb hft (pairM_typed hb hp
    (sndM_typed hE hb hst hp0) (fstM_typed hE hb hft hp0)))) rfl (by qsx) rfl

include hE hb hp hft hst hsv hwt in
/-- `(p.2, p.1).2 ≡ p.1`, by the same steps through `Prod.snd`. -/
theorem snd_pair :
    E[ΓP3 ηB ηP ηW] ⊢ sndM ηB ηS (pairM ηB ηP (sp ηB ηS) (fp ηB ηF)) ≡ fp ηB ηF : mB ηB := by
  have hΓ := ΓP3_wf hE hb hp hwt
  have hp0 : E[ΓP3 ηB ηP ηW] ⊢ #0 : tPM ηB ηP := var_of_get hΓ ⟨0, by decide⟩ (by qsx [ΓP3, ΓP2])
  have h1 : E ⊢ sndM ηB ηS (pairM ηB ηP (sp ηB ηS) (fp ηB ηF)) ⤳*
      .app (.app (.app (Expr.wkClosed (n := 3)
        ((E.get ηS).defValue{(![.zero, .zero] : Fin 2 → Level 0)} : Expr ζ 0 0)) (mB ηB)) (mB ηB))
        (pairM ηB ηP (sp ηB ηS) (fp ηB ηF)) :=
    .single (.frame (K := .app _) (.frame (K := .app _) (.frame (K := .app _) .delta)))
  rw [hsv] at h1; qsx [prSndValM, prSndM] at h1
  have h2 := whredS_step h1 (.frame (K := .app _) (.frame (K := .app _) .beta)); qsx at h2
  have h3 := whredS_step h2 (.frame (K := .app _) .beta); qsx at h3
  have h4 := whredS_step h3 .beta; qsx at h4
  have h5 := whredS_step h4 .iota; rw [hp] at h5; qsx at h5
  have h6 := whredS_step h5 (.frame (K := .app _) .beta); qsx at h6
  have h7 := whredS_step h6 .beta; qsx at h7
  exact defeq_rw (WHRedS.defeq hE hΓ h7 (sndM_typed hE hb hst (pairM_typed hb hp
    (sndM_typed hE hb hst hp0) (fstM_typed hE hb hft hp0)))) rfl (by qsx) rfl

include hE hb hp hwt hwv in
/-- `swapR p q ≡ q = (p.2, p.1)`: δ of `swapR`, two β. -/
theorem swap_red :
    E[ΓP3 ηB ηP ηW] ⊢ .app (.app (swapM ηW) #0) #1 ≡
      eqA ηE l1M (tPM ηB ηP) #1 (pairM ηB ηP (sp ηB ηS) (fp ηB ηF)) : .prop := by
  have hΓ := ΓP3_wf hE hb hp hwt
  have hp0 : E[ΓP3 ηB ηP ηW] ⊢ #0 : tPM ηB ηP := var_of_get hΓ ⟨0, by decide⟩ (by qsx [ΓP3, ΓP2])
  have hp1 : E[ΓP3 ηB ηP ηW] ⊢ #1 : tPM ηB ηP := var_of_get hΓ ⟨1, by decide⟩ (by qsx [ΓP3, ΓP2])
  have h1 : E ⊢ (.app (.app (swapM ηW) #0) #1 : Expr ζ 0 3) ⤳*
      .app (.app (Expr.wkClosed (n := 3)
        ((E.get ηW).defValue{(Fin.elim0 : Fin 0 → Level 0)} : Expr ζ 0 0)) #0) #1 :=
    .single (.frame (K := .app _) (.frame (K := .app _) .delta))
  rw [hwv] at h1; qsx [swapValM] at h1
  have h2 := whredS_step h1 (.frame (K := .app _) .beta); qsx at h2
  have h3 := whredS_step h2 .beta; qsx at h3
  exact defeq_rw (WHRedS.defeq hE hΓ h3 (swapApp_typed hE hwt hp0 hp1)) rfl (by qsx) rfl

include hE hot in
/-- `orB` congruence. -/
theorem orBM_defeq {n : Nat} {Γ : Ctx ζ 0 0 n} {a₁ a₂ b₁ b₂ : Expr ζ 0 n}
    (hbB : ∀ {k : Nat} {Δ : Ctx ζ 0 0 k}, E[Δ] ⊢ mB ηB : .sort l1M)
    (ha : E[Γ] ⊢ a₁ ≡ a₂ : mB ηB) (hb' : E[Γ] ⊢ b₁ ≡ b₂ : mB ηB) :
    E[Γ] ⊢ orBM ηO a₁ b₁ ≡ orBM ηO a₂ b₂ : mB ηB := by
  have hBB : ∀ {k : Nat} {Δ : Ctx ζ 0 0 k}, E[Δ] ⊢ .forallE (mB ηB) (mB ηB) : .sort (.imax l1M l1M) :=
    fun {_ _} => .forallEDF hbB hbB hbB
  have h1 : E[Γ] ⊢ .app (.const ηO Fin.elim0) a₁ ≡ .app (.const ηO Fin.elim0) a₂ :
      .forallE (mB ηB) (mB ηB) :=
    defeq_rw (.appDF hbB hBB (orBC_typed hE hot) ha
      (defeq_rw (hBB (Δ := Γ)) (by qsx) (by qsx) rfl)) rfl rfl (by qsx)
  exact defeq_rw (.appDF hbB hbB h1 hb' (defeq_rw (hbB (Δ := Γ)) (by qsx) (by qsx) rfl)) rfl rfl
    (by qsx)

/-- `orB p.1 p.2 = orB x.1 x.2` -/
def respP (ηB : Head ζ (.inductive bSig)) (ηE : Head ζ (.inductive Eq.sig))
    (ηF ηS : Head ζ (.const .def 2)) (ηO : Head ζ (.const .def 0)) {n : Nat}
    (p x : Expr ζ 0 n) : Expr ζ 0 n :=
  eqA ηE l1M (mB ηB) (orBM ηO (fstM ηB ηF p) (sndM ηB ηS p)) (orBM ηO (fstM ηB ηF x) (sndM ηB ηS x))

/-- The motive `fun b _ => P b → P q` of the transport along `h`, under `p q h`. -/
def moE (ηB : Head ζ (.inductive bSig)) (ηP : Head ζ (.inductive ppSig))
    (ηE : Head ζ (.inductive Eq.sig)) (ηF ηS : Head ζ (.const .def 2))
    (ηO : Head ζ (.const .def 0)) : Expr ζ 0 3 :=
  .lam (tPM ηB ηP) (.lam (eqA ηE l1M (tPM ηB ηP) #1 #3)
    (.forallE (respP ηB ηE ηF ηS ηO #0 #3) (respP ηB ηE ηF ηS ηO #0 #1)))

/-- `Eq.rec (motive := fun b _ => P b → P q) id h : P (p.2, p.1) → P q`, under `p q h`. -/
def eqRecM (ηB : Head ζ (.inductive bSig)) (ηP : Head ζ (.inductive ppSig))
    (ηE : Head ζ (.inductive Eq.sig)) (ηF ηS : Head ζ (.const .def 2))
    (ηO : Head ζ (.const .def 0)) : Expr ζ 0 3 :=
  .recr ηE 0 ![l1M] .zero ![tPM ηB ηP, #1] (fun _ => moE ηB ηP ηE ηF ηS ηO)
    (fun _ _ => .lam (respP ηB ηE ηF ηS ηO #0 #1) #3) ![pairM ηB ηP (sp ηB ηS) (fp ηB ηF)] #2

/-- `fun p q h => Eq.rec id h (orB_comm p.1 p.2)`: the inhabitant of `orU._proof_1`'s
statement. -/
def respPrfM (ηB : Head ζ (.inductive bSig)) (ηP : Head ζ (.inductive ppSig))
    (ηE : Head ζ (.inductive Eq.sig)) (ηF ηS : Head ζ (.const .def 2))
    (ηO ηW : Head ζ (.const .def 0)) : Expr ζ 0 0 :=
  (ΓP3 ηB ηP ηW).lam (.app (eqRecM ηB ηP ηE ηF ηS ηO)
    (.app (.app ((commM ηB ηE ηO).wkClosed) (fp ηB ηF)) (sp ηB ηS)))

include hE hb hq hft hst hot in
theorem respP_typed {n : Nat} {Γ : Ctx ζ 0 0 n} {p x : Expr ζ 0 n}
    (hp' : E[Γ] ⊢ p : tPM ηB ηP) (hx : E[Γ] ⊢ x : tPM ηB ηP) :
    E[Γ] ⊢ respP ηB ηE ηF ηS ηO p x : .prop :=
  eqA_typed hq (mB_typed hb) (orBfs_typed hE hb hft hst hot hp') (orBfs_typed hE hb hft hst hot hx)

include hE hb hp hq hcv hmv hot hov hft hfv hst hsv hwt hwv in
/-- The inhabitant of `orU._proof_1`'s statement. -/
theorem respPrfM_typed :
    E[.nil] ⊢ respPrfM ηB ηP ηE ηF ηS ηO ηW : respTyM ηB ηP ηE ηF ηS ηO ηW := by
  have hP : ∀ {k : Nat} {Δ : Ctx ζ 0 0 k}, E[Δ] ⊢ tPM ηB ηP : .sort l1M := fun {_ _} =>
    tPM_typed hb hp
  have hΓ := ΓP3_wf hE hb hp hwt
  have hp0 : E[ΓP3 ηB ηP ηW] ⊢ #0 : tPM ηB ηP := var_of_get hΓ ⟨0, by decide⟩ (by qsx [ΓP3, ΓP2])
  have hp1 : E[ΓP3 ηB ηP ηW] ⊢ #1 : tPM ηB ηP := var_of_get hΓ ⟨1, by decide⟩ (by qsx [ΓP3, ΓP2])
  have hh : E[ΓP3 ηB ηP ηW] ⊢ #2 : .app (.app (swapM ηW) #0) #1 :=
    var_of_get hΓ ⟨2, by decide⟩ (by qsx [ΓP3, ΓP2])
  have hmaj := Defeq.defeqDF (swap_red hE hb hp hwt hwv (ηE := ηE) (ηF := ηF) (ηS := ηS)) hh
  have hpair : E[ΓP3 ηB ηP ηW] ⊢ pairM ηB ηP (sp ηB ηS) (fp ηB ηF) : tPM ηB ηP :=
    pairM_typed hb hp (sndM_typed hE hb hst hp0) (fstM_typed hE hb hft hp0)
  -- the motive
  have h4 : E[(ΓP3 ηB ηP ηW).snoc (tPM ηB ηP)] ⊢ ok := .snoc hΓ ⟨_, hP⟩
  have he4 : E[(ΓP3 ηB ηP ηW).snoc (tPM ηB ηP)] ⊢ eqA ηE l1M (tPM ηB ηP) #1 #3 : .prop :=
    eqA_typed hq hP (var_of_get h4 ⟨1, by decide⟩ (by qsx [ΓP3, ΓP2]))
      (var_of_get h4 ⟨3, by decide⟩ (by qsx [ΓP3, ΓP2]))
  have h5 : E[((ΓP3 ηB ηP ηW).snoc (tPM ηB ηP)).snoc (eqA ηE l1M (tPM ηB ηP) #1 #3)] ⊢ ok :=
    .snoc h4 ⟨_, he4⟩
  have hP5 := respP_typed hE hb hq hot hft hst (ηE := ηE)
    (var_of_get h5 ⟨0, by decide⟩ (T := tPM ηB ηP) (by qsx [ΓP3, ΓP2]))
    (var_of_get h5 ⟨3, by decide⟩ (T := tPM ηB ηP) (by qsx [ΓP3, ΓP2]))
  have h6 := ctx_snoc h5 hP5
  have hP6 := respP_typed hE hb hq hot hft hst (ηE := ηE)
    (var_of_get h6 ⟨0, by decide⟩ (T := tPM ηB ηP) (by qsx [ΓP3, ΓP2]))
    (var_of_get h6 ⟨1, by decide⟩ (T := tPM ηB ηP) (by qsx [ΓP3, ΓP2]))
  have hfa5 := typed_of_eq' (Defeq.forallEDF hP5 hP6 hP6) (l' := .zero)
    (Level.ext fun ν => by simp [Nat.imax])
  have hlam4 : E[(ΓP3 ηB ηP ηW).snoc (tPM ηB ηP)] ⊢ .lam (eqA ηE l1M (tPM ηB ηP) #1 #3)
      (.forallE (respP ηB ηE ηF ηS ηO #0 #3) (respP ηB ηE ηF ηS ηO #0 #1)) :
      .forallE (eqA ηE l1M (tPM ηB ηP) #1 #3) .prop := .lamDF he4 .sortDF .sortDF hfa5 hfa5
  have hMty4 : E[(ΓP3 ηB ηP ηW).snoc (tPM ηB ηP)] ⊢
      .forallE (eqA ηE l1M (tPM ηB ηP) #1 #3) .prop : _ := .forallEDF he4 .sortDF .sortDF
  have hMo : E[ΓP3 ηB ηP ηW] ⊢ moE ηB ηP ηE ηF ηS ηO :
      .forallE (tPM ηB ηP) (.forallE (eqA ηE l1M (tPM ηB ηP) #1 #3) .prop) :=
    .lamDF hP hMty4 hMty4 hlam4 hlam4
  -- the motive at `(p.2, p.1)` and `h`
  have hβa : E[ΓP3 ηB ηP ηW] ⊢ .app (moE ηB ηP ηE ηF ηS ηO) (pairM ηB ηP (sp ηB ηS) (fp ηB ηF)) ≡
      .lam (eqA ηE l1M (tPM ηB ηP) #1 (pairM ηB ηP (sp ηB ηS) (fp ηB ηF)))
        (.forallE (respP ηB ηE ηF ηS ηO #0 (pairM ηB ηP (sndM ηB ηS #0) (fstM ηB ηF #0)))
          (respP ηB ηE ηF ηS ηO #0 #1)) :
      .forallE (eqA ηE l1M (tPM ηB ηP) #1 (pairM ηB ηP (sp ηB ηS) (fp ηB ηF))) .prop :=
    defeq_rw (beta_defeq hP hMty4 hlam4 hpair) rfl (by qsx [respP]) (by qsx)
  have heqa := eqA_typed hq hP hp1 hpair
  have h4' := ctx_snoc hΓ heqa
  have hq0' : E[(ΓP3 ηB ηP ηW).snoc (eqA ηE l1M (tPM ηB ηP) #1
      (pairM ηB ηP (sp ηB ηS) (fp ηB ηF)))] ⊢ #0 : tPM ηB ηP :=
    var_of_get h4' ⟨0, by decide⟩ (by qsx [ΓP3, ΓP2])
  have hPa := respP_typed hE hb hq hot hft hst (ηE := ηE) hq0'
    (pairM_typed hb hp (sndM_typed hE hb hst hq0') (fstM_typed hE hb hft hq0'))
  have h5' := ctx_snoc h4' hPa
  have hPq := respP_typed hE hb hq hot hft hst (ηE := ηE)
    (var_of_get h5' ⟨0, by decide⟩ (T := tPM ηB ηP) (by qsx [ΓP3, ΓP2]))
    (var_of_get h5' ⟨1, by decide⟩ (T := tPM ηB ηP) (by qsx [ΓP3, ΓP2]))
  have hF4 := typed_of_eq' (Defeq.forallEDF hPa hPq hPq) (l' := .zero)
    (Level.ext fun ν => by simp [Nat.imax])
  have hβb : E[ΓP3 ηB ηP ηW] ⊢ .app (.lam (eqA ηE l1M (tPM ηB ηP) #1
      (pairM ηB ηP (sp ηB ηS) (fp ηB ηF)))
      (.forallE (respP ηB ηE ηF ηS ηO #0 (pairM ηB ηP (sndM ηB ηS #0) (fstM ηB ηF #0)))
        (respP ηB ηE ηF ηS ηO #0 #1))) #2 ≡
      .forallE (respP ηB ηE ηF ηS ηO #0 (pairM ηB ηP (sp ηB ηS) (fp ηB ηF)))
        (respP ηB ηE ηF ηS ηO #0 #1) : .prop :=
    defeq_rw (beta_defeq heqa .sortDF hF4 hmaj) rfl (by qsx [respP]) (by qsx)
  have hβ2 : E[ΓP3 ηB ηP ηW] ⊢ .app (.app (moE ηB ηP ηE ηF ηS ηO)
      (pairM ηB ηP (sp ηB ηS) (fp ηB ηF))) #2 ≡
      .forallE (respP ηB ηE ηF ηS ηO #0 (pairM ηB ηP (sp ηB ηS) (fp ηB ηF)))
        (respP ηB ηE ηF ηS ηO #0 #1) : .prop :=
    (defeq_rw (.appDF heqa .sortDF hβa hmaj (defeq_rw (.sortDF (l := .zero)) (by qsx) (by qsx) rfl))
      rfl rfl (by qsx)).trans hβb
  -- the minor premise `fun x => x : P q → P q`
  have hP3 := respP_typed hE hb hq hot hft hst (ηE := ηE) hp0 hp1
  have hm4 := ctx_snoc hΓ hP3
  have hP4 := respP_typed hE hb hq hot hft hst (ηE := ηE)
    (var_of_get hm4 ⟨0, by decide⟩ (T := tPM ηB ηP) (by qsx [ΓP3, ΓP2]))
    (var_of_get hm4 ⟨1, by decide⟩ (T := tPM ηB ηP) (by qsx [ΓP3, ΓP2]))
  have hv3 : E[(ΓP3 ηB ηP ηW).snoc (respP ηB ηE ηF ηS ηO #0 #1)] ⊢ #3 :
      respP ηB ηE ηF ηS ηO #0 #1 := var_of_get hm4 ⟨3, by decide⟩ (by qsx [respP])
  have hmin : E[ΓP3 ηB ηP ηW] ⊢ .lam (respP ηB ηE ηF ηS ηO #0 #1) #3 :
      .forallE (respP ηB ηE ηF ηS ηO #0 #1) (respP ηB ηE ηF ηS ηO #0 #1) :=
    .lamDF hP3 hP4 hP4 hv3 hv3
  have hrefl := reflA_typed hq hP hp1 (η := ηE)
  have heq11 := eqA_typed hq hP hp1 hp1 (η := ηE)
  have hβr1 : E[ΓP3 ηB ηP ηW] ⊢ .app (moE ηB ηP ηE ηF ηS ηO) #1 ≡
      .lam (eqA ηE l1M (tPM ηB ηP) #1 #1)
        (.forallE (respP ηB ηE ηF ηS ηO #0 #1) (respP ηB ηE ηF ηS ηO #0 #1)) :
      .forallE (eqA ηE l1M (tPM ηB ηP) #1 #1) .prop :=
    defeq_rw (beta_defeq hP hMty4 hlam4 hp1) rfl (by qsx [respP]) (by qsx)
  have hr4 := ctx_snoc hΓ heq11
  have hPr := respP_typed hE hb hq hot hft hst (ηE := ηE)
    (var_of_get hr4 ⟨0, by decide⟩ (T := tPM ηB ηP) (by qsx [ΓP3, ΓP2]))
    (var_of_get hr4 ⟨1, by decide⟩ (T := tPM ηB ηP) (by qsx [ΓP3, ΓP2]))
  have hr5 := ctx_snoc hr4 hPr
  have hPr' := respP_typed hE hb hq hot hft hst (ηE := ηE)
    (var_of_get hr5 ⟨0, by decide⟩ (T := tPM ηB ηP) (by qsx [ΓP3, ΓP2]))
    (var_of_get hr5 ⟨1, by decide⟩ (T := tPM ηB ηP) (by qsx [ΓP3, ΓP2]))
  have hFr := typed_of_eq' (Defeq.forallEDF hPr hPr' hPr') (l' := .zero)
    (Level.ext fun ν => by simp [Nat.imax])
  have hβr2 : E[ΓP3 ηB ηP ηW] ⊢ .app (.lam (eqA ηE l1M (tPM ηB ηP) #1 #1)
      (.forallE (respP ηB ηE ηF ηS ηO #0 #1) (respP ηB ηE ηF ηS ηO #0 #1)))
      (reflA ηE l1M (tPM ηB ηP) #1) ≡
      .forallE (respP ηB ηE ηF ηS ηO #0 #1) (respP ηB ηE ηF ηS ηO #0 #1) : .prop :=
    defeq_rw (beta_defeq heq11 .sortDF hFr hrefl) rfl (by qsx [respP]) (by qsx)
  have hβr : E[ΓP3 ηB ηP ηW] ⊢ .app (.app (moE ηB ηP ηE ηF ηS ηO) #1)
      (reflA ηE l1M (tPM ηB ηP) #1) ≡
      .forallE (respP ηB ηE ηF ηS ηO #0 #1) (respP ηB ηE ηF ηS ηO #0 #1) : .prop :=
    (defeq_rw (.appDF heq11 .sortDF hβr1 hrefl (defeq_rw (.sortDF (l := .zero)) (by qsx) (by qsx)
      rfl)) rfl rfl (by qsx)).trans hβr2
  have hmin' := Defeq.defeqDF hβr.symm hmin
  -- `Eq.rec`
  have hrec := Defeq.recrDF (E := E) (Γ := ΓP3 ηB ηP ηW) (η := ηE) (s := 0) (ls := ![l1M])
    (l := .zero) (ps₁ := ![tPM ηB ηP, #1]) (ps₂ := ![tPM ηB ηP, #1])
    (ms₁ := fun _ => moE ηB ηP ηE ηF ηS ηO) (ms₂ := fun _ => moE ηB ηP ηE ηF ηS ηO)
    (mins₁ := fun _ _ => .lam (respP ηB ηE ηF ηS ηO #0 #1) #3)
    (mins₂ := fun _ _ => .lam (respP ηB ηE ηF ηS ηO #0 #1) #3)
    (is₁ := ![pairM ηB ηP (sp ηB ηS) (fp ηB ηF)]) (is₂ := ![pairM ηB ηP (sp ηB ηS) (fp ηB ηF)])
    (maj₁ := #2) (maj₂ := #2) (by rw [hq]; exact EraseProof.Test.NVP.eqBlock_subsingleton)
    ?_ ?_ ?_ ?_ hmaj hβ2.left
  rotate_left
  · intro p; fin_cases p <;> rw [hq]
    · exact typed_of_eq hP (by eqty)
    · exact typed_of_eq hp1 (by eqty)
  · intro t; fin_cases t; rw [hq]; exact typed_of_eq hMo (by eqty)
  · intro t c; fin_cases t; fin_cases c; rw [hq]; exact typed_of_eq hmin' (by eqty)
  · intro i; fin_cases i; rw [hq]; exact typed_of_eq hpair (by eqty)
  have hrec' : E[ΓP3 ηB ηP ηW] ⊢ eqRecM ηB ηP ηE ηF ηS ηO :
      .forallE (respP ηB ηE ηF ηS ηO #0 (pairM ηB ηP (sp ηB ηS) (fp ηB ηF)))
        (respP ηB ηE ηF ηS ηO #0 #1) := .defeqDF hβ2 hrec
  -- `orB_comm p.1 p.2`
  have hc := Defeq.wkClosed (Γ := ΓP3 ηB ηP ηW) (commM_typed hE hb hcv hmv hot hov hq)
  have hc' := typed_of_eq hc (T' := .forallE (mB ηB) (.forallE (mB ηB) (commEq ηB ηE ηO #3 #4)))
    (by qsx [commTyM])
  have hc1 := typed_of_eq (app_typed hc' (fstM_typed hE hb hft hp0))
    (T' := .forallE (mB ηB) (commEq ηB ηE ηO (fstM ηB ηF #0) #3)) (by qsx)
  have hc2 := typed_of_eq (app_typed hc1 (sndM_typed hE hb hst hp0))
    (T' := commEq ηB ηE ηO (fp ηB ηF) (sp ηB ηS)) (by qsx)
  have hdc : E[ΓP3 ηB ηP ηW] ⊢ commEq ηB ηE ηO (fp ηB ηF) (sp ηB ηS) ≡
      respP ηB ηE ηF ηS ηO #0 (pairM ηB ηP (sp ηB ηS) (fp ηB ηF)) : .prop :=
    eqA_defeq hq (mB_typed hb) (orBfs_typed hE hb hft hst hot hp0)
      (orBM_defeq hE hot (mB_typed hb)
        (fst_pair hE hb hp hft hfv hst hwt).symm (snd_pair hE hb hp hft hst hsv hwt).symm)
  have hbody := typed_of_eq (app_typed hrec' (.defeqDF hdc hc2))
    (T' := respP ηB ηE ηF ηS ηO #0 #1) (by qsx [respP])
  exact typed_of_eq (Ctx.lam_congr (Γ := .nil) (Δ := ΓP3 ηB ηP ηW) hΓ hbody)
    (by qsx [respTyM, respP, ΓP3, ΓP2])

end Prf

end EraseProof.Test.NVQP
