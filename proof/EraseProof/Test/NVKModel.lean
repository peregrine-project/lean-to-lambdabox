import EraseProof.Test.NVPModel

/-!
# NV-K: the Metalean model of the program

The premises of the final theorem about the program and its model, for NV-K (`Test/NVPData.lean`):
NV-P's environment extended by the theorem `hEq : B.t = B.t`, which Metalean loads as an opaque
entry of type `@Eq B B.t B.t` (`henv`, `hwf`), and the erased term, NV-P's spine on the major
`hEq` (`he`, `hty`, by `NVP.tE_typed_of`).
-/

open Lean Metalean

namespace EraseProof.Test.NVK

open EraseProof.Test.NV1 (tr_B tr_T trLevels_nil mB mT bSig bBlock indB_typed const_typed)
open EraseProof.Test.NVP (ζB ηEB ηBB ηCB EB BB hqB hbB wfB hcB BB_Eq BB_B BB_t BB_casesOn eqA
  reflA eqA_typed reflA_typed l1M trLevel_l1 tr_eqC eqCasesOnTyM tEm tr_eOf tE_typed_of mT_typed
  mB_typed)

abbrev ζK : Sigs := ζB.snoc (.const .«opaque» 0)
abbrev ηEK : Head ζK (.inductive Eq.sig) := .there ηEB
abbrev ηBK : Head ζK (.inductive bSig) := .there ηBB
abbrev ηCK : Head ζK (.const .def 2) := .there ηCB
abbrev ηHK : Head ζK (.const .«opaque» 0) := .here

/-- `hEq`'s statement `@Eq.{1} B B.t B.t` in `EB`. -/
def hEqTyM : Metalean.Expr ζB 0 0 := eqA ηEB l1M (mB ηBB) (mT ηBB) (mT ηBB)

/-- The Metalean environment of NV-K. -/
def EK : Env ζK := EB.snoc (.«opaque» hEqTyM)

theorem hqK : (EK.get ηEK).block = Eq.block := by
  simp! [EK, EB, NVP.EA, Env.get, Entry.block]
theorem hbK : (EK.get ηBK).block = bBlock := by
  simp! [EK, EB, NVP.EA, NV1.E1, Env.get, Entry.block]

theorem hEqTyM_typed : EB[.nil] ⊢ hEqTyM : .prop :=
  eqA_typed hqB (mB_typed hbB) (mT_typed hbB) (mT_typed hbB)

/-- `hwf`: `@Eq.refl B B.t` witnesses `hEq`'s opaque entry. -/
theorem hwf : EnvWF EK :=
  .snoc wfB (.«opaque» (reflA_typed hqB (mB_typed hbB) (mT_typed hbB)) ⟨_, hEqTyM_typed⟩)

/-- The name table of NV-K. -/
def BK : Binds ζK := (Binds.wk BB).set `hEq (.const .here)

theorem BK_Eq : BK `Eq = some (.ind ηEK 0) := rfl
theorem BK_B : BK `B = some (.ind ηBK 0) := rfl
theorem BK_t : BK `B.t = some (.ctor ηBK 0 1 []) := rfl
theorem BK_casesOn : BK `Eq.casesOn = some (.const ηCK) := rfl
theorem BK_hEq : BK `hEq = some (.const ηHK) := rfl

theorem tr_hEqTy : TrM EB BB [] .nil [] hEqTy hEqTyM :=
  tr_eqC BB_Eq trLevel_l1 (tr_B BB_B) (tr_T BB_t) (tr_T BB_t)

/-- `henv`: the program is the Lean form of `EK` with table `BK`. -/
theorem henv : ProgEnv P ζK EK BK :=
  ProgEnv.thm NVP.henv (by decide) (by decide) rfl
    (show ConstsIn _ (.app (.app (.const `rfl [NVP.l1]) NV1.tB) NV1.cT) by
      simp [ConstsIn, NV1.tB, NV1.cT, hEq_thm])
    tr_hEqTy hEqTyM_typed

/-- `hEq` in Metalean. -/
abbrev hEqM : Metalean.Expr ζK 0 0 := .const ηHK Fin.elim0

/-- The erased term in Metalean. -/
def tE : Metalean.Expr ζK 0 0 := tEm ηEK ηBK ηCK hEqM

/-- `he`: the erased term is the Lean form of `tE`. -/
theorem he : TrM EK BK [] .nil [] e tE :=
  tr_eOf BK_Eq BK_B BK_t BK_casesOn (TrM.const BK_hEq trLevels_nil)

theorem hcK : (EK.get ηCK).constType = eqCasesOnTyM ηEK := by
  simp! [EK, EB, Env.get, Entry.constType, eqCasesOnTyM, NVP.motM, NVP.minM, reflA, NV1.mMot,
    funext_iff, Fin.forall_fin_two, Fin.forall_fin_one]

theorem hcH : (EK.get ηHK).constType = eqA ηEK l1M (mB ηBK) (mT ηBK) (mT ηBK) := by
  simp! [EK, Env.get, Entry.constType, hEqTyM, eqA, mB, mT, funext_iff, Fin.forall_fin_two,
    Fin.forall_fin_one]

theorem hEqM_typed : EK[.nil] ⊢ hEqM : eqA ηEK l1M (mB ηBK) (mT ηBK) (mT ηBK) :=
  const_typed hwf ηHK Fin.elim0 (by rw [hcH]; eqsimp [Expr.wkClosed])

/-- `hty`: `tE` is typed. -/
theorem hty : ∃ T, EK[.nil] ⊢ tE : T :=
  tE_typed_of hqK hbK hwf hcK hEqM_typed

end EraseProof.Test.NVK
