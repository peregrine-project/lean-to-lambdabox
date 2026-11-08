import EraseProof.Test.NVQPResp
import EraseProof.Test.NVSModel
import EraseProof.Test.NV1Collect

/-!
# NV-QP: the Metalean model of the program

The premises of the final theorem about the program and its model, for NV-QP
(`Test/NVQPData.lean`): the program `P` is the Lean form of the well-formed Metalean environment
`E14` with name table `B14` (`henv`, `hwf`), and the erased term `e` is the Lean form of the closed
Metalean term `tE`, which is typed (`he`, `hty`). The environment extends NV-Q's quotient entry over
NV-P's environment (`EQ`) by, oldest first, the block of `Prod`, the definitions `Prod.fst`,
`Prod.snd` (structure projections), `B.casesOn`, `orB.match_1`, `orB` and `swapR`, the theorem
`orU._proof_1` as an opaque constant (inhabited by `respPrfM`, `Test/NVQPResp.lean`), and the
definitions `orU`, `useTF` and `useFT`, whose values are typed by `Test/NVQPBlocks.lean` and
`Test/NVQPDefs.lean`.
-/

open Lean Metalean

namespace EraseProof.Test.NVQP

open EraseProof.Test.NV1 (tB bSig bBlock mB mF mT typed_of_eq var_of_get const_typed fin0_eq lu
  casesOnTyM casesOnValM casesOnValM_typed minsC tr_B tr_F tr_T notSpecial_bvar notSpecial_const
  trLevels_nil largeElimB recTy casesOnTy casesOnVal tr_mot)
open EraseProof.Test.NVS (ppSig mPP mPPmk q0 q1 r0 r1 r2 tr_const0 tr_const1 trM_eq typedExt_self
  trL_one)
open EraseProof.Test.NVP (l1 eqA l1M mB_typed trLevels_one trLevels_two trLevel_l1 tr_eqC)
open EraseProof.Test.NVQ (ζQ ηQ ηEQ ηBQ EQ BQ wfQ henvQ qs)

/-! ## The environments -/

abbrev ζ4 : Sigs := ζQ.snoc (.inductive ppSig)
abbrev ζ5 : Sigs := ζ4.snoc (.const .def 2)
abbrev ζ6 : Sigs := ζ5.snoc (.const .def 2)
abbrev ζ7 : Sigs := ζ6.snoc (.const .def 1)
abbrev ζ8 : Sigs := ζ7.snoc (.const .def 1)
abbrev ζ9 : Sigs := ζ8.snoc (.const .def 0)
abbrev ζ10 : Sigs := ζ9.snoc (.const .def 0)
abbrev ζ11 : Sigs := ζ10.snoc (.const .«opaque» 0)
abbrev ζ12 : Sigs := ζ11.snoc (.const .def 0)
abbrev ζ13 : Sigs := ζ12.snoc (.const .def 0)
abbrev ζ14 : Sigs := ζ13.snoc (.const .def 0)

/-! Heads: `B` (`b`), `Prod` (`p`), `Eq` (`e`), the quotient entry (`q`), `Prod.fst` (`f`),
`Prod.snd` (`s`), `B.casesOn` (`c`), `orB.match_1` (`m`), `orB` (`o`), `swapR` (`w`),
`orU._proof_1` (`h`), `orU` (`u`), `useTF` (`t`), at each environment. -/

abbrev b4 : Head ζ4 (.inductive bSig) := .there ηBQ
abbrev b5 : Head ζ5 (.inductive bSig) := .there b4
abbrev b6 : Head ζ6 (.inductive bSig) := .there b5
abbrev b7 : Head ζ7 (.inductive bSig) := .there b6
abbrev b8 : Head ζ8 (.inductive bSig) := .there b7
abbrev b9 : Head ζ9 (.inductive bSig) := .there b8
abbrev b10 : Head ζ10 (.inductive bSig) := .there b9
abbrev b11 : Head ζ11 (.inductive bSig) := .there b10
abbrev b12 : Head ζ12 (.inductive bSig) := .there b11
abbrev b13 : Head ζ13 (.inductive bSig) := .there b12
abbrev b14 : Head ζ14 (.inductive bSig) := .there b13
abbrev p4 : Head ζ4 (.inductive ppSig) := .here
abbrev p5 : Head ζ5 (.inductive ppSig) := .there p4
abbrev p6 : Head ζ6 (.inductive ppSig) := .there p5
abbrev p7 : Head ζ7 (.inductive ppSig) := .there p6
abbrev p8 : Head ζ8 (.inductive ppSig) := .there p7
abbrev p9 : Head ζ9 (.inductive ppSig) := .there p8
abbrev p10 : Head ζ10 (.inductive ppSig) := .there p9
abbrev p11 : Head ζ11 (.inductive ppSig) := .there p10
abbrev p12 : Head ζ12 (.inductive ppSig) := .there p11
abbrev p13 : Head ζ13 (.inductive ppSig) := .there p12
abbrev e4 : Head ζ4 (.inductive Eq.sig) := .there ηEQ
abbrev e5 : Head ζ5 (.inductive Eq.sig) := .there e4
abbrev e6 : Head ζ6 (.inductive Eq.sig) := .there e5
abbrev e7 : Head ζ7 (.inductive Eq.sig) := .there e6
abbrev e8 : Head ζ8 (.inductive Eq.sig) := .there e7
abbrev e9 : Head ζ9 (.inductive Eq.sig) := .there e8
abbrev e10 : Head ζ10 (.inductive Eq.sig) := .there e9
abbrev e11 : Head ζ11 (.inductive Eq.sig) := .there e10
abbrev q4 : Head ζ4 .quot := .there ηQ
abbrev q5 : Head ζ5 .quot := .there q4
abbrev q6 : Head ζ6 .quot := .there q5
abbrev q7 : Head ζ7 .quot := .there q6
abbrev q8 : Head ζ8 .quot := .there q7
abbrev q9 : Head ζ9 .quot := .there q8
abbrev q10 : Head ζ10 .quot := .there q9
abbrev q11 : Head ζ11 .quot := .there q10
abbrev q12 : Head ζ12 .quot := .there q11
abbrev q13 : Head ζ13 .quot := .there q12
abbrev f5 : Head ζ5 (.const .def 2) := .here
abbrev f6 : Head ζ6 (.const .def 2) := .there f5
abbrev f7 : Head ζ7 (.const .def 2) := .there f6
abbrev f8 : Head ζ8 (.const .def 2) := .there f7
abbrev f9 : Head ζ9 (.const .def 2) := .there f8
abbrev f10 : Head ζ10 (.const .def 2) := .there f9
abbrev f11 : Head ζ11 (.const .def 2) := .there f10
abbrev sn6 : Head ζ6 (.const .def 2) := .here
abbrev sn7 : Head ζ7 (.const .def 2) := .there sn6
abbrev sn8 : Head ζ8 (.const .def 2) := .there sn7
abbrev sn9 : Head ζ9 (.const .def 2) := .there sn8
abbrev sn10 : Head ζ10 (.const .def 2) := .there sn9
abbrev sn11 : Head ζ11 (.const .def 2) := .there sn10
abbrev c7 : Head ζ7 (.const .def 1) := .here
abbrev c8 : Head ζ8 (.const .def 1) := .there c7
abbrev c9 : Head ζ9 (.const .def 1) := .there c8
abbrev c10 : Head ζ10 (.const .def 1) := .there c9
abbrev m8 : Head ζ8 (.const .def 1) := .here
abbrev m9 : Head ζ9 (.const .def 1) := .there m8
abbrev m10 : Head ζ10 (.const .def 1) := .there m9
abbrev o9 : Head ζ9 (.const .def 0) := .here
abbrev o10 : Head ζ10 (.const .def 0) := .there o9
abbrev o11 : Head ζ11 (.const .def 0) := .there o10
abbrev w10 : Head ζ10 (.const .def 0) := .here
abbrev w11 : Head ζ11 (.const .def 0) := .there w10
abbrev w12 : Head ζ12 (.const .def 0) := .there w11
abbrev w13 : Head ζ13 (.const .def 0) := .there w12
abbrev h11 : Head ζ11 (.const .«opaque» 0) := .here
abbrev u12 : Head ζ12 (.const .def 0) := .here
abbrev u13 : Head ζ13 (.const .def 0) := .there u12
abbrev t13 : Head ζ13 (.const .def 0) := .here
abbrev t14 : Head ζ14 (.const .def 0) := .there t13

def E4 : Env ζ4 := EQ.snoc (.inductive prBlock)
def E5 : Env ζ5 := E4.snoc (.def (prFstTyM p4) (prFstValM p4))
def E6 : Env ζ6 := E5.snoc (.def (prSndTyM p5) (prSndValM p5))
def E7 : Env ζ7 := E6.snoc (.def (casesOnTyM b6) (casesOnValM b6))
def E8 : Env ζ8 := E7.snoc (.def (omTyM b7) (omValM b7 c7))
def E9 : Env ζ9 := E8.snoc (.def (orBTyM b8) (orBValM b8 m8))
def E10 : Env ζ10 := E9.snoc (.def (swapTyM b9 p9) (swapValM b9 p9 e9 f9 sn9))
def E11 : Env ζ11 := E10.snoc (.«opaque» (respTyM b10 p10 e10 f10 sn10 o10 w10))
def E12 : Env ζ12 := E11.snoc (.def (orUTyM b11 p11 q11 w11) (orUValM b11 p11 e11 q11 f11 sn11 o11 w11 h11))
def E13 : Env ζ13 := E12.snoc (.def (mB b12) (useValM b12 p12 q12 w12 u12 (mT b12) (mF b12)))
def E14 : Env ζ14 := E13.snoc (.def (mB b13) (useValM b13 p13 q13 w13 u13 (mF b13) (mT b13)))

/-- Read a head's entry of the environments. -/
syntax (name := _qenvs) "qenvs" : tactic
macro_rules
  | `(tactic| qenvs) => `(tactic| simp! [E4, E5, E6, E7, E8, E9, E10, E11, E12, E13, E14,
  NVQ.EQ, NVP.EB, NVP.EA, NV1.E1, Env.get, Entry.block, Entry.constType, Entry.defValue,
  Entry.eqHead, prFstTyM, prSndTyM, prFstValM, prSndValM, prFstM, prSndM, ΓPr, Ctx.pi, Ctx.lam,
  casesOnTyM, casesOnValM, minsC, NV1.mMot, omTyM, omValM, motMM, orBTyM, orBValM, motBM, swapTyM,
  swapValM, respTyM, orUTyM, quotTM, tPM, mPP, mPPmk, mB, mF, mT, fstM, sndM, fstBB, sndBB, orBM,
  pairM, swapM, eqA, Quot.eqApp, funext_iff, Fin.forall_fin_one, Fin.forall_fin_two, fin0_eq])

theorem t_p4 : (E4.get p4).block = prBlock := by qenvs
theorem t_p5 : (E5.get p5).block = prBlock := by qenvs
theorem t_b6 : (E6.get b6).block = bBlock := by qenvs
theorem t_b7 : (E7.get b7).block = bBlock := by qenvs
theorem t_c7t : (E7.get c7).constType = casesOnTyM b7 := by qenvs

theorem t_b8 : (E8.get b8).block = bBlock := by qenvs
theorem t_m8t : (E8.get m8).constType = omTyM b8 := by qenvs
theorem t_b9 : (E9.get b9).block = bBlock := by qenvs
theorem t_p9 : (E9.get p9).block = prBlock := by qenvs
theorem t_e9 : (E9.get e9).block = Eq.block := by qenvs
theorem t_f9t : (E9.get f9).constType = prFstTyM p9 := by qenvs
theorem t_s9t : (E9.get sn9).constType = prSndTyM p9 := by qenvs
theorem t_b10 : (E10.get b10).block = bBlock := by qenvs
theorem t_p10 : (E10.get p10).block = prBlock := by qenvs
theorem t_e10 : (E10.get e10).block = Eq.block := by qenvs
theorem t_f10t : (E10.get f10).constType = prFstTyM p10 := by qenvs
theorem t_s10t : (E10.get sn10).constType = prSndTyM p10 := by qenvs
theorem t_o10t : (E10.get o10).constType = orBTyM b10 := by qenvs
theorem t_w10t : (E10.get w10).constType = swapTyM b10 p10 := by qenvs
theorem t_c10v : (E10.get c10).defValue = casesOnValM b10 := by qenvs
theorem t_m10v : (E10.get m10).defValue = omValM b10 c10 := by qenvs
theorem t_o10v : (E10.get o10).defValue = orBValM b10 m10 := by qenvs
theorem t_f10v : (E10.get f10).defValue = prFstValM p10 := by qenvs
theorem t_s10v : (E10.get sn10).defValue = prSndValM p10 := by qenvs
theorem t_w10v : (E10.get w10).defValue = swapValM b10 p10 e10 f10 sn10 := by qenvs
theorem t_b11 : (E11.get b11).block = bBlock := by qenvs
theorem t_p11 : (E11.get p11).block = prBlock := by qenvs
theorem t_e11 : (E11.get e11).block = Eq.block := by qenvs
theorem t_f11t : (E11.get f11).constType = prFstTyM p11 := by qenvs
theorem t_s11t : (E11.get sn11).constType = prSndTyM p11 := by qenvs
theorem t_o11t : (E11.get o11).constType = orBTyM b11 := by qenvs
theorem t_w11t : (E11.get w11).constType = swapTyM b11 p11 := by qenvs
theorem t_q11 : (E11.get q11).eqHead = e11 := by qenvs
theorem t_h11t : (E11.get h11).constType = respTyM b11 p11 e11 f11 sn11 o11 w11 := by qenvs
theorem t_b12 : (E12.get b12).block = bBlock := by qenvs
theorem t_p12 : (E12.get p12).block = prBlock := by qenvs
theorem t_w12t : (E12.get w12).constType = swapTyM b12 p12 := by qenvs
theorem t_u12t : (E12.get u12).constType = orUTyM b12 p12 q12 w12 := by qenvs
theorem t_b13 : (E13.get b13).block = bBlock := by qenvs
theorem t_p13 : (E13.get p13).block = prBlock := by qenvs
theorem t_w13t : (E13.get w13).constType = swapTyM b13 p13 := by qenvs
theorem t_u13t : (E13.get u13).constType = orUTyM b13 p13 q13 w13 := by qenvs
theorem t_b14 : (E14.get b14).block = bBlock := by qenvs
theorem t_t14t : (E14.get t14).constType = mB b14 := by qenvs

/-! ## Well-formedness -/

theorem wf4 : EnvWF E4 := .snoc wfQ (.inductive (prBlock_wf _))
theorem wf5 : EnvWF E5 :=
  .snoc wf4 (.def (prFstValM_typed wf4 t_p4).regular (prFstValM_typed wf4 t_p4))
theorem wf6 : EnvWF E6 :=
  .snoc wf5 (.def (prSndValM_typed wf5 t_p5).regular (prSndValM_typed wf5 t_p5))
theorem wf7 : EnvWF E7 :=
  .snoc wf6 (.def (casesOnValM_typed t_b6).regular (casesOnValM_typed t_b6))
theorem wf8 : EnvWF E8 :=
  .snoc wf7 (.def (omValM_typed wf7 t_b7 t_c7t).regular (omValM_typed wf7 t_b7 t_c7t))
theorem wf9 : EnvWF E9 :=
  .snoc wf8 (.def (orBValM_typed wf8 t_b8 t_m8t).regular (orBValM_typed wf8 t_b8 t_m8t))
theorem wf10 : EnvWF E10 :=
  .snoc wf9 (.def (swapValM_typed wf9 t_b9 t_p9 t_e9 t_f9t t_s9t).regular
    (swapValM_typed wf9 t_b9 t_p9 t_e9 t_f9t t_s9t))
theorem wf11 : EnvWF E11 :=
  .snoc wf10 (.«opaque» (respPrfM_typed wf10 t_b10 t_p10 t_e10 t_c10v t_m10v t_o10t t_o10v t_f10t
    t_f10v t_s10t t_s10v t_w10t t_w10v)
    ⟨_, respTyM_typed wf10 t_b10 t_p10 t_e10 t_f10t t_s10t t_o10t t_w10t⟩)
theorem wf12 : EnvWF E12 :=
  .snoc wf11 (.def (orUValM_typed wf11 t_b11 t_p11 t_e11 t_f11t t_s11t t_o11t t_w11t t_q11 t_h11t).regular
    (orUValM_typed wf11 t_b11 t_p11 t_e11 t_f11t t_s11t t_o11t t_w11t t_q11 t_h11t))
theorem wf13 : EnvWF E13 :=
  .snoc wf12 (.def ⟨_, mB_typed t_b12⟩
    (useValM_typed wf12 t_b12 t_p12 t_w12t t_u12t (mTT t_b12) (mFT t_b12)))
theorem wf14 : EnvWF E14 :=
  .snoc wf13 (.def ⟨_, mB_typed t_b13⟩
    (useValM_typed wf13 t_b13 t_p13 t_w13t t_u13t (mFT t_b13) (mTT t_b13)))


/-! ## Name tables -/

def B4 : Binds ζ4 := fun n =>
  if n = `Prod then some (.ind p4 0)
  else if n = `Prod.mk then some (.ctor p4 0 0 [0, 1])
  else if n = `Prod.rec then some (.recr p4 0 [[[0, 1]]])
  else Binds.wk BQ n
def B5 : Binds ζ5 := (Binds.wk B4).set `Prod.fst (.const .here)
def B6 : Binds ζ6 := (Binds.wk B5).set `Prod.snd (.const .here)
def B7 : Binds ζ7 := (Binds.wk B6).set `B.casesOn (.const .here)
def B8 : Binds ζ8 := (Binds.wk B7).set `orB.match_1 (.const .here)
def B9 : Binds ζ9 := (Binds.wk B8).set `orB (.const .here)
def B10 : Binds ζ10 := (Binds.wk B9).set `swapR (.const .here)
def B11 : Binds ζ11 := (Binds.wk B10).set `orU._proof_1 (.const .here)
def B12 : Binds ζ12 := (Binds.wk B11).set `orU (.const .here)
def B13 : Binds ζ13 := (Binds.wk B12).set `useTF (.const .here)
def B14 : Binds ζ14 := (Binds.wk B13).set `useFT (.const .here)

/-! ## Generic `TrM` facts for `Prod`'s constants and the quotient -/

section TrGeneric
variable {ζ : Sigs} {E : Env ζ} {B : Binds ζ} {lps : List Name} {n : Nat}
  {Γ : Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}

theorem tr_Pr {η : Head ζ (.inductive ppSig)} (h : B `Prod = some (.ind η 0)) {u v : Lean.Level}
    {l m : Metalean.Level lps.length} (hu : TrLevel lps u = some l) (hv : TrLevel lps v = some m)
    {α β : Lean.Expr} {α' β' : Metalean.Expr ζ lps.length n} (hα : TrM E B lps Γ Δ α α')
    (hβ : TrM E B lps Γ Δ β β') :
    TrM E B lps Γ Δ (.app (.app (.const `Prod [u, v]) α) β) (mPP η l m α' β') :=
  TrM.special (as := [α, β]) (as' := [α', β']) h rfl rfl
    (by
      intro i x x' h1 h2
      rcases i with _ | _ | i <;> simp at h1 h2 <;> subst h1 h2
      · exact hα
      · exact hβ)
    (SatTr.indSat (E := E) (lps := lps) (η := η) (s := 0) (us := [u, v]) (ls := ![l, m])
      (ps := ![α', β']) (is := Fin.elim0) (rest := []) (trLevels_two hu hv))

theorem tr_Prmk {η : Head ζ (.inductive ppSig)} (h : B `Prod.mk = some (.ctor η 0 0 [0, 1]))
    {u v : Lean.Level} {l m : Metalean.Level lps.length} (hu : TrLevel lps u = some l)
    (hv : TrLevel lps v = some m) {α β a b : Lean.Expr} {α' β' a' b' : Metalean.Expr ζ lps.length n}
    (hα : TrM E B lps Γ Δ α α') (hβ : TrM E B lps Γ Δ β β') (ha : TrM E B lps Γ Δ a a')
    (hb : TrM E B lps Γ Δ b b') :
    TrM E B lps Γ Δ (.app (.app (.app (.app (.const `Prod.mk [u, v]) α) β) a) b)
      (mPPmk η l m α' β' a' b') :=
  TrM.special (as := [α, β, a, b]) (as' := [α', β', a', b']) h rfl rfl
    (by
      intro i x x' h1 h2
      rcases i with _ | _ | _ | _ | i <;> simp at h1 h2 <;> subst h1 h2
      · exact hα
      · exact hβ
      · exact ha
      · exact hb)
    (SatTr.ctorSat (E := E) (lps := lps) (η := η) (s := 0) (c := 0) (us := [u, v]) (order := [0, 1])
      (ls := ![l, m]) (fs := [a', b']) (rest := []) (ps := ![α', β']) (fds := ![a', b'])
      (recFds := Fin.elim0) (trLevels_two hu hv) rfl rfl
      (by intro o; fin_cases o <;> exact ⟨_, _, rfl, rfl, rfl⟩))

theorem tr_quot {η : Head ζ .quot} (h : B `Quot = some (.quot η .type)) {u : Lean.Level}
    {l : Metalean.Level lps.length} {α r : Lean.Expr} {α' r' : Metalean.Expr ζ lps.length n}
    (hl : TrLevel lps u = some l) (hα : TrM E B lps Γ Δ α α') (hr : TrM E B lps Γ Δ r r') :
    TrM E B lps Γ Δ (.app (.app (.const `Quot [u]) α) r) (.quot η l α' r') :=
  TrM.special (c := `Quot) (us := [u]) (as := [α, r]) (as' := [α', r']) h rfl rfl
    (by
      intro i x x' h1 h2
      rcases i with _ | _ | i <;> simp at h1 h2 <;> subst h1 h2 <;> assumption)
    (SatTr.quotType (rest := []) (by simp [hl]))

/-- `x.1`, `x.2` through `Prod.fst`, `Prod.snd` at `B B`. -/
theorem tr_fst {ηB : Head ζ (.inductive bSig)} {ηF : Head ζ (.const .def 2)}
    (hB : B `B = some (.ind ηB 0)) (hF : B `Prod.fst = some (.const ηF)) {x : Lean.Expr}
    {x' : Metalean.Expr ζ 0 n} {Γ : Ctx ζ ([] : List Name).length 0 n}
    {Δ : MLCtx ζ ([] : List Name).length n} (hx : TrM E B [] Γ Δ x x') :
    TrM E B [] Γ Δ (fstB x) (fstM ηB ηF x') :=
  TrM.app (notSpecial_const hF ⟨_, rfl⟩) (TrM.app (notSpecial_const hF ⟨_, rfl⟩)
    (TrM.app (notSpecial_const hF ⟨_, rfl⟩) (TrM.const hF (trLevels_two rfl rfl)) (tr_B hB))
    (tr_B hB)) hx

theorem tr_snd {ηB : Head ζ (.inductive bSig)} {ηS : Head ζ (.const .def 2)}
    (hB : B `B = some (.ind ηB 0)) (hS : B `Prod.snd = some (.const ηS)) {x : Lean.Expr}
    {x' : Metalean.Expr ζ 0 n} {Γ : Ctx ζ ([] : List Name).length 0 n}
    {Δ : MLCtx ζ ([] : List Name).length n} (hx : TrM E B [] Γ Δ x x') :
    TrM E B [] Γ Δ (sndB x) (sndM ηB ηS x') :=
  TrM.app (notSpecial_const hS ⟨_, rfl⟩) (TrM.app (notSpecial_const hS ⟨_, rfl⟩)
    (TrM.app (notSpecial_const hS ⟨_, rfl⟩) (TrM.const hS (trLevels_two rfl rfl)) (tr_B hB))
    (tr_B hB)) hx

theorem tr_orB {ηO : Head ζ (.const .def 0)} (hO : B `orB = some (.const ηO)) {a b : Lean.Expr}
    {a' b' : Metalean.Expr ζ 0 n} {Γ : Ctx ζ ([] : List Name).length 0 n}
    {Δ : MLCtx ζ ([] : List Name).length n} (ha : TrM E B [] Γ Δ a a') (hb : TrM E B [] Γ Δ b b') :
    TrM E B [] Γ Δ (orBC a b) (orBM ηO a' b') :=
  TrM.app (notSpecial_const hO ⟨_, rfl⟩) (TrM.app (notSpecial_const hO ⟨_, rfl⟩) (tr_const0 hO) ha)
    hb

theorem tr_tP {ηB : Head ζ (.inductive bSig)} {ηP : Head ζ (.inductive ppSig)}
    (hB : B `B = some (.ind ηB 0)) (hP : B `Prod = some (.ind ηP 0))
    {Γ : Ctx ζ ([] : List Name).length 0 n} {Δ : MLCtx ζ ([] : List Name).length n} :
    TrM E B [] Γ Δ tP (tPM ηB ηP) :=
  tr_Pr hP rfl rfl (tr_B hB) (tr_B hB)

end TrGeneric

/-! ## The block of `Prod` in `E4`/`B4` -/

theorem tr_prTy : TrM E4 B4 [`u, `v] .nil [] Prod_ind.type prTyM :=
  TrM.forallE (TrM.sort rfl) (TrM.forallE (TrM.sort rfl) (TrM.sort rfl))

theorem tr_prConst : TrM E4 B4 [`u, `v] .nil [] (.const `Prod [.param `u, .param `v])
    (prTermM p4) := by
  have h := TrM.special (E := E4) (B := B4) (lps := [`u, `v]) (Γ := .nil) (Δ := [])
    (c := `Prod) (us := [.param `u, .param `v]) (as := []) (as' := []) rfl rfl rfl
    (fun _ _ _ h => nomatch h)
    (SatTr.indEta (E := E4) (lps := [`u, `v]) (args := []) (η := p4) (s := 0)
      (us := [.param `u, .param `v]) (ls := ![q0, q1]) (trLevels_two rfl rfl) (by decide))
  rw [indTerm_eqPr t_p4] at h
  exact h

theorem tr_prMkTy : TrM E4 B4 [`u, `v] .nil [] Prod_mk.type (prMkTyM p4) :=
  TrM.forallE (TrM.sort rfl) (TrM.forallE (TrM.sort rfl) (TrM.forallE (TrM.bvar rfl)
    (TrM.forallE (TrM.bvar rfl) (tr_Pr rfl rfl rfl (TrM.bvar rfl) (TrM.bvar rfl)))))

theorem tr_prMk : TrM E4 B4 [`u, `v] .nil [] (.const `Prod.mk [.param `u, .param `v])
    (prMkTermM p4) :=
  TrM.special (as := []) (as' := []) rfl rfl rfl (fun _ _ _ h => nomatch h)
    (SatTr.ctorEta (args := []) (η := p4) (s := 0) (c := 0) (order := [0, 1])
      (trLevels_two rfl rfl) (by decide) (ctorTerm_eqPr t_p4))

theorem tr_prRecTy : TrM E4 B4 [`u_1, `u, `v] .nil [] Prod_rec.type (prRecTyM p4) :=
  TrM.forallE (TrM.sort rfl) (TrM.forallE (TrM.sort rfl)
    (TrM.forallE (TrM.forallE (tr_Pr rfl rfl rfl (TrM.bvar rfl) (TrM.bvar rfl)) (TrM.sort rfl))
      (TrM.forallE (TrM.forallE (TrM.bvar rfl) (TrM.forallE (TrM.bvar rfl)
          (TrM.app notSpecial_bvar (TrM.bvar rfl)
            (tr_Prmk rfl rfl rfl (TrM.bvar rfl) (TrM.bvar rfl) (TrM.bvar rfl) (TrM.bvar rfl)))))
        (TrM.forallE (tr_Pr rfl rfl rfl (TrM.bvar rfl) (TrM.bvar rfl))
          (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl))))))

theorem tr_prRec : TrM E4 B4 [`u_1, `u, `v] .nil []
    (.const `Prod.rec [.param `u_1, .param `u, .param `v]) (prRecTermM p4) :=
  TrM.special (as := []) (as' := []) rfl rfl rfl (fun _ _ _ h => nomatch h)
    (SatTr.recrEta (E := E4) (lps := [`u_1, `u, `v]) (args := []) (η := p4) (s := 0)
      (us := [.param `u_1, .param `u, .param `v]) (us' := [.param `u, .param `v]) (l := r0)
      (ls := ![r1, r2]) (fun _ _ => [0, 1]) (Or.inl ⟨by rw [t_p4]; exact largeElimPr, _, rfl, rfl⟩)
      (trLevels_two rfl rfl) (by intro t c; fin_cases t; fin_cases c; rfl) (by decide)
      (recrTerm_eqPr t_p4))

def IsPr : Fin ppSig.nsorts → InductiveVal := fun _ => Prod_ind
def CsPr : (s : Fin ppSig.nsorts) → Fin (ppSig.nctors s) → ConstructorVal := fun _ _ => Prod_mk
def RsPr : Fin ppSig.nsorts → RecursorVal := fun _ => Prod_rec
def ordersPr : (s : Fin ppSig.nsorts) → Fin (ppSig.nctors s) → List Nat := fun _ _ => [0, 1]

theorem PPr_eq : IndBlock.decls IsPr CsPr RsPr =
    [.recInfo Prod_rec, .ctorInfo Prod_mk, .inductInfo Prod_ind] := rfl

theorem indBlockPr : IndBlock E4 B4 p4 [`u, `v] IsPr CsPr RsPr ordersPr where
  levels := rfl
  ind s := by fin_cases s; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  ctor s c := by
    fin_cases s; fin_cases c
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, [0, 1], [], rfl, rfl, rfl, by decide, .nil,
      List.Perm.refl _⟩
  ctorType s c := by fin_cases s; fin_cases c; exact ⟨_, [], rfl, rfl, rfl⟩
  recr s := by
    fin_cases s
    exact ⟨rfl, rfl, fun _ => ⟨`u_1, rfl⟩, fun h => absurd (by rw [t_p4]; exact largeElimPr) h,
      rfl, rfl, rfl, rfl, rfl, rfl⟩
  recrType s := by fin_cases s; rfl
  recMajor s := by fin_cases s; exact ⟨_, _, _, _, _, rfl, rfl⟩
  minors s t c := by fin_cases s; fin_cases t; fin_cases c; rfl
  recIHs s := by
    fin_cases s
    exact ⟨_, _, rfl, rfl, fun t c => by fin_cases t; fin_cases c; rfl⟩
  indexVars s _ h := by fin_cases s; exact h.elim fun i _ => i.elim0

theorem constTypedPr : ∀ ci ∈ IndBlock.decls IsPr CsPr RsPr, ConstTyped E4 B4 ci := by
  rw [PPr_eq]
  intro ci hci
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hci
  rcases hci with rfl | rfl | rfl
  · exact ⟨_, _, tr_prRecTy, tr_prRec, prRecTermM_typed t_p4⟩
  · exact ⟨_, _, tr_prMkTy, tr_prMk, prMkTermM_typed t_p4⟩
  · exact ⟨_, _, tr_prTy, tr_prConst, prTermM_typed t_p4⟩

def P0 : List ConstantInfo := qs.reverse.map .quotInfo ++ NVP.P

theorem henv4 : ProgEnv (IndBlock.decls IsPr CsPr RsPr ++ P0) ζ4 E4 B4 :=
  ProgEnv.induct (I := prBlock) (lps := [`u, `v]) (orders := ordersPr) henvQ (by decide)
    (by rw [PPr_eq]; decide) (by decide)
    (fun n hn => by
      rw [PPr_eq] at hn
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
        not_or] at hn
      obtain ⟨h1, h2, h3⟩ := hn
      have h1' : n ≠ `Prod.rec := h1
      have h2' : n ≠ `Prod.mk := h2
      have h3' : n ≠ `Prod := h3
      simp [B4, h1', h2', h3'])
    indBlockPr constTypedPr

/-! ## `Prod.fst`, `Prod.snd` -/

theorem tr_fstTy : TrM E4 B4 [`u, `v] .nil [] Prod_fst.type (prFstTyM p4) :=
  TrM.forallE (TrM.sort rfl) (TrM.forallE (TrM.sort rfl)
    (TrM.forallE (tr_Pr rfl rfl rfl (TrM.bvar rfl) (TrM.bvar rfl)) (TrM.bvar rfl)))

theorem tr_fstVal : TrM E4 B4 [`u, `v] .nil [] Prod_fst.value (prFstValM p4) := by
  have hst : (E4.get p4).block.IsStructure 0 0 := t_p4 ▸ prStruct
  have hp := TrM.projStruct (E := E4) (B := B4) (lps := [`u, `v]) (Γ := ΓPr p4)
    (Δ := MLCtx.pushLam (MLCtx.pushLam (MLCtx.pushLam ([] : MLCtx ζ4 2 0) none) none) none)
    (S := `Prod) (i := 0) (e := .bvar 0) (e' := #2) hst (by decide) rfl (TrM.bvar rfl)
    (typedExt_self (self_typed t_p4 hst))
  rw [projTerm_eqPr0 hst t_p4] at hp
  exact TrM.lam (TrM.sort rfl) (TrM.lam (TrM.sort rfl)
    (TrM.lam (tr_Pr rfl rfl rfl (TrM.bvar rfl) (TrM.bvar rfl)) hp))

theorem henv5 : ProgEnv (.defnInfo Prod_fst :: IndBlock.decls IsPr CsPr RsPr ++ P0) ζ5 E5 B5 :=
  ProgEnv.defn henv4 (by decide) (by decide) rfl rfl tr_fstTy tr_fstVal

theorem tr_sndTy : TrM E5 B5 [`u, `v] .nil [] Prod_snd.type (prSndTyM p5) :=
  TrM.forallE (TrM.sort rfl) (TrM.forallE (TrM.sort rfl)
    (TrM.forallE (tr_Pr rfl rfl rfl (TrM.bvar rfl) (TrM.bvar rfl)) (TrM.bvar rfl)))

theorem tr_sndVal : TrM E5 B5 [`u, `v] .nil [] Prod_snd.value (prSndValM p5) := by
  have hst : (E5.get p5).block.IsStructure 0 0 := t_p5 ▸ prStruct
  have hp := TrM.projStruct (E := E5) (B := B5) (lps := [`u, `v]) (Γ := ΓPr p5)
    (Δ := MLCtx.pushLam (MLCtx.pushLam (MLCtx.pushLam ([] : MLCtx ζ5 2 0) none) none) none)
    (S := `Prod) (i := 1) (e := .bvar 0) (e' := #2) hst (by decide) rfl (TrM.bvar rfl)
    (typedExt_self (self_typed t_p5 hst))
  rw [projTerm_eqPr1 hst t_p5] at hp
  exact TrM.lam (TrM.sort rfl) (TrM.lam (TrM.sort rfl)
    (TrM.lam (tr_Pr rfl rfl rfl (TrM.bvar rfl) (TrM.bvar rfl)) hp))

theorem henv6 : ProgEnv (.defnInfo Prod_snd :: .defnInfo Prod_fst :: IndBlock.decls IsPr CsPr RsPr ++
    P0) ζ6 E6 B6 :=
  ProgEnv.defn henv5 (by decide) (by decide) rfl rfl tr_sndTy tr_sndVal


/-! ## `B.casesOn` in `E6`/`B6` -/

theorem tr_casesOnTy6 : TrM E6 B6 [`u] .nil [] casesOnTy (casesOnTyM b6) :=
  TrM.forallE (tr_mot rfl)
    (TrM.forallE (tr_B rfl)
      (TrM.forallE (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_F rfl))
        (TrM.forallE (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_T rfl))
          (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl)))))

theorem tr_casesOnVal6 : TrM E6 B6 [`u] .nil [] casesOnVal (casesOnValM b6) := by
  have h : TrM E6 B6 [`u] .nil [] casesOnVal _ :=
    TrM.lam (tr_mot rfl) (TrM.lam (tr_B rfl)
      (TrM.lam (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_F rfl))
        (TrM.lam (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_T rfl))
          (TrM.special (c := `B.rec) (us := [.param `u])
            (as := [.bvar 3, .bvar 1, .bvar 0, .bvar 2]) (as' := [#0, #2, #3, #1]) rfl rfl rfl
            (by
              intro i a a' h1 h2
              rcases i with _ | _ | _ | _ | i <;> simp at h1 h2 <;> subst h1 h2 <;>
                exact TrM.bvar rfl)
            (SatTr.recrSat (E := E6) (lps := [`u]) (η := b6) (s := 0) (us := [.param `u])
              (us' := []) (ls := Fin.elim0) (l := lu) (fun _ _ => []) ![#0, #2, #3, #1] []
              minsC (Or.inl ⟨by rw [t_b6]; exact largeElimB, _, rfl, rfl⟩) trLevels_nil
              (by intro t c; fin_cases t; fin_cases c <;> rfl)
              (by
                intro t c; fin_cases t; fin_cases c <;> rw [t_b6] <;> rfl))))))
  convert h using 1
  simp only [casesOnValM]
  exprEq

theorem henv7 : ProgEnv (.defnInfo NV1.B_casesOn :: .defnInfo Prod_snd :: .defnInfo Prod_fst ::
    IndBlock.decls IsPr CsPr RsPr ++ P0) ζ7 E7 B7 :=
  ProgEnv.defn henv6 (by decide) (by decide) rfl rfl tr_casesOnTy6 tr_casesOnVal6

/-! ## `orB.match_1`, `orB`, `swapR` -/

theorem tr_matchTy : TrM E7 B7 [`u_1] .nil [] matchTy (omTyM b7) :=
  TrM.forallE (TrM.forallE (tr_B rfl) (TrM.forallE (tr_B rfl) (TrM.sort rfl)))
    (TrM.forallE (tr_B rfl) (TrM.forallE (tr_B rfl)
      (TrM.forallE (TrM.forallE (tr_B rfl) (TrM.app notSpecial_bvar
          (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_F rfl)) (TrM.bvar rfl)))
        (TrM.forallE (TrM.forallE (tr_B rfl) (TrM.app notSpecial_bvar
            (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_T rfl)) (TrM.bvar rfl)))
          (TrM.app notSpecial_bvar (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl))
            (TrM.bvar rfl))))))

theorem tr_matchVal : TrM E7 B7 [`u_1] .nil [] matchVal (omValM b7 c7) :=
  TrM.lam (TrM.forallE (tr_B rfl) (TrM.forallE (tr_B rfl) (TrM.sort rfl)))
    (TrM.lam (tr_B rfl) (TrM.lam (tr_B rfl)
      (TrM.lam (TrM.forallE (tr_B rfl) (TrM.app notSpecial_bvar
          (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_F rfl)) (TrM.bvar rfl)))
        (TrM.lam (TrM.forallE (tr_B rfl) (TrM.app notSpecial_bvar
            (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_T rfl)) (TrM.bvar rfl)))
          (TrM.app (notSpecial_const (B := B7) rfl ⟨_, rfl⟩)
            (TrM.app (notSpecial_const (B := B7) rfl ⟨_, rfl⟩)
              (TrM.app (notSpecial_const (B := B7) rfl ⟨_, rfl⟩)
                (TrM.app (notSpecial_const (B := B7) rfl ⟨_, rfl⟩) (tr_const1 rfl rfl)
                  (TrM.lam (tr_B rfl) (TrM.app notSpecial_bvar
                    (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl)) (TrM.bvar rfl))))
                (TrM.bvar rfl))
              (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl)))
            (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl)))))))

theorem henv8 : ProgEnv (.defnInfo orB_match_1 :: .defnInfo NV1.B_casesOn :: .defnInfo Prod_snd ::
    .defnInfo Prod_fst :: IndBlock.decls IsPr CsPr RsPr ++ P0) ζ8 E8 B8 :=
  ProgEnv.defn henv7 (by decide) (by decide) rfl rfl tr_matchTy tr_matchVal

theorem tr_orBVal : TrM E8 B8 [] .nil [] orBVal (orBValM b8 m8) :=
  TrM.lam (tr_B rfl) (TrM.lam (tr_B rfl)
    (TrM.app (notSpecial_const (B := B8) rfl ⟨_, rfl⟩)
      (TrM.app (notSpecial_const (B := B8) rfl ⟨_, rfl⟩)
        (TrM.app (notSpecial_const (B := B8) rfl ⟨_, rfl⟩)
          (TrM.app (notSpecial_const (B := B8) rfl ⟨_, rfl⟩)
            (TrM.app (notSpecial_const (B := B8) rfl ⟨_, rfl⟩) (tr_const1 rfl trL_one)
              (TrM.lam (tr_B rfl) (TrM.lam (tr_B rfl) (tr_B rfl))))
            (TrM.bvar rfl))
          (TrM.bvar rfl))
        (TrM.lam (tr_B rfl) (TrM.bvar rfl)))
      (TrM.lam (tr_B rfl) (tr_T rfl))))

theorem henv9 : ProgEnv (.defnInfo orB_def :: .defnInfo orB_match_1 :: .defnInfo NV1.B_casesOn ::
    .defnInfo Prod_snd :: .defnInfo Prod_fst :: IndBlock.decls IsPr CsPr RsPr ++ P0) ζ9 E9 B9 :=
  ProgEnv.defn henv8 (by decide) (by decide) rfl rfl
    (TrM.forallE (tr_B rfl) (TrM.forallE (tr_B rfl) (tr_B rfl))) tr_orBVal

theorem tr_swapVal : TrM E9 B9 [] .nil [] swapRVal (swapValM b9 p9 e9 f9 sn9) :=
  TrM.lam (tr_tP rfl rfl) (TrM.lam (tr_tP rfl rfl)
    (tr_eqC rfl trLevel_l1 (tr_tP rfl rfl) (TrM.bvar rfl)
      (tr_Prmk rfl rfl rfl (tr_B rfl) (tr_B rfl) (tr_snd rfl rfl (TrM.bvar rfl))
        (tr_fst rfl rfl (TrM.bvar rfl)))))

theorem henv10 : ProgEnv (.defnInfo swapR_def :: .defnInfo orB_def :: .defnInfo orB_match_1 ::
    .defnInfo NV1.B_casesOn :: .defnInfo Prod_snd :: .defnInfo Prod_fst ::
    IndBlock.decls IsPr CsPr RsPr ++ P0) ζ10 E10 B10 :=
  ProgEnv.defn henv9 (by decide) (by decide) rfl rfl
    (TrM.forallE (tr_tP rfl rfl) (TrM.forallE (tr_tP rfl rfl) (TrM.sort rfl))) tr_swapVal

/-! ## `orU._proof_1` -/

theorem tr_respTy : TrM E10 B10 [] .nil [] respTy (respTyM b10 p10 e10 f10 sn10 o10 w10) :=
  TrM.forallE (tr_tP rfl rfl) (TrM.forallE (tr_tP rfl rfl)
    (TrM.forallE (TrM.app (notSpecial_const (B := B10) rfl ⟨_, rfl⟩)
        (TrM.app (notSpecial_const (B := B10) rfl ⟨_, rfl⟩) (tr_const0 rfl) (TrM.bvar rfl))
        (TrM.bvar rfl))
      (tr_eqC rfl trLevel_l1 (tr_B rfl)
        (tr_orB rfl (tr_fst rfl rfl (TrM.bvar rfl)) (tr_snd rfl rfl (TrM.bvar rfl)))
        (tr_orB rfl (tr_fst rfl rfl (TrM.bvar rfl)) (tr_snd rfl rfl (TrM.bvar rfl))))))

/-- The value of the theorem does not name it. -/
theorem resp_fresh : ConstsIn (· ≠ resp_thm.name) resp_thm.value :=
  constsIn_of_all (p := fun c => c != `orU._proof_1) (fun c h => by simpa [resp_thm] using h)
    (by krfl)

theorem henv11 : ProgEnv (.thmInfo resp_thm :: .defnInfo swapR_def :: .defnInfo orB_def ::
    .defnInfo orB_match_1 :: .defnInfo NV1.B_casesOn :: .defnInfo Prod_snd :: .defnInfo Prod_fst ::
    IndBlock.decls IsPr CsPr RsPr ++ P0) ζ11 E11 B11 :=
  ProgEnv.thm henv10 (by decide) (by decide) rfl resp_fresh tr_respTy
    (respTyM_typed wf10 t_b10 t_p10 t_e10 t_f10t t_s10t t_o10t t_w10t)

/-! ## `orU`, `useTF`, `useFT` -/

theorem tr_liftF : TrM E11 B11 [] .nil [] liftF (liftFM b11 p11 f11 sn11 o11) :=
  TrM.lam (tr_tP rfl rfl) (tr_orB rfl (tr_fst rfl rfl (TrM.bvar rfl)) (tr_snd rfl rfl (TrM.bvar rfl)))

theorem tr_orUVal : TrM E11 B11 [] .nil [] orUVal (orUValM b11 p11 e11 q11 f11 sn11 o11 w11 h11) := by
  have h := TrM.special (E := E11) (B := B11) (lps := []) (Γ := .nil) (Δ := []) (c := `Quot.lift)
    (us := [l1, l1]) (as := [tP, .const `swapR [], tB, liftF, .const `orU._proof_1 []])
    (as' := [tPM b11 p11, swapM w11, mB b11, liftFM b11 p11 f11 sn11 o11, .const h11 Fin.elim0])
    (b := .quot q11 .lift) rfl rfl rfl
    (by
      intro i x x' h1 h2
      rcases i with _ | _ | _ | _ | _ | i <;> simp at h1 h2 <;> subst h1 h2
      · exact tr_tP rfl rfl
      · exact tr_const0 rfl
      · exact tr_B rfl
      · exact tr_liftF
      · exact tr_const0 rfl)
    (SatTr.quotEta (t₀ := liftEtaM e11 q11) rfl (by decide) rfl)
  exact trM_eq h rfl

theorem henv12 : ProgEnv (.defnInfo orU_def :: .thmInfo resp_thm :: .defnInfo swapR_def ::
    .defnInfo orB_def :: .defnInfo orB_match_1 :: .defnInfo NV1.B_casesOn :: .defnInfo Prod_snd ::
    .defnInfo Prod_fst :: IndBlock.decls IsPr CsPr RsPr ++ P0) ζ12 E12 B12 :=
  ProgEnv.defn henv11 (by decide) (by decide) rfl rfl
    (TrM.forallE (tr_quot rfl trLevel_l1 (tr_tP rfl rfl) (tr_const0 rfl)) (tr_B rfl)) tr_orUVal

section TrUse
variable {ζ : Sigs} {E : Env ζ} {B : Binds ζ} {ηB : Head ζ (.inductive bSig)}
  {ηP : Head ζ (.inductive ppSig)} {ηQ : Head ζ .quot} {ηW ηU : Head ζ (.const .def 0)}

theorem tr_useVal (hB : B `B = some (.ind ηB 0)) (hP : B `Prod = some (.ind ηP 0))
    (hmk : B `Prod.mk = some (.ctor ηP 0 0 [0, 1])) (hq : B `Quot.mk = some (.quot ηQ .ctor))
    (hw : B `swapR = some (.const ηW)) (hu : B `orU = some (.const ηU)) {a b : Lean.Expr}
    {a' b' : Metalean.Expr ζ 0 0} (ha : TrM E B [] .nil [] a a') (hb : TrM E B [] .nil [] b b') :
    TrM E B [] .nil [] (useVal a b) (useValM ηB ηP ηQ ηW ηU a' b') :=
  TrM.app (notSpecial_const hu ⟨_, rfl⟩) (tr_const0 hu)
    (TrM.special (c := `Quot.mk) (us := [l1]) (as := [tP, .const `swapR [], pairB a b])
      (as' := [tPM ηB ηP, swapM ηW, pairM ηB ηP a' b']) hq rfl rfl
      (by
        intro i x x' h1 h2
        rcases i with _ | _ | _ | i <;> simp at h1 h2 <;> subst h1 h2
        · exact tr_tP hB hP
        · exact tr_const0 hw
        · exact tr_Prmk hmk rfl rfl (tr_B hB) (tr_B hB) ha hb)
      (SatTr.quotMk (rest := []) rfl))

end TrUse

theorem henv13 : ProgEnv (.defnInfo useTF_def :: .defnInfo orU_def :: .thmInfo resp_thm ::
    .defnInfo swapR_def :: .defnInfo orB_def :: .defnInfo orB_match_1 :: .defnInfo NV1.B_casesOn ::
    .defnInfo Prod_snd :: .defnInfo Prod_fst :: IndBlock.decls IsPr CsPr RsPr ++ P0) ζ13 E13 B13 :=
  ProgEnv.defn henv12 (by decide) (by decide) rfl rfl (tr_B rfl)
    (tr_useVal rfl rfl rfl rfl rfl rfl (tr_T rfl) (tr_F rfl))

theorem henv14 : ProgEnv P ζ14 E14 B14 :=
  ProgEnv.defn henv13 (by decide) (by decide) rfl rfl (tr_B rfl)
    (tr_useVal rfl rfl rfl rfl rfl rfl (tr_F rfl) (tr_T rfl))

/-! ## The premises -/

/-- The erased term `useTF` in Metalean. -/
def tE : Metalean.Expr ζ14 0 0 := .const t14 Fin.elim0

/-- The Metalean environment of NV-QP. -/
abbrev E : Env ζ14 := E14
/-- The name table of NV-QP. -/
abbrev B : Binds ζ14 := B14

/-- `henv`: the program is the Lean form of `E` with table `B`. -/
theorem henv : ProgEnv P ζ14 E B := henv14

/-- `hwf`: `E` is well formed. -/
theorem hwf : EnvWF E := wf14

/-- `he`: the erased term is the Lean form of `tE`. -/
theorem he : TrM E B [] .nil [] e tE := tr_const0 rfl

theorem tE_typed : E[.nil] ⊢ tE : mB b14 :=
  const_typed wf14 t14 Fin.elim0 (by rw [t_t14t]; qsx)

/-- `hty`: `tE` is typed. -/
theorem hty : ∃ T, E[.nil] ⊢ tE : T := ⟨_, tE_typed⟩

end EraseProof.Test.NVQP
