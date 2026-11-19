import EraseProof.Simulation.Cases
import EraseProof.Simulation.Quot
import EraseProof.Simulation.Rec
import EraseProof.Statements

/-!
# The relation-level simulation

`erases_correct` (`MR E/ErasureCorrectness.v:51`), by induction on the source evaluation `e ⇓ v`
with the motive `ErasesSim`: every erasure of `e`, with erased dependencies, evaluates in λ□ to an
erasure of `v`. Each rule is its case lemma (`Simulation/Cases.lean`, `Simulation/Ind.lean`,
`Simulation/Quot.lean`, `Simulation/Rec.lean`). Every alternative of a `casesOn` is a λ under its
field binders, so the ι cases use the motive at the alternative applied to the fields itself, and
the motive needs no strengthening to head-β-reducts. Adapted from `ML-V Simulation/Main.lean`.
-/

open Lean Erasure

namespace EraseProof

open SimCases

/-- The relation-level simulation: an erasure, with erased dependencies, of a marked source term
that evaluates, evaluates in λ□ to an erasure of the source value. Adapted from
`ML-V Simulation/Main.lean:218`. Reference: `erases_correct` (`MR E/ErasureCorrectness.v:51`); MC
§7.3, Thm 7.3. -/
theorem erases_correct : erases_correct_statement := by
  intro env σ lenv ê v tb hinj hbinj _ hcl hnat hnc hrs _ her hdeps hev
  suffices h : ErasesSim σ lenv ê v from h her hdeps
  clear her hdeps
  induction hev with
  | beta hns _ _ hok _ ihf iha ihb => exact erases_correct_beta hns hok ihf iha ihb
  | etaBeta hns _ _ hok _ ihf iha ihb => exact erases_correct_etaBeta hns hok ihf iha ihb
  | zeta _ _ hok _ ihv ihb => exact erases_correct_zeta hok ihv ihb
  | delta hu hm _ ih => exact erases_correct_delta hinj hu hm ih
  | constAtom ha => exact erases_correct_constAtom ha
  | ctor hc hl hlv _ _ ih => exact erases_correct_ctor hbinj hcl hc hl hlv ih
  | casesIota hco hlen hm hmv hcv hok _ halt _ ihm ihalt =>
    exact erases_correct_casesIota hbinj hcl hco hlen hm hmv hcv hok halt ihm ihalt
  | casesLitZero hco hn hlen hm hmv _ _ halt _ ihm ihalt =>
    exact erases_correct_casesLitZero hbinj hnat hco hn hlen hm hmv halt ihm ihalt
  | casesLitSucc hco hn hlen hm hmv _ _ halt _ ihm ihalt =>
    exact erases_correct_casesLitSucc hbinj hnat hco hn hlen hm hmv halt ihm ihalt
  | casesFrozen hco hlen hcs hcn hm _ _ halt _ ih =>
    exact erases_correct_casesFrozen hco hlen hcs hcn hm halt ih
  | quotMk hc hk _ _ iha => exact erases_correct_quotMk hc hk iha
  | quotLift hc hk _ _ hc' hk' hok _ ihf ihq ihb =>
    exact erases_correct_quotLift hc hk hc' hk' hok ihf ihq ihb
  | recIota hcr hall _ hblk hni hshape hihs hps hms hmins hlm _ _ hcv hmi hmk hok hrfs hrl _ _
      ihm ihmaj ihih ihv =>
    exact erases_correct_recIota hbinj hcl hnat hnc hrs hcr hall hblk hni hshape hihs hps hms
      hmins hlm hcv hmi hmk hok hrfs hrl ihm ihmaj ihih ihv
  | proj _ hcv hfs _ ihe => exact erases_correct_proj hbinj hcl hcv hfs ihe
  | projFrozen hp _ _ ihe => exact erases_correct_projFrozen hbinj hp ihe
  | lit _ => exact erases_correct_lit hbinj hnat
  | appCong hns hf hnb _ _ ihf _ => exact erases_correct_appCong hns hf hnb ihf
  | atom ha => exact erases_correct_atom ha
  | etaLam => exact erases_correct_etaLam
  | frozen _ => exact erases_correct_frozen
  | frozenApp hns _ _ _ _ ihf iha => exact erases_correct_frozenApp hns ihf iha

end EraseProof
