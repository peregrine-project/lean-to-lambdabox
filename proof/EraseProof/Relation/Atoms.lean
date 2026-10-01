import EraseProof.Relation.Basic
import EraseProof.Source.Eval

/-!
# Erasures of atom spines

An atom constant has no rule of `Erases` but `Erases.box`, so the erasure of an atom spine
`c a₁ … aₙ` is headed by `□` (`Erases.headOf_atomSpine`). A λ□ evaluation result headed by `□` is
`□` (`LBEval.eq_box_of_headOf`). Together: an erasure of an atom spine that is a λ□ evaluation
result is `□` (`Erases.atomSpine_box`), as for the `tInd`-headed values of PCUIC.
-/

open Lean Lean4Lean Erasure

namespace EraseProof

section
variable {venv : VEnv} {σ : EvalEnv} {lenv : GlobalDeclarations}

/-- A λ□ evaluation result headed by `□` is `□`. Reference: `eval_to_mkApps_tBox_inv`
(`MR E/EWcbvEval.v:985`), with `headOf` in place of `mkApps`. -/
theorem LBEval.eq_box_of_headOf (hev : LBEval fl lenv s t) (hh : headOf t = .box) :
    t = .box := by
  have hm : ∀ (h : LBTerm) (as : List LBTerm), headOf (mkApps h as) = headOf h := by
    intro h as
    induction as generalizing h with
    | nil => rfl
    | cons a as ih => exact ih (.app h a)
  induction hev using LBEval.ind with
  | box => rfl
  | beta _ _ _ _ _ ih => exact ih hh
  | zeta _ _ _ ih => exact ih hh
  | iota _ _ _ _ _ _ _ _ ih => exact ih hh
  | iotaBlock _ _ _ _ _ _ _ _ ih => exact ih hh
  | iotaSing _ _ _ _ _ _ ih => exact ih hh
  | fix _ _ _ _ _ _ _ ih => exact ih hh
  | fixValue => simp only [headOf, hm] at hh; cases hh
  | fix' _ _ _ _ _ _ _ ih => exact ih hh
  | delta _ _ _ ih => exact ih hh
  | proj _ _ _ _ _ _ _ ih => exact ih hh
  | projBlock _ _ _ _ _ _ _ ih => exact ih hh
  | projProp => rfl
  | construct => simp only [headOf, hm] at hh; cases hh
  | constructBlock => cases hh
  | @appCong _ f' _ _ _ hb _ ihf =>
    have hf : f' = .box := ihf hh
    subst hf
    simp [isBoxT] at hb
  | prim => cases hh
  | atom ha =>
    rename_i t
    cases t with
    | box => rfl
    | app => simp [lbAtom] at ha
    | _ => cases hh

/-- An erasure of an atom spine is headed by `□`: an atom constant `c` (`σ.isAtom c = true`) has
no rule of `Erases` but `Erases.box`, since `Erases.const` and `Erases.constRec` need
`σ.isAtom c = false`. Reference: `erases_mkApps_inv` (`MR E/ErasureProperties.v:105`) for
`tInd`-headed terms, which erase only by `erases_box` (`MR E/Extract.v:140`); DV-11. -/
theorem Erases.headOf_atomSpine (hsp : AtomSpine σ e)
    (h : Erases venv Us σ.isAtom rc Δ e t) : headOf t = .box := by
  induction hsp generalizing t with
  | const ha =>
    cases h with
    | const hc => exact nomatch ha.symm.trans hc
    | constRec hc _ => exact nomatch ha.symm.trans hc
    | box _ => rfl
  | app _ ih =>
    cases h with
    | app hf _ =>
      have hh := ih hf
      exact hh
    | box _ => rfl

/-- An erasure of an atom spine that is an evaluation result is `□`. Reference: none directly;
the analogue of `tInd`-headed values, which erase only by `erases_box` (`MR E/Extract.v:140`);
DV-11. -/
theorem Erases.atomSpine_box (hsp : AtomSpine σ e) (h : Erases venv Us σ.isAtom rc [] e t)
    (hv : LBEval defaultFlags lenv s t) : t = .box :=
  LBEval.eq_box_of_headOf hv (Erases.headOf_atomSpine hsp h)

end

end EraseProof
