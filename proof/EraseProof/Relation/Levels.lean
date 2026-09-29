import EraseProof.Relation.Basic
import EraseProof.Typing.InstLevels
import EraseProof.Erasability
import EraseProof.Env

/-!
# Universe instantiation of the erasure relation

A constant's body is erased once, at its level parameters `ps`; the source semantics' δ rule
instantiates it at the occurrence's levels `us` with the shipping `Erasure.Pure.instLevels`.
`Erases.instLevels` says that the erasure of the body is also an erasure of the instantiated body,
in the instantiated context: the λ□ side does not mention levels, the translation premises follow
from `TrS.instLevels`, and the `□` rule from `IsErasable.instL`. No hypothesis on the environment is
needed: lean4lean's `IsDefEq.instL` holds in any environment.
-/

open Lean Lean4Lean Erasure

namespace EraseProof

section
variable {venv : VEnv} {P : List ConstantInfo}

-- `henv` stands for the reference's `wf Σ.1`; the model's `IsDefEq.instL` does not need it.
set_option linter.unusedVariables false in
/-- The relation is stable under universe instantiation, under binders (`Δ.instL`). Reference:
`erases_subst_instance_decl` (`MR E/ErasureProperties.v:412`). -/
theorem Erases.instLevels (henv : ProgEnv P venv)
    (hus : us.mapM (VLevel.ofLevel Us) = some us') (hlen : us.length = ps.length)
    (h : Erases venv ps ac rc Δ b t) :
    Erases venv Us ac rc (Δ.instL us') (Pure.instLevels ps us b) t := by
  have hls : ∀ l ∈ us', l.WF Us.length := VLevel.WF.of_mapM_ofLevel hus
  induction h with
  | bvar => exact .bvar
  | fvar => exact .fvar
  | lam hA _ ih => exact .lam (hA.instLevels hus hlen) ih
  | letE hT hv _ _ ihv ihb =>
    exact .letE (hT.instLevels hus hlen) (hv.instLevels hus hlen) ihv ihb
  | app _ _ ihf iha => exact .app ihf iha
  | const hc => exact .const hc
  | constRec hc hr => exact .constRec hc hr
  | mdata _ ih => exact .mdata ih
  | box hb =>
    obtain ⟨e', he', he'E⟩ := hb
    refine .box ⟨_, he'.instLevels hus hlen, ?_⟩
    rw [VLCtx.instL_toCtx]
    exact he'E.instL hls

end

end EraseProof
