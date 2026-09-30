import EraseProof.Core.Block

/-!
# The shipping core's correctness

`erasePure_erases`: the output of the shipping traversal run at the pure backend
(`Erasure.erasePure`, `LeanToLambdaBox/Erasure/Pure.lean`) on a translated closed term is an erasure
of it (`Erases`) whose λ□ dependencies are erased (`ErasesDeps`), in a λ□ environment whose
recursive blocks are erased (`BlocksErased`) and whose bodies are closed (`LenvClosed`).

The proof is an induction on the traversal's fuel (`traversal_spec`): at every fuel, `visitExpr`
meets `ExprSpec` and `visitMutual` meets `MutualSpec`, one step per case of the traversal
(`Core/Steps.lean`; the recursive blocks in `Core/Block.lean`). `erasePure` runs `visitExpr` at
`Erasure.travFuel` from the empty state, with no locals and no fix variables
(`visitExpr_initial`), over the closure that `collectDeps` computes, whose properties
(`collectDeps_spec`, `collectDeps_sub`) make up `CoreEnv`.

Reference: `erases_erase` (`MR E/ErasureFunction.v:1228`) with `erase_global_erases_deps`
(`MR E/ErasureFunctionProperties.v:172`) and `erase_constant_body` (`MR E/ErasureFunction.v:1309`);
MetaCoq paper §7.3, p. 8:62; Letouzey Lemma 11 (𝓔 ⊆ ◀). The traversal is fuelled and the
theorem is about its successful runs (DV-17); its output is not `expanded_eprogram` (DV-9).
-/

open Lean Lean4Lean Erasure

namespace EraseProof

section
variable {venv : VEnv} {P decls : List ConstantInfo} {view : EnvView} {cfg : ErasureConfig}

/-- The fuel induction of `erasePure_erases`: over a closure `decls` of a program `P` (`CoreEnv`),
at every fuel, every run of `visitExpr` meets `ExprSpec` and every run of `visitMutual` meets
`MutualSpec`. A run at fuel `0` fails; at fuel `n + 1` each case of the traversal is one step
lemma, from the statement at the fuels up to `n`. Reference: the induction of `erases_erase`
(`MR E/ErasureFunction.v:1228`) over `erase` (`MR E/ErasureFunction.v:989`), together with
`erase_global_erases_deps` (`MR E/ErasureFunctionProperties.v:172`); the fuel replaces the
well-founded recursion of `erase` (DV-17). -/
theorem traversal_spec (hG : CoreEnv venv P decls) (n : Nat) :
    (∀ e, ExprSpec venv view cfg decls n e) ∧ ∀ c, MutualSpec venv view cfg decls n c := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  cases n with
  | zero =>
    exact ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrun => (nomatch hrun),
      fun _ _ _ _ _ _ _ _ _ _ _ _ hrun => (nomatch hrun)⟩
  | succ k =>
    have ihE : ∀ m ≤ k, ∀ e, ExprSpec venv view cfg decls m e :=
      fun m hm => (ih m (Nat.lt_succ_of_le hm)).1
    have ihM : ∀ m ≤ k, ∀ c, MutualSpec venv view cfg decls m c :=
      fun m hm => (ih m (Nat.lt_succ_of_le hm)).2
    refine ⟨fun e => ?_, fun c => ?_⟩
    · cases e with
      | fvar => exact visitExpr_fvar_step hG
      | lam => exact visitExpr_lam_step hG ihE
      | letE => exact visitExpr_letE_step hG ihE
      | app => exact visitExpr_app_step hG ihE ihM
      | const => exact visitExpr_const_step hG ihE ihM
      | mdata => exact visitExpr_mdata_step hG ihE
      | _ => exact visitExpr_other_step hG rfl
    · intro S st tc ps st' ps' hsc hc
      obtain ⟨ci, hci, -⟩ := hsc c hc
      by_cases hb : ∃ v, ci.value? (allowOpaque := true) = some v ∧
          axiomatized view cfg ci = false ∧ RecursiveDecl ci = true
      · obtain ⟨v, hv, hax, hrec⟩ := hb
        exact visitMutual_rec_step hG ihE hci hv hax hrec hsc hc
      · refine visitMutual_nonrec_step hG ihE hci (fun v hv hax => ?_) hsc hc
        cases h : RecursiveDecl ci
        · rfl
        · exact absurd ⟨v, hv, hax, h⟩ hb

/-- The run that `erasePure` performs: `visitExpr` at `Erasure.travFuel` from the empty state,
with no locals and no fix variables, on a closed translated term whose constants are declared in
the closure `decls`. Its result is an erasure of the term with the registered constants as the
only targets (`RecIn`), its λ□ dependencies are erased, and the final λ□ environment has erased
blocks and closed bodies. It is `traversal_spec` at the initial context (`CtxOK` with no targets
and the empty context), the scope of all declared constants (`ScopeOK` by `DepClosed`) and the
empty state (`StateOK.empty`); the final `StateOK` gives `BlocksErased` (with `KernameInj`) and
`LenvClosed`. Reference: `erases_erase` (`MR E/ErasureFunction.v:1228`) in the empty context,
with `erase_global_erases_deps` (`MR E/ErasureFunctionProperties.v:172`) for the environment that
`erase_global_deps` (`MR E/ErasureFunction.v:1602`) returns. -/
theorem visitExpr_initial (hG : CoreEnv venv P decls)
    {Us : List Name} {e : Expr} {e' : VExpr} {t : LBTerm} {s : ErasureState} {ps : PureState}
    (he : TrS venv Us [] e e') (hcs : ConstsIn (fun c => (findDecl decls c).isSome) e)
    (hrun : (visitExpr (m := PureM) travFuel e).runPure {} { «config» := cfg } ⟨decls, view⟩ {} =
      .ok ((t, s), ps)) :
    Erases venv Us (evalEnvOf view cfg decls).isAtom (RecIn s.gdecls) [] e t ∧
      ErasesDeps venv (evalEnvOf view cfg decls) s.gdecls t ∧
      BlocksErased venv (evalEnvOf view cfg decls) s.gdecls ∧ LenvClosed s.gdecls := by
  have hctx : CtxOK venv Us (fun _ _ => False) cfg { «config» := cfg } [] {} :=
    ⟨.nil, (fun _ _ h => nomatch h), (fun _ _ h => h.elim), (fun _ _ h => nomatch h), rfl⟩
  have hsc : ScopeOK decls (fun c => (findDecl decls c).isSome) := by
    intro c hc
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.1 hc
    have hd := hG.deps ci (List.mem_of_find?_eq_some hci)
    exact ⟨ci, hci, hd.2.2, fun v hv d hdv => (hd.2.1 v hv).occursV hdv⟩
  obtain ⟨her, hdeps, hgr⟩ := (traversal_spec hG travFuel).1 e hctx hsc
    (fun c hc => .inl (hcs.occursV hc)) StateOK.empty he hrun
  exact ⟨her.mono_rc fun _ _ h => h.elim, hdeps, hgr.ok.blocksErased hG.inj, hgr.ok.closed⟩

end

section
variable {venv : VEnv} {P decls : List ConstantInfo}

/-- Function-level lemma: the output of the shipping traversal on the pure backend is an erasure
of the input whose dependencies are erased, in a closed λ□ environment. Reference: `erases_erase`
(`MR E/ErasureFunction.v:1228`) with `erase_global_erases_deps`
(`MR E/ErasureFunctionProperties.v:172`) and `erase_constant_body` (`MR E/ErasureFunction.v:1309`);
MC §7.3, p. 8:62; Let. Lemma 11 (𝓔 ⊆ ◀). -/
theorem erasePure_erases {view : EnvView} {cfg : ErasureConfig} {p : Program}
    {inl : List Kername} (henv : ProgEnv P venv) (hview : ViewAgrees view P)
    (he : TrS venv Us [] e e') (hdecls : collectDeps view e = .ok decls)
    (hrun : erasePure view cfg decls e = .ok (p, inl)) :
    ∃ lenv t, p = .untyped lenv (some t) ∧
      Erases venv Us (evalEnvOf view cfg decls).isAtom (RecIn lenv) [] e t ∧
      ErasesDeps venv (evalEnvOf view cfg decls) lenv t ∧
      BlocksErased venv (evalEnvOf view cfg decls) lenv ∧ LenvClosed lenv := by
  obtain ⟨hinj, -, -, hdc, hcl, hcs⟩ := collectDeps_spec hdecls
  have hG : CoreEnv venv P decls := ⟨henv, collectDeps_sub henv hview he hdecls, hinj, hcl, hdc⟩
  obtain ⟨⟨⟨t, s⟩, ps⟩, hx, hp⟩ := Except.ok_of_bind hrun
  cases hp
  exact ⟨s.gdecls, t, rfl, visitExpr_initial hG he hcs hx⟩

end

end EraseProof
