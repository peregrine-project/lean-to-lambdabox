import LeanToLambdaBox.ErasesEnv
import LeanToLambdaBox.ErasureRun

/-!
# `SpecEnv` — the specification environment of a run state

`SpecEnv env bo s Γspec` says `Γspec` is a specification environment adequate for the
erasure state `s`: its entries are `ErasesDecl`-justified, every constant `s` registered
is declared in it, and every inductive `s` registered contributes its block, constructor
and eliminator entries.

The state occurs only through the *domain* of the two registries, so the predicate is
antitone in it: `SpecEnv.mono` re-reads one environment at every smaller state a run
passes through. That is what lets sibling sub-runs be threaded under one universally
quantified `Γspec` instead of merging environments.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean Erasure

/--
`Γspec` is a specification environment for the run state `s`.

`keys` and `decls` are `ErasesEnv`'s first two clauses; the last three are the coverage
the state demands. An eliminator entry is demanded only for an informative inductive —
`ErasesDecl.elim` declares no other, because the emitted `.case` of a non-informative one
is stuck on every value a run produces.
-/
structure SpecEnv (env : VEnv) (bo : Name → Option Expr) (s : ErasureState)
    (Γspec : GlobalDeclarations) : Prop where
  /-- The keys of `Γspec` are distinct. -/
  keys : (Γspec.map Prod.fst).Nodup
  /-- Every declaration `Γspec` answers with is `ErasesDecl`-justified. -/
  decls : ∀ kn d, LBTerm.envLookup Γspec kn = some d → ErasesDecl env bo kn d
  /-- Every registered constant is declared, at its canonical kername. -/
  consts : ∀ n : Name, (s.constants.get? n).isSome →
    (LBTerm.envLookup Γspec (toKername n)).isSome
  /-- Every registered inductive contributes its block declaration. -/
  inds : ∀ n : Name, (s.inductives.get? n).isSome →
    ∃ iid np nfs, IndInfo env n iid np nfs ∧
      (LBTerm.envLookup Γspec iid.mutualBlockName).isSome
  /-- Every constructor of a registered inductive is declared. -/
  ctors : ∀ n : Name, (s.inductives.get? n).isSome →
    ∀ c k, CtorOf env c n k → (LBTerm.envLookup Γspec (toKername c)).isSome
  /-- The `casesOn` eliminator of a registered informative inductive is declared. -/
  elims : ∀ n : Name, (s.inductives.get? n).isSome →
    ∀ kn, CasesOnOf env n kn → InformativeInd env n →
      (LBTerm.envLookup Γspec kn).isSome

/-- `SpecEnv` is antitone in the run state: an environment adequate for a state is
adequate for every state below it. The proof is `StateLe`'s two domain clauses. -/
theorem SpecEnv.mono {env : VEnv} {bo : Name → Option Expr} {s₁ s : ErasureState}
    {Γspec : GlobalDeclarations} (h : StateLe s₁ s) (H : SpecEnv env bo s Γspec) :
    SpecEnv env bo s₁ Γspec where
  keys := H.keys
  decls := H.decls
  consts n hn := H.consts n (h.consts hn)
  inds n hn := H.inds n (h.inds hn)
  ctors n hn := H.ctors n (h.inds hn)
  elims n hn := H.elims n (h.inds hn)

/-- A specification environment of a state is a specification environment of any program
whose reachable kernames it declares and whose reached compiler bodies it holds erasures
of. Those two clauses are the ones that mention a program, so they are premises: the state
records which constants a run consulted, not what a given program reaches. -/
theorem SpecEnv.erasesEnv {env : VEnv} {bo : Name → Option Expr} {s : ErasureState}
    {Γspec : GlobalDeclarations} (H : SpecEnv env bo s Γspec) {t : LBTerm}
    (hdeps : ∀ kn, ReachableFrom Γspec t kn → (LBTerm.envLookup Γspec kn).isSome)
    (hdefns : ∀ c b, bo c = some b → ReachableFrom Γspec t (toKername c) →
      ∃ b₀, LBTerm.envLookup Γspec (toKername c) = some (.constantDecl ⟨some b₀⟩) ∧
        ∀ Us' ups us, Erases env Us' [] (b.instantiateLevelParams ups us) b₀) :
    ErasesEnv env bo Γspec t :=
  .mk H.keys H.decls hdeps hdefns

/-- The four-entry fixture is a specification environment for the initial state, whose
registries are empty. Read with `SpecEnv.mono`, it is one for every state below any state
it is read at. -/
theorem demoEnv_specEnv {env : VEnv} {bo : Name → Option Expr} (h : DemoSource env bo) :
    SpecEnv env bo {} demoEnv where
  keys := demoEnv_keys
  decls := demoEnv_decls h
  consts n hn := by simp at hn
  inds n hn := by simp at hn
  ctors n hn := by simp at hn
  elims n hn := by simp at hn

end LeanToLambdaBox
