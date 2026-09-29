import EraseProof.Env

/-!
# The evaluation environment

The environment the source semantics evaluates in: the program's declarations, and the constants
the configuration remaps to foreign code, which evaluation does not unfold. `EvalEnv.unfold?` is
the δ rule's lookup: the value of a definition or theorem that is not remapped.
-/

open Lean

namespace EraseProof

/-- The program's environment as evaluation sees it: MetaRocq's `cst_body` view of `Σ`, with the
configuration's `@[extern]` remapping. Reference: the environment of `MR P/PCUICWcbvEval.v:231
eval` (`declared_constant`, `cst_body`), DV-12. -/
structure EvalEnv where
  decls : List ConstantInfo
  axiomatized : ConstantInfo → Bool

/-- Unfoldable constants: definitions and theorems that the configuration does not remap;
axioms and opaques have no δ rule (DV-10). Reference: the premise `cst_body decl = Some body` of
`eval_delta` (`MR P/PCUICWcbvEval.v:247`). -/
def EvalEnv.unfold? (σ : EvalEnv) (c : Name) : Option (ConstantInfo × Expr) :=
  match findDecl σ.decls c with
  | some ci@(.defnInfo v) => if σ.axiomatized ci then none else some (ci, v.value)
  | some ci@(.thmInfo v) => if σ.axiomatized ci then none else some (ci, v.value)
  | _ => none

/-- An unfoldable constant is the first declaration of its name, and a definition or a theorem.
Reference: the premises `declared_constant` and `cst_body decl = Some body` of `eval_delta`
(`MR P/PCUICWcbvEval.v:247`). -/
theorem EvalEnv.unfold?_some {σ : EvalEnv} (hu : σ.unfold? c = some (ci, b)) :
    findDecl σ.decls c = some ci ∧ ((∃ v, ci = .defnInfo v) ∨ ∃ v, ci = .thmInfo v) := by
  unfold EvalEnv.unfold? at hu
  split at hu
  · split at hu
    · cases hu
    · cases hu; exact ⟨‹_›, .inl ⟨_, rfl⟩⟩
  · split at hu
    · cases hu
    · cases hu; exact ⟨‹_›, .inr ⟨_, rfl⟩⟩
  · cases hu

end EraseProof
