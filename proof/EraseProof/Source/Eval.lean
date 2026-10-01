import EraseProof.Atoms

/-!
# The source semantics

`SrcEval σ e v`: weak call-by-value, big-step evaluation of closed Lean terms in the evaluation
environment `σ`, after PCUIC's `eval` (`MR P/PCUICWcbvEval.v:231`). Recursion lives in constants:
a recursive constant (`RecursiveDecl`) is a value that unfolds when applied, as a PCUIC `tFix` with
`rarg = 0`; atom constants (`EvalEnv.isAtom`) are values; other constants without a δ rule are
stuck. `SrcEval.value`: every result is a value (`SrcValue`).
-/

open Lean Erasure

namespace EraseProof

/-- Occurrence of a name in value positions (constants, λ bodies, applications, `let` values and
bodies, `mdata`): the syntactic self-reference test that makes a declaration recursive.
Reference: none (DV-7). -/
def OccursV (n : Name) : Expr → Bool
  | .const n' _ => n == n'
  | .lam _ _ e _ | .mdata _ e | .proj _ _ e => OccursV n e
  | .app a b | .letE _ _ a b _ => OccursV n a || OccursV n b
  | _ => false

/-- A declaration is recursive when it belongs to a block of several members or mentions itself in
a value position: the constants the eraser compiles to `tFix`. Reference: none; the counterpart of
a `tFix` value (`MR P/PCUICWcbvEval.v:51 atom`), DV-7. -/
def RecursiveDecl (ci : ConstantInfo) : Bool :=
  ci.all.length != 1 || OccursV ci.name (ci.value! (allowOpaque := true))

/-- λ, sort, Π. Reference: `MR P/PCUICWcbvEval.v:51 atom` (`tLambda`, `tSort`, `tProd`). -/
def SrcAtom : Expr → Prop
  | .lam .. | .sort _ | .forallE .. => True
  | _ => False

/-- Heads excluded by `appCong`: λ, arity heads and recursive constants. Reference: the side
condition of `eval_app_cong` (`MR P/PCUICWcbvEval.v:311`: `~~ (isLambda f' || isFixApp f' ||
isArityHead f' || isConstructApp f' || isPrimApp f')`). -/
def BlocksCong (σ : EvalEnv) : Expr → Prop
  | .lam .. | .sort _ | .forallE .. => True
  | .const c _ => ∃ ci b, σ.unfold? c = some (ci, b) ∧ RecursiveDecl ci = true
  | _ => False

/-- Weak call-by-value evaluation of closed source terms. A recursive constant is a value that
unfolds when applied (PCUIC `tFix` with `rarg = 0`, DV-7); an atom constant is a value (DV-11);
other δ-less constants are stuck (DV-10, DV-12). Reference: `MR P/PCUICWcbvEval.v:231 eval`;
MC §5.6; Let. Def. 9 (weak reductions), call-by-value instance (DV-22). -/
inductive SrcEval (σ : EvalEnv) : Expr → Expr → Prop
  /-- `eval_beta` (`MR P/PCUICWcbvEval.v:234`). -/
  | beta : SrcEval σ f (.lam n A b bi) → SrcEval σ a a' → SrcEval σ (b.instantiate1' a') v →
      SrcEval σ (.app f a) v
  /-- `eval_zeta` (`MR P/PCUICWcbvEval.v:241`). -/
  | zeta : SrcEval σ val val' → SrcEval σ (b.instantiate1' val') v →
      SrcEval σ (.letE n T val b nd) v
  /-- `eval_delta` (`MR P/PCUICWcbvEval.v:247`), non-recursive constants. -/
  | delta : σ.unfold? c = some (ci, body) → RecursiveDecl ci = false →
      SrcEval σ (Pure.instLevels ci.levelParams us body) v → SrcEval σ (.const c us) v
  /-- `eval_delta` to a `tFix` value (`MR P/PCUICWcbvEval.v:247`, `:51`). -/
  | fixAtom : σ.unfold? c = some (ci, body) → RecursiveDecl ci = true →
      SrcEval σ (.const c us) (.const c us)
  /-- `eval_fix` (`MR P/PCUICWcbvEval.v:273`) with `rarg = 0`, `argsv = []`. -/
  | fixApp : SrcEval σ f (.const c us) → σ.unfold? c = some (ci, body) →
      RecursiveDecl ci = true → SrcEval σ a a' →
      SrcEval σ (.app (Pure.instLevels ci.levelParams us body) a') v → SrcEval σ (.app f a) v
  /-- `eval_atom` on `tInd`/propositional `tConstruct` (`MR P/PCUICWcbvEval.v:331`, `:51`). -/
  | constAtom : findDecl σ.decls c = some ci → σ.isAtom c = true →
      SrcEval σ (.const c us) (.const c us)
  /-- `eval_app_cong` (`MR P/PCUICWcbvEval.v:311`). -/
  | appCong : SrcEval σ f f' → ¬ BlocksCong σ f' → SrcEval σ a a' →
      SrcEval σ (.app f a) (.app f' a')
  /-- Metadata is transparent (Lean syntax). -/
  | mdata : SrcEval σ e v → SrcEval σ (.mdata d e) v
  /-- `eval_atom` (`MR P/PCUICWcbvEval.v:331`) on λ, sort, Π. -/
  | atom : SrcAtom e → SrcEval σ e e

/-- Spines headed by an atom constant. Reference: `mkApps (tInd …) args` and propositional
`mkApps (tConstruct …) args` values (`MR P/PCUICWcbvEval.v:500 value`), DV-11. -/
inductive AtomSpine (σ : EvalEnv) : Expr → Prop
  | const : σ.isAtom c = true → AtomSpine σ (.const c us)
  | app : AtomSpine σ f → AtomSpine σ (.app f a)

/-- The shapes of source values. Reference: `MR P/PCUICWcbvEval.v:500 value`; MC §5.6, Fig. 12. -/
inductive SrcValue (σ : EvalEnv) : Expr → Prop
  | lam : SrcValue σ (.lam n A b bi)
  | sort : SrcValue σ (.sort u)
  | forallE : SrcValue σ (.forallE n A B bi)
  | fixConst : σ.unfold? c = some (ci, b) → RecursiveDecl ci = true → SrcValue σ (.const c us)
  | spine : AtomSpine σ e → SrcValue σ e

section
variable {σ : EvalEnv}

/-- Evaluation results are values. Reference: `eval_to_value` (`MR P/PCUICWcbvEval.v:570`); MC
§5.6, Fig. 12. -/
theorem SrcEval.value (hev : SrcEval σ e v) : SrcValue σ v := by
  induction hev with
  | beta _ _ _ _ _ ih => exact ih
  | zeta _ _ _ ih => exact ih
  | delta _ _ _ ih => exact ih
  | fixAtom hu hr => exact .fixConst hu hr
  | fixApp _ _ _ _ _ _ _ ih => exact ih
  | constAtom _ ha => exact .spine (.const ha)
  | appCong _ hb _ ihf =>
    cases ihf with
    | lam => exact absurd trivial hb
    | sort => exact absurd trivial hb
    | forallE => exact absurd trivial hb
    | fixConst hu hr => exact absurd ⟨_, _, hu, hr⟩ hb
    | spine hs => exact .spine (.app hs)
  | mdata _ ih => exact ih
  | atom ha =>
    rename_i e
    cases e with
    | lam => exact .lam
    | sort => exact .sort
    | forallE => exact .forallE
    | _ => exact False.elim ha

end

end EraseProof
