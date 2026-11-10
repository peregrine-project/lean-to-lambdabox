import EraseProof.Source.EvalEnv
import LeanToLambdaBox.Erasure.Pure

/-!
# Atom constants

The fragment's counterpart of PCUIC's inductive types and propositional constructors: constants
without a δ rule whose declared type is evidently an arity (type formers) or evidently a
proposition headed by an axiom or opaque (proofs). They are values of the source semantics, and
their λ□ image is `□`. Every test is syntactic, like `isPropositionalArity`
(`MR P/PCUICFirstorder.v:103`), which reads an inductive's declared arity with `destArity`.
-/

open Lean Erasure

namespace EraseProof

/-- Syntactic arity `Π x₁…xₙ, Sort u`: its binder count and final level (`mdata` transparent).
Reference: `isArity` (`MR P/PCUICTyping.v:29`); the declared arity `isPropositional` reads
(`MR P/PCUICFirstorder.v:109`). -/
def arityShape : Expr → Option (Nat × Level)
  | .sort u => some (0, u)
  | .forallE _ _ b _ => (arityShape b).map fun (n, u) => (n + 1, u)
  | .mdata _ e => arityShape e
  | _ => none

/-- A level that is zero under every assignment, recognised structurally. Reference:
`isPropositionalArity` (`MR P/PCUICFirstorder.v:103`), for Lean levels (DV-4). -/
def EvidentZero : Level → Bool
  | .zero => true
  | .max a b => EvidentZero a && EvidentZero b
  | .imax _ b => EvidentZero b
  | _ => false

/-- Declarations that no δ rule unfolds: in master's model (`TrEnv'.axiom`, `TrEnv'.opaque` add
no defeq), in `SrcEval` (`EvalEnv.unfold?`) and in the oracle (`Pure.whnf` unfolds `defnInfo`
only). The fragment's counterpart of inductive types, which never δ-reduce. By kind, so remapped
`@[extern]` definitions are excluded. Reference: `tInd` heads (`MR P/PCUICWcbvEval.v:51 atom`),
DV-11. -/
def DeltaFree : ConstantInfo → Bool
  | .axiomInfo _ | .opaqueInfo _ => true
  | _ => false

/-- An evident proposition: `Π x₁…xₘ, h.{vs} a₁…aₙ`, whose head `h` is a `DeltaFree` declaration
with declared type a syntactic arity `Π y₁…yₙ, Sort u` of exactly `n` binders, and whose sort at
the occurrence, `u` with `h`'s level parameters instantiated by `vs`, is evidently zero.
Reference: `isPropositional` (`MR P/PCUICFirstorder.v:109`), as `MR E/Extract.v:106
erases_tConstruct` uses it (DV-11). -/
def EvidentProp (decls : List ConstantInfo) : Expr → Bool
  | .forallE _ _ b _ => EvidentProp decls b
  | .mdata _ e => EvidentProp decls e
  | e => match e.getAppFn with
    | .const h vs => match findDecl decls h with
      | some ci => DeltaFree ci && match arityShape ci.type with
        | some (n, u) => n == e.getAppNumArgs && EvidentZero (Pure.instLevel ci.levelParams vs u)
        | none => false
      | none => false
    | _ => false

/-- δ-less constants that are values: evident type formers and proofs of evident propositions.
Reference: `tInd` and `tConstruct` in `MR P/PCUICWcbvEval.v:51 atom`; `MR E/Extract.v:106
erases_tConstruct` (`~~ isPropositional`); DV-11. -/
def EvalEnv.isAtom (σ : EvalEnv) (c : Name) : Bool :=
  match findDecl σ.decls c with
  | some ci => (σ.unfold? c).isNone && ((arityShape ci.type).isSome || EvidentProp σ.decls ci.type)
  | none => false

end EraseProof
