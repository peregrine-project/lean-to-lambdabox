import Lean.Data.Name

/-!
# `CasesNames` — the eliminator name test, on its own

Two name predicates that both the source semantics and the fragment checker read:
`lastComponent` and `isCasesOnName`. `SourceEval.CasesOnShape` names the second and
`Supported.supportedHead` names both, so the pair sits in a leaf module of its own rather
than in either consumer — the source-evaluation layer must not import the shipping-code
closure to ask whether a constant is called `I.casesOn`.
-/

namespace LeanToLambdaBox

open Lean

/-- The last string component of `c`, if it has one. -/
def lastComponent (c : Name) : Option String :=
  match c with
  | .str _ s => some s
  | _ => none

/-- Is `c` a `casesOn` eliminator name, `I.casesOn`? -/
def isCasesOnName (c : Name) : Bool :=
  match lastComponent c with
  | some s => s == "casesOn"
  | none => false

end LeanToLambdaBox
