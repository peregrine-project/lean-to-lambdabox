import LeanToLambdaBox.Basic
import Lean4Lean.Verify.Axioms

/-!
# The program's closure

`collectDeps view e` computes the declarations that the term `e` depends on, reading the Lean
environment through an `EnvView`, and says whether `e` lies in the fragment without inductive
types, literals, projections and metavariables (`EraseError.outOfFragment` otherwise).
-/

open Lean

-- Decidable equality of kernames, for `findCollision`. Reference: `reflect_kername`
-- (`MR common/theories/Kernames.v:325`).
deriving instance DecidableEq for ModPath
deriving instance DecidableEq for Kername

namespace Erasure

/-- Errors of the pure path. `outOfFragment` routes `#erase` to the unchanged `Meta`
path; the others are errors of `#erase`. Reference: none; MetaRocq's `erase` is total under
`NormalizationIn` (`MR E/ErasureFunction.v:989 erase`), our run is fuelled (DV-17). -/
inductive EraseError where
  | outOfFragment (what : String)
  | nameCollision (a b : Name)
  | fuel (site : String)
  | failed (msg : String)
deriving Inhabited

/-- What the pure path reads about the Lean environment: the implementation-side
environment, the counterpart of MetaRocq's abstract environment `X` related to `Σ` by
`abstract_env_ext_rel` (hypothesis of `MR E/ErasureFunctionProperties.v:657 erase_correct`).
Built by `EnvView.ofEnvironment`, trusted glue as quoting is in MetaRocq (MC p. 8:5). -/
structure EnvView where
  find? : Name → Option ConstantInfo
  isExtern : Name → Bool
  inlineAttr? : Name → Option Compiler.InlineAttributeKind

/-- Trusted glue: the view `#erase` builds from the elaboration environment.
Reference: none (MetaRocq's quoting is likewise trusted, MC p. 8:5). -/
def EnvView.ofEnvironment (env : Environment) : EnvView where
  find? := env.find?
  isExtern := Lean.isExtern env
  inlineAttr? := Compiler.getInlineAttribute? env

/-- List lookup of a declaration by name. Reference: `lookup_env`
(`MR common/theories/Environment.v:483`). -/
def findConst (decls : List ConstantInfo) (c : Name) : Option ConstantInfo :=
  decls.find? (·.name == c)

/-! ## `collectDeps`: the program's closure and the routing criterion -/

/-- The constants an expression mentions, or the master gap that puts it outside the fragment.
Reference: `term_global_deps` (`MR E/EAstUtils.v:406`), on the source side. -/
def exprConsts : Expr → Except EraseError (List Name)
  | .bvar _ => pure []
  | .fvar _ => throw (.outOfFragment "free variable")
  | .mvar _ => throw (.outOfFragment "metavariable")
  | .sort u => if u.hasMVar' then throw (.outOfFragment "level metavariable") else pure []
  | .const c us =>
    if us.any (·.hasMVar') then throw (.outOfFragment "level metavariable") else pure [c]
  | .app f a => return (← exprConsts f) ++ (← exprConsts a)
  | .lam _ t b _ | .forallE _ t b _ => return (← exprConsts t) ++ (← exprConsts b)
  | .letE _ t v b _ => return (← exprConsts t) ++ (← exprConsts v) ++ (← exprConsts b)
  | .lit _ => throw (.outOfFragment "literal")
  | .mdata _ e => exprConsts e
  | .proj .. => throw (.outOfFragment "projection")

/-- The names a declaration depends on (type, value, block members), or the master gap.
Reference: the dependencies `MR E/ErasureFunction.v:1602 erase_global_deps` follows. -/
def declDeps : ConstantInfo → Except EraseError (List Name)
  | .axiomInfo v => exprConsts v.type
  | .defnInfo v => return (← exprConsts v.type) ++ (← exprConsts v.value) ++ v.all
  | .thmInfo v => return (← exprConsts v.type) ++ (← exprConsts v.value) ++ v.all
  | .opaqueInfo v => return (← exprConsts v.type) ++ (← exprConsts v.value) ++ v.all
  | .quotInfo _ => throw (.outOfFragment "quotient")
  | .inductInfo _ => throw (.outOfFragment "inductive type")
  | .ctorInfo _ => throw (.outOfFragment "constructor")
  | .recInfo _ => throw (.outOfFragment "recursor")

/-- Depth-first closure. `fuel` bounds the number of work-list steps; every name is expanded at
most once. The first `outOfFragment` stops the scan. A view that answers `find? n` with a
declaration of another name is rejected (a real `Environment` never does). Reference:
`MR E/ErasureFunction.v:1602 erase_global_deps` (keeps what the term uses). -/
def closure (view : EnvView) : Nat → List Name → List ConstantInfo →
    Except EraseError (List ConstantInfo)
  | 0, _, _ => throw (.fuel "collectDeps")
  | _+1, [], acc => pure acc
  | f+1, n :: todo, acc =>
    if acc.any (·.name == n) then closure view f todo acc
    else match view.find? n with
      | none => throw (.outOfFragment "unknown constant")
      | some ci =>
        if ci.name != n then throw (.failed "view returned a declaration of another name")
        else do closure view f ((← declDeps ci) ++ todo) (ci :: acc)

/-- Two distinct closure constants with the same kername, if any. Reference: none (`toKername`
is not injective, DV-14). -/
def findCollision : List ConstantInfo → Option (Name × Name)
  | [] => none
  | ci :: cs => match cs.find? (fun cj => toKername cj.name == toKername ci.name) with
    | some cj => some (ci.name, cj.name)
    | none => findCollision cs

/-- Work-list bound of `collectDeps`: no Lean environment has `2^32` constants. Reference: none. -/
def collectFuel : Nat := 2 ^ 32

/-- The program's own environment: the dependency closure of `e` through types, values and block
members. The fragment scan completes before the collision check, so `outOfFragment` takes
precedence over `nameCollision`. Reference: the environment `Σ'` that
`MR E/ErasureFunction.v:1602 erase_global_deps` keeps, computed on the source side (DV-3). -/
def collectDeps (view : EnvView) (e : Expr) : Except EraseError (List ConstantInfo) := do
  let decls ← closure view collectFuel (← exprConsts e) []
  match findCollision decls with
  | some (a, b) => throw (.nameCollision a b)
  | none => pure decls

end Erasure
