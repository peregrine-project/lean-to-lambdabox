import LeanToLambdaBox.Basic
import LeanToLambdaBox.Erasure.ExprOps

/-!
# The pure path's errors and its view of the environment

`EraseError` are the errors of the pure path, `EnvView` is what it reads about the Lean
environment, `findConst` looks a declaration up in a list, and `findCollision` finds two constants
of a list with one kername. The fragment test `collectDeps` (`LeanToLambdaBox/Erasure/Entry.lean`)
uses them.
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
  implementedBy? : Name → Option Name

/-- Trusted glue: the view `#erase` builds from the elaboration environment.
Reference: none (MetaRocq's quoting is likewise trusted, MC p. 8:5). -/
def EnvView.ofEnvironment (env : Environment) : EnvView where
  find? := env.find?
  isExtern := Lean.isExtern env
  inlineAttr? := Compiler.getInlineAttribute? env
  implementedBy? := Compiler.getImplementedBy? env

/-- List lookup of a declaration by name. Reference: `lookup_env`
(`MR common/theories/Environment.v:483`). -/
def findConst (decls : List ConstantInfo) (c : Name) : Option ConstantInfo :=
  decls.find? (·.name == c)

/-- Two distinct closure constants with the same kername, if any. Reference: none (`toKername`
is not injective, DV-14). -/
def findCollision : List ConstantInfo → Option (Name × Name)
  | [] => none
  | ci :: cs => match cs.find? (fun cj => toKername cj.name == toKername ci.name) with
    | some cj => some (ci.name, cj.name)
    | none => findCollision cs

/-- Bound on the number of declarations `collectDeps` adds to a closure: no Lean environment has
`2^32` constants. Reference: none. -/
def collectFuel : Nat := 2 ^ 32

end Erasure
