import LeanToLambdaBox.Erasure
import LeanToLambdaBox.Erasure.Collect
import LeanToLambdaBox.Erasure.Pure

/-!
# The entry point of `#erase`

`Erasure.eraseEntry view cfg e` is what `#erase` runs. `Erasure.route` decides the path from
`collectDeps`: a program in the fragment is erased by `erasePure` over its closure, a program
outside it by the `CoreM` backend (`Erasure.erase`), and every other error of `collectDeps` or of
`erasePure` is an error of `#erase`.
-/

open Lean

namespace Erasure

/-- Where `#erase` sends an input (S-E). Reference: none. -/
inductive Route where
  | viaPure (r : Except EraseError (Program × List Kername))
  | viaMeta

/-- The routing decision (S-E): in-fragment programs take the pure path; `outOfFragment` goes to
the unchanged `Meta` path; every other `collectDeps` error is an error of `#erase`. Reference:
none. -/
def route (view : EnvView) (cfg : ErasureConfig) (e : Expr) : Route :=
  match collectDeps view e with
  | .ok decls => .viaPure (erasePure view cfg decls e)
  | .error (.outOfFragment _) => .viaMeta
  | .error err => .viaPure (.error err)

/-- The text of an error of the pure path in the message of `#erase`. Reference: none. -/
def EraseError.describe : EraseError → String
  | .outOfFragment w => s!"outside the fragment: {w}"
  | .nameCollision a b => s!"the constants {a} and {b} have the same kername"
  | .fuel site => s!"out of fuel in {site}"
  | .failed msg => msg

/-- The `#erase` entry point after S-E. Reference: the erasure run of
`MR E/ErasureFunctionProperties.v:657 erase_correct`
(`erase … = t'`, `erase_global_deps … = Σ'`). -/
def eraseEntry (view : EnvView) (cfg : ErasureConfig) (e : Expr) :
    CoreM (Program × List Kername) :=
  match route view cfg e with
  | .viaPure (.ok r) => pure r
  | .viaPure (.error err) => throwError "erasure failed: {err.describe}"
  | .viaMeta => erase e cfg

end Erasure
