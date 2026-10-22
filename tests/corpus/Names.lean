import LeanToLambdaBox

/-!
Corpus name-mangling examples (checkpoint 1). Every program here is inside the verification scope
(definitions only, Church numerals); what varies is the Lean name of the constants. The eraser maps
a Lean name to a kername with `toKername`: the last component goes through `cleanIdent` (every
character other than an ASCII letter, digit or `_` becomes `_u<code>`), the other components are
copied as they are. Each program is erased under `{nat := .peano}` to `<name>.peano.ast` and under
the default configuration to `<name>.default.ast`; the readouts (`N_R_*`, applied to `Nat`, outside
the scope) under `{nat := .peano}` only.
-/

namespace Nm

def CNat : Type 1 := ∀ α : Type, (α → α) → α → α

/-- `two'` becomes `two_u39`. -/
def two' : CNat := fun _ s z => s (s z)
/-- A distinct constant whose name is the mangled name of `two'` (value one). -/
def «two_u39» : CNat := fun _ s z => s z
/-- Uses both: 2 + 1 = 3. -/
def both : CNat := fun α s z => two' α s («two_u39» α s z)

/-- Subscript digit in the last component. -/
def dbl₂ : CNat := fun α s z => two' α s (two' α s z)

end Nm

/-- Non-ASCII namespace component (copied into the kername's module path as it is). -/
def Ωmega.k : Nm.CNat := Nm.two'

/-- A namespace component containing `"` (copied as it is into a quoted S-expression string). -/
def «q"q».k : Nm.CNat := Nm.two'

/-- `a.b.c` and `«a.b».c`: different Lean names, different kernames (as S-expressions). -/
def a.b.c : Nm.CNat := Nm.two'
def «a.b».c : Nm.CNat := Nm.dbl₂
def dotBoth : Nm.CNat := fun α s z => a.b.c α s («a.b».c α s z)

/-- A private definition (its name has a numeric component). -/
private def privTwo : Nm.CNat := Nm.two'

#erase Nm.two' config {nat := .peano} to "N_prime.peano.ast"
#erase Nm.two' to "N_prime.default.ast"
-- `two'` and `two_u39` have the same kername, and `#erase` fails (R-3). `#guard_msgs` pins the
-- error; no file is written.
/-- error: erasure failed: the constants Nm.two_u39 and Nm.two' have the same kername -/
#guard_msgs (error) in
#erase Nm.both config {nat := .peano} to "N_collision.peano.ast"
/-- error: erasure failed: the constants Nm.two_u39 and Nm.two' have the same kername -/
#guard_msgs (error) in
#erase Nm.both to "N_collision.default.ast"
#erase (Nm.both Nat Nat.succ Nat.zero) config {nat := .peano} to "N_R_collision.peano.ast"
#erase Nm.dbl₂ config {nat := .peano} to "N_subscript.peano.ast"
#erase Nm.dbl₂ to "N_subscript.default.ast"
#erase Ωmega.k config {nat := .peano} to "N_unicodeNs.peano.ast"
#erase Ωmega.k to "N_unicodeNs.default.ast"
#erase «q"q».k config {nat := .peano} to "N_quoteNs.peano.ast"
#erase «q"q».k to "N_quoteNs.default.ast"
#erase dotBoth config {nat := .peano} to "N_dotBoth.peano.ast"
#erase dotBoth to "N_dotBoth.default.ast"
#erase (dotBoth Nat Nat.succ Nat.zero) config {nat := .peano} to "N_R_dotBoth.peano.ast"
#erase privTwo config {nat := .peano} to "N_private.peano.ast"
#erase privTwo to "N_private.default.ast"

