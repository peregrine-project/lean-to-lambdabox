import LeanToLambdaBox

/-!
The inductive of an axiom's result. `Nat.beq` has no compiled code and is erased as an axiom; its
values are constructors of `Bool`, which the backend builds. A program that only returns or passes
on such a value, without a `match` on `Nat` (which registers `Bool` for its test), used to get a
λ□ environment without `Bool`. `Bool` and `Decidable` are now registered with the axiom, for
`#erase` and for `#erase_lcnf` (whose base phase erases such constants as `#erase` does).
-/

namespace AxiomResult

def fb (n : Nat) : Bool := Nat.beq n 4
def fbMain : Bool := fb 3

def dec (n : Nat) : Decidable (n = 4) := Nat.decEq n 4

end AxiomResult

#erase AxiomResult.fbMain to "fb.ast"
#erase_lcnf AxiomResult.fbMain to "fb.lcnf.ast"
#erase AxiomResult.dec to "dec.ast"
