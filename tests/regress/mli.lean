import LeanToLambdaBox

/-!
The `.mli` signature that `#erase ... mli` writes for each type that has an OCaml representation in
the runtime of `benchmarks/via_malfunction`: `Nat` and `Int` are `Z.t`, `Option` is `option`, `Array`
is `LeanArray.array`, and `Prod` is an OCaml pair. Arrows and products under a type constructor or
inside a product are parenthesized (`A * B * C` would be an OCaml triple). `String` has no such
representation: it gets `unit` and a warning.
-/

def rInt (i : Int) : Int := i
#erase rInt mli "rInt.mli"

def rOpt (o : Option Nat) : Option Nat := o
#erase rOpt mli "rOpt.mli"

def rArr (a : Array Nat) : Array Nat := a
#erase rArr mli "rArr.mli"

def rPair (p : Nat × Bool) : Nat × Bool := p
#erase rPair mli "rPair.mli"

def rNestL (p : (Nat × Nat) × Nat) : (Nat × Nat) × Nat := p
#erase rNestL mli "rNestL.mli"

def rNestR (p : Nat × (Nat × Nat)) : Nat × (Nat × Nat) := p
#erase rNestR mli "rNestR.mli"

def rListPair (l : List (Nat × Nat)) : List (Nat × Nat) := l
#erase rListPair mli "rListPair.mli"

def rListFun (l : List (Nat → Nat)) : List (Nat → Nat) := l
#erase rListFun mli "rListFun.mli"

def rOptFun (o : Option (Nat → Nat)) : Option (Nat → Nat) := o
#erase rOptFun mli "rOptFun.mli"

def rFunPair (p : (Nat → Nat) × Nat) : (Nat → Nat) × Nat := p
#erase rFunPair mli "rFunPair.mli"

def rHof (f : Nat → Nat) : Nat → Nat := f
#erase rHof mli "rHof.mli"

def rStr (s : String) : String := s
/--
warning: failed to translate String into ML type, emitting unit instead.
---
warning: failed to translate String into ML type, emitting unit instead.
-/
#guard_msgs (warning) in
#erase rStr mli "rStr.mli"
