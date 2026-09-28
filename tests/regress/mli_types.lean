import LeanToLambdaBox

/-!
`.mli` signatures of result types that `to_ml_type` translates (register entry S-2, claim C1):
`Int`, `Option`, a flat pair, `Array`, and arrows and pairs under `List`, `Option` and `×`, which
OCaml needs parenthesized; `rHof` has an arrow in argument position. Each signature was checked by
linking the erased program with an OCaml harness written against it and running it.
-/

def rInt (n : Nat) : Int := Int.ofNat n - 10
#erase rInt to "rInt.ast" mli "rInt.mli"

def rOpt (n : Nat) : Option Nat := if n = 0 then none else some n
#erase rOpt to "rOpt.ast" mli "rOpt.mli"

def rPair (n : Nat) : Nat × Bool := (n, n == 0)
#erase rPair to "rPair.ast" mli "rPair.mli"

def rListPair (n : Nat) : List (Nat × Nat) := [(n, n + 1)]
#erase rListPair to "rListPair.ast" mli "rListPair.mli"

def rOptFun (n : Nat) : Option (Nat → Nat) := some (· + n)
#erase rOptFun to "rOptFun.ast" mli "rOptFun.mli"

def rFunPair (n : Nat) : (Nat → Nat) × Nat := ((· + n), n)
#erase rFunPair to "rFunPair.ast" mli "rFunPair.mli"

def rListFun (n : Nat) : List (Nat → Nat) := [(· + n)]
#erase rListFun to "rListFun.ast" mli "rListFun.mli"

def rArr (n : Nat) : Array Nat := Array.mk [n, n + 1]
#erase rArr to "rArr.ast" mli "rArr.mli"

def rHof (f : Nat → Nat) : Nat := f 0
#erase rHof to "rHof.ast" mli "rHof.mli"
