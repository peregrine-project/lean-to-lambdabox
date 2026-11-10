import LeanToLambdaBox

/-!
`Nat` literals with `nat := .machine`, the default. The largest literal that a 63-bit signed
integer holds is 2^62 - 1, `Erasure.machineMaxLiteral`. A larger literal is an error of `#erase` and
of `#erase_lcnf`. The range check used to compare in `BitVec 63`, so that a literal of at least
2^63 was first reduced modulo 2^63 and could be accepted with a wrong value (2^63 became 0). With
`nat := .peano`, `#erase_lcnf` has the bound of `#erase`.
-/

-- peregrine: validate max.ast

namespace MachineLiteral

def max : Nat := 4611686018427387903
def tooBig : Nat := 4611686018427387904
def wraps : Nat := 9223372036854775808
def wrapsToFive : Nat := 18446744073709551621
def large : Nat := 65537

end MachineLiteral

#erase MachineLiteral.max to "max.ast"

/--
error: #erase: the Nat literal 4611686018427387904 in MachineLiteral.tooBig exceeds 4611686018427387903, the largest literal that `nat := .machine` erases to a 63-bit signed integer
-/
#guard_msgs (error, drop info) in
#erase MachineLiteral.tooBig to "tooBig.ast"

/--
error: #erase: the Nat literal 9223372036854775808 in MachineLiteral.wraps exceeds 4611686018427387903, the largest literal that `nat := .machine` erases to a 63-bit signed integer
-/
#guard_msgs (error, drop info) in
#erase MachineLiteral.wraps to "wraps.ast"

/--
error: #erase: the Nat literal 18446744073709551621 in MachineLiteral.wrapsToFive exceeds 4611686018427387903, the largest literal that `nat := .machine` erases to a 63-bit signed integer
-/
#guard_msgs (error, drop info) in
#erase MachineLiteral.wrapsToFive to "wrapsToFive.ast"

/-- error: Nat literal 9223372036854775808 not representable as a 63-bit signed integer. -/
#guard_msgs (error, drop info) in
#erase_lcnf MachineLiteral.wraps

/--
error: #erase_lcnf: the Nat literal 65537 exceeds 65536, the largest literal that `nat := .peano` erases to `Nat.succ` applications
-/
#guard_msgs (error, drop info) in
#erase_lcnf MachineLiteral.large config {nat := .peano}
