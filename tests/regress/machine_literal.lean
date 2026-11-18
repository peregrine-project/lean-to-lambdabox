import LeanToLambdaBox

/-!
`Nat` literals with `nat := .machine`. A literal up to `Erasure.machineMaxLiteral` (`2 ^ 62 - 1`,
the largest 63-bit signed integer) becomes a `primInt`. A larger literal is an error, for both
`#erase` and `#erase_lcnf`. The range test used to compare in `BitVec 63`, that is modulo
`2 ^ 63`, so `2 ^ 63` passed and was emitted as `primInt 0` (#29).
-/

namespace MachineLiteral

def largest : Nat := 4611686018427387903
def first : Nat := 4611686018427387904
def wraps : Nat := 9223372036854775808
def wrapsFive : Nat := 9223372036854775813

end MachineLiteral

#erase MachineLiteral.largest to "largest.ast"
#erase_lcnf MachineLiteral.largest to "largest.lcnf.ast"

/--
error: #erase: the Nat literal 4611686018427387904 in MachineLiteral.first exceeds 4611686018427387903, the largest literal that `nat := .machine` erases to a 63-bit signed integer
-/
#guard_msgs (error, drop info) in
#erase MachineLiteral.first to "first.ast"

/--
error: #erase: the Nat literal 9223372036854775808 in MachineLiteral.wraps exceeds 4611686018427387903, the largest literal that `nat := .machine` erases to a 63-bit signed integer
-/
#guard_msgs (error, drop info) in
#erase MachineLiteral.wraps to "wraps.ast"

/--
error: #erase: the Nat literal 9223372036854775813 in MachineLiteral.wrapsFive exceeds 4611686018427387903, the largest literal that `nat := .machine` erases to a 63-bit signed integer
-/
#guard_msgs (error, drop info) in
#erase MachineLiteral.wrapsFive to "wrapsFive.ast"

/-- error: Nat literal 9223372036854775808 not representable as a 63-bit signed integer. -/
#guard_msgs (error, drop info) in
#erase_lcnf MachineLiteral.wraps to "wraps.lcnf.ast"
