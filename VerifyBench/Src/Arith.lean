-- Frozen program source for `VerifyBench/Arith.lean`; pinned by `scripts/frozen.sh`.

def benchArith (n : Nat) : Nat :=
  2 ^ (((n * 3) - n) + 3)
