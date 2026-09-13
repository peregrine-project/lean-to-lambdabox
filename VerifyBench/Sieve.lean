import LeanToLambdaBox
import VerifyBench.Src.Sieve

-- Extract to LambdaBox AST
#erase countPrimes config {extern := .preferLogical, nat := .peano, csimp := false,} to "VerifyBench/ast/Sieve.ast"
