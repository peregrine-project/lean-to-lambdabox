import LeanToLambdaBox
import VerifyBench.Src.Quicksort

-- Extract to LambdaBox AST
#erase quicksortBench config {extern := .preferLogical, nat := .peano, csimp := false,} to "VerifyBench/ast/Quicksort.ast"
