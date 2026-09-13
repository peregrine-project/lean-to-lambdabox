import LeanToLambdaBox
import VerifyBench.Src.Fannkuch

-- Extract to LambdaBox AST
#erase runBenchmark config {extern := .preferLogical, nat := .peano, csimp := false,} to "VerifyBench/ast/Fannkuch.ast"
