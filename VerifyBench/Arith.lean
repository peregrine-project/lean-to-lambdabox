import LeanToLambdaBox
import VerifyBench.Src.Arith

-- Extract to LambdaBox AST
#erase benchArith config {extern := .preferLogical, nat := .peano, csimp := false} to "VerifyBench/ast/Arith.ast"
