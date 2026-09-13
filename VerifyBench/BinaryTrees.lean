import LeanToLambdaBox
import VerifyBench.Src.BinaryTrees

-- Extract to LambdaBox AST
#erase binaryTreesSimple config {extern := .preferLogical, nat := .peano, csimp := false} to "VerifyBench/ast/BinaryTrees.ast"
