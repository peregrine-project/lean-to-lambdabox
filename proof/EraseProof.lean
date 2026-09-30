import EraseProof.Atoms
import EraseProof.Env
import EraseProof.Env.Unfold
import EraseProof.Erasability
import EraseProof.Erasability.Eval
import EraseProof.Erasability.Inv
import EraseProof.Oracle
import EraseProof.Oracle.Agree
import EraseProof.Oracle.Atom
import EraseProof.Oracle.AtomShapes
import EraseProof.Oracle.Infer
import EraseProof.Oracle.Whnf
import EraseProof.Relation.Abstract
import EraseProof.Relation.Atoms
import EraseProof.Relation.Basic
import EraseProof.Relation.Deps
import EraseProof.Relation.Levels
import EraseProof.Relation.Subst
import EraseProof.Simulation
import EraseProof.Simulation.Cases
import EraseProof.Simulation.Fix
import EraseProof.Source.Defeq
import EraseProof.Source.Eval
import EraseProof.Source.EvalEnv
import EraseProof.Source.Restrict
import EraseProof.Source.Steps
import EraseProof.Target
import EraseProof.Test.Atoms
import EraseProof.Test.Bridge
import EraseProof.Test.LBEval
import EraseProof.Test.NV1
import EraseProof.Test.NV2
import EraseProof.Test.NV3
import EraseProof.Test.NV5
import EraseProof.Test.NV6
import EraseProof.Test.NV7
import EraseProof.Test.Oracle
import EraseProof.Typing.Abstract
import EraseProof.Typing.Basic
import EraseProof.Typing.Inst
import EraseProof.Typing.InstLevels
import EraseProof.Typing.Uniq
import EraseProof.Typing.Weak

/-!
# EraseProof

Correctness of the shipping eraser `LeanToLambdaBox` against lean4lean's model of Lean's kernel.
This root module imports every module of the library.
-/
