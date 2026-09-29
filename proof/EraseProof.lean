import EraseProof.Env
import EraseProof.Env.Unfold
import EraseProof.Source.EvalEnv
import EraseProof.Typing.Basic
import EraseProof.Typing.Inst
import EraseProof.Typing.Uniq
import EraseProof.Typing.Weak

/-!
# EraseProof

Correctness of the shipping eraser `LeanToLambdaBox` against lean4lean's model of Lean's kernel.
This root module imports every module of the library.
-/
