-- This module serves as the root of the `LeanToLambdaBox` library.
-- Import modules here that should be built as part of the library.
-- λ□ syntax, the shipping erasure (`#erase`), its relevance oracle and the printer.
import LeanToLambdaBox.Basic
import LeanToLambdaBox.Printing
import LeanToLambdaBox.Relevance
import LeanToLambdaBox.Erasure
-- Operational semantics of λ□: a Lean translation of MetaRocq's `EWcbvEval`.
import LeanToLambdaBox.Semantics.Substitution
import LeanToLambdaBox.Semantics.Env
import LeanToLambdaBox.Semantics.Flags
import LeanToLambdaBox.Semantics.Values
import LeanToLambdaBox.Semantics.Eval
import LeanToLambdaBox.Semantics.Metatheory
import LeanToLambdaBox.Semantics.Compute
-- Target-side metatheory: fvar↔de-Bruijn transport, closedness, output shape, fixpoints.
import LeanToLambdaBox.Abstract
import LeanToLambdaBox.Closed
import LeanToLambdaBox.OutputShape
import LeanToLambdaBox.FixMetatheory
import LeanToLambdaBox.FixUnfold
import LeanToLambdaBox.IotaBridge
-- The `optimize` pass and its correctness theorem.
import LeanToLambdaBox.Optimize
-- Source-side erasability and the verified relevance check.
import LeanToLambdaBox.Erasability
import LeanToLambdaBox.RelevanceCheck
import LeanToLambdaBox.CheckerAdequacy
-- The `EraseM` run/admissibility toolkit for the shipping erasure.
import LeanToLambdaBox.ErasureRun
-- The reified slice of the elaboration environment and its adequacy statement.
import LeanToLambdaBox.Witness.SourceTable
-- What erasure means: the specification relation, its transport lemmas and its totality.
import LeanToLambdaBox.Erases
import LeanToLambdaBox.ErasesAbstract
import LeanToLambdaBox.ErasesStrengthen
import LeanToLambdaBox.ErasesUniform
import LeanToLambdaBox.ErasesTotal
-- The source-side evaluation and its subject reduction.
import LeanToLambdaBox.SourceEval
import LeanToLambdaBox.SubjectReduction
-- The pass layer: the runtime library's bodies, the pass relation, its fixpoint closure,
-- and the forward simulation on the fragment W1 covers.
import LeanToLambdaBox.ElimBody
import LeanToLambdaBox.Lower
import LeanToLambdaBox.LowerFix
import LeanToLambdaBox.LowerCorrect
-- The specification bundle, the output boundary, the supported fragment, the environments.
import LeanToLambdaBox.ErasureSpec
import LeanToLambdaBox.Output
import LeanToLambdaBox.Supported
import LeanToLambdaBox.ErasesEnv
import LeanToLambdaBox.SpecEnv
-- The capstone and the green ladder.
import LeanToLambdaBox.Capstone
import LeanToLambdaBox.Green
