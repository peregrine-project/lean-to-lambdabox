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
-- The reified slice of the elaboration environment, its adequacy statement, and the
-- translation witnesses a rung reads off it.
import LeanToLambdaBox.Witness.SourceTable
import LeanToLambdaBox.Witness.TrWitness
-- The kernel facts taken from the fork as one named premise, and their corollaries.
import LeanToLambdaBox.Upstream
import LeanToLambdaBox.Origin
-- What erasure means: the specification relation, its transport lemmas and its totality.
import LeanToLambdaBox.Erases
import LeanToLambdaBox.ErasesAbstract
import LeanToLambdaBox.ErasesStrengthen
import LeanToLambdaBox.ErasesUniform
import LeanToLambdaBox.ErasesTotal
import LeanToLambdaBox.ErasesAlpha
-- The source-side evaluation, its subject reduction, the simulation's arms and its closing.
import LeanToLambdaBox.SourceEval
import LeanToLambdaBox.SubjectReduction
import LeanToLambdaBox.ErasesCorrect
import LeanToLambdaBox.ErasesCorrect.Close
-- The pass layer: the runtime library's bodies, the pass relation, its fixpoint closure,
-- and the composite of erasure with the pass.
import LeanToLambdaBox.ElimBody
import LeanToLambdaBox.Lower
import LeanToLambdaBox.LowerFix
import LeanToLambdaBox.ErasesLB
-- The specification bundle, the output boundary, the supported fragment, the environments.
import LeanToLambdaBox.ErasureSpec
import LeanToLambdaBox.Output
import LeanToLambdaBox.Supported
import LeanToLambdaBox.ErasesEnv
import LeanToLambdaBox.SpecEnv
-- The first-order answer predicate and the capstone.
import LeanToLambdaBox.FirstOrderInd
import LeanToLambdaBox.Capstone
-- The bridge from the shipping erasure to the specification: the run invariant, the
-- eighteen motives of the `partial_fixpoint` induction, the member steps that discharge
-- them, the aggregator, and the cold-start shape and decomposition lemmas.
import LeanToLambdaBox.Bridge
import LeanToLambdaBox.VisitExprRefines
import LeanToLambdaBox.VisitExprRefines.Step.Env
import LeanToLambdaBox.VisitExprRefines.Step.Mechanical
import LeanToLambdaBox.VisitExprRefines.Step.Passes
import LeanToLambdaBox.ColdStartRun
-- The green ladder.
import LeanToLambdaBox.Green
