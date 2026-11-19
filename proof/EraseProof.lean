import EraseProof.Bridge.CLAccept
import EraseProof.Semantics.Cases
import EraseProof.Semantics.Iota
import EraseProof.Semantics.Rec
import EraseProof.Semantics.Decode
import EraseProof.Semantics.Frozen
import EraseProof.Bridge.CLRead
import EraseProof.Bridge.CLStore
import EraseProof.Bridge.CLNames
import EraseProof.Core.Collect
import EraseProof.Core.CollectSpec
import EraseProof.Core.CollectOk
import EraseProof.Statements
import EraseProof.Relation.Inst
import EraseProof.Relation.Abstract
import EraseProof.Relation.Lookup
import EraseProof.Source.Marks
import EraseProof.Source.MarkRead
import EraseProof.Simulation.Cases
import EraseProof.Simulation.Ind
import EraseProof.Simulation.Quot
import EraseProof.Simulation.Rec
import EraseProof.Simulation.Main
import EraseProof.Source.Decls
import EraseProof.Test.Marks
import EraseProof.Test.NV1Run
import EraseProof.Test.NV0Premises
import EraseProof.Test.NV1Premises
import EraseProof.Test.NV2Premises
import EraseProof.Test.DeclOf
import EraseProof.Test.RecIH
import EraseProof.Oracle.Rename
import EraseProof.Oracle.Det
import EraseProof.Oracle.Atom
import EraseProof.Core.State
import EraseProof.Core.RegisterInd
import EraseProof.Core.Glue
import EraseProof.Core.Steps
import EraseProof.Core.StepsApp
import EraseProof.Core.StepsRun
import EraseProof.Core.StepsCtor
import EraseProof.Core.StepsCases
import EraseProof.Core.StepsCasesSat
import EraseProof.Core.StepsQuot
import EraseProof.Core.NonRec
import EraseProof.Core.CtorProp
import EraseProof.Core.StepsProj
/-!
# Verification of the eraser

The library root of the proof package: the correctness of the erasure behind `#erase`
(`LeanToLambdaBox`) against con-leche's set-theoretic model of Lean's kernel. The checks are in
`scripts/check.sh`.

* `EraseProof.Target`: λ□ and its evaluation.
* `EraseProof.Spec`: the definitions the statements are about (the bridge to con-leche, the
  con-leche checks, the marks, the source semantics, the erasure relation, `Sound`).
* `EraseProof.TargetLift`: closedness, lifting, free variables, closed substitution and the
  abstraction of a free variable on λ□ terms.
* `EraseProof.Relation.Basic`, `EraseProof.Relation.Inst`: closedness, congruence, inversion,
  substitution and universe instantiation of the erasure relation.
* `EraseProof.Relation.Abstract`: closing a binder the traversal opened with a free variable.
* `EraseProof.Relation.Lookup`: what the erased dependencies give of the λ□ environment
  (constants' bodies, inductive blocks), and their stability under abstraction and growth.
* `EraseProof.Source.Marks`: marks under substitution; `unmark` commutes with lifting, universe
  instantiation and instantiation.
* `EraseProof.Source.MarkRead`: a marking reads through `unmark` as the term it marks, and its
  `eta` marks sit on λs.
* `EraseProof.TargetFacts`: the induction principle of λ□ evaluation.
* `EraseProof.Relation.Deps`: erased dependencies under substitution and λ□ evaluation.
* `EraseProof.Source.Value`: the shapes of source values; every evaluation result is one.
* `EraseProof.Simulation.Cases`: the cases β, ζ, δ, atoms, application congruence and the frozen
  rules of the relation-level simulation.
* `EraseProof.Simulation.Ind`: the constructor, `casesOn`, projection and literal cases of the
  relation-level simulation, and the λ□ evaluation facts they use.
* `EraseProof.Simulation.Quot`: the quotient cases of the relation-level simulation.
* `EraseProof.Simulation.RecFix`: the λ□ fixpoint of a recursor of a single inductive, unfolded.
* `EraseProof.Simulation.Rec`: the recursor ι case of the relation-level simulation.
* `EraseProof.Simulation.Main`: the relation-level simulation `erases_correct`.
* `EraseProof.Source.Decls`: the closure property of a list of declarations, and what its lookups
  and the `casesOn` recognizer give.
* `EraseProof.Bridge.CLRead`: con-leche's reading of the source semantics' operations on terms.
* `EraseProof.Bridge.CLAccept`: what con-leche's acceptance of the program gives.
* `EraseProof.Semantics.Cases`: the invariant of the meaning of source evaluation in con-leche's
  model, and its cases β, ζ, δ, application congruence, constructor values, the frozen
  application and the value rules.
* `EraseProof.Semantics.Iota`: its cases `casesOn` ι (on a constructor value and on a `Nat`
  literal), projection and frozen projection, and the premise of its `let` case.
* `EraseProof.Semantics.Rec`: its cases recursor ι, quotient lift and quotient constructor.
* `EraseProof.Semantics.Decode`: the stored records of a recognized `casesOn` (its value, recursor
  and constructors), of a one-member block's former and of the quotient constants; the grading of a
  certified term.
* `EraseProof.Semantics.Frozen`: its case `casesOn` on a frozen discriminant (a proof), reduced
  by con-leche's semantic ι at a constructor application built for the step.
* `EraseProof.Bridge.CLStore`: what con-leche's fold stores of the program's declarations.
* `EraseProof.Bridge.CLNames`: the names con-leche's acceptance binds are the program's, and every
  declaration of the program the fragment test may scan reads only names of the program.
* `EraseProof.Core.Collect`: the closure of the fragment test is part of the program
  (`collectDeps_sub`).
* `EraseProof.Core.CollectSpec`: the closure of the fragment test is closed under what the source
  semantics and the traversal read, with distinct kernames and block names (`collectDeps_spec`).
* `EraseProof.Core.CollectOk`: the fragment test accepts a program whose read closure lies inside
  the first-phase fragment (`collectDeps_ok_of`).
* `EraseProof.Oracle.Rename`: the pure oracle commutes with a renaming of free variables and keeps
  its results within the free variables of its inputs and locals; so do the markings (`MarkOf`).
* `EraseProof.Oracle.Det`: the marking is a function of its input (`markOf_det`).
* `EraseProof.Oracle.Atom`: the oracle never answers `false` on an atom spine (`Pure.isErasable_atom`).
* `EraseProof.Core.State`: the traversal's state invariant and the registration of constants.
* `EraseProof.Core.RegisterInd`: the registration of an inductive block keeps the invariant.
* `EraseProof.Core.Glue`: a returning run of `#erase`'s entry point on an input inside the
  fragment is a run of the pure path.
* `EraseProof.Core.Steps`: the statement of the traversal's correctness at one fuel, over
  markings under renamed locals, and its steps for `□`, free variables, the rejected terms,
  metadata, λ and `let`.
* `EraseProof.Core.StepsApp`: the steps for application spines and constants without a rule of
  their own, and for `visitMutual`.
* `EraseProof.Core.StepsRun`: runs of the traversal's environment helpers at the pure backend.
* `EraseProof.Core.StepsCtor`: the η-expansion of a spine to its head's arity, and the step for
  constructor spines.
* `EraseProof.Core.StepsCases`: a `casesOn` alternative erased under its fields' binders
  (`visitAlt`), and the λ□ `case` (`visitCasesOn`).
* `EraseProof.Core.StepsCasesSat`: the step for `casesOn` spines: the `□`, reduced and `case`
  branches of `visitCases`.
* `EraseProof.Core.StepsQuot`: the step for spines headed by `Quot.mk` or `Quot.lift`.
* `EraseProof.Core.NonRec`: a value `visitMutual` erases is of a one-member block and has a scope
  without its own constant, by the order of con-leche's fold (`coreEnv_value`).
* `EraseProof.Core.CtorProp`: the oracle boxes the constructor spines of inductives declared in
  `Prop`, by con-leche's check of the constructors' conclusions (`ctorPropBoxed_of`).
* `EraseProof.Core.StepsProj`: the steps for projections and Nat literals.
* `EraseProof.Statements`: the statements, as definitions of type `Prop`, that `spec.pin` pins.
-/
