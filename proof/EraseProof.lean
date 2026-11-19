import EraseProof.Bridge.CLAccept
import EraseProof.Semantics.Cases
import EraseProof.Semantics.Iota
import EraseProof.Semantics.Rec
import EraseProof.Semantics.Decode
import EraseProof.Bridge.CLRead
import EraseProof.Bridge.CLStore
import EraseProof.Bridge.CLNames
import EraseProof.Core.Collect
import EraseProof.Core.CollectSpec
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
import EraseProof.Source.Restrict
import EraseProof.Test.Marks
import EraseProof.Test.NV1Run
import EraseProof.Test.NV0Premises
import EraseProof.Test.NV1Premises
import EraseProof.Test.NV2Premises
import EraseProof.Test.DeclOf
import EraseProof.Oracle.Rename
import EraseProof.Core.State
import EraseProof.Core.RegisterInd
import EraseProof.Core.Glue
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
* `EraseProof.Source.Restrict`: source evaluation in the program restricts to a
  dependency-closed sub-environment.
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
* `EraseProof.Bridge.CLStore`: what con-leche's fold stores of the program's declarations.
* `EraseProof.Bridge.CLNames`: the names con-leche's acceptance binds are the program's, and every
  declaration of the program the fragment test may scan reads only names of the program.
* `EraseProof.Core.Collect`: the closure of the fragment test is part of the program
  (`collectDeps_sub`).
* `EraseProof.Core.CollectSpec`: the closure of the fragment test is closed under what the source
  semantics and the traversal read, with distinct kernames and block names (`collectDeps_spec`).
* `EraseProof.Oracle.Rename`: the pure oracle commutes with a renaming of free variables and keeps
  its results within the free variables of its inputs and locals; so do the markings (`MarkOf`).
* `EraseProof.Core.State`: the traversal's state invariant and the registration of constants.
* `EraseProof.Core.RegisterInd`: the registration of an inductive block keeps the invariant.
* `EraseProof.Core.Glue`: a returning run of `#erase`'s entry point on an input inside the
  fragment is a run of the pure path.
* `EraseProof.Statements`: the statements, as definitions of type `Prop`, that `spec.pin` pins.
-/
