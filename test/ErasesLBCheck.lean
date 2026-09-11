/-
The composite's interface, measured: for every introduction lemma of `ErasesLB` and
`ErasesLBFix`, its full statement and its axiom footprint.
`scripts/erasesLB.sh` runs this file and diffs its output against `test/erasesLB.expected`.
A premise added to or dropped from one of these lemmas changes the fixture, which is what
makes a silent weakening of the composite visible; `test/Ledger.lean` measures the top-level
results and this file measures the layer they are composed out of.
-/
import LeanToLambdaBox.ErasesLB

open LeanToLambdaBox

#check @ErasesLB
#check @ErasesLBAlt
#check @ErasesLBAlts
#check @ErasesLBFixAlt
#check @ErasesLBFixAlts

#check @Erases.mkApps
#check @ErasesLB.exists_mid
#check @ErasesLB.box
#check @ErasesLB.app
#check @ErasesLB.ctor_head
#check @ErasesLB.ctor
#check @ErasesLB.fix
#check @ErasesLB.cases
#check @erasesLB_of_spine

#check @ErasesLBFix.of_erasesLB
#check @ErasesLBFix.exists_erasesLB
#check @ErasesLBFix.exists_mid
#check @ErasesLBFix.fixvar
#check @ErasesLBFix.box
#check @ErasesLBFix.app
#check @ErasesLBFix.ctor_head
#check @ErasesLBFix.ctor
#check @ErasesLBFix.cases
#check @ErasesLBFix.fix

#print axioms LeanToLambdaBox.Erases.mkApps
#print axioms LeanToLambdaBox.ErasesLB.box
#print axioms LeanToLambdaBox.ErasesLB.app
#print axioms LeanToLambdaBox.ErasesLB.ctor_head
#print axioms LeanToLambdaBox.ErasesLB.ctor
#print axioms LeanToLambdaBox.ErasesLB.fix
#print axioms LeanToLambdaBox.ErasesLB.cases
#print axioms LeanToLambdaBox.erasesLB_of_spine
#print axioms LeanToLambdaBox.ErasesLBFix.fixvar
#print axioms LeanToLambdaBox.ErasesLBFix.box
#print axioms LeanToLambdaBox.ErasesLBFix.app
#print axioms LeanToLambdaBox.ErasesLBFix.ctor_head
#print axioms LeanToLambdaBox.ErasesLBFix.ctor
#print axioms LeanToLambdaBox.ErasesLBFix.cases
#print axioms LeanToLambdaBox.ErasesLBFix.fix
