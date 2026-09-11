/-
The trust ledger: the axiom footprint of the top-level results, measured.
`scripts/ledger.sh` runs this file and diffs its output against `test/ledger.expected`.
One `#print axioms` per line; a result whose footprint changes changes the fixture.
The commented lines are the ledger of `doc/rework/01-DESIGN.md` §4.14: each is uncommented
by the wave that proves the theorem it names. The rows below them are the §5 theorems that
already exist — subject reduction, the fragment of the pass simulation covered so far under
the names it is proved at, the `optimize` corollary and the certified evaluator.
Provenance for the axiom names printed here lives in `doc/trust.md`, the single home of
the trust rows.
-/
import LeanToLambdaBox

-- #print axioms LeanToLambdaBox.erases_correct
-- #print axioms LeanToLambdaBox.lower_correct
-- #print axioms LeanToLambdaBox.lowerFix_correct
-- #print axioms LeanToLambdaBox.visitExpr_refines_erasesLB
-- #print axioms LeanToLambdaBox.visitExpr_refines_erasesLBFix
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorder
#print axioms LeanToLambdaBox.Green.green_G1
-- #print axioms LeanToLambdaBox.Green.green_G8

#print axioms LeanToLambdaBox.SEval.defeq
#print axioms LeanToLambdaBox.lower_correct_deltaChain
#print axioms LeanToLambdaBox.lowerFix_correct_atom
#print axioms LeanToLambdaBox.LBOptimize_correct
#print axioms LeanToLambdaBox.lbEval_sound
