/-
The trust ledger: the axiom footprint of the top-level results, measured.
`scripts/ledger.sh` runs this file and diffs the output against `test/ledger.expected`.
One `#print axioms` per line; a result whose footprint changes changes the fixture.
-/
import LeanToLambdaBox.ColdStart
import LeanToLambdaBox.VisitExprRefines
import LeanToLambdaBox.ErasesCorrect
import LeanToLambdaBox.Optimize

#print axioms LeanToLambdaBox.shipping_erase_correct_firstorder_coldstart
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorderι_coldstart
#print axioms LeanToLambdaBox.visitExpr_refines_erases
#print axioms LeanToLambdaBox.erases_correct
#print axioms LeanToLambdaBox.LBOptimize_correct
