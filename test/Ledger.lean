/-
The trust ledger: the axiom footprint of the top-level results, measured.
`scripts/ledger.sh` runs this file and diffs its output against `test/ledger.expected`.
One `#print axioms` per line; a result whose footprint changes changes the fixture.
The commented lines are the ledger of `doc/rework/01-DESIGN.md` §4.14 that no theorem
inhabits yet: each is uncommented by the wave that proves the theorem it names. The rows
below them are the §5 theorems that exist — the simulation and its three arms, the
corollaries of `ErasesEnv` and of `UpstreamAsks` the arms spend, the first-order answer,
the pass layer's two transports, subject reduction, the `optimize` corollary, the certified
evaluator, and one line per green rung. `ErasesEnv.tabled`'s discharge is measured as its
two halves, `constants_of_tabled` and `constOrigin_of_constants`: the step between them is
filed ask 4 and no theorem spans it.
Provenance for the axiom names printed here lives in `doc/trust.md`, the single home of
the trust rows; `#print axioms` measures a proved theorem's footprint and cannot measure a
hypothesis, so the class of each binder — including `hev`, which `green_G5` is the first
rung to inhabit — is a `doc/trust.md` row and not a line of the fixture.
-/
import LeanToLambdaBox

#print axioms LeanToLambdaBox.erases_correct
#print axioms LeanToLambdaBox.erases_correct_lb
#print axioms LeanToLambdaBox.erases_correct_of_steps
#print axioms LeanToLambdaBox.step_iota
#print axioms LeanToLambdaBox.step_proj
#print axioms LeanToLambdaBox.step_delta
#print axioms LeanToLambdaBox.simulate_of_erases_correct
#print axioms LeanToLambdaBox.ErasesEnv.runtimeKey_isCasesOn
#print axioms LeanToLambdaBox.erases_elimSpine_no_value
#print axioms LeanToLambdaBox.ErasesEnv.ctorArity
#print axioms LeanToLambdaBox.not_erasable_of_informative
#print axioms LeanToLambdaBox.CasesOnShape.agree
#print axioms LeanToLambdaBox.ElimDecl.uniq
#print axioms LeanToLambdaBox.neverZeroB_sound
#print axioms LeanToLambdaBox.Lower.appReady
#print axioms LeanToLambdaBox.firstorder_erases_deterministic
#print axioms LeanToLambdaBox.firstorder_no_box
#print axioms LeanToLambdaBox.fOFields_of_asks
#print axioms LeanToLambdaBox.LowerBlock.lambda_of_fixLambda
#print axioms LeanToLambdaBox.Lower.constToFix
#print axioms LeanToLambdaBox.constants_of_tabled
#print axioms LeanToLambdaBox.constOrigin_of_constants
-- #print axioms LeanToLambdaBox.visitExpr_refines_erasesLB
-- #print axioms LeanToLambdaBox.visitExpr_refines_erasesLBFix
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorder
#print axioms LeanToLambdaBox.Green.green_G1
#print axioms LeanToLambdaBox.Green.green_G2
#print axioms LeanToLambdaBox.Green.green_G3
#print axioms LeanToLambdaBox.Green.green_G4
#print axioms LeanToLambdaBox.Green.green_G5
#print axioms LeanToLambdaBox.Green.green_G6
#print axioms LeanToLambdaBox.Green.g5_seval
#print axioms LeanToLambdaBox.Green.spikeNatFacts_natEnv
-- #print axioms LeanToLambdaBox.Green.green_G8

#print axioms LeanToLambdaBox.SEval.defeq
#print axioms LeanToLambdaBox.LBOptimize_correct
#print axioms LeanToLambdaBox.lbEval_sound
