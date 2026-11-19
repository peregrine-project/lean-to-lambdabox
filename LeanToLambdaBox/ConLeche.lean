import ConLeche.MainTheorem

/-!
Checks that the eraser, which does not use the module system, can import con-leche, which does, and
pins the axioms of its main theorem and of its consequence for `False`. Neither depends on an
axiom beyond Lean's three; con-leche's set theory is a hypothesis of `ConLeche.model_exists`, not
an axiom.
-/

/-- info: 'ConLeche.model_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConLeche.model_exists

/-- info: 'ConLeche.no_False_declaration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConLeche.no_False_declaration
