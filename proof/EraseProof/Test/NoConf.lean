import EraseProof.Metatheory.NoConf

/-!
Pins the axiom footprint of the no-confusion lemmas of `EraseProof.Metatheory.NoConf` to
`propext`, `Classical.choice` and `Quot.sound`: they reach neither `sorryAx` nor Metalean's
`Cardinal.exists_inaccessibles`.
-/

/-- info: 'EraseProof.TypeEq.sort_ne_forallE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms EraseProof.TypeEq.sort_ne_forallE

/-- info: 'EraseProof.TypeEq.sort_ne_ind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms EraseProof.TypeEq.sort_ne_ind

/-- info: 'EraseProof.TypeEq.forallE_ne_ind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms EraseProof.TypeEq.forallE_ne_ind

/-- info: 'EraseProof.TypeEq.sort_ne_quot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms EraseProof.TypeEq.sort_ne_quot

/-- info: 'EraseProof.TypeEq.forallE_ne_quot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms EraseProof.TypeEq.forallE_ne_quot

/-- info: 'EraseProof.TypeEq.ind_ne_quot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms EraseProof.TypeEq.ind_ne_quot
