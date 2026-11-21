import LeanToLambdaBox

/-!
The fragment test excludes a definition, theorem or opaque of a mutual block, whose `all` is not
the list of its own name alone (register entry S-51). Under `structural := .kernel`, a mutual block
defined by structural recursion has no `_unsafe_rec` exclusion, and its members share one
`brecOn`; the test checks that it is now outside the fragment and takes the `Meta` path:
- `useEven`: `even (s (s (s z)))` for the block `even`/`odd` on a Peano type `LN`, as in
  `lcnf.lean`, under `{nat := .peano, structural := .kernel}`; `ST.useEv` of `structural.lean`
  is the same block shape on `Nat`;
- `usePf`: a function applied to the theorem `evT` of the mutual block `evT`/`odT`, under the
  default configuration; the closure reads the theorem's type only, so before S-51 the program is
  in the fragment under every configuration (a proof `evT (s z)` in a definition is abstracted by
  Lean into an auxiliary theorem `usePf._proof_1`, whose value the closure does not read);
- `useSingle`: a definition by structural recursion alone in its block (`all` is its own name),
  which stays in the fragment.
`#erase` writes `useEven`, `usePf` and `useSingle`; peregrine evaluates them to `MB.LB.f`,
`MB.LB.t` and `MB.LB.t`.
-/

-- peregrine: validate useEven.ast
-- peregrine: eval useEven.ast
-- peregrine: validate usePf.ast
-- peregrine: eval usePf.ast
-- peregrine: validate useSingle.ast
-- peregrine: eval useSingle.ast

open Lean Erasure

namespace MB
inductive LN | z | s (n : LN)
inductive LB | f | t

mutual
  def even : LN → LB
    | .z => .t
    | .s n => odd n
  def odd : LN → LB
    | .z => .f
    | .s n => even n
end
def useEven : LB := even (.s (.s (.s .z)))

mutual
  theorem evT : LN → True
    | .z => trivial
    | .s n => odT n
  theorem odT : LN → True
    | .z => trivial
    | .s n => evT n
end
def withAll (_ : LN → True) : LB := .t
def usePf : LB := withAll evT

def isZ : LN → LB
  | .z => .t
  | .s n => isZ n
def useSingle : LB := isZ (.s .z)
end MB

/-- The blocks, as the declarations record them. -/
def blocks (ns : List Name) : CoreM Unit := do
  for n in ns do logInfo m!"{n}: {(← getConstInfo n).all}"

/-- info: MB.even: [MB.even, MB.odd]
---
info: MB.evT: [MB.evT, MB.odT]
---
info: MB.isZ: [MB.isZ]
-/
#guard_msgs in
#eval blocks [``MB.even, ``MB.evT, ``MB.isZ]

/-- The fragment test's verdict on the constant `n` under `cfg`, and the route of `#erase`. -/
def check (cfg : ErasureConfig) (n : Name) : CoreM Unit := do
  let view := EnvView.ofEnvironment (← getEnv)
  let verdict := match collectDeps view cfg (.const n []) with
    | .ok _ => "in the fragment"
    | .error err => err.describe
  let r := match route view cfg (.const n []) with
    | .viaPure (.ok _) => "pure path"
    | .viaPure (.error err) => s!"pure path, error: {err.describe}"
    | .viaMeta => "Meta path"
  logInfo s!"{verdict}; {r}"

/-- info: outside the fragment: mutual block [MB.even, MB.odd]; Meta path -/
#guard_msgs in
#eval check { nat := .peano, structural := .kernel } ``MB.useEven
/-- info: outside the fragment: recursive definition MB.even; Meta path -/
#guard_msgs in
#eval check { nat := .peano } ``MB.useEven
/-- info: outside the fragment: mutual block [MB.evT, MB.odT]; Meta path -/
#guard_msgs in
#eval check {} ``MB.usePf
/-- info: outside the fragment: mutual block [MB.evT, MB.odT]; Meta path -/
#guard_msgs in
#eval check { nat := .peano, structural := .kernel } ``MB.usePf
/-- info: in the fragment; pure path -/
#guard_msgs in
#eval check { nat := .peano, structural := .kernel } ``MB.useSingle

#guard_msgs (drop warning, drop info) in
#erase MB.useEven config {nat := .peano, structural := .kernel} to "useEven.ast"
#guard_msgs (drop warning, drop info) in
#erase MB.usePf to "usePf.ast"
#guard_msgs (drop warning, drop info) in
#erase MB.useSingle config {nat := .peano, structural := .kernel} to "useSingle.ast"
