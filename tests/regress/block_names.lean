import LeanToLambdaBox

/-!
A mutual inductive block is named by `mutualBlockKername`: its members' names printed without
`«»` escapes, joined. The test checks:
- the kernel evaluates the name (`decide`): `B` and `P2` give the ids `B` and `P2`, which differ,
  and `«weird ind»` gives `weird_u32ind` (the escaping printer gives `_u171weird_u32ind_u187`
  through a `partial` function, which the kernel does not evaluate);
- `pick.ast`, a program over `BlockNames.«weird ind»`, declares its block under
  `BlockNames_u46weird_u32ind` and uses that name for its constructors and its case; peregrine
  validates it and evaluates it to the constructor `b`;
- two inductives whose names differ only by `«»` quoting, `BlockNames.«c.d»` and
  `BlockNames.c.d`, have one block name (register entry R-3); a program over both is an error of
  `#erase` on both paths (register entry S-52): on the `Meta` path (a Nat literal under the default
  configuration) the program has two declarations of that kername, and on the pure path (under
  `nat := .peano`) `collectDeps` finds the collision.
-/

-- peregrine: validate pick.ast
-- peregrine: eval pick.ast

open Lean

example : (mutualBlockKername [`B]).id = "B" := by decide
example : (mutualBlockKername [`P2]).id = "P2" := by decide
example : (mutualBlockKername [`B] == mutualBlockKername [`P2]) = false := by decide
example : (mutualBlockKername [Name.mkSimple "weird ind"]).id = "weird_u32ind" := by decide

namespace BlockNames

inductive «weird ind» | a | b

def flip (x : «weird ind») : «weird ind» := «weird ind».casesOn (motive := fun _ => «weird ind») x .b .a

def pick : «weird ind» := flip .a

inductive «c.d» | p
inductive c.d | q
def pickBoth (_ : «c.d») (_ : c.d) : Nat := 0
def useBoth : Nat := pickBoth .p .q

end BlockNames

#erase BlockNames.pick to "pick.ast"

example : mutualBlockKername [`BlockNames.«c.d»] = mutualBlockKername [`BlockNames.c.d] := by decide

/-- The route of `useBoth` under `cfg`. -/
def routeBoth (cfg : Erasure.ErasureConfig) : CoreM Unit := do
  match Erasure.route (Erasure.EnvView.ofEnvironment (← getEnv)) cfg (.const ``BlockNames.useBoth []) with
  | .viaPure (.ok _) => logInfo "pure path"
  | .viaPure (.error err) => logInfo s!"pure path, error: {err.describe}"
  | .viaMeta => logInfo "Meta path"

/-- info: Meta path -/
#guard_msgs in #eval routeBoth {}
/-- info: pure path, error: the constants BlockNames.c.d and BlockNames.«c.d» have the same kername -/
#guard_msgs in #eval routeBoth {nat := .peano}

/-- error: erasure failed: two declarations of the program have the kername ((MPfile ()) "BlockNames_u46c_u46d") -/
#guard_msgs (error) in
#erase BlockNames.useBoth to "both.ast"
/-- error: erasure failed: the constants BlockNames.c.d and BlockNames.«c.d» have the same kername -/
#guard_msgs (error) in
#erase BlockNames.useBoth config {nat := .peano} to "both.peano.ast"
