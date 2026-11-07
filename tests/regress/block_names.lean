import LeanToLambdaBox

/-!
A mutual inductive block is named by `mutualBlockKername`: its members' names printed without
`«»` escapes, joined. The test checks:
- the kernel evaluates the name (`decide`): `B` and `P2` give the ids `B` and `P2`, which differ,
  and `«weird ind»` gives `weird_u32ind` (the escaping printer gives `_u171weird_u32ind_u187`
  through a `partial` function, which the kernel does not evaluate);
- `pick.ast`, a program over `BlockNames.«weird ind»`, declares its block under
  `BlockNames_u46weird_u32ind` and uses that name for its constructors and its case; peregrine
  validates it and evaluates it to the constructor `b`.
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

end BlockNames

#erase BlockNames.pick to "pick.ast"
