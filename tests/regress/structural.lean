import LeanToLambdaBox

/-!
Under `structural := .kernel` (register entry S-42), a definition by structural recursion is erased
through its kernel definition, which applies `T.brecOn` (and so the recursor `T.rec`, erased since
S-40) to a function of the `T.below` table, instead of through the `_unsafe_rec` definition that
the code generator compiles. `declInfoCore` makes the choice on the `Meta` path; the checks below
show it on:
- `ST.add` (recursion on the second argument of `Nat`): the kernel definition under
  `nat := .peano`; the `_unsafe_rec` definition by default, and under `nat := .machine`, where
  `Nat.rec` stays a constant;
- `ST.wfHalf` (well-founded recursion) and `ST.loop` (`partial`): the `_unsafe_rec` definition;
- `Nat.recCompiled`, the `@[csimp]` replacement of `Nat.rec`: the `_unsafe_rec` definition (its
  kernel definition applies `Nat.rec` through `Nat.brecOn`, which csimp replaces by
  `Nat.recCompiled` again);
- `ST.Tree.size` (a nested inductive, whose recursor stays a constant): the `_unsafe_rec`
  definition.

Under `structural := .kernel` the fragment test admits a definition by structural recursion
(register entry S-44), and the pure oracle reduces recursor applications (S-43), which the types
of the `below` tables need. The programs below are in the fragment and take the pure path, unless
stated otherwise, and `#erase` writes them under `nat := .peano`:
- `useAdd`: `add 2 3`; `useAddDefault` is the same without the flag (outside the fragment, the
  `Meta` path, through `add._unsafe_rec`), and `useAddNoCsimp` without `csimp` (which the pure
  path does not apply);
- `useLength`: `List.length` (with `extern := .preferLogical`, since `List.length` adds with
  `Nat.add`, which is `@[extern]`);
- `useMap`: the second element of a `List.map`, and `usePairs`: a recursion two constructors deep
  (`_ :: _ :: t`); their `match` has a wildcard pattern, which Lean compiles with a sparse
  `casesOn` that tests constructor indices with `Nat.land`, defined by well-founded recursion
  (`Nat.bitwise`), so they stay outside the fragment and take the `Meta` path, which erases
  `List.mapTR` and `pairs` through their kernel definitions;
- `usePairs2`: the recursion of `usePairs` with exhaustive patterns, read from the `below` table;
- `useEv`: `isEv 3`, for the mutual structural recursion `isEv`/`isOd` on `Nat`, which the
  fragment test excludes as a mutual block (register entry S-51), so it takes the `Meta` path;
- `useGet`: a recursion with a `Prop` argument `i < l.length`, erased to □.
peregrine evaluates them to 5, 5, 5, 3, `t`, 2, 2, `false` and `t` (peregrine prints a list without
its elements, so `useMap` takes one). The fragment test excludes `ST.wfHalf` (well-founded
recursion), `ST.loop` (`partial`) and `ST.Tree.size` (a mutual block with its local function
`sizes`, over a nested inductive), and, without the flag, `ST.add`.
-/

-- peregrine: validate useAdd.ast
-- peregrine: eval useAdd.ast
-- peregrine: validate useAddDefault.ast
-- peregrine: eval useAddDefault.ast
-- peregrine: validate useAddNoCsimp.ast
-- peregrine: eval useAddNoCsimp.ast
-- peregrine: validate useLength.ast
-- peregrine: eval useLength.ast
-- peregrine: validate useMap.ast
-- peregrine: eval useMap.ast
-- peregrine: validate useEv.ast
-- peregrine: eval useEv.ast
-- peregrine: validate usePairs.ast
-- peregrine: eval usePairs.ast
-- peregrine: validate usePairs2.ast
-- peregrine: eval usePairs2.ast
-- peregrine: validate useGet.ast
-- peregrine: eval useGet.ast

open Lean Erasure

namespace ST
inductive B | f | t

def neg : B → B
  | .f => .t
  | .t => .f

def add : Nat → Nat → Nat
  | n, 0 => n
  | n, m + 1 => (add n m).succ
def useAdd : Nat := add 2 3

def useLength : Nat := [B.t, B.f, B.t].length
def useMap : B := match [B.t, B.f].map neg with
  | _ :: b :: _ => b
  | _ => B.f

mutual
def isEv : Nat → Bool
  | 0 => true
  | n + 1 => isOd n
def isOd : Nat → Bool
  | 0 => false
  | n + 1 => isEv n
end
def useEv : Bool := isEv 3

def pairs : List B → Nat
  | _ :: _ :: t => (pairs t).succ
  | _ => 0
def usePairs : Nat := pairs [B.t, B.f, B.t, B.f, B.t]

def pairs2 : List B → Nat
  | [] => 0
  | [_] => 0
  | _ :: _ :: t => (pairs2 t).succ
def usePairs2 : Nat := pairs2 [B.t, B.f, B.t, B.f, B.t]

def get : (l : List B) → (i : Nat) → i < l.length → B
  | a :: _, 0, _ => a
  | _ :: t, i + 1, h => get t i (Nat.lt_of_succ_lt_succ h)
def useGet : B := get [B.f, B.t, B.f] 1 (by decide)

def wfHalf (n : Nat) : Nat := if n = 0 then 0 else (wfHalf (n / 2)).succ
termination_by n
decreasing_by omega

partial def loop (n : Nat) : Nat := loop n

inductive Tree | node : List Tree → Tree
def Tree.size : Tree → Nat
  | .node ts => (sizes ts).succ
where sizes : List Tree → Nat
  | [] => 0
  | t :: ts => t.size + sizes ts
end ST

/-- The declaration that `declInfoCore` erases `n` through, under `cfg`. -/
def decl (cfg : ErasureConfig) (n : Name) : CoreM Unit := do
  logInfo m!"{((← declInfoCore cfg n).map (·.name)).getD .anonymous}"

/-- info: ST.add -/
#guard_msgs in #eval decl { nat := .peano, structural := .kernel } ``ST.add
/-- info: ST.add._unsafe_rec -/
#guard_msgs in #eval decl { nat := .peano } ``ST.add
/-- info: ST.add._unsafe_rec -/
#guard_msgs in #eval decl { structural := .kernel } ``ST.add
/-- info: ST.isOd -/
#guard_msgs in #eval decl { nat := .peano, structural := .kernel } ``ST.isOd
/-- info: ST.wfHalf._unsafe_rec -/
#guard_msgs in #eval decl { nat := .peano, structural := .kernel } ``ST.wfHalf
/-- info: ST.loop._unsafe_rec -/
#guard_msgs in #eval decl { nat := .peano, structural := .kernel } ``ST.loop
/-- info: Nat.recCompiled._unsafe_rec -/
#guard_msgs in #eval decl { nat := .peano, structural := .kernel } ``Nat.recCompiled
/-- info: Nat.recCompiled -/
#guard_msgs in
#eval decl { nat := .peano, structural := .kernel, csimp := false } ``Nat.recCompiled
/-- info: ST.Tree.size._unsafe_rec -/
#guard_msgs in #eval decl { nat := .peano, structural := .kernel } ``ST.Tree.size

/-- The fragment test's verdict on the constant `n` under `nat := .peano, structural := .kernel`. -/
def check (n : Name) : CoreM Unit := do
  match collectDeps (EnvView.ofEnvironment (← getEnv)) { nat := .peano, structural := .kernel }
      (.const n []) with
  | .ok _ => logInfo "in the fragment"
  | .error err => logInfo err.describe

def ST.useWf : Nat := ST.wfHalf 6
def ST.useLoop : Nat := ST.loop 0
def ST.useTree : Nat := ST.Tree.size (.node [])

/-- info: in the fragment -/
#guard_msgs in
#eval check ``ST.useAdd
/-- info: in the fragment -/
#guard_msgs in
#eval check ``ST.useLength
/-- info: outside the fragment: recursive definition Nat.bitwise -/
#guard_msgs in
#eval check ``ST.useMap
/-- info: outside the fragment: mutual block [ST.isEv, ST.isOd] -/
#guard_msgs in
#eval check ``ST.useEv
/-- info: outside the fragment: recursive definition Nat.bitwise -/
#guard_msgs in
#eval check ``ST.usePairs
/-- info: in the fragment -/
#guard_msgs in
#eval check ``ST.usePairs2
/-- info: in the fragment -/
#guard_msgs in
#eval check ``ST.useGet
/-- info: outside the fragment: recursive definition ST.wfHalf -/
#guard_msgs in
#eval check ``ST.useWf
/-- info: outside the fragment: partial definition ST.loop -/
#guard_msgs in
#eval check ``ST.useLoop
/-- info: outside the fragment: mutual block [ST.Tree.size.sizes, ST.Tree.size] -/
#guard_msgs in
#eval check ``ST.useTree
/-- info: outside the fragment: recursive definition ST.add -/
#guard_msgs in
#eval show CoreM Unit from do
  match collectDeps (EnvView.ofEnvironment (← getEnv)) { nat := .peano } (.const ``ST.useAdd []) with
  | .ok _ => logInfo "in the fragment"
  | .error err => logInfo err.describe

#guard_msgs (drop warning, drop info) in
#erase ST.useAdd config {nat := .peano, structural := .kernel} to "useAdd.ast"
#guard_msgs (drop warning, drop info) in
#erase ST.useAdd config {nat := .peano} to "useAddDefault.ast"
#guard_msgs (drop warning, drop info) in
#erase ST.useAdd config {nat := .peano, structural := .kernel, csimp := false} to "useAddNoCsimp.ast"
#guard_msgs (drop warning, drop info) in
#erase ST.useLength config {nat := .peano, extern := .preferLogical, structural := .kernel} to "useLength.ast"
#guard_msgs (drop warning, drop info) in
#erase ST.useMap config {nat := .peano, structural := .kernel} to "useMap.ast"
#guard_msgs (drop warning, drop info) in
#erase ST.useEv config {nat := .peano, structural := .kernel} to "useEv.ast"
#guard_msgs (drop warning, drop info) in
#erase ST.usePairs config {nat := .peano, structural := .kernel} to "usePairs.ast"
#guard_msgs (drop warning, drop info) in
#erase ST.usePairs2 config {nat := .peano, structural := .kernel} to "usePairs2.ast"
#guard_msgs (drop warning, drop info) in
#erase ST.useGet config {nat := .peano, structural := .kernel} to "useGet.ast"

/-! `Erasure.usesConst` is evaluated by the kernel (S-49). -/
example : usesConst (· == `B.t) (.app (.const `f []) (.const `B.t [])) = true := by decide
example : usesConst (· == `B.f) (.app (.const `f []) (.const `B.t [])) = false := by decide
