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

The fragment test excludes definitions with an `_unsafe_rec` companion, so the programs below take
the `Meta` path, and `#erase` writes them under `nat := .peano`:
- `useAdd`: `add 2 3`; `useAddDefault` is the same without the flag, and `useAddNoCsimp` without
  `csimp` (`Nat.brecOn` then applies `Nat.rec` itself, which `visitRec` erases, instead of
  `Nat.recCompiled`);
- `useLength`, `useMap`: `List.length`, and the second element of a `List.map` (through their
  `@[csimp]` replacements `List.lengthTR` and `List.mapTR`, whose auxiliary functions are
  structural; peregrine prints a list without its elements);
- `useEv`: `isEv 3`, for the mutual structural recursion `isEv`/`isOd` on `Nat`;
- `usePairs`: a recursion two constructors deep (`_ :: _ :: t`), read from the `below` table;
- `useGet`: a recursion with a `Prop` argument `i < l.length`, erased to □.
peregrine evaluates them to 5, 5, 5, 3, `t`, `false`, 2 and `t`.
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

/-- info: outside the fragment: recursive definition ST.add -/
#guard_msgs in
#eval check ``ST.useAdd

#guard_msgs (drop warning, drop info) in
#erase ST.useAdd config {nat := .peano, structural := .kernel} to "useAdd.ast"
#guard_msgs (drop warning, drop info) in
#erase ST.useAdd config {nat := .peano} to "useAddDefault.ast"
#guard_msgs (drop warning, drop info) in
#erase ST.useAdd config {nat := .peano, structural := .kernel, csimp := false} to "useAddNoCsimp.ast"
#guard_msgs (drop warning, drop info) in
#erase ST.useLength config {nat := .peano, structural := .kernel} to "useLength.ast"
#guard_msgs (drop warning, drop info) in
#erase ST.useMap config {nat := .peano, structural := .kernel} to "useMap.ast"
#guard_msgs (drop warning, drop info) in
#erase ST.useEv config {nat := .peano, structural := .kernel} to "useEv.ast"
#guard_msgs (drop warning, drop info) in
#erase ST.usePairs config {nat := .peano, structural := .kernel} to "usePairs.ast"
#guard_msgs (drop warning, drop info) in
#erase ST.useGet config {nat := .peano, structural := .kernel} to "useGet.ast"
