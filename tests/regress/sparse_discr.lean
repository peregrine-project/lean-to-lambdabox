import LeanToLambdaBox

/-!
Matches whose discriminant is not a variable and whose sparse `casesOn` uses its catch-all
(register entry S-14). Lean v4.33's match compiler passes the discriminant to the catch-all; the
eraser binds the discriminant with `let discr := …` and the catch-all uses `discr`, so the
discriminant is evaluated once:
- the generic path: `stepN`, and `step`, which matches on its own recursive call (S-14's example:
  `step n` evaluates `step (n - 1)` once, so it takes linear time, not exponential time);
- the machine `Nat` path (`predSub2`) and the machine `Int` path (`negOr`), which already bind the
  discriminant to `n`; `n` is now bound to `discr`.
Two matches get no `let`: one that Lean compiles to a plain `casesOn` (`codeOf`), and one applied to
an extra argument (`shiftBy`), which `inlineMatchers` leaves as a β-redex whose parameter is the
discriminant, so that the `casesOn` receives a variable.
The `#eval` below checks that each file refers once to the function that computes the discriminant
(`Discr.step`, `sub2`, `neg`, `colorOf`). Without the `let`, the catch-all of `stepN`, `predSub2`
and `negOr` adds one reference per constructor that has no alternative. Under Peano naturals,
peregrine evaluates `all.ast` to Lean's value 26.
-/

-- peregrine: validate all.ast
-- peregrine: eval all.ast

namespace Discr

inductive Color | red | green | blue

def step : Nat → Color
  | 0 => .green
  | n + 1 =>
    match step n with
    | .red => .blue
    | c => c

def stepN (n : Nat) : Nat :=
  match step n with
  | .green => 1
  | _ => 0
#erase stepN to "stepN.ast"

def colorOf (n : Nat) : Color := if n = 0 then .red else .blue

def code : Color → Nat
  | .red => 1
  | .green => 2
  | .blue => 3

def shiftBy (n k : Nat) : Nat :=
  (match colorOf n with
   | .red => (· + 1)
   | c => (code c + ·)) k
#erase shiftBy to "shiftBy.ast"

def sub2 (n : Nat) : Nat := n - 2

def predSub2 (n : Nat) : Nat :=
  match sub2 n with
  | k + 1 => k
  | m => m
#erase predSub2 to "predSub2.ast"

def neg (n : Nat) : Int := -(n : Int)

def negOr (n : Nat) : Int :=
  match neg n with
  | .negSucc k => k
  | i => i
#erase negOr to "negOr.ast"

def codeOf (n : Nat) : Nat :=
  match colorOf n with
  | .red => 1
  | .green => 2
  | .blue => 3
#erase codeOf to "codeOf.ast"

/-- `1 + 6 + 0 + 2 + 0 + 6 + 8 + 3 = 26`. -/
def all : Nat :=
  stepN 16 + predSub2 9 + predSub2 1 + (negOr 3).toNat + (negOr 0).toNat + shiftBy 0 5 +
    shiftBy 1 5 + codeOf 1
#guard all = 26

/-- The number of references to the constant `Discr.<name>` in the emitted file `file`. -/
def constRefs (file name : String) : IO Nat := do
  let s ← IO.FS.readFile file
  return (s.splitOn s!"(tConst ((MPdot (MPfile ()) \"Discr\") \"{name}\"))").length - 1

#eval show IO Unit from do
  let mut wrong := #[]
  for (file, name) in [("stepN.ast", "step"), ("shiftBy.ast", "colorOf"), ("predSub2.ast", "sub2"),
      ("negOr.ast", "neg"), ("codeOf.ast", "colorOf")] do
    let n ← constRefs file name
    unless n == 1 do
      wrong := wrong.push s!"{file} refers to Discr.{name} {n} times"
  unless wrong.isEmpty do
    throw <| IO.userError s!"expected one reference each: {wrong.toList}"

end Discr

#erase Discr.all config {nat := .peano, extern := .preferLogical} to "all.ast"
