import LeanToLambdaBox

/-!
Matches that the match compiler turns into something other than a plain `T.casesOn`:
- a match with a wildcard or an inaccessible pattern becomes a sparse `casesOn` (alternatives for
  some constructors, in the order of the match, then a catch-all for the others);
- the derived `BEq` and `DecidableEq` of a type with at least 10 constructors use per-constructor
  eliminators `T.c.elim`, which have one alternative and make the other constructors unreachable.
Each constructor gets its own alternative or the catch-all, and an unreachable one gets `□`. When
the catch-all is used and the discriminant is not a variable, the discriminant is let-bound, so that
it is computed once.

`check.ast` covers the generic path on user types: a catch-all for three constructors (`isRed`),
alternatives out of constructor order (`pick`), a catch-all that receives the discriminant
(`leftOr`), nested matches (`second`), a discriminant that is a call (`redCode`, `stepN`, and `step`,
which matches on its own recursive call), a match applied to an extra argument (`applyTo`) and an
eliminator applied directly (`viaElim`). Peregrine evaluates it to `B.t`, meaning that every
function returns Lean's value. `optVal.prune.ast` has a catch-all for a constructor with a proof
field, with constructor pruning. The other files cover the machine `Nat` and `Int` paths, where
the catch-all stands for either constructor, and a plain `casesOn` on each path.

The `#eval` at the end checks that each file with a discriminant that is a call refers once to the
function that computes it: without the `let`, every branch of the catch-all would compute it again.
-/

-- peregrine: validate check.ast
-- peregrine: eval check.ast
-- peregrine: validate optVal.prune.ast

namespace Cases

inductive B | f | t
inductive N | z | s (n : N)
inductive L | nil | cons (h : N) (t : L)

def and : B → B → B
  | .t, b => b
  | .f, _ => .f

def eqN : N → N → B
  | .z, .z => .t
  | .s m, .s n => eqN m n
  | _, _ => .f

def n1 : N := .s .z
def n2 : N := .s n1
def n3 : N := .s n2

inductive Color | red | green | blue | black

def isRed : Color → B
  | .red => .t
  | _ => .f

inductive Tri | a | b | c

def pick : Tri → N
  | .c => n3
  | .a => n1
  | _ => n2

inductive Tree | leaf | node (l : Tree) (v : N) (r : Tree)

def leftOr : Tree → Tree
  | .node l _ _ => l
  | t => t

def root : Tree → N
  | .node _ v _ => v
  | .leaf => .z

def second : L → N
  | .cons _ (.cons y _) => y
  | _ => .z

def colorOf : N → Color
  | .z => .red
  | .s _ => .blue

def code : Color → N
  | .red => .z
  | .green => n1
  | .blue => n2
  | .black => n3

def redCode (n : N) : N :=
  match colorOf n with
  | .red => n3
  | c => code c

def step : N → Color
  | .z => .green
  | .s n =>
    match step n with
    | .red => .blue
    | c => c

def stepN (n : N) : N :=
  match step n with
  | .green => n1
  | _ => .z

def applyTo (c : Color) (n : N) : N :=
  (match c with | .red => N.s | _ => fun m => .s (.s m)) n

inductive Big
  | c0 (n : N)
  | c1 (a b : N)
  | c2 | c3 | c4 | c5 | c6 | c7 | c8
  | c9 (n : N)

def viaElim (x : Big) (h : x.ctorIdx = 1) (k : N) : N :=
  Big.c1.elim (motive := fun _ => N → N) x h (fun _ b _ => b) k

/-- Each function applied to arguments, compared with Lean's value. -/
def check : B :=
  and (isRed .red) <| and (match isRed .blue with | .f => .t | .t => .f) <|
  and (eqN (pick .a) n1) <| and (eqN (pick .b) n2) <| and (eqN (pick .c) n3) <|
  and (eqN (root (leftOr (.node (.node .leaf n1 .leaf) n2 .leaf))) n1) <|
  and (eqN (root (leftOr .leaf)) .z) <|
  and (eqN (second (.cons n1 (.cons n2 .nil))) n2) <| and (eqN (second (.cons n1 .nil)) .z) <|
  and (eqN (redCode .z) n3) <| and (eqN (redCode n1) n2) <| and (eqN (stepN n3) n1) <|
  and (eqN (applyTo .red n1) n2) <| and (eqN (applyTo .green n1) n3) <|
  eqN (viaElim (.c1 n1 n2) rfl n3) n2
#guard check matches .t

inductive Opt
  | none
  | some (n : N) (h : n = n)

def optVal : Opt → N
  | .none => .z
  | _ => n1

def predOr0 : Nat → Nat
  | n + 1 => n
  | _ => 0

def isZero : Nat → Bool
  | .zero => true
  | _ => false

def sub2 (n : Nat) : Nat := n - 2

def predSub2 (n : Nat) : Nat :=
  match sub2 n with
  | k + 1 => k
  | m => m

def natCase : Nat → Nat
  | 0 => 3
  | n + 1 => n

def negPart : Int → Nat
  | .negSucc n => n
  | _ => 0

def natPart : Int → Nat
  | .ofNat n => n
  | _ => 0

def neg (n : Nat) : Int := -(n : Int)

def negOr (n : Nat) : Int :=
  match neg n with
  | .negSucc k => k
  | i => i

def intCase : Int → Nat
  | .ofNat n => n
  | .negSucc n => n

end Cases

open Cases in
#erase check to "check.ast"
#erase Cases.optVal config {remove_irrel_constr_args := true} to "optVal.prune.ast"
#erase Cases.predOr0 to "predOr0.ast"
#erase Cases.isZero to "isZero.ast"
#erase Cases.predSub2 to "predSub2.ast"
#erase Cases.natCase to "natCase.ast"
#erase Cases.negPart to "negPart.ast"
#erase Cases.natPart to "natPart.ast"
#erase Cases.negOr to "negOr.ast"
#erase Cases.intCase to "intCase.ast"

/-- The number of references to the constant `ns.id` in the file `file`. -/
def refs (file ns id : String) : IO Nat := do
  let s ← IO.FS.readFile file
  return (s.splitOn s!"(tConst ((MPdot (MPfile ()) \"{ns}\") \"{id}\"))").length - 1

#eval show IO Unit from do
  for (file, ns, id) in [("check.ast", "Cases", "step"), ("check.ast", "Cases", "colorOf"),
      ("predSub2.ast", "Cases", "sub2"), ("negOr.ast", "Cases", "neg")] do
    let n ← refs file ns id
    unless n == 1 do
      throw <| IO.userError s!"{file} refers to {ns}.{id} {n} times"
