import LeanToLambdaBox

/-!
Matches that Lean v4.33 compiles to a sparse `casesOn` (alternatives for some constructors, then a
catch-all) or to per-constructor eliminators `T.c.elim` (register entry S-13), on each path of
`Erasure.visitCases`:
- the generic path: a catch-all for three constructors (`isRed`), alternatives given in another
  order than the constructors' (`pick`: `.c`, then `.a`), a catch-all that receives the scrutinee
  (`leftOr`), nested matches on `List` (`second`), a discriminant that is not a variable
  (`redCode`), a catch-all for a constructor with a proof field, with and without pruning (`optVal`),
  and a match applied to an extra argument (`applyTo`);
- the machine `Nat` path: the catch-all stands for `Nat.zero` (`predOr0`) or for `Nat.succ`
  (`isZero`);
- the machine `Int` path: the catch-all stands for `Int.ofNat` (`negPart`) or for `Int.negSucc`
  (`natPart`);
- per-constructor eliminators, which have no catch-all: `Big.c1.elim` called directly with an extra
  argument (`viaElim`), and the derived `BEq` of an inductive with 10 constructors (`bigEq`).
`checks` applies the functions to arguments and pairs each result with Lean's value, which `#guard`
checks. Under Peano naturals, peregrine evaluates `count.ast` (the number of results equal to Lean's
value) to 25 and `sum.ast` (the sum of the results) to 90; its printer shows only the last field of
a constructor, so the results are not evaluated as a list. `bigEq` is left out of `checks`, as the
derived `BEq` casts with `Eq.ndrec`, which reaches the axiom `Eq.rec`.
-/

-- peregrine: validate count.ast
-- peregrine: eval count.ast
-- peregrine: validate sum.ast
-- peregrine: eval sum.ast

namespace Sparse

inductive Color | red | green | blue | black

def isRed : Color → Bool
  | .red => true
  | _ => false
#erase isRed to "isRed.ast"

inductive Tri | a | b | c

def pick : Tri → Nat
  | .c => 3
  | .a => 1
  | _ => 7
#erase pick to "pick.ast"

inductive Tree | leaf | node (l : Tree) (v : Nat) (r : Tree)

def leftOr : Tree → Tree
  | .node l _ _ => l
  | t => t
#erase leftOr to "leftOr.ast"

def root : Tree → Nat
  | .node _ v _ => v
  | .leaf => 9

def second : List Nat → Nat
  | _ :: y :: _ => y
  | _ => 0
#erase second to "second.ast"

def colorOf (n : Nat) : Color := if n = 0 then .red else .blue

def code : Color → Nat
  | .red => 1
  | .green => 2
  | .blue => 3
  | .black => 4

def redCode (n : Nat) : Nat :=
  match colorOf n with
  | .red => 10
  | c => code c
#erase redCode to "redCode.ast"

inductive Opt
  | none
  | some (n : Nat) (h : 0 < n)

def optVal : Opt → Nat
  | .none => 0
  | _ => 1
#erase optVal to "optVal.ast"
#erase optVal config {remove_irrel_constr_args := true} to "optVal.prune.ast"

def applyTo (c : Color) (n : Nat) : Nat :=
  (match c with | .red => (· + 1) | _ => (· * 2)) n
#erase applyTo to "applyTo.ast"

def predOr0 : Nat → Nat
  | n + 1 => n
  | _ => 0
#erase predOr0 to "predOr0.ast"

def isZero : Nat → Nat
  | .zero => 1
  | _ => 0
#erase isZero to "isZero.ast"

def negPart : Int → Nat
  | .negSucc n => n + 1
  | _ => 0
#erase negPart to "negPart.ast"

def natPart : Int → Nat
  | .ofNat n => n
  | _ => 0
#erase natPart to "natPart.ast"

inductive Big
  | c0 (n : Nat)
  | c1 (a b : Nat)
  | c2 | c3 | c4 | c5 | c6 | c7 | c8
  | c9 (n : Nat)
deriving BEq

def viaElim (x : Big) (h : x.ctorIdx = 1) (k : Nat) : Nat :=
  Big.c1.elim (motive := fun _ => Nat → Nat) x h (fun a b k => a + b * k) k
#erase viaElim to "viaElim.ast"

def bigEq (x y : Big) : Nat := if x == y then 1 else 0
#erase bigEq to "bigEq.ast"

def b2n (b : Bool) : Nat := if b then 1 else 0

def checks : List (Nat × Nat) :=
  [ (b2n (isRed .red), 1), (b2n (isRed .blue), 0),
    (pick .a, 1), (pick .b, 7), (pick .c, 3),
    (root (leftOr (.node (.node .leaf 5 .leaf) 6 .leaf)), 5), (root (leftOr (.node .leaf 6 .leaf)), 9),
    (root (leftOr .leaf), 9),
    (second [4, 8, 9], 8), (second [4], 0),
    (redCode 0, 10), (redCode 1, 3),
    (optVal .none, 0), (optVal (.some 2 (by decide)), 1),
    (applyTo .red 3, 4), (applyTo .green 3, 6),
    (predOr0 3, 2), (predOr0 0, 0), (isZero 0, 1), (isZero 2, 0),
    (negPart (-3), 3), (negPart 3, 0), (natPart 3, 3), (natPart (-3), 0),
    (viaElim (.c1 2 3) rfl 4, 14) ]

#guard checks.all fun (r, v) => r == v
#guard [bigEq (.c1 1 2) (.c1 1 2), bigEq (.c1 1 2) (.c1 2 1), bigEq .c3 .c3, bigEq .c3 .c4,
    bigEq (.c9 1) .c2] = [1, 0, 1, 0, 0]

def countEq : List (Nat × Nat) → Nat
  | [] => 0
  | (r, v) :: rest => b2n (Nat.beq r v) + countEq rest

def sumFst : List (Nat × Nat) → Nat
  | [] => 0
  | (r, _) :: rest => r + sumFst rest

def count : Nat := countEq checks
def sum : Nat := sumFst checks
#guard count = 25
#guard sum = 90

end Sparse

#erase Sparse.count config {nat := .peano, extern := .preferLogical} to "count.ast"
#erase Sparse.sum config {nat := .peano, extern := .preferLogical} to "sum.ast"
