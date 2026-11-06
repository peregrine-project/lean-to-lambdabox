import LeanToLambdaBox

/-!
`#erase_lcnf` on the programs of `cases.lean`, plus shapes that LCNF represents differently from kernel
terms: join points, local functions, mutual recursion, structure projections and type classes.
`peregrine eval` gives `t` for `check.ast` and `more.ast`, meaning that every function returns Lean's
value. The `Nat` and `Int` files check the machine paths with `validate`, as their operations are axioms.
-/

-- peregrine: validate check.ast
-- peregrine: eval check.ast
-- peregrine: validate more.ast
-- peregrine: eval more.ast
-- peregrine: validate natCase.ast
-- peregrine: validate intCase.ast
-- peregrine: validate more.mono.ast
-- peregrine: eval more.mono.ast
-- peregrine: validate isZero.mono.ast

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


namespace More

inductive LB | f | t
inductive LN | z | s (n : LN)

def add : LN → LN → LN
  | .z, m => m
  | .s n, m => .s (add n m)

def eq : LN → LN → LB
  | .z, .z => .t
  | .s a, .s b => eq a b
  | _, _ => .f

def both : LB → LB → LB
  | .t, b => b
  | .f, _ => .f

def n1 : LN := .s .z
def n2 : LN := .s n1
def n3 : LN := .s n2

mutual
  def even : LN → LB
    | .z => .t
    | .s n => odd n
  def odd : LN → LB
    | .z => .f
    | .s n => even n
end

/-- A match in non-tail position gives a join point. -/
def joinPoint (a b : LB) : LN :=
  let x := match a, b with
    | .t, .t => n2
    | .t, .f => n1
    | _, _ => .z
  add x x

def joinShared (a b : LB) (n : LN) : LN :=
  let k := add n n1
  match a with
  | .t => match b with
    | .t => add k k
    | .f => k
  | .f => k

structure Pt where
  x : LN
  y : LN

def Pt.swap (p : Pt) : Pt := { x := p.y, y := p.x }

class Sized (α : Type) where
  size : α → LN

instance : Sized LB where
  size | .t => n1 | .f => .z

instance : Sized LN where
  size n := add n n1

def total {α} [Sized α] : List α → LN
  | [] => .z
  | a :: l => add (Sized.size a) (total l)

def localFun (n : LN) : LN :=
  let f := fun m => add m n
  add (f n1) (f n2)

def partialApp (n : LN) : LN := (add n) n1

def allT : List LB → LB
  | [] => .t
  | b :: l => both b (allT l)

def more : LB :=
  allT [ eq (joinPoint .t .t) (add n2 n2),
    eq (joinPoint .t .f) n2,
    eq (joinPoint .f .t) .z,
    eq (joinShared .t .t n1) (add n2 n2),
    eq (joinShared .f .t n1) n2,
    even n2, odd n3,
    eq (Pt.swap { x := n1, y := n3 }).x n3,
    eq (total [LB.t, LB.f, LB.t]) n2,
    eq (total [n1, n2]) (add n2 n3),
    eq (localFun n1) (add n3 n2),
    eq (partialApp n2) n3 ]

end More

open Cases in
#erase_lcnf check to "check.ast"
#erase_lcnf More.more to "more.ast"
#erase_lcnf Cases.natCase to "natCase.ast"
#erase_lcnf Cases.intCase to "intCase.ast"
#erase_lcnf mono More.more to "more.mono.ast"
/- At the mono phase a definition without compiled code is an axiom: the kernel value of
`Nat.decEq` builds a `Decidable`, while mono code matches on the `Bool` that mono represents
`Decidable` by. -/
#erase_lcnf mono Cases.isZero config {nat := .peano, extern := .preferLogical} to "isZero.mono.ast"
