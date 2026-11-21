import LeanToLambdaBox

/-!
Corpus examples: small programs over `Nat`, Prop-carrying arguments, subtypes, structures with a
Prop field, wildcard matches and derived `BEq`/`DecidableEq`.

Each function is erased three times: with the default configuration (`<f>.default.ast`), with
constructor pruning (`<f>.prune.ast`), and applied to a literal under Peano naturals with logical
`@[extern]` definitions (`<f>.peano.ast`), which `peregrine eval` can run.
-/

namespace Tiny

def double (n : Nat) : Nat := n + n

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

def predOfPos (n : Nat) (_h : 0 < n) : Nat := n - 1

def usePred (n : Nat) : Nat := if h : 0 < n then predOfPos n h else 0

def halfEven (x : {n : Nat // n % 2 = 0}) : Nat := x.val / 2

def useHalf (n : Nat) : Nat := halfEven ⟨2 * n, by omega⟩

structure Interval where
  lo : Nat
  hi : Nat
  ok : lo ≤ hi

def Interval.width (i : Interval) : Nat := i.hi - i.lo

def width (n : Nat) : Nat := (Interval.mk n (n + 3) (by omega)).width

inductive Color | red | green | blue | black

def isRed : Color → Bool
  | .red => true
  | _ => false

def colorCode (n : Nat) : Nat :=
  let c := match n % 4 with | 0 => Color.red | 1 => .green | 2 => .blue | _ => .black
  if isRed c then 1 else 0

def second : List Nat → Nat
  | _ :: y :: _ => y
  | _ => 0

def secondN (n : Nat) : Nat := second (List.range n)

def predOr0 : Nat → Nat
  | n + 1 => n
  | _ => 0

structure Pt where
  x : Nat
  y : Nat
deriving BEq

def ptEq (n : Nat) : Bool := (Pt.mk n 1) == (Pt.mk 1 n)

def ptEqN (n : Nat) : Nat := if ptEq n then 1 else 0

inductive Shape
  | circle (r : Nat)
  | rect (w h : Nat)
  | dot
deriving BEq, DecidableEq

def shapeOf (n : Nat) : Shape :=
  match n % 3 with
  | 0 => .circle n
  | 1 => .rect n (n + 1)
  | _ => .dot

def shapeEq (n : Nat) : Nat :=
  (if shapeOf n == shapeOf (n + 3) then 1 else 0)
  + (if decide (shapeOf n = shapeOf (n + 3)) then 10 else 0)
  + (if shapeOf n == shapeOf n then 100 else 0)
  + (if decide (shapeOf n = shapeOf (n + 1)) then 1000 else 0)

inductive Big
  | c0 (n : Nat)
  | c1 (a b : Nat)
  | c2 | c3 | c4 | c5 | c6 | c7 | c8
  | c9 (n : Nat)
deriving BEq, DecidableEq

def bigOf (n : Nat) : Big :=
  match n % 10 with
  | 0 => .c0 n
  | 1 => .c1 n (n + 1)
  | 2 => .c2 | 3 => .c3 | 4 => .c4 | 5 => .c5 | 6 => .c6 | 7 => .c7 | 8 => .c8
  | _ => .c9 (n / 10)

def bigEq (n : Nat) : Nat :=
  (if bigOf n == bigOf (n + 10) then 1 else 0)
  + (if decide (bigOf n = bigOf (n + 20)) then 10 else 0)
  + (if bigOf n == bigOf n then 100 else 0)
  + (if decide (bigOf n = bigOf (n + 1)) then 1000 else 0)

end Tiny

#erase Tiny.double to "double.default.ast" mli "double.default.mli"
#erase Tiny.double config {remove_irrel_constr_args := true} to "double.prune.ast"
#erase (Tiny.double 3) config {nat := .peano, extern := .preferLogical} to "double.peano.ast"

#erase Tiny.fact to "fact.default.ast" mli "fact.default.mli"
#erase Tiny.fact config {remove_irrel_constr_args := true} to "fact.prune.ast"
#erase (Tiny.fact 4) config {nat := .peano, extern := .preferLogical} to "fact.peano.ast"

#erase Tiny.usePred to "usePred.default.ast" mli "usePred.default.mli"
#erase Tiny.usePred config {remove_irrel_constr_args := true} to "usePred.prune.ast"
#erase (Tiny.usePred 3) config {nat := .peano, extern := .preferLogical} to "usePred.peano.ast"

#erase Tiny.useHalf to "useHalf.default.ast" mli "useHalf.default.mli"
#erase Tiny.useHalf config {remove_irrel_constr_args := true} to "useHalf.prune.ast"
#erase (Tiny.useHalf 3) config {nat := .peano, extern := .preferLogical} to "useHalf.peano.ast"

#erase Tiny.width to "width.default.ast" mli "width.default.mli"
#erase Tiny.width config {remove_irrel_constr_args := true} to "width.prune.ast"
#erase (Tiny.width 2) config {nat := .peano, extern := .preferLogical} to "width.peano.ast"

#erase Tiny.colorCode to "colorCode.default.ast" mli "colorCode.default.mli"
#erase Tiny.colorCode config {remove_irrel_constr_args := true} to "colorCode.prune.ast"
#erase (Tiny.colorCode 4) config {nat := .peano, extern := .preferLogical} to "colorCode.peano.ast"

#erase Tiny.secondN to "secondN.default.ast" mli "secondN.default.mli"
#erase Tiny.secondN config {remove_irrel_constr_args := true} to "secondN.prune.ast"
#erase (Tiny.secondN 3) config {nat := .peano, extern := .preferLogical} to "secondN.peano.ast"

#erase Tiny.predOr0 to "predOr0.default.ast" mli "predOr0.default.mli"
#erase Tiny.predOr0 config {remove_irrel_constr_args := true} to "predOr0.prune.ast"
#erase (Tiny.predOr0 3) config {nat := .peano, extern := .preferLogical} to "predOr0.peano.ast"

#erase Tiny.ptEqN to "ptEqN.default.ast" mli "ptEqN.default.mli"
#erase Tiny.ptEqN config {remove_irrel_constr_args := true} to "ptEqN.prune.ast"
#erase (Tiny.ptEqN 1) config {nat := .peano, extern := .preferLogical} to "ptEqN.peano.ast"

#erase Tiny.shapeEq to "shapeEq.default.ast" mli "shapeEq.default.mli"
#erase Tiny.shapeEq config {remove_irrel_constr_args := true} to "shapeEq.prune.ast"
#erase (Tiny.shapeEq 2) config {nat := .peano, extern := .preferLogical} to "shapeEq.peano.ast"

#erase Tiny.bigEq to "bigEq.default.ast" mli "bigEq.default.mli"
#erase Tiny.bigEq config {remove_irrel_constr_args := true} to "bigEq.prune.ast"
#erase (Tiny.bigEq 2) config {nat := .peano, extern := .preferLogical} to "bigEq.peano.ast"
