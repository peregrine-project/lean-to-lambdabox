/-
This will keep the argument `n` in the .cons constructors at runtime.
Switch to using `{ l: List α // l.length = n }`?
`n` could then probably be removed as an unused function argument by the compiler.
-/
inductive SizedList (α: Type): (length: Nat) -> Type where
  | nil: SizedList α 0
  | cons: forall n, α -> SizedList α n -> SizedList α (n+1)

namespace SizedList
def map (f: α -> β): SizedList α n -> SizedList β n 
| .nil => .nil
| .cons n a as => .cons n (f a) (map f as)

def rev (l: SizedList α n): SizedList α n := Nat.zero_add n ▸ revAcc .nil l
where
  revAcc {m n} (acc: SizedList α m): (l: SizedList α n) -> SizedList α (m+n)
  | .nil => acc
  | .cons n a as =>
    Nat.succ_add_eq_add_succ m n ▸ revAcc (.cons m a acc) as
end SizedList

inductive DependentList (α: Type) (f: α -> Type): (List α) -> Type where
  | unit: DependentList α f .nil
  | pair: forall (a: α) (as: List α), f a -> DependentList α f as -> DependentList α f (.cons a as)

namespace DependentList
def map {f g: α -> Type} (fn: forall a, f a -> g a) (l: DependentList α f as): DependentList α g as :=
  match l with
  | .unit => .unit
  | .pair a as x t => .pair a as (fn a x) (t.map fn)

def forget (l: DependentList α (fun _ => β) as): List β :=
  match l with
  | .unit => []
  | .pair _ _ x t => x :: forget t
end DependentList
