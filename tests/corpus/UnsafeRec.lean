import LeanToLambdaBox

/-!
Corpus examples of unsafe recursion inside the verification scope: a recursive constant, a
two-member mutual block, and a recursive constant whose value is not a λ. Church numerals only; no
inductive type in any dependency closure. Each program is erased under `{nat := .peano}` to
`<name>.peano.ast` and under the default configuration to `<name>.default.ast`.
-/

namespace URec

universe u

def CN : Type (u+1) := (α : Type u) → (α → α) → α → α
def one : CN.{u} := fun _ s z => s z
def csucc (n : CN.{u}) : CN.{u} := fun α s z => s (n α s z)

/-- A recursive constant whose recursive call sits under a discarded λ: `uf n = n`. -/
unsafe def uf (n : CN.{0}) : CN.{0} := (fun _ => n) (fun (x : CN.{0}) => uf x)

/-- Church booleans over `Type 1`, so that they select between functions on `CN.{0}`. -/
def CB : Type 2 := (α : Type 1) → α → α → α
def btrue : CB := fun _ t _ => t
def bfalse : CB := fun _ _ f => f

mutual
/-- `ua b n` is `n` if `b`, else `ub btrue (csucc n)`. -/
unsafe def ua (b : CB) (n : CN.{0}) : CN.{0} :=
  b (CN.{0} → CN.{0}) (fun m => m) (fun m => ub btrue (csucc m)) n
/-- `ub b n` is `n` if `b`, else `ua btrue (csucc n)`. -/
unsafe def ub (b : CB) (n : CN.{0}) : CN.{0} :=
  b (CN.{0} → CN.{0}) (fun m => m) (fun m => ua btrue (csucc m)) n
end

/-- A recursive constant whose value is an application, not a λ: `ug n = n`. -/
unsafe def ug : CN.{0} → CN.{0} :=
  (fun (_ : CN.{0} → CN.{0}) (n : CN.{0}) => n) (fun (x : CN.{0}) => ug x)

end URec

#erase URec.uf URec.one.{0} config {nat := .peano} to "ufOne.peano.ast"
#erase URec.uf URec.one.{0} to "ufOne.default.ast"
#erase URec.ua URec.bfalse URec.one.{0} config {nat := .peano} to "uaFalseOne.peano.ast"
#erase URec.ua URec.bfalse URec.one.{0} to "uaFalseOne.default.ast"
#erase URec.ug URec.one.{0} config {nat := .peano} to "ugOne.peano.ast"
#erase URec.ug URec.one.{0} to "ugOne.default.ast"
