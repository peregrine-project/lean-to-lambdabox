import EraseProof.Statements
import EraseProof.Test.Run

/-!
# The recursor clauses of `RulesCanonical` on a recursive family

`RulesCanonical` holds, in the kernel, of an environment with the recursor of a `Nat`-like family
(one inductive hypothesis, on the field of its constructor), and fails when the recursive call is at
other levels than the recursor's own, when the recursor's level parameters repeat, when the call has
the wrong number of arguments, or when it recurses on a field the minor premise does not name.
-/

namespace EraseProof.Test.RecIH

open ConLeche

def nm (s : String) : Name := .str .anonymous s
def nm2 (a b : String) : Name := .str (.str .anonymous a) b
def kN : Expr := .const (nm "N") []
def kZ : Expr := .const (nm2 "N" "z") []
def kS : Expr := .const (nm2 "N" "s") []
def kMot : Expr := .forallE kN (.sort (.param (nm "u")))

/-- `N.rec.{u} : (motive : N → Sort u) → motive z → ((n : N) → motive n → motive (s n)) → (t : N) →
motive t` -/
def recTy : Expr :=
  .forallE kMot (.forallE (.app (.bvar 0) kZ) (.forallE
    (.forallE kN (.forallE (.app (.bvar 2) (.bvar 0)) (.app (.bvar 3) (.app kS (.bvar 1)))))
    (.forallE kN (.app (.bvar 3) (.bvar 0)))))

def recCall (us : List Level) (args : List Nat) : Expr :=
  args.foldl (fun f i => .app f (.bvar i)) (.const (nm2 "N" "rec") us)

def ruleZ : RecRule :=
  { ctor := nm2 "N" "z", nfields := 0, fire := .plain, rhs := .lam kMot (.lam kN (.lam kN (.bvar 1))) }
def ruleS (us : List Level) (args : List Nat) : RecRule :=
  { ctor := nm2 "N" "s", nfields := 1, fire := .plain,
    rhs := .lam kMot (.lam kN (.lam kN (.lam kN
      (.app (.app (.bvar 1) (.bvar 0)) (recCall us args))))) }

def env (lps : List Name) (us : List Level) (args : List Nat) : Env :=
  ⟨[ .recInfo ⟨nm2 "N" "rec", lps, recTy⟩ 3 3 false [ruleZ, ruleS us args]
   , .ctorInfo ⟨nm2 "N" "s", [], .forallE kN kN⟩ 0 1 (nm "N")
   , .ctorInfo ⟨nm2 "N" "z", [], kN⟩ 0 0 (nm "N")
   , .indInfo ⟨nm "N", [], .sort (.succ .zero)⟩
       { eta := false, all := [nm "N"], nparams := 0, nIdx := 0,
         ctors := [nm2 "N" "z", nm2 "N" "s"], neverZero := true } ], []⟩

theorem canonical : RulesCanonical (env [nm "u"] [.param (nm "u")] [3, 2, 1, 0]) = true := by
  krfl

theorem wrong_levels : RulesCanonical (env [nm "u"] [] [3, 2, 1, 0]) = false := by
  krfl

theorem dup_levels : RulesCanonical (env [nm "u", nm "u"] [.param (nm "u"), .param (nm "u")]
    [3, 2, 1, 0]) = false := by
  krfl

theorem wrong_arity : RulesCanonical (env [nm "u"] [.param (nm "u")] [3, 2, 0]) = false := by
  krfl

theorem wrong_field : RulesCanonical (env [nm "u"] [.param (nm "u")] [3, 2, 1, 1]) = false := by
  krfl

end EraseProof.Test.RecIH
