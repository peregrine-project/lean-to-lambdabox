import LeanToLambdaBox

/-!
Corpus examples inside the verification scope (the checkpoint-1 examples): every constant in the
dependency closure of each erased term is a definition, theorem, axiom or opaque, and every
expression in the closure is built from sort/forallE/lam/app/letE/const/bvar only. Each program is
erased under `{nat := .peano}` to `<name>.peano.ast` and under the default configuration to
`<name>.default.ast`.

The READOUT section applies an in-scope program to `Nat`/`Nat.succ`/`Nat.zero` or
`Bool`/`true`/`false`, so that peregrine prints a first-order value; it is erased under
`{nat := .peano}` only. The readout wrapper itself is outside the scope (inductive type and
constructors, no recursor, no match, no literal); the in-scope program is the head of the
application.
-/

namespace Ex

universe u v w

/-! ## Church numerals -/

def CNat : Type 1 := ∀ α : Type, (α → α) → α → α

def zero : CNat := fun _ _ z => z
def succ (n : CNat) : CNat := fun α s z => s (n α s z)
def add (m n : CNat) : CNat := fun α s z => m α s (n α s z)
def mul (m n : CNat) : CNat := fun α s => m α (n α s)
/-- `pow m n = m ^ n`: iterate `m α` (at type `α → α`) `n` times. -/
def pow (m n : CNat) : CNat := fun α => n (α → α) (m α)
/-- Predecessor by iteration at type `(α → α) → α`. -/
def pred (n : CNat) : CNat :=
  fun α s z => n ((α → α) → α) (fun g h => h (g s)) (fun _ => z) (fun x => x)

def one : CNat := succ zero
def two : CNat := succ one
def three : CNat := add two one
def six : CNat := mul two three
def eight : CNat := pow two three
def nine : CNat := pow three two
def five : CNat := pred six

/-! ## Church booleans and if-then-else -/

def CBool : Type 1 := ∀ α : Type, α → α → α

def ctrue : CBool := fun _ t _ => t
def cfalse : CBool := fun _ _ f => f
def cnot (b : CBool) : CBool := fun α t f => b α f t
def cand (a b : CBool) : CBool := fun α t f => a α (b α t f) f
def isZero (n : CNat) : CBool := fun α t f => n α (fun _ => f) t
/-- if-then-else at any `α : Type`. -/
def cite (b : CBool) {α : Type} (t e : α) : α := b α t e
/-- if-then-else between Church numerals, pointwise (a `CNat` lives in `Type 1`). -/
def citeN (b : CBool) (t e : CNat) : CNat := fun α s z => cite b (t α s z) (e α s z)

def isZeroSix : CBool := isZero six
def isZeroZero : CBool := isZero zero
def notAnd : CBool := cnot (cand ctrue cfalse)
def pickN : CNat := citeN (isZero zero) three six

/-! ## Universe-polymorphic combinators, used at several universes -/

def pid {α : Sort u} (a : α) : α := a
def comp {α : Sort u} {β : Sort v} {γ : Sort w} (g : β → γ) (f : α → β) : α → γ := fun x => g (f x)
def pconst {α : Sort u} {β : Sort v} (a : α) (_ : β) : α := a
def pflip {α : Sort u} {β : Sort v} {γ : Sort w} (f : α → β → γ) (b : β) (a : α) : γ := f a b

/-- `pid` at `Sort 2` (on a `CNat`) and at `Sort 1` (on `α`). -/
def pidTwoLevels : CNat := fun α s z => pid (α := α) (pid six α s z)
/-- `comp` at `Sort 2` (on `CNat → CNat`) and at `Sort 1` inside. -/
def compEx : CNat := comp succ (comp succ succ) three
/-- `pflip` at `Sort 2` with a `CBool` argument. -/
def pflipEx : CNat := pflip (fun (_ : CBool) (n : CNat) => n) two ctrue

/-- A Church numeral type parametric in the sort: `CNatU.{0}` is a proposition (impredicative
encoding), `CNatU.{1}` is the predicative `CNat`. -/
def CNatU := ∀ α : Sort u, (α → α) → α → α
def twoU : CNatU.{u} := fun _ s z => s (s z)
def threeU : CNatU.{u} := fun _ s z => s (s (s z))
def mulU (m n : CNatU.{u}) : CNatU.{u} := fun α s => m α (n α s)
def sixU : CNatU.{u} := mulU twoU threeU
/-- The same definition at `u := 1`, as a `CNat`. -/
def sixU1 : CNat := sixU.{1}

/-! ## Type arguments, type formers, type aliases -/

def twiceAt (α : Type) (f : α → α) (x : α) : α := f (f x)
/-- A type argument in argument position: erased to □. -/
def fourAt : CNat := fun α s z => twiceAt α s (twiceAt α s z)
/-- A type-former argument `F`. -/
def twiceF (F : Type → Type) (g : ∀ β, F β → F β) (β : Type) (x : F β) : F β := g β (g β x)
/-- `twiceF` at `F := fun γ => γ → γ`: the result type `F α` is a β-redex. -/
def fourF : CNat := fun α s z => twiceF (fun γ => γ → γ) (fun _ f x => f (f x)) α s z

/-- A type alias, used in the types of other definitions. -/
def Endo (α : Type) : Type := α → α
def twiceE {α : Type} (f : Endo α) : Endo α := fun x => f (f x)
/-- An alias of `CNat` stated through `Endo`. -/
def CNatE : Type 1 := ∀ α : Type, Endo α → Endo α
def fourE : CNatE := fun _ f => twiceE (twiceE f)
def ofCNatE (n : CNatE) : CNat := n
def fourE' : CNat := ofCNatE fourE

/-- Aliases of sorts: erasability must see through them. -/
def MyType : Type 1 := Type
def MyProp : Type := Prop
def Pairish (α : Type) : MyType := α → α → α
def firstOf {α : Type} (p : Pairish α) (x y : α) : α := p x y
def pairEx : CNat := fun α s z => firstOf (α := α) (fun a _ => s a) z z

/-- A polymorphic (rank-2) argument. -/
def applyPoly (f : ∀ {α : Type}, α → α) : CNat := fun _ s z => f (s (f z))
def polyEx : CNat := applyPoly (fun x => x)
def polyExPid : CNat := applyPoly (fun x => pid x)

/-! ## Proofs: Prop axioms, theorems, proof arguments -/

axiom P : Prop
axiom hP : P
axiom Q : MyProp
axiom hQ : Q

theorem pp : ∀ p : Prop, p → p := fun _ h => h

/-- A proof argument `h : P`. -/
def guard (_ : P) (n : CNat) : CNat := n
/-- An argument of type `∀ p : Prop, p → p`. -/
def withPolyProof (_ : ∀ p : Prop, p → p) (n : CNat) : CNat := n
/-- A proof argument of a proposition given through a sort alias. -/
def guardQ (_ : Q) (n : CNat) : CNat := n
/-- A function taking a proof, used relevantly. -/
def underProof : P → CNat := fun _ => two
def mapProof (f : P → CNat) (h : P) : CNat := f h

/-- An axiom of Prop type as argument. -/
def axiomArg : CNat := guard hP six
/-- A theorem as argument (applied to a Prop and an axiom). -/
def theoremArg : CNat := guard (pp P hP) three
/-- A theorem as a higher-order proof argument. -/
def theoremFnArg : CNat := withPolyProof pp two
/-- A proof lambda as argument. -/
def lambdaProofArg : CNat := withPolyProof (fun _ h => h) two
def propAliasArg : CNat := guardQ hQ one
def underProofEx : CNat := mapProof underProof hP
/-- A proof built from a relevant computation is still a proof. -/
theorem proofWithComputation : P := (fun (_ : CNat) => hP) six
set_option linter.defProp false in
/-- The same proof as a `def` of Prop type. -/
def proofDef : P := (fun (_ : CNat) => hP) six
def proofWithComputationArg : CNat := guard proofWithComputation five
/-- `pconst` at `v := 0`: the second argument is a proof. -/
def pconstEx : CNat := pconst six hP
/-- `pid` at `u := 0`, on a proof, as an argument. -/
def pidProofArg : CNat := guard (pid hP) two

/-! ## let-bindings -/

/-- A let with a relevant value. -/
def letVal : CNat := let x := two; add x x
/-- A let binding a type, and a let whose type is that type. -/
def letType : CNat := let T : Type 1 := CNat; let y : T := three; y
/-- A let binding a proof. -/
def letProof : CNat := let h : P := hP; guard h six
/-- A let binding a function. -/
def letFun : CNat := let f : CNat → CNat := succ; f (f two)
/-- `have` (a non-dependent let). -/
def haveVal : CNat := have x := three; mul x x
/-- Lets under binders: a relevant value, a type variable, and a value typed by it. -/
def letInner : CNat := fun α s z => let s2 := fun y => s (s y); let β := α; let z' : β := z; s2 (s2 z')

/-! ## Eta, partial application, compiler attributes -/

def succE : CNat → CNat := succ
def add2 : CNat → CNat := add two
def seven : CNat := add2 five

opaque opaqueTwo : CNat := two
def opaqueEx : CNat := succ opaqueTwo

def twoImpl : CNat := three
/-- `@[implemented_by]`: the compiled Lean program would use `twoImpl`. -/
@[implemented_by twoImpl] def twoSpec : CNat := two
def implEx : CNat := succ twoSpec

@[inline] def inlTwo : CNat := two
@[macro_inline] def mfirst (a _b : CNat) : CNat := a
def attrEx : CNat := mfirst inlTwo three


/-! ## Proof arguments without axioms

Under a PCUIC-style weak call-by-value source semantics an axiom constant does not evaluate, so the
programs above that pass `hP`/`hQ` in an evaluated position do not evaluate at the source; these
twins use a defined proposition and λ-proofs or theorems instead. -/

def P' : Prop := ∀ p : Prop, p → p
theorem hP' : P' := fun _ h => h
def guard' (_ : P') (n : CNat) : CNat := n
/-- A λ-proof as argument. -/
def lamProofArg' : CNat := guard' (fun _ h => h) six
/-- A theorem constant as argument. -/
def thmProofArg' : CNat := guard' hP' six
/-- A let binding a λ-proof. -/
def letProof' : CNat := let h : P' := fun _ x => x; guard' h six
/-- A proof variable passed on. -/
def passProof' (h : P') : CNat := guard' h three
def passProofEx' : CNat := passProof' (fun _ x => x)
/-- A proof whose proposition is `CNatU.{0}` (the impredicative numeral type). -/
def mixU (_ : CNatU.{0}) (n : CNat) : CNat := n
def mixUEx : CNat := mixU twoU.{0} six

/-! ## Erasability hidden by transparency or by a let

`Erasure.isErasable` decides with `Meta.isProp`/`Meta.isTypeFormerType` at default transparency. -/

def IProp : Type := Prop
axiom R : IProp
axiom hR : R
def R2 : IProp := ∀ p : Prop, p → p
theorem hR2 : R2 := fun _ h => h
def guardR (_ : R) (n : CNat) : CNat := n
def guardR2 (_ : R2) (n : CNat) : CNat := n
attribute [irreducible] IProp
/-- A Prop axiom whose sort is hidden behind an `@[irreducible]` alias of `Prop`. Lean's own code
generator also keeps `hR` (without `noncomputable` it reports `Ex.hR not supported by code
generator`). -/
noncomputable def irrAxiomArg : CNat := guardR hR six
/-- A theorem whose proposition's sort is hidden behind the same alias (Lean's code generator:
`Ex.hR2 not supported by code generator`). -/
noncomputable def irrThmArg : CNat := guardR2 hR2 six
/-- A proof whose proposition's sort is a let-bound alias of `Prop`. -/
def letSortAlias : CNat := let S' : Type := Prop; let Q' : S' := P'; let h : Q' := hP'; guard' h six

/-! ## Relevant axioms (validated, but peregrine does not evaluate programs with axioms) -/

axiom A : Type
axiom S : A → A
axiom Z : A
noncomputable def sixOnAxioms : A := six A S Z

/-! ## Erasure under `{nat := .peano}` and the default configuration -/

end Ex

open Ex

#erase Ex.zero config {nat := .peano} to "zero.peano.ast"
#erase Ex.zero to "zero.default.ast"
#erase Ex.two config {nat := .peano} to "two.peano.ast"
#erase Ex.two to "two.default.ast"
#erase Ex.six config {nat := .peano} to "six.peano.ast"
#erase Ex.six to "six.default.ast"
#erase Ex.eight config {nat := .peano} to "eight.peano.ast"
#erase Ex.eight to "eight.default.ast"
#erase Ex.nine config {nat := .peano} to "nine.peano.ast"
#erase Ex.nine to "nine.default.ast"
#erase Ex.five config {nat := .peano} to "five.peano.ast"
#erase Ex.five to "five.default.ast"
#erase Ex.succ config {nat := .peano} to "succ.peano.ast"
#erase Ex.succ to "succ.default.ast"
#erase Ex.isZeroSix config {nat := .peano} to "isZeroSix.peano.ast"
#erase Ex.isZeroSix to "isZeroSix.default.ast"
#erase Ex.isZeroZero config {nat := .peano} to "isZeroZero.peano.ast"
#erase Ex.isZeroZero to "isZeroZero.default.ast"
#erase Ex.notAnd config {nat := .peano} to "notAnd.peano.ast"
#erase Ex.notAnd to "notAnd.default.ast"
#erase Ex.pickN config {nat := .peano} to "pickN.peano.ast"
#erase Ex.pickN to "pickN.default.ast"
#erase Ex.pidTwoLevels config {nat := .peano} to "pidTwoLevels.peano.ast"
#erase Ex.pidTwoLevels to "pidTwoLevels.default.ast"
#erase Ex.compEx config {nat := .peano} to "compEx.peano.ast"
#erase Ex.compEx to "compEx.default.ast"
#erase Ex.pflipEx config {nat := .peano} to "pflipEx.peano.ast"
#erase Ex.pflipEx to "pflipEx.default.ast"
#erase Ex.sixU1 config {nat := .peano} to "sixU1.peano.ast"
#erase Ex.sixU1 to "sixU1.default.ast"
#erase Ex.sixU.{1} config {nat := .peano} to "sixU_at1.peano.ast"
#erase Ex.sixU.{1} to "sixU_at1.default.ast"
#erase Ex.sixU.{0} config {nat := .peano} to "sixU_at0.peano.ast"
#erase Ex.sixU.{0} to "sixU_at0.default.ast"
#erase Ex.fourAt config {nat := .peano} to "fourAt.peano.ast"
#erase Ex.fourAt to "fourAt.default.ast"
#erase Ex.fourF config {nat := .peano} to "fourF.peano.ast"
#erase Ex.fourF to "fourF.default.ast"
#erase Ex.fourE' config {nat := .peano} to "fourE'.peano.ast"
#erase Ex.fourE' to "fourE'.default.ast"
#erase Ex.pairEx config {nat := .peano} to "pairEx.peano.ast"
#erase Ex.pairEx to "pairEx.default.ast"
#erase Ex.polyEx config {nat := .peano} to "polyEx.peano.ast"
#erase Ex.polyEx to "polyEx.default.ast"
#erase Ex.polyExPid config {nat := .peano} to "polyExPid.peano.ast"
#erase Ex.polyExPid to "polyExPid.default.ast"
#erase Ex.axiomArg config {nat := .peano} to "axiomArg.peano.ast"
#erase Ex.axiomArg to "axiomArg.default.ast"
#erase Ex.theoremArg config {nat := .peano} to "theoremArg.peano.ast"
#erase Ex.theoremArg to "theoremArg.default.ast"
#erase Ex.theoremFnArg config {nat := .peano} to "theoremFnArg.peano.ast"
#erase Ex.theoremFnArg to "theoremFnArg.default.ast"
#erase Ex.lambdaProofArg config {nat := .peano} to "lambdaProofArg.peano.ast"
#erase Ex.lambdaProofArg to "lambdaProofArg.default.ast"
#erase Ex.propAliasArg config {nat := .peano} to "propAliasArg.peano.ast"
#erase Ex.propAliasArg to "propAliasArg.default.ast"
#erase Ex.underProofEx config {nat := .peano} to "underProofEx.peano.ast"
#erase Ex.underProofEx to "underProofEx.default.ast"
#erase Ex.proofWithComputation config {nat := .peano} to "proofWithComputation.peano.ast"
#erase Ex.proofWithComputation to "proofWithComputation.default.ast"
#erase Ex.proofDef config {nat := .peano} to "proofDef.peano.ast"
#erase Ex.proofDef to "proofDef.default.ast"
#erase Ex.proofWithComputationArg config {nat := .peano} to "proofWithComputationArg.peano.ast"
#erase Ex.proofWithComputationArg to "proofWithComputationArg.default.ast"
#erase Ex.pconstEx config {nat := .peano} to "pconstEx.peano.ast"
#erase Ex.pconstEx to "pconstEx.default.ast"
#erase Ex.pidProofArg config {nat := .peano} to "pidProofArg.peano.ast"
#erase Ex.pidProofArg to "pidProofArg.default.ast"
#erase (Ex.pid Ex.hP) config {nat := .peano} to "pidOnProof.peano.ast"
#erase (Ex.pid Ex.hP) to "pidOnProof.default.ast"
#erase Ex.pp config {nat := .peano} to "pp.peano.ast"
#erase Ex.pp to "pp.default.ast"
#erase Ex.CNat config {nat := .peano} to "typeCNat.peano.ast"
#erase Ex.CNat to "typeCNat.default.ast"
#erase (Ex.pid Ex.CNat) config {nat := .peano} to "pidOfType.peano.ast"
#erase (Ex.pid Ex.CNat) to "pidOfType.default.ast"
#erase Ex.letVal config {nat := .peano} to "letVal.peano.ast"
#erase Ex.letVal to "letVal.default.ast"
#erase Ex.letType config {nat := .peano} to "letType.peano.ast"
#erase Ex.letType to "letType.default.ast"
#erase Ex.letProof config {nat := .peano} to "letProof.peano.ast"
#erase Ex.letProof to "letProof.default.ast"
#erase Ex.letFun config {nat := .peano} to "letFun.peano.ast"
#erase Ex.letFun to "letFun.default.ast"
#erase Ex.haveVal config {nat := .peano} to "haveVal.peano.ast"
#erase Ex.haveVal to "haveVal.default.ast"
#erase Ex.letInner config {nat := .peano} to "letInner.peano.ast"
#erase Ex.letInner to "letInner.default.ast"
#erase Ex.succE config {nat := .peano} to "succE.peano.ast"
#erase Ex.succE to "succE.default.ast"
#erase Ex.add2 config {nat := .peano} to "add2.peano.ast"
#erase Ex.add2 to "add2.default.ast"
#erase Ex.seven config {nat := .peano} to "seven.peano.ast"
#erase Ex.seven to "seven.default.ast"
#erase Ex.opaqueEx config {nat := .peano} to "opaqueEx.peano.ast"
#erase Ex.opaqueEx to "opaqueEx.default.ast"
#erase Ex.implEx config {nat := .peano} to "implEx.peano.ast"
#erase Ex.implEx to "implEx.default.ast"
#erase Ex.attrEx config {nat := .peano} to "attrEx.peano.ast"
#erase Ex.attrEx to "attrEx.default.ast"
#erase Ex.lamProofArg' config {nat := .peano} to "lamProofArg'.peano.ast"
#erase Ex.lamProofArg' to "lamProofArg'.default.ast"
#erase Ex.thmProofArg' config {nat := .peano} to "thmProofArg'.peano.ast"
#erase Ex.thmProofArg' to "thmProofArg'.default.ast"
#erase Ex.letProof' config {nat := .peano} to "letProof'.peano.ast"
#erase Ex.letProof' to "letProof'.default.ast"
#erase Ex.passProofEx' config {nat := .peano} to "passProofEx'.peano.ast"
#erase Ex.passProofEx' to "passProofEx'.default.ast"
#erase Ex.mixUEx config {nat := .peano} to "mixUEx.peano.ast"
#erase Ex.mixUEx to "mixUEx.default.ast"
#erase Ex.irrAxiomArg config {nat := .peano} to "irrAxiomArg.peano.ast"
#erase Ex.irrAxiomArg to "irrAxiomArg.default.ast"
#erase Ex.irrThmArg config {nat := .peano} to "irrThmArg.peano.ast"
#erase Ex.irrThmArg to "irrThmArg.default.ast"
#erase Ex.letSortAlias config {nat := .peano} to "letSortAlias.peano.ast"
#erase Ex.letSortAlias to "letSortAlias.default.ast"
#erase Ex.sixOnAxioms config {nat := .peano} to "sixOnAxioms.peano.ast"
#erase Ex.sixOnAxioms to "sixOnAxioms.default.ast"
-- A let directly in the erased term.
#erase (let x := Ex.two; Ex.mul x x) config {nat := .peano} to "topLet.peano.ast"
#erase (let x := Ex.two; Ex.mul x x) to "topLet.default.ast"
-- A lambda over a type directly in the erased term.
#erase (fun (α : Type) (s : α → α) (z : α) => Ex.six α s z) config {nat := .peano} to "topLam.peano.ast"
#erase (fun (α : Type) (s : α → α) (z : α) => Ex.six α s z) to "topLam.default.ast"

/-! ## READOUT (wrapper outside the scope): apply to `Nat`, `Nat.succ`, `Nat.zero` or `Bool`, `true`,
`false`; `{nat := .peano}` only -/

#erase (Ex.zero Nat Nat.succ Nat.zero) config {nat := .peano} to "R_zero.peano.ast"
#erase (Ex.two Nat Nat.succ Nat.zero) config {nat := .peano} to "R_two.peano.ast"
#erase (Ex.six Nat Nat.succ Nat.zero) config {nat := .peano} to "R_six.peano.ast"
#erase (Ex.eight Nat Nat.succ Nat.zero) config {nat := .peano} to "R_eight.peano.ast"
#erase (Ex.nine Nat Nat.succ Nat.zero) config {nat := .peano} to "R_nine.peano.ast"
#erase (Ex.five Nat Nat.succ Nat.zero) config {nat := .peano} to "R_five.peano.ast"
#erase (Ex.isZeroSix Bool true false) config {nat := .peano} to "R_isZeroSix.peano.ast"
#erase (Ex.isZeroZero Bool true false) config {nat := .peano} to "R_isZeroZero.peano.ast"
#erase (Ex.notAnd Bool true false) config {nat := .peano} to "R_notAnd.peano.ast"
#erase (Ex.pickN Nat Nat.succ Nat.zero) config {nat := .peano} to "R_pickN.peano.ast"
#erase (Ex.pidTwoLevels Nat Nat.succ Nat.zero) config {nat := .peano} to "R_pidTwoLevels.peano.ast"
#erase (Ex.compEx Nat Nat.succ Nat.zero) config {nat := .peano} to "R_compEx.peano.ast"
#erase (Ex.pflipEx Nat Nat.succ Nat.zero) config {nat := .peano} to "R_pflipEx.peano.ast"
#erase (Ex.sixU1 Nat Nat.succ Nat.zero) config {nat := .peano} to "R_sixU1.peano.ast"
#erase (Ex.fourAt Nat Nat.succ Nat.zero) config {nat := .peano} to "R_fourAt.peano.ast"
#erase (Ex.fourF Nat Nat.succ Nat.zero) config {nat := .peano} to "R_fourF.peano.ast"
#erase (Ex.fourE' Nat Nat.succ Nat.zero) config {nat := .peano} to "R_fourE'.peano.ast"
#erase (Ex.pairEx Nat Nat.succ Nat.zero) config {nat := .peano} to "R_pairEx.peano.ast"
#erase (Ex.polyEx Nat Nat.succ Nat.zero) config {nat := .peano} to "R_polyEx.peano.ast"
#erase (Ex.polyExPid Nat Nat.succ Nat.zero) config {nat := .peano} to "R_polyExPid.peano.ast"
#erase (Ex.axiomArg Nat Nat.succ Nat.zero) config {nat := .peano} to "R_axiomArg.peano.ast"
#erase (Ex.theoremArg Nat Nat.succ Nat.zero) config {nat := .peano} to "R_theoremArg.peano.ast"
#erase (Ex.theoremFnArg Nat Nat.succ Nat.zero) config {nat := .peano} to "R_theoremFnArg.peano.ast"
#erase (Ex.lambdaProofArg Nat Nat.succ Nat.zero) config {nat := .peano} to "R_lambdaProofArg.peano.ast"
#erase (Ex.propAliasArg Nat Nat.succ Nat.zero) config {nat := .peano} to "R_propAliasArg.peano.ast"
#erase (Ex.underProofEx Nat Nat.succ Nat.zero) config {nat := .peano} to "R_underProofEx.peano.ast"
#erase (Ex.proofWithComputationArg Nat Nat.succ Nat.zero) config {nat := .peano} to "R_proofWithComputationArg.peano.ast"
#erase (Ex.pconstEx Nat Nat.succ Nat.zero) config {nat := .peano} to "R_pconstEx.peano.ast"
#erase (Ex.pidProofArg Nat Nat.succ Nat.zero) config {nat := .peano} to "R_pidProofArg.peano.ast"
#erase (Ex.letVal Nat Nat.succ Nat.zero) config {nat := .peano} to "R_letVal.peano.ast"
#erase (Ex.letType Nat Nat.succ Nat.zero) config {nat := .peano} to "R_letType.peano.ast"
#erase (Ex.letProof Nat Nat.succ Nat.zero) config {nat := .peano} to "R_letProof.peano.ast"
#erase (Ex.letFun Nat Nat.succ Nat.zero) config {nat := .peano} to "R_letFun.peano.ast"
#erase (Ex.haveVal Nat Nat.succ Nat.zero) config {nat := .peano} to "R_haveVal.peano.ast"
#erase (Ex.letInner Nat Nat.succ Nat.zero) config {nat := .peano} to "R_letInner.peano.ast"
#erase (Ex.seven Nat Nat.succ Nat.zero) config {nat := .peano} to "R_seven.peano.ast"
#erase (Ex.opaqueEx Nat Nat.succ Nat.zero) config {nat := .peano} to "R_opaqueEx.peano.ast"
#erase (Ex.implEx Nat Nat.succ Nat.zero) config {nat := .peano} to "R_implEx.peano.ast"
#erase (Ex.attrEx Nat Nat.succ Nat.zero) config {nat := .peano} to "R_attrEx.peano.ast"
#erase (Ex.lamProofArg' Nat Nat.succ Nat.zero) config {nat := .peano} to "R_lamProofArg'.peano.ast"
#erase (Ex.thmProofArg' Nat Nat.succ Nat.zero) config {nat := .peano} to "R_thmProofArg'.peano.ast"
#erase (Ex.letProof' Nat Nat.succ Nat.zero) config {nat := .peano} to "R_letProof'.peano.ast"
#erase (Ex.passProofEx' Nat Nat.succ Nat.zero) config {nat := .peano} to "R_passProofEx'.peano.ast"
#erase (Ex.mixUEx Nat Nat.succ Nat.zero) config {nat := .peano} to "R_mixUEx.peano.ast"
#erase (Ex.irrAxiomArg Nat Nat.succ Nat.zero) config {nat := .peano} to "R_irrAxiomArg.peano.ast"
#erase (Ex.irrThmArg Nat Nat.succ Nat.zero) config {nat := .peano} to "R_irrThmArg.peano.ast"
#erase (Ex.letSortAlias Nat Nat.succ Nat.zero) config {nat := .peano} to "R_letSortAlias.peano.ast"
#erase ((let x := Ex.two; Ex.mul x x) Nat Nat.succ Nat.zero) config {nat := .peano} to "R_topLet.peano.ast"
