import LeanToLambdaBox

/-!
Corpus examples whose dependency closure contains no inductive type: only sorts, Π-types,
λ-abstractions, applications, `let`, definitions and axioms.

Covered: Church numerals and booleans with their operations, polymorphic identity and composition,
functions taking proof or type arguments, `let`-bindings of values, types and proofs,
universe-polymorphic definitions, and a Prop-typed axiom used as an argument.
-/

namespace Scope

universe u v w

/-- Church numerals over a carrier in `Type`. -/
def Church : Type 1 := (α : Type) → (α → α) → α → α

def czero : Church := fun _ _ x => x
def csucc (n : Church) : Church := fun α f x => f (n α f x)
def cadd (m n : Church) : Church := fun α f x => m α f (n α f x)
def cmul (m n : Church) : Church := fun α f => m α (n α f)
def cexp (m n : Church) : Church := fun α => n (α → α) (m α)

def cone : Church := csucc czero
def ctwo : Church := csucc cone
def cthree : Church := cadd cone ctwo
def csix : Church := cmul ctwo cthree
def ceight : Church := cexp ctwo cthree

/-- Church booleans. -/
def CBool : Type 1 := (α : Type) → α → α → α

def ctrue : CBool := fun _ t _ => t
def cfalse : CBool := fun _ _ f => f
def cand (a b : CBool) : CBool := fun α t f => a α (b α t f) f
def cisZero (n : Church) : CBool := fun α t f => n α (fun _ => f) t

/-- Universe-polymorphic combinators. -/
def pid {α : Sort u} (a : α) : α := a
def pcomp {α : Sort u} {β : Sort v} {γ : Sort w} (g : β → γ) (f : α → β) : α → γ :=
  fun x => g (f x)
def pconst {α : Sort u} {β : Sort v} (a : α) (_ : β) : α := a
def pflip {α : Sort u} {β : Sort v} {γ : Sort w} (f : α → β → γ) (b : β) (a : α) : γ := f a b

def twice {α : Sort u} (f : α → α) : α → α := pcomp f f
def cfour : Church := twice csucc ctwo

/-- Explicit type arguments and type-former arguments. -/
def applyAt (α : Sort u) (f : α → α) (x : α) : α := f x
def typeArg : Church := applyAt Church csucc cthree
def mapF (F : Type 1 → Type 1) (g : F Church → F Church) (x : F Church) : F Church := g x
def typeFormerArg : Church := mapF (fun T => T) csucc czero

/-- A Prop-typed axiom and proof arguments. -/
axiom P : Prop
axiom hP : P

def withProof (_h : P) {α : Sort u} (x : α) : α := x
def proofId (p : Prop) (h : p) : p := h
def useAxiom : Church := withProof hP ctwo
def useProofTerm : Church := withProof (proofId P hP) cthree
def implProof (h : P → P) : Church := withProof (h hP) cone
def useImpl : Church := implProof (fun h => h)

/-- `let`-bindings of a value, a type, a proof and a function. -/
def letVal : Church := let two := csucc cone; cadd two two
def letType : Church := let T := Church; let x : T := ctwo; x
def letProof : Church := let h : P := hP; withProof h ctwo
def letFun : Church := let sq := fun (n : Church) => cmul n n; sq cthree

/-- Universe-polymorphic definitions used at several universes, including `Prop`. -/
def upoly.{a} (α : Sort a) (x : α) : α := x
def upolyType : Church := upoly Church ctwo
def upolyProp : P := upoly P hP
def upolyUse : Church := withProof (upoly P hP) (pid (pconst cone hP))
def upolyFun : Church := pflip (fun (m n : Church) => cadd m n) cone ctwo

end Scope

#erase Scope.czero to "czero.ast"
#erase Scope.csucc to "csucc.ast"
#erase Scope.cadd to "cadd.ast"
#erase Scope.cmul to "cmul.ast"
#erase Scope.cexp to "cexp.ast"
#erase Scope.csix to "csix.ast"
#erase Scope.ceight to "ceight.ast"
#erase Scope.cisZero to "cisZero.ast"
#erase (Scope.cand Scope.ctrue (Scope.cisZero Scope.czero)) to "cand.ast"
#erase @Scope.pid to "pid.ast"
#erase @Scope.pcomp to "pcomp.ast"
-- With their universes given, `pid` and `pcomp` are in the fragment of the pure path (`@Scope.pid`
-- and `@Scope.pcomp` leave them as metavariables).
#erase @Scope.pid.{1} to "pidU1.ast"
#erase @Scope.pcomp.{1,1,1} to "pcompU111.ast"
#erase Scope.cfour to "cfour.ast"
#erase Scope.typeArg to "typeArg.ast"
#erase Scope.typeFormerArg to "typeFormerArg.ast"
#erase Scope.useAxiom to "useAxiom.ast"
#erase Scope.useProofTerm to "useProofTerm.ast"
#erase Scope.useImpl to "useImpl.ast"
#erase Scope.letVal to "letVal.ast"
#erase Scope.letType to "letType.ast"
#erase Scope.letProof to "letProof.ast"
#erase Scope.letFun to "letFun.ast"
#erase Scope.upolyType to "upolyType.ast"
#erase Scope.upolyProp to "upolyProp.ast"
#erase Scope.upolyUse to "upolyUse.ast"
#erase Scope.upolyFun to "upolyFun.ast"
#erase Scope.csix config {nat := .peano, extern := .preferLogical} to "csix.peano.ast"
#erase Scope.letProof config {nat := .peano, extern := .preferLogical} to "letProof.peano.ast"
