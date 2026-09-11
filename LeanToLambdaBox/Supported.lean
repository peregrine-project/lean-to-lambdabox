import LeanToLambdaBox.ErasureSpec
import LeanToLambdaBox.Witness.SourceTable

/-!
# `Supported` — the fragment the bridge covers, and its checker

`Supported env bo e` is the syntactic fragment of `Lean.Expr` on which the erasure is claimed
correct: a shape condition on `e` (`SupportedTm`) together with the same condition on every
definition body reachable from `e` through `bo`. Each exclusion is a named rule or a named side
condition, so the coverage holes are readable off the predicate rather than buried in a
hypothesis bundle — in particular the sparse-`casesOn` shape, on which the shipping erasure
panics and emits a wrong program that still passes `peregrine validate`.

`supportedB` is the decision procedure: total, fuel-indexed (the dependency closure is cyclic
through mutual blocks, so no structural recursion on `e` reaches it), and run on a reified
`Witness.SourceTable` rather than on the `Lean.Environment`, because no term denotes the
latter. It returns the *name* of the hole it found, which is what generates the coverage table.
`supportedB_sound` is the bridge: a `.ok ()` verdict on an adequate table establishes
`Supported`.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean Witness

/-! ## The holes -/

/-- Why a term is outside the fragment. One constructor per audited coverage hole. -/
inductive SupportError where
  /-- A sparse `casesOn` (`f._sparseCasesOn_i`): the erasure recovers the inductive from the
      head's name prefix, which for this shape is the enclosing function, and panics. -/
  | sparseCasesOn (c : Name)
  /-- A matcher application that survived `Erasure.prepare_erasure`'s matcher inlining: the
      alternatives may carry `Lean.CasesAltInfo.default` or a side condition, neither of which
      the branch rule models. -/
  | sideConditionElim (c : Name)
  /-- An elimination whose minor premise is not a manifest λ-telescope of its constructor's
      field count, under-application included: the erasure η-expands it, and the specification
      relation has no η rule. -/
  | etaContractedMinor (c : Name)
  /-- A string literal: `Erasure.visitLiteral` panics on one and returns `□`. -/
  | strLit
  /-- A `Nat` literal whose peano tower the table cannot build. -/
  | machineNat
  /-- A `Quot` primitive in a computationally relevant position. -/
  | quotPrim (c : Name)
  /-- An `IO`-like, `String`-like or machine-integer primitive. -/
  | ioLike (c : Name)
  /-- A constant whose shipping implementation is not its logical body. -/
  | implementedBy (c : Name)
  /-- A metavariable. -/
  | mvar
  /-- An elimination of a non-informative inductive into data: the emitted `.case` is stuck at
      every flag point, because the erasure marks no inductive propositional. Keyed on the
      *shape*, not the name — `Acc.casesOn` compiles in Lean, so a name-keyed exclusion would
      not close the hole. -/
  | propElimIntoData (I : Name)
  /-- A constant the table does not know. -/
  | unknownConst (c : Name)
  /-- The closure did not saturate within the fuel. Exhaustion never certifies an untraversed
      body. -/
  | outOfFuel
  deriving Repr, DecidableEq, Inhabited

/-! ## Manifest λ-telescopes -/

/-- `e` is a manifest λ-telescope of depth at least `n`.

The ι fragment needs it: `Erasure.lambdaOrIntroToArity`'s intro branch η-expands a non-`.lam`
minor premise, and the specification relation has no η rule, so only manifest lambdas keep the
erasure inside it. Lean's `match` compiler emits minors as explicit `fun a b => …`, so real
pattern-matching code is inside the fragment; hand-written η-contracted minors are not. -/
def IsLamTelescope : Nat → Expr → Prop
  | 0,   _            => True
  | n+1, .lam _ _ b _ => IsLamTelescope n b
  | _+1, _            => False

@[simp] theorem IsLamTelescope_zero (e : Expr) : IsLamTelescope 0 e := trivial

/-- The decision procedure for `IsLamTelescope`. -/
def isLamTelescopeB : Nat → Expr → Bool
  | 0,   _            => true
  | n+1, .lam _ _ b _ => isLamTelescopeB n b
  | _+1, _            => false

/-- `isLamTelescopeB` decides `IsLamTelescope`. -/
theorem isLamTelescopeB_iff : ∀ (n : Nat) (e : Expr),
    isLamTelescopeB n e = true ↔ IsLamTelescope n e
  | 0, _ => by simp [isLamTelescopeB]
  | _+1, .lam _ _ b _ => isLamTelescopeB_iff _ b
  | _+1, .bvar _ | _+1, .fvar _ | _+1, .mvar _ | _+1, .sort _ | _+1, .const _ _
  | _+1, .app _ _ | _+1, .letE _ _ _ _ _ | _+1, .lit _ | _+1, .mdata _ _
  | _+1, .proj _ _ _ | _+1, .forallE _ _ _ _ => by simp [isLamTelescopeB, IsLamTelescope]

/-- Manifest λ-telescopes survive opening a binder (both sides descend at the same de Bruijn
depth). -/
theorem IsLamTelescope.instantiate1' {n : Nat} {e v : Expr} :
    IsLamTelescope n e → ∀ k, IsLamTelescope n (e.instantiate1' v k) := by
  induction n generalizing e with
  | zero => intro _ _; trivial
  | succ n ih =>
    match e with
    | .lam nm ty b bi =>
      intro h k
      show IsLamTelescope (n + 1) (Expr.lam nm _ (b.instantiate1' v (k + 1)) bi)
      exact ih h (k + 1)
    | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .app _ _ | .letE _ _ _ _ _
    | .lit _ | .mdata _ _ | .proj _ _ _ | .forallE _ _ _ _ => intro h _; exact absurd h id

/-- `IsLamTelescope.instantiate1'` at the real `Lean.Expr.instantiate1`, transported along
lean4lean's modelling equation. -/
theorem IsLamTelescope.instantiate1 {n : Nat} {e : Expr} (x : FVarId)
    (h : IsLamTelescope n e) : IsLamTelescope n (e.instantiate1 (.fvar x)) := by
  rw [Lean.Expr.instantiate1_eq]
  exact h.instantiate1' 0

/-! ## Name classes -/

/-- The `Quot` primitives. `Quot.sound` is not among them: it is `Prop`-typed, hence erased. -/
def quotPrimNames : List Name := [``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind]

/-- Root names whose declarations the fragment excludes: the `IO`/`ST` monads, tasks, strings,
machine integers and floats. A constant under any of them is out. -/
def ioLikeRoots : List Name :=
  [``IO, ``EIO, ``BaseIO, ``ST, ``EStateM, ``Task, ``String, ``Float, ``Float32,
   ``UInt8, ``UInt16, ``UInt32, ``UInt64, ``USize, ``ByteArray, ``FloatArray, ``Thunk,
   ``System.FilePath]

/-- Is `c` the name, or a name under, one of `ioLikeRoots`? -/
def isIoLike (c : Name) : Bool := ioLikeRoots.any fun r => r == c || r.isPrefixOf c

/-- The last string component of `c`, if it has one. -/
def lastComponent (c : Name) : Option String :=
  match c with
  | .str _ s => some s
  | _ => none

/-- Is `c` a sparse `casesOn` — `f._sparseCasesOn_i`, named after the enclosing function rather
than after an inductive type? -/
def isSparseCasesOn (c : Name) : Bool :=
  match lastComponent c with
  | some s => "_sparseCasesOn_".isPrefixOf s
  | none => false

/-- Is `c` a `casesOn` eliminator name, `I.casesOn`? -/
def isCasesOnName (c : Name) : Bool :=
  match lastComponent c with
  | some s => s == "casesOn"
  | none => false

/-- Is `c` a matcher — `f.match_i` or one of its splitter variants? -/
def isMatcherName (c : Name) : Bool :=
  match lastComponent c with
  | some s => "match_".isPrefixOf s || "splitter".isPrefixOf s
  | none => false

/-- Is `c` a recursor of a tabled inductive type? Such a constant is body-less and reaches the
consumer through the axiom route, so the fragment lets it through. -/
def isRecursorName (tbl : SourceTable) (c : Name) : Bool :=
  match lastComponent c with
  | some s =>
    (s == "rec" || s == "recOn" || s == "brecOn" || s == "below" || s == "ndrec") &&
      (tbl.ind? c.getPrefix).isSome
  | none => false

/-- The tabled constructor of `c`, with its inductive type, if `c` is one. -/
def ctorOf? (tbl : SourceTable) (c : Name) : Option (Name × ReifiedCtor) :=
  match tbl.ind? c.getPrefix with
  | some I => (I.ctors.find? (·.name == c)).map fun cb => (c.getPrefix, cb)
  | none => none

/-! ## Informativity -/

/-- The result sort of a Π-telescope. -/
def resultSort : Expr → Option Level
  | .forallE _ _ b _ => resultSort b
  | .sort l => some l
  | _ => none

/-- The result sort of a `VExpr` Π-telescope. -/
def vResultSort : VExpr → Option VLevel
  | .forallE _ b => vResultSort b
  | .sort l => some l
  | _ => none

/-- Is the tabled inductive informative — does its declared type land in `Sort (u+1)` rather
than in `Prop`? The successor shape is what survives translation: `VLevel.ofLevel` maps a
`Level.succ` to a `VLevel.succ`, which is never `VLevel.zero`. -/
def informativeB (I : ReifiedInduct) : Bool :=
  match resultSort I.type with
  | some (.succ _) => true
  | _ => false

/-- The modelled inductive `I` is informative: `env` knows it, and its model type lands in a
successor sort. This is the fragment boundary N18 draws — an elimination of a non-informative
inductive into data is stuck on the target, because the erasure marks no inductive
propositional. -/
def InformativeInd (env : VEnv) (I : Name) : Prop :=
  ∃ ci, env.constants I = some ci ∧ ∃ l, vResultSort ci.type = some (.succ l)

/-- `env` can build a peano tower: `Nat` and both of its constructors are modelled. -/
def PeanoReady (env : VEnv) : Prop :=
  env.contains ``Nat ∧ env.contains ``Nat.zero ∧ env.contains ``Nat.succ

/-- The table can build a peano tower: `Nat` is tabled with its two constructors at the kernel
indices `Erasure.visitLiteral`'s peano arm rebuilds. -/
def peanoReadyB (tbl : SourceTable) : Bool :=
  match tbl.ind? ``Nat with
  | some I =>
    (I.ctors.any fun c => c.name == ``Nat.zero && c.cidx == 0) &&
      (I.ctors.any fun c => c.name == ``Nat.succ && c.cidx == 1)
  | none => false

/-! ## The checker -/

/-- Head check of an application spine: the head constant `c` applied to `args`. -/
def supportedHead (tbl : SourceTable) (c : Name) (args : List Expr) :
    Except SupportError Unit :=
  if quotPrimNames.contains c then .error (.quotPrim c)
  else if isIoLike c then .error (.ioLike c)
  else if isSparseCasesOn c then .error (.sparseCasesOn c)
  else if isMatcherName c then .error (.sideConditionElim c)
  else if isCasesOnName c then
    match tbl.ind? c.getPrefix with
    | none => .error (.sparseCasesOn c)
    | some I =>
      if !informativeB I then .error (.propElimIntoData c.getPrefix)
      else
        let discrPos := I.numParams + 1 + I.numIndices
        let minors := (args.drop (discrPos + 1)).take I.ctors.length
        if minors.length != I.ctors.length then .error (.etaContractedMinor c)
        else if (List.zip minors I.ctors).all
            (fun p => isLamTelescopeB p.2.numFields p.1) then .ok ()
        else .error (.etaContractedMinor c)
  else if isRecursorName tbl c then .ok ()
  else if (tbl.ind? c).isSome then .ok ()
  else match ctorOf? tbl c with
    | some _ => .ok ()
    | none => if (tbl.decl? c).isSome then .ok () else .error (.unknownConst c)

/-- Shape check of `e` applied to `args`, at the positions the erasure visits: binder types and
`Π` bodies are erased before they are reached, so they carry no obligation. The accumulator
carries the application spine down to its head, which is where saturation and the minor
premises' telescopes are decided; each argument is checked as a term on the way.

One function rather than a mutually recursive pair, so that the definition is structurally
recursive on `Expr` and a `by rfl` discharge reduces through it. -/
def supportedGo (tbl : SourceTable) : Expr → List Expr → Except SupportError Unit
  | .app f a, args => do supportedGo tbl a []; supportedGo tbl f (a :: args)
  | .const c _, args => supportedHead tbl c args
  | .mdata _ b, args => supportedGo tbl b args
  | .lam _ _ b _, _ => supportedGo tbl b []
  | .letE _ _ v b _, _ => do supportedGo tbl v []; supportedGo tbl b []
  | .proj _ _ b, _ => supportedGo tbl b []
  | .lit (.strVal _), _ => .error .strLit
  | .lit (.natVal _), _ => if peanoReadyB tbl then .ok () else .error .machineNat
  | .mvar _, _ => .error .mvar
  | .bvar _, _ => .ok ()
  | .fvar _, _ => .ok ()
  | .sort _, _ => .ok ()
  | .forallE _ _ _ _, _ => .ok ()

/-- Shape check of a term in non-application position. -/
def supportedTerm (tbl : SourceTable) (e : Expr) : Except SupportError Unit :=
  supportedGo tbl e []

/-! ## The dependency closure -/

/-- The constants `e` names, at the positions the erasure visits. -/
def constNames : Expr → List Name
  | .const c _ => [c]
  | .app f a => constNames f ++ constNames a
  | .lam _ _ b _ => constNames b
  | .letE _ _ v b _ => constNames v ++ constNames b
  | .mdata _ b => constNames b
  | .proj _ _ b => constNames b
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ | .forallE _ _ _ _ => []

/-- One δ-step: add the constants named by the tabled bodies of the names seen so far. -/
def stepNames (tbl : SourceTable) (s : List Name) : List Name :=
  s ++ s.flatMap fun c => match tbl.body? c with
    | some b => constNames b
    | none => []

/-- The dependency closure of `e`, unfolded `n` times. -/
def reachNames (tbl : SourceTable) (e : Expr) : Nat → List Name
  | 0 => constNames e
  | n + 1 => stepNames tbl (reachNames tbl e n)

/-- Has the closure saturated: does every tabled body of a listed name name only listed
names? -/
def saturatedB (tbl : SourceTable) (ns : List Name) : Bool :=
  ns.all fun c => match tbl.body? c with
    | some b => (constNames b).all (ns.contains ·)
    | none => true

/-- Shape-check the tabled body of every name in the list. -/
def checkNames (tbl : SourceTable) : List Name → Except SupportError Unit
  | [] => .ok ()
  | c :: rest =>
    match tbl.body? c with
    | some b => do supportedTerm tbl b; checkNames tbl rest
    | none => checkNames tbl rest

/-- **The fragment checker.** Total and fuel-indexed: the dependency closure is cyclic through
mutual blocks, so it is not structural on `e`, and a `partial def` would be kernel-opaque, which
is exactly what a `by rfl` discharge cannot afford. Exhaustion is an error
(`SupportError.outOfFuel`) — it never certifies an untraversed body. -/
def supportedB (tbl : SourceTable) (fuel : Nat) (e : Expr) : Except SupportError Unit := do
  supportedTerm tbl e
  let ns := reachNames tbl e fuel
  if saturatedB tbl ns then checkNames tbl ns else .error .outOfFuel

end LeanToLambdaBox
