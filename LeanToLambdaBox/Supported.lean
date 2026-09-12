import LeanToLambdaBox.CasesNames
import LeanToLambdaBox.ErasureSpec
import LeanToLambdaBox.Witness.SourceTable

/-!
# `Supported` — the fragment the bridge covers, and its checker

`Supported env tbl e` is the fragment of `Lean.Expr` on which the erasure is claimed correct: a
shape condition on `e` (`SupportedTm`) together with the same condition on every definition body
δ-reachable from `e`. Each exclusion is a named rule or a named side condition, so the coverage
holes are readable off the predicate rather than buried in a hypothesis bundle — in particular
the sparse-`casesOn` shape, on which the shipping erasure panics and emits a wrong program that
still passes `peregrine validate`. Two indices, not one: the model states informativity and the
peano tower, and the reachability clause is about the `Erasure.prepare_erasure`d bodies, which a
`VEnv` does not carry.

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
  /-- A constant whose shipping implementation is not its logical body. `supportedB` reports
      no instance of it: the table carries no attribute column, and what excludes the shape is
      the configuration hypothesis `ConfigPinned` — `csimp = false`, `extern = .preferLogical`.
      The constructor names the hole the coverage table reports. -/
  | implementedBy (c : Name)
  /-- A metavariable. -/
  | mvar
  /-- An elimination of a non-informative inductive into data: the emitted `.case` is stuck at
      every flag point, because the erasure marks no inductive propositional. Keyed on the
      *shape*, not the name — `Acc.casesOn` compiles in Lean, so a name-keyed exclusion would
      not close the hole. -/
  | propElimIntoData (I : Name)
  /-- A constructor occurrence applied to fewer than `numParams + numFields` arguments: the
      erasure η-expands it and pushes the supplied prefix under the new binders, where weak
      evaluation never reaches it. -/
  | underAppliedCtor (c : Name)
  /-- An eliminator occurrence applied to fewer than `dp + 1 + nm` arguments — the arguments
      before the major premise, the major premise, and one minor per constructor. Same η path,
      same defect. -/
  | underAppliedElim (c : Name)
  /-- A recursor head. It is tabled body-less, it is neither a constructor nor a type former,
      and the ι rule is keyed on `casesOn` names, so a spine headed by one has no source
      evaluation at all and a program reaching it would be vacuously covered. -/
  | recursorHead (c : Name)
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

/-- Is `c` a sparse `casesOn` — `f._sparseCasesOn_i`, named after the enclosing function rather
than after an inductive type? -/
def isSparseCasesOn (c : Name) : Bool :=
  match lastComponent c with
  | some s => "_sparseCasesOn_".isPrefixOf s
  | none => false

/-- Is `c` a matcher — `f.match_i` or one of its splitter variants? -/
def isMatcherName (c : Name) : Bool :=
  match lastComponent c with
  | some s => "match_".isPrefixOf s || "splitter".isPrefixOf s
  | none => false

/-- Is `c` a recursor of a tabled inductive type? Such a constant is outside the fragment:
`Witness.reify%` tables it body-less, so δ cannot fire at it, no value arm classifies it, and
the ι rule reads `casesOn` names only. -/
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

/-- N19's constructor half at one occurrence: if `c` is a tabled constructor, the spine it
heads supplies at least its parameters and its fields. Vacuous at every other head. -/
def ctorSaturatedB (tbl : SourceTable) (c : Name) (args : List Expr) : Bool :=
  match ctorOf? tbl c with
  | some p => decide (p.2.numParams + p.2.numFields ≤ args.length)
  | none => true

/-! ## Informativity -/

/-- The result sort of a Π-telescope. -/
def resultSort : Expr → Option Level
  | .forallE _ _ b _ => resultSort b
  | .sort l => some l
  | _ => none

/-- Is the tabled inductive relevant — does its declared result sort never evaluate to
`Prop`? This is the twin of the relation's `InformativeInd`, so the fragment checker and
`Erases.proj` accept the same type formers. The stricter successor shape is `succSortB`. -/
def informativeB (I : ReifiedInduct) : Bool :=
  match resultSort I.type with
  | some l => l.isNeverZero
  | none => false

/-- Does the tabled inductive's declared type land in a syntactic `Sort (u+1)`? Strictly
stronger than `informativeB` — it rejects `Prod`, whose result sort is a `max` of two
successors — and read only by the first-order fragment, whose `FirstOrderDecl.informative`
clause is a declared scope restriction. -/
def succSortB (I : ReifiedInduct) : Bool :=
  match resultSort I.type with
  | some (.succ _) => true
  | _ => false

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
      else if !decide (I.numParams + 1 + I.numIndices + 1 + I.ctors.length ≤ args.length) then
        .error (.underAppliedElim c)
      else
        let discrPos := I.numParams + 1 + I.numIndices
        let minors := (args.drop (discrPos + 1)).take I.ctors.length
        if minors.length != I.ctors.length then .error (.etaContractedMinor c)
        else if (List.zip minors I.ctors).all
            (fun p => isLamTelescopeB p.2.numFields p.1) then .ok ()
        else .error (.etaContractedMinor c)
  else if !ctorSaturatedB tbl c args then .error (.underAppliedCtor c)
  else if isRecursorName tbl c then .error (.recursorHead c)
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
  | .proj S _ b, _ =>
    match tbl.ind? S with
    | none => .error (.unknownConst S)
    | some I => if informativeB I then supportedGo tbl b [] else .error (.propElimIntoData S)
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


/-! ## The safety column -/

/-- Every declaration the reified table pins is safe in `lenv` — none is `unsafe` or
`partial`. `Witness.SourceTableAdequate` pins level parameters, types, bodies and the
constructor split but not the safety flag, and every statement that puts a tabled name in the
model reads it through `ErasureSpec.decl_adequate`, which is stated at safe declarations only.
Class **D** for the reason the table's own adequacy is: no term denotes `lenv`. -/
structure TableSafe (lenv : Lean.Environment) (tbl : SourceTable) : Prop where
  /-- The constant column. -/
  decls : ∀ (n : Name) (ci : ConstantInfo), (tbl.decl? n).isSome → lenv.find? n = some ci →
    DefinitionSafety.safe ≤ ci.safety
  /-- The inductive column. -/
  inds : ∀ (n : Name) (ci : ConstantInfo), (tbl.ind? n).isSome → lenv.find? n = some ci →
    DefinitionSafety.safe ≤ ci.safety
  /-- The constructors of the inductive column. -/
  ctors : ∀ (n : Name) (I : ReifiedInduct) (c : ReifiedCtor) (ci : ConstantInfo),
    tbl.ind? n = some I → c ∈ I.ctors → lenv.find? c.name = some ci →
    DefinitionSafety.safe ≤ ci.safety

/-! ## The fragment -/

/-- **N19's constructor half**: a tabled constructor occurs applied to at least its
parameters and its fields. Vacuous at every other head. Under-application is excluded because
the erasure η-expands it and pushes the supplied prefix under the new binders, where weak
evaluation never reaches it, and the pass relation has no η arm. -/
def CtorSaturated (tbl : SourceTable) (c : Name) (args : List Expr) : Prop :=
  ∀ p : Name × ReifiedCtor, ctorOf? tbl c = some p →
    p.2.numParams + p.2.numFields ≤ args.length

/-- `ctorSaturatedB` decides `CtorSaturated`. -/
theorem ctorSaturatedB_iff {tbl : SourceTable} {c : Name} {args : List Expr} :
    ctorSaturatedB tbl c args = true ↔ CtorSaturated tbl c args := by
  simp only [ctorSaturatedB, CtorSaturated]
  cases h : ctorOf? tbl c with
  | none => simp
  | some p => simp

/-- The four exclusions every head carries, one per error the name classes report. -/
structure PlainHead (c : Name) : Prop where
  /-- Not a `Quot` primitive — `SupportError.quotPrim`. -/
  notQuotPrim : quotPrimNames.contains c = false
  /-- Not an `IO`-like, `String`-like or machine-integer primitive — `SupportError.ioLike`. -/
  notIoLike : isIoLike c = false
  /-- Not a sparse `casesOn` — `SupportError.sparseCasesOn`. -/
  notSparse : isSparseCasesOn c = false
  /-- Not a surviving matcher — `SupportError.sideConditionElim`. -/
  notSideCondition : isMatcherName c = false

/-- A head the table knows, in one of the three columns the fragment admits — the exclusion
`SupportError.unknownConst` reports. Each of the three also puts the name in the model. A
recursor is not among them: `SupportError.recursorHead` excludes it. -/
inductive KnownHead (env : VEnv) (tbl : SourceTable) : Name → Prop
  /-- A tabled inductive type. -/
  | indType {c : Name} {I : ReifiedInduct} (h : tbl.ind? c = some I) (hm : env.contains c) :
      KnownHead env tbl c
  /-- A constructor of a tabled inductive type. -/
  | ctor {c : Name} {p : Name × ReifiedCtor} (h : ctorOf? tbl c = some p) (hm : env.contains c) :
      KnownHead env tbl c
  /-- A tabled constant. -/
  | defn {c : Name} {d : ReifiedDecl} (h : tbl.decl? c = some d) (hm : env.contains c) :
      KnownHead env tbl c

/-- **The shape condition**, at a term and the application spine it is read under: `e` applied
to `args` is inside the fragment. The spine is an index because saturation and the minor
premises' telescopes are conditions on the head, which is where `Erasure.visitConstApp` decides
them; every argument carries the condition on its own.

There is no rule for `.lit (.strVal _)` (`SupportError.strLit`) and none for `.mvar`
(`SupportError.mvar`): those shapes are outside the fragment, which is what having no rule
says. -/
inductive SupportedTm (env : VEnv) (tbl : SourceTable) : Expr → List Expr → Prop
  /-- A de Bruijn variable. -/
  | bvar {i : Nat} {args : List Expr} : SupportedTm env tbl (.bvar i) args
  /-- A free variable. -/
  | fvar {x : FVarId} {args : List Expr} : SupportedTm env tbl (.fvar x) args
  /-- A sort: erased before it is visited. -/
  | sort {u : Level} {args : List Expr} : SupportedTm env tbl (.sort u) args
  /-- A `Π` type: erased before it is visited. -/
  | forallE {n : Name} {ty b : Expr} {bi : BinderInfo} {args : List Expr} :
      SupportedTm env tbl (.forallE n ty b bi) args
  /-- Metadata is transparent to the erasure. -/
  | mdata {d : MData} {b : Expr} {args : List Expr} (h : SupportedTm env tbl b args) :
      SupportedTm env tbl (.mdata d b) args
  /-- A λ: its binder type is erased, its body carries the condition at the empty spine. -/
  | lam {n : Name} {ty b : Expr} {bi : BinderInfo} {args : List Expr}
      (hb : SupportedTm env tbl b []) : SupportedTm env tbl (.lam n ty b bi) args
  /-- A `let`: value and body carry the condition. -/
  | letE {n : Name} {ty v b : Expr} {nd : Bool} {args : List Expr}
      (hv : SupportedTm env tbl v []) (hb : SupportedTm env tbl b []) :
      SupportedTm env tbl (.letE n ty v b nd) args
  /-- A projection. `hind` and `hinf` are **N18**'s projection half: the structure is tabled
      and informative, without which the emitted `.proj` is stuck on the target for the same
      reason the `casesApp` rule's `hinf` covers (`SupportError.propElimIntoData`). `hb` is the
      discriminant's own condition. -/
  | proj {S : Name} {i : Nat} {b : Expr} {args : List Expr} {I : ReifiedInduct}
      (hind : tbl.ind? S = some I) (hinf : InformativeInd env S)
      (hb : SupportedTm env tbl b []) :
      SupportedTm env tbl (.proj S i b) args
  /-- An application: the argument is a term of its own, and the head reads it in the spine. -/
  | app {f a : Expr} {args : List Expr} (ha : SupportedTm env tbl a [])
      (hf : SupportedTm env tbl f (a :: args)) : SupportedTm env tbl (.app f a) args
  /-- A `Nat` literal, whose peano tower both the model and the table can build — the
      exclusion `SupportError.machineNat` reports. `hidx` pins the two kernel constructor
      indices `Erasure.visitLiteral`'s peano arm rebuilds. -/
  | natLit {n : Nat} {args : List Expr} (hpeano : PeanoReady env)
      (hidx : peanoReadyB tbl = true) : SupportedTm env tbl (.lit (.natVal n)) args
  /-- A plain constant head. `hrec` is restriction **N21** — a recursor spine has no source
      evaluation at all (`SupportError.recursorHead`) — and `hsat` is **N19**'s constructor
      half (`SupportError.underAppliedCtor`). -/
  | const {c : Name} {us : List Level} {args : List Expr} (hplain : PlainHead c)
      (hcases : isCasesOnName c = false) (hrec : isRecursorName tbl c = false)
      (hsat : CtorSaturated tbl c args) (hknown : KnownHead env tbl c) :
      SupportedTm env tbl (.const c us) args
  /-- A `casesOn` head, applied. `hind` names the inductive type the erasure recovers from the
      head's name prefix; `hinf` is its informativity, without which the emitted `.case` is
      stuck on the target, since the erasure marks no inductive propositional
      (`SupportError.propElimIntoData`); `hlen` and `htel` are the minor premises, one per
      constructor and each a manifest λ-telescope of its constructor's field count, which is
      what keeps the erasure's intro branch from η-expanding
      (`SupportError.etaContractedMinor`); `harity` is **N19**'s eliminator half
      (`SupportError.underAppliedElim`), which `hlen` does not imply at a constructor-free
      inductive type. -/
  | casesApp {c : Name} {us : List Level} {args minors : List Expr} {I : ReifiedInduct}
      (hplain : PlainHead c) (hcases : isCasesOnName c = true)
      (hind : tbl.ind? c.getPrefix = some I) (hinf : InformativeInd env c.getPrefix)
      (harity : I.numParams + 1 + I.numIndices + 1 + I.ctors.length ≤ args.length)
      (hmin : minors = (args.drop (I.numParams + 1 + I.numIndices + 1)).take I.ctors.length)
      (hlen : minors.length = I.ctors.length)
      (htel : ∀ (j : Nat) (m : Expr) (cb : ReifiedCtor), minors[j]? = some m →
        I.ctors[j]? = some cb → IsLamTelescope cb.numFields m) :
      SupportedTm env tbl (.const c us) args

/-- `c` is δ-reachable from `e`: it is named by `e`, or by the tabled body of a name reachable
from `e`. The closure the checker walks. -/
inductive Reaches (tbl : SourceTable) (e : Expr) : Name → Prop
  /-- A constant `e` names. -/
  | root {c : Name} (h : c ∈ constNames e) : Reaches tbl e c
  /-- A constant named by the tabled body of a reachable name. -/
  | body {c d : Name} {b : Expr} (hc : Reaches tbl e c) (hb : tbl.body? c = some b)
      (hd : d ∈ constNames b) : Reaches tbl e d

/-- **The fragment.** `e` is inside it, and so is every definition body δ-reachable from it —
the second half is what `SupportError.outOfFuel` protects: a checker run that exhausts its fuel
certifies no body. -/
structure Supported (env : VEnv) (tbl : SourceTable) (e : Expr) : Prop where
  /-- The subject's own shape. -/
  term : SupportedTm env tbl e []
  /-- The shape of every reachable tabled body. -/
  bodies : ∀ (c : Name) (b : Expr), Reaches tbl e c → tbl.body? c = some b →
    SupportedTm env tbl b []

/-! ## The projection head, read back

**N18**'s projection half, in the form `Erases.proj`'s `hinf` consumes it.
-/

/-- The projection rule's three conjuncts, read off a verdict at a `.proj` node. -/
theorem SupportedTm.proj_inv {env : VEnv} {tbl : SourceTable} {S : Name} {i : Nat}
    {b : Expr} {args : List Expr} (h : SupportedTm env tbl (.proj S i b) args) :
    (∃ I, tbl.ind? S = some I) ∧ InformativeInd env S ∧ SupportedTm env tbl b [] := by
  cases h with | proj hind hinf hb => exact ⟨⟨_, hind⟩, hinf, hb⟩

/-- **The fact `Erases.proj` demands, read back off the fragment verdict.** -/
theorem Supported.projInto {env : VEnv} {tbl : SourceTable} {S : Name} {i : Nat} {e : Expr}
    (h : Supported env tbl (.proj S i e)) : InformativeInd env S :=
  h.term.proj_inv.2.1

/-- The tabled inductive the projection's head names. -/
theorem Supported.projInd {env : VEnv} {tbl : SourceTable} {S : Name} {i : Nat} {e : Expr}
    (h : Supported env tbl (.proj S i e)) : ∃ I, tbl.ind? S = some I :=
  h.term.proj_inv.1

/-! ## Soundness: the model-side conjuncts -/

section Soundness

variable {lenv : Lean.Environment} {env : VEnv} {Us : List Name}
  {gw : Void IO.RealWorld → NameGenerator} {tbl : SourceTable}

/-- A safe declaration of `lenv` is a constant of the model. -/
theorem ErasureSpec.contains_of_find (P : ErasureSpec lenv env Us gw) {n : Name}
    {ci : ConstantInfo} (h : lenv.find? n = some ci)
    (hs : DefinitionSafety.safe ≤ ci.safety) : env.contains n :=
  let ⟨vc, hvc, _⟩ := P.decl_adequate n ci h hs
  ⟨vc, hvc⟩

/-- The relevance of a `Π`-telescope's result sort survives translation: `VLevel.ofLevel` is a
homomorphism, and `Lean4Lean.ofLevel_isNeverZero` carries never-zero-ness across it. -/
theorem vResultSort_of_trExprS {Δ : VLCtx} {t : Expr} {vt : VExpr} {u : Level}
    (h : TrExprS env Us Δ t vt) (hr : resultSort t = some u) (hnz : u.isNeverZero = true) :
    ∃ l, vResultSort vt = some l ∧ l.IsNeverZero := by
  induction h with
  | sort hu =>
    simp only [resultSort, Option.some.injEq] at hr
    subst hr
    exact ⟨_, rfl, Lean4Lean.ofLevel_isNeverZero hu hnz⟩
  | forallE _ _ _ _ _ ih => exact ih (by simpa [resultSort] using hr)
  | bvar _ | fvar _ | const _ _ _ | app _ _ _ _ _ _ | lam _ _ _ _ _ | letE _ _ _ _ _ _ _
  | lit _ _ _ | mdata _ _ | proj _ _ _ => simp [resultSort] at hr

/-- A tabled inductive type the checker calls relevant is relevant in the model: the table
pins its declared type to `lenv`'s, `ErasureSpec.decl_adequate` translates that type, and
`vResultSort_of_trExprS` carries the never-zero result sort across. -/
theorem informativeInd_of_tabled (P : ErasureSpec lenv env Us gw)
    (ht : SourceTableAdequate lenv tbl) (hsafe : TableSafe lenv tbl) {J : Name}
    {I : ReifiedInduct} (hind : tbl.ind? J = some I) (hinf : informativeB I = true) :
    InformativeInd env J := by
  obtain ⟨iv, hfind, -, htype, -, -, -, -, -⟩ := ht.inds J I (mem_of_lookup hind)
  have hs := hsafe.inds J _ (by rw [hind]; rfl) hfind
  obtain ⟨vc, hvc, htr⟩ := P.decl_adequate J _ hfind hs
  refine ⟨vc, hvc, ?_⟩
  simp only [informativeB] at hinf
  split at hinf
  · rename_i u hu
    have hty : resultSort (ConstantInfo.inductInfo iv).type = some u := by
      show resultSort iv.type = some u
      rw [htype]; exact hu
    exact vResultSort_of_trExprS htr.2.2 hty hinf
  · exact Bool.noConfusion hinf

/-- The model can build a peano tower whenever the table can: `Nat` and its two constructors
are tabled, hence pinned in `lenv`, hence constants of the model. -/
theorem peanoReady_of_tabled (P : ErasureSpec lenv env Us gw)
    (ht : SourceTableAdequate lenv tbl) (hsafe : TableSafe lenv tbl)
    (h : peanoReadyB tbl = true) : PeanoReady env := by
  simp only [peanoReadyB] at h
  split at h
  · rename_i I hind
    obtain ⟨iv, hfind, -, -, -, -, -, -, hctors⟩ := ht.inds _ I (mem_of_lookup hind)
    simp only [Bool.and_eq_true, List.any_eq_true] at h
    obtain ⟨⟨cz, hczmem, hcz⟩, ⟨cs, hcsmem, hcs⟩⟩ := h
    simp only [beq_iff_eq] at hcz hcs
    refine ⟨P.contains_of_find hfind (hsafe.inds _ _ (by rw [hind]; rfl) hfind), ?_, ?_⟩
    · obtain ⟨cv, hcvf, -⟩ := hctors cz hczmem
      rw [hcz.1] at hcvf
      exact P.contains_of_find hcvf (hsafe.ctors _ I cz _ hind hczmem (hcz.1 ▸ hcvf))
    · obtain ⟨cv, hcvf, -⟩ := hctors cs hcsmem
      rw [hcs.1] at hcvf
      exact P.contains_of_find hcvf (hsafe.ctors _ I cs _ hind hcsmem (hcs.1 ▸ hcvf))
  · exact Bool.noConfusion h

end Soundness

/-! ## Soundness: the checker -/

section Checker

variable {lenv : Lean.Environment} {env : VEnv} {Us : List Name}
  {gw : Void IO.RealWorld → NameGenerator} {tbl : SourceTable}

/-- An `all` check over a zip, read at an index. -/
theorem zip_all_getElem? {α β : Type} {f : α × β → Bool} :
    ∀ {l₁ : List α} {l₂ : List β}, (l₁.zip l₂).all f = true →
      ∀ (i : Nat) (a : α) (b : β), l₁[i]? = some a → l₂[i]? = some b → f (a, b) = true
  | [], _, _, _, _, _, ha, _ => by simp at ha
  | _ :: _, [], _, _, _, _, _, hb => by simp at hb
  | x :: xs, y :: ys, h, 0, a, b, ha, hb => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at h
    simp only [List.getElem?_cons_zero, Option.some.injEq] at ha hb
    subst ha; subst hb; exact h.1
  | x :: xs, y :: ys, h, i + 1, a, b, ha, hb => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at h
    exact zip_all_getElem? h.2 i a b (by simpa using ha) (by simpa using hb)

/-- The tabled constructor `ctorOf?` finds is a constructor of a tabled inductive type. -/
theorem ctorOf?_spec {c : Name} {p : Name × ReifiedCtor} (h : ctorOf? tbl c = some p) :
    ∃ I, tbl.ind? c.getPrefix = some I ∧ p.2 ∈ I.ctors ∧ p.2.name = c := by
  simp only [ctorOf?] at h
  split at h
  · rename_i I hI
    cases hf : I.ctors.find? (·.name == c) with
    | none => rw [hf] at h; cases h
    | some cb =>
      rw [hf] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      exact ⟨I, hI, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf⟩
  · cases h

/-- A head the checker accepts is a head the fragment accepts. -/
theorem supportedHead_sound (P : ErasureSpec lenv env Us gw) (ht : SourceTableAdequate lenv tbl)
    (hsafe : TableSafe lenv tbl) {c : Name} {us : List Level} {args : List Expr}
    (h : supportedHead tbl c args = .ok ()) : SupportedTm env tbl (.const c us) args := by
  simp only [supportedHead] at h
  split at h
  · cases h
  rename_i hq
  split at h
  · cases h
  rename_i hio
  split at h
  · cases h
  rename_i hsp
  split at h
  · cases h
  rename_i hma
  have hplain : PlainHead c :=
    ⟨by simpa using hq, by simpa using hio, by simpa using hsp, by simpa using hma⟩
  split at h
  · rename_i hco
    split at h
    · cases h
    rename_i I hI
    split at h
    · cases h
    rename_i hinfB
    split at h
    · cases h
    rename_i harity
    split at h
    · cases h
    rename_i hlen
    split at h
    · rename_i hall
      refine .casesApp hplain hco hI
        (informativeInd_of_tabled P ht hsafe hI (by simpa using hinfB))
        (by simpa using harity) rfl (by simpa using hlen) ?_
      intro j m cb hm hcb
      exact (isLamTelescopeB_iff _ _).1 (zip_all_getElem? hall j m cb hm hcb)
    · cases h
  rename_i hco
  split at h
  · cases h
  rename_i hsat
  split at h
  · cases h
  rename_i hrecn
  refine .const hplain (by simpa using hco) (by simpa using hrecn)
    (ctorSaturatedB_iff.1 (by simpa using hsat)) ?_
  split at h
  · rename_i hsome
    obtain ⟨I, hI⟩ := Option.isSome_iff_exists.1 (by simpa using hsome)
    obtain ⟨iv, hfind, -, -, -, -, -, -, -⟩ := ht.inds c I (mem_of_lookup hI)
    exact .indType hI (P.contains_of_find hfind (hsafe.inds c _ (by rw [hI]; rfl) hfind))
  split at h
  · rename_i p hp
    obtain ⟨I, hI, hmem, hname⟩ := ctorOf?_spec hp
    obtain ⟨-, -, -, -, -, -, -, -, hctors⟩ := ht.inds _ I (mem_of_lookup hI)
    obtain ⟨cv, hcvf, -⟩ := hctors p.2 hmem
    rw [hname] at hcvf
    exact .ctor hp (P.contains_of_find hcvf (hsafe.ctors _ I p.2 _ hI hmem (hname ▸ hcvf)))
  split at h
  · rename_i hsome
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 (by simpa using hsome)
    obtain ⟨⟨ci, hfind, -, -⟩, -⟩ := ht.decls c d (mem_of_lookup hd)
    exact .defn hd (P.contains_of_find hfind (hsafe.decls c ci (by rw [hd]; rfl) hfind))
  · cases h

/-- A term the checker accepts, at the spine it accepts it under, is inside the fragment. -/
theorem supportedGo_sound (P : ErasureSpec lenv env Us gw) (ht : SourceTableAdequate lenv tbl)
    (hsafe : TableSafe lenv tbl) : ∀ (e : Expr) (args : List Expr),
    supportedGo tbl e args = .ok () → SupportedTm env tbl e args := by
  intro e
  induction e with
  | bvar i => intro _ _; exact .bvar
  | fvar x => intro _ _; exact .fvar
  | mvar m => intro _ h; simp only [supportedGo] at h; cases h
  | sort u => intro _ _; exact .sort
  | const c us =>
    intro args h
    exact supportedHead_sound P ht hsafe (by simpa only [supportedGo] using h)
  | app f a ihf iha =>
    intro args h
    simp only [supportedGo] at h
    cases ha : supportedGo tbl a [] with
    | error er => rw [ha] at h; cases h
    | ok u => rw [ha] at h; exact .app (iha [] ha) (ihf (a :: args) h)
  | lam n ty b bi ihty ihb =>
    intro args h; exact .lam (ihb [] (by simpa only [supportedGo] using h))
  | forallE n ty b bi ihty ihb => intro _ _; exact .forallE
  | letE n ty v b nd ihty ihv ihb =>
    intro args h
    simp only [supportedGo] at h
    cases hv : supportedGo tbl v [] with
    | error er => rw [hv] at h; cases h
    | ok u => rw [hv] at h; exact .letE (ihv [] hv) (ihb [] h)
  | lit l =>
    intro args h
    cases l with
    | natVal n =>
      simp only [supportedGo] at h
      split at h
      · exact .natLit (peanoReady_of_tabled P ht hsafe (by assumption)) (by assumption)
      · cases h
    | strVal s => simp only [supportedGo] at h; cases h
  | mdata d b ihb => intro args h; exact .mdata (ihb args (by simpa only [supportedGo] using h))
  | proj S i b ihb =>
    intro args h
    simp only [supportedGo] at h
    split at h
    · cases h
    rename_i I hI
    split at h
    · exact .proj hI (informativeInd_of_tabled P ht hsafe hI (by assumption)) (ihb [] h)
    · cases h

/-- The δ-closure grows with the fuel: the constants of `e` are in every unfolding. -/
theorem mem_reachNames {e : Expr} {c : Name} (h : c ∈ constNames e) :
    ∀ n, c ∈ reachNames tbl e n
  | 0 => h
  | n + 1 => by
    show c ∈ stepNames tbl (reachNames tbl e n)
    simp only [stepNames]
    exact List.mem_append_left _ (mem_reachNames h n)

/-- A saturated list holding `e`'s own constants holds everything δ-reachable from `e`. -/
theorem mem_of_reaches {e : Expr} {ns : List Name} {c : Name} (hsat : saturatedB tbl ns = true)
    (hroot : ∀ d ∈ constNames e, d ∈ ns) (h : Reaches tbl e c) : c ∈ ns := by
  induction h with
  | root hc => exact hroot _ hc
  | body _ hb hd ih =>
    have hall := List.all_eq_true.1 hsat _ ih
    simp only [hb] at hall
    exact List.mem_of_elem_eq_true (List.all_eq_true.1 hall _ hd)

/-- Every tabled body of a checked name passes the shape check. -/
theorem checkNames_sound : ∀ {ns : List Name}, checkNames tbl ns = .ok () →
    ∀ {c : Name}, c ∈ ns → ∀ {b : Expr}, tbl.body? c = some b →
      supportedTerm tbl b = .ok () := by
  intro ns
  induction ns with
  | nil => intro _ c hc; simp at hc
  | cons a rest ih =>
    intro h c hc b hb
    simp only [checkNames] at h
    have hrest : checkNames tbl rest = .ok () := by
      split at h
      · rename_i b' _
        cases hs : supportedTerm tbl b' with
        | error er => rw [hs] at h; cases h
        | ok u => rw [hs] at h; exact h
      · exact h
    rcases List.mem_cons.1 hc with rfl | hc'
    · simp only [hb] at h
      cases hs : supportedTerm tbl b with
      | error er => rw [hs] at h; cases h
      | ok u => cases u; rfl
    · exact ih hrest hc' hb

/-- **The checker is sound.** A `.ok ()` verdict on a table that is an adequate, safe copy of
`lenv`'s slice puts the subject and every δ-reachable tabled body inside the fragment. `hsafe`
is what carries the model-side conjuncts — informativity and the peano tower — across:
`SourceTableAdequate` pins every column of a declaration but its safety, and
`ErasureSpec.decl_adequate` reads safe declarations only. -/
theorem supportedB_sound (P : ErasureSpec lenv env Us gw) (ht : SourceTableAdequate lenv tbl)
    (hsafe : TableSafe lenv tbl) {fuel : Nat} {e : Expr}
    (h : supportedB tbl fuel e = .ok ()) : Supported env tbl e := by
  simp only [supportedB] at h
  cases hterm : supportedTerm tbl e with
  | error er => rw [hterm] at h; cases h
  | ok u =>
    rw [hterm] at h
    cases u
    replace h : (if saturatedB tbl (reachNames tbl e fuel) = true then
        checkNames tbl (reachNames tbl e fuel)
      else .error SupportError.outOfFuel) = .ok () := h
    split at h
    · rename_i hsat
      refine ⟨supportedGo_sound P ht hsafe e [] hterm, fun c b hreach hbody => ?_⟩
      exact supportedGo_sound P ht hsafe b []
        (checkNames_sound h (mem_of_reaches hsat (fun d hd => mem_reachNames hd fuel) hreach)
          hbody)
    · cases h

end Checker

/-! ## Opening a binder -/

/-- The fragment is closed under opening a binder with a free variable — the form the bridge's
binder cases recurse in (`lambdaMonocular` and `letMonocular` call the continuation on
`body.instantiate1 (.fvar x)`). The spine is instantiated with the term, because an
application's arguments are read in it. -/
theorem SupportedTm.instantiate1' {env : VEnv} {tbl : SourceTable} {e : Expr}
    {args : List Expr} (x : FVarId) (h : SupportedTm env tbl e args) :
    ∀ k, SupportedTm env tbl (e.instantiate1' (.fvar x) k)
      (args.map (·.instantiate1' (.fvar x) k)) := by
  induction h with
  | bvar =>
    intro k
    simp only [Expr.instantiate1']
    split
    · exact .bvar
    · split
      · exact .fvar
      · exact .bvar
  | fvar => intro _; exact .fvar
  | sort => intro _; exact .sort
  | forallE => intro _; exact .forallE
  | mdata _ ih => intro k; exact .mdata (ih k)
  | lam _ ihb => intro k; exact .lam (ihb (k + 1))
  | letE _ _ ihv ihb => intro k; exact .letE (ihv k) (ihb (k + 1))
  | proj hind hinf _ ihb => intro k; exact .proj hind hinf (ihb k)
  | app _ _ iha ihf => intro k; exact .app (iha k) (ihf k)
  | natLit hpeano hidx => intro _; exact .natLit hpeano hidx
  | @const c us args hplain hcases hrec hsat hknown =>
    intro _
    exact .const hplain hcases hrec (fun p hp => by simpa using hsat p hp) hknown
  | @casesApp c us args minors I hplain hcases hind hinf harity hmin hlen htel =>
    intro k
    refine .casesApp (minors := minors.map (·.instantiate1' (.fvar x) k)) hplain hcases hind
      hinf (by simpa using harity) ?_ (by simpa using hlen) ?_
    · rw [hmin, List.map_take, List.map_drop]
    · intro j m cb hm hcb
      rw [List.getElem?_map] at hm
      obtain ⟨m₀, hm₀, rfl⟩ := Option.map_eq_some_iff.1 hm
      exact (htel j m₀ cb hm₀ hcb).instantiate1' k

/-- `SupportedTm.instantiate1'` at the real `Lean.Expr.instantiate1`, transported along
lean4lean's modelling equation. -/
theorem SupportedTm.instantiate1 {env : VEnv} {tbl : SourceTable} {e : Expr}
    {args : List Expr} (x : FVarId) (h : SupportedTm env tbl e args) :
    SupportedTm env tbl (e.instantiate1 (.fvar x)) (args.map (·.instantiate1 (.fvar x))) := by
  simp only [Lean.Expr.instantiate1_eq]
  exact h.instantiate1' x 0

/-! ## Self-test -/

/-- The sparse-`casesOn` shape is reported by name, at every table: the checker keys it on the
head's last component, which for this shape names the enclosing function rather than an
inductive type. The verdict is computed by the kernel — `String.isPrefixOf`, which
`isSparseCasesOn` calls, does not reduce in the elaborator — and `Except` carries no
`DecidableEq`, so the computed part is the error it names. -/
example : supportedB ⟨[], []⟩ 64 (.const `f._sparseCasesOn_1 []) =
    .error (.sparseCasesOn `f._sparseCasesOn_1) := by
  have h : (match supportedB ⟨[], []⟩ 64 (.const `f._sparseCasesOn_1 []) with
      | .error e => e
      | .ok _ => .outOfFuel) = .sparseCasesOn `f._sparseCasesOn_1 := by decide +kernel
  cases hx : supportedB ⟨[], []⟩ 64 (.const `f._sparseCasesOn_1 []) with
  | ok u => simp only [hx] at h; exact absurd h (by simp)
  | error e => simp only [hx] at h; exact congrArg _ h

/-- The table of one `Prop`-valued nullary structure, for the projection self-test. -/
def propStructTable : SourceTable :=
  ⟨[], [(`P, ⟨[], .sort .zero, 0, 0, [`P], []⟩)]⟩

/-- **N18's projection half is live.** A projection out of a `Prop`-valued structure is
rejected on the shape. Hand-built, because no tracked program carries such a node
(`doc/coverage.md`). -/
example : supportedB propStructTable 64 (.proj `P 0 (.bvar 0))
    = .error (.propElimIntoData `P) := by
  have h : (match supportedB propStructTable 64 (.proj `P 0 (.bvar 0)) with
      | .error e => e
      | .ok _ => .outOfFuel) = .propElimIntoData `P := by decide +kernel
  cases hx : supportedB propStructTable 64 (.proj `P 0 (.bvar 0)) with
  | ok u => simp only [hx] at h; exact absurd h (by simp)
  | error e => simp only [hx] at h; exact congrArg _ h

end LeanToLambdaBox
