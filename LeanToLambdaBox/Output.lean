import LeanToLambdaBox.OutputShape
import LeanToLambdaBox.Closed
import LeanToLambdaBox.Semantics.Env

/-!
# The output boundary — what the emitted program satisfies

`LBWfPeregrine` is what peregrine's `untyped_transform_pipeline` needs from the emitted
program: the well-formedness `peregrine validate` checks, plus the constructor-saturation
invariant `remove_params_optimization` consumes and `validate` omits. Every clause is stated
over the environment **and** the term, mirroring MetaRocq's `expanded_eprogram_cstrs`.

Fixpoint η — MetaRocq's `EEtaExpandedFix.expanded` — is **not** part of it: the erasure emits
bare `tFix` constant bodies, so the clause is false on emitted output. It is stated separately
as `LBExpandedFix`, and `PeregrinePre` is the conjunction peregrine's first pass actually
requires. The gap is a shipping finding, not paperwork: `guarded_to_unguarded_fix` is the
identity on terms and discharges its whole evaluation-preservation obligation from that clause.

`ErasableAxioms` is the reachability form of `axiom_free`: a `Prop`-typed axiom is erasable,
hence boxed, hence unreachable, so the condition to state is that every *reachable* body-less
constant has a realizer on the consumer side. It is a hypothesis of the capstone, decidable on
the emitted program.
-/

namespace LeanToLambdaBox

open Lean (Name FVarId)

/-! ## Subterms -/

/-- `d` occurs in `t`: the reflexive-transitive subterm relation. Binder types do not exist in
λ□, so every constructor descends into every term component. -/
inductive SubTerm : LBTerm → LBTerm → Prop
  | refl {t} : SubTerm t t
  | lambda {d n b} : SubTerm d b → SubTerm d (.lambda n b)
  | letInVal {d n v b} : SubTerm d v → SubTerm d (.letIn n v b)
  | letInBody {d n v b} : SubTerm d b → SubTerm d (.letIn n v b)
  | appFn {d f a} : SubTerm d f → SubTerm d (.app f a)
  | appArg {d f a} : SubTerm d a → SubTerm d (.app f a)
  | constructArg {d iid k args x} : x ∈ args → SubTerm d x → SubTerm d (.construct iid k args)
  | caseDiscr {d info discr alts} : SubTerm d discr → SubTerm d (.case info discr alts)
  | caseAlt {d info discr alts ns b} : (ns, b) ∈ alts → SubTerm d b →
      SubTerm d (.case info discr alts)
  | proj {d p e} : SubTerm d e → SubTerm d (.proj p e)
  | fixBody {d defs i fd} : fd ∈ defs → SubTerm d fd.body → SubTerm d (.fix defs i)

/-! ## Constructor spines -/

/-- `t` *is* a constructor spine of `(iid, k)` with `n` arguments: `n` counts the arguments
stored in the `.construct` node and the arguments applied to it. The erasure emits applied
form, so `n` is the length of the `.app` chain. -/
inductive IsConstructSpine : LBTerm → InductiveId → Nat → Nat → Prop
  | construct {iid k args} : IsConstructSpine (.construct iid k args) iid k args.length
  | app {f a iid k n} : IsConstructSpine f iid k n → IsConstructSpine (.app f a) iid k (n + 1)

/-- `t` is a constructor-headed application. -/
def CtorHeaded (t : LBTerm) : Prop := ∃ iid k n, IsConstructSpine t iid k n

/-- A constructor spine *occurring* in `t`, counted at its maximal application depth — the
subject of the saturation invariant. The `appFn` clause is guarded by `¬ CtorHeaded f` so that
a spine is counted once, at its outermost application, and not again with fewer arguments. -/
inductive ConstructSpine : LBTerm → InductiveId → Nat → Nat → Prop
  | root {t iid k n} : IsConstructSpine t iid k n → ConstructSpine t iid k n
  | appFn {f a iid k n} : ¬ CtorHeaded f → ConstructSpine f iid k n →
      ConstructSpine (.app f a) iid k n
  | appArg {f a iid k n} : ConstructSpine a iid k n → ConstructSpine (.app f a) iid k n
  | constructArg {iid' k' args x iid k n} : x ∈ args → ConstructSpine x iid k n →
      ConstructSpine (.construct iid' k' args) iid k n
  | lambda {nm b iid k n} : ConstructSpine b iid k n → ConstructSpine (.lambda nm b) iid k n
  | letInVal {nm v b iid k n} : ConstructSpine v iid k n → ConstructSpine (.letIn nm v b) iid k n
  | letInBody {nm v b iid k n} : ConstructSpine b iid k n → ConstructSpine (.letIn nm v b) iid k n
  | caseDiscr {info discr alts iid k n} : ConstructSpine discr iid k n →
      ConstructSpine (.case info discr alts) iid k n
  | caseAlt {info discr alts ns b iid k n} : (ns, b) ∈ alts → ConstructSpine b iid k n →
      ConstructSpine (.case info discr alts) iid k n
  | proj {p e iid k n} : ConstructSpine e iid k n → ConstructSpine (.proj p e) iid k n
  | fixBody {defs i fd iid k n} : fd ∈ defs → ConstructSpine fd.body iid k n →
      ConstructSpine (.fix defs i) iid k n

/-! ## Fixpoint spines -/

/-- `t` *is* a `.fix` spine: the block `defs` at index `i`, applied to `n` arguments. -/
inductive IsFixSpine : LBTerm → List (@FixDef LBTerm) → Nat → Nat → Prop
  | fix {defs i} : IsFixSpine (.fix defs i) defs i 0
  | app {f a defs i n} : IsFixSpine f defs i n → IsFixSpine (.app f a) defs i (n + 1)

/-- `t` is a `.fix`-headed application. -/
def FixHeaded (t : LBTerm) : Prop := ∃ defs i n, IsFixSpine t defs i n

/-- A `.fix` spine occurring in `t`, counted at its maximal application depth. -/
inductive FixSpine : LBTerm → List (@FixDef LBTerm) → Nat → Nat → Prop
  | root {t defs i n} : IsFixSpine t defs i n → FixSpine t defs i n
  | appFn {f a defs i n} : ¬ FixHeaded f → FixSpine f defs i n → FixSpine (.app f a) defs i n
  | appArg {f a defs i n} : FixSpine a defs i n → FixSpine (.app f a) defs i n
  | constructArg {iid k args x defs i n} : x ∈ args → FixSpine x defs i n →
      FixSpine (.construct iid k args) defs i n
  | lambda {nm b defs i n} : FixSpine b defs i n → FixSpine (.lambda nm b) defs i n
  | letInVal {nm v b defs i n} : FixSpine v defs i n → FixSpine (.letIn nm v b) defs i n
  | letInBody {nm v b defs i n} : FixSpine b defs i n → FixSpine (.letIn nm v b) defs i n
  | caseDiscr {info discr alts defs i n} : FixSpine discr defs i n →
      FixSpine (.case info discr alts) defs i n
  | caseAlt {info discr alts ns b defs i n} : (ns, b) ∈ alts → FixSpine b defs i n →
      FixSpine (.case info discr alts) defs i n
  | proj {p e defs i n} : FixSpine e defs i n → FixSpine (.proj p e) defs i n
  | fixBody {defs' j fd defs i n} : fd ∈ defs' → FixSpine fd.body defs i n →
      FixSpine (.fix defs' j) defs i n

/-! ## Per-node clauses -/

/-- Every constant `t` names is declared in `Γ`. -/
def NoDangling (Γ : GlobalDeclarations) (t : LBTerm) : Prop :=
  ∀ kn, SubTerm (.const kn) t → LBTerm.envLookup Γ kn ≠ none

/-- Every constructor `t` names is declared in `Γ`. -/
def CtorsDeclared (Γ : GlobalDeclarations) (t : LBTerm) : Prop :=
  ∀ iid k args, SubTerm (.construct iid k args) t → constructorArity Γ iid k ≠ none

/-- The inductive body an `InductiveId` selects. -/
def inductiveBody (Γ : GlobalDeclarations) (iid : InductiveId) : Option OneInductiveBody :=
  match LBTerm.envLookup Γ iid.mutualBlockName with
  | some (.inductiveDecl body) => body.bodies[iid.idx]?
  | _ => none

/-- Every `.case` node in `t` has one alternative per declared constructor, each binding that
constructor's fields. -/
def CasesExhaustive (Γ : GlobalDeclarations) (t : LBTerm) : Prop :=
  ∀ iid np discr alts, SubTerm (.case (iid, np) discr alts) t →
    ∃ oib, inductiveBody Γ iid = some oib ∧ alts.length = oib.ctors.length ∧
      ∀ i (h : i < alts.length) (h' : i < oib.ctors.length),
        (alts[i]).1.length = (oib.ctors[i]).nargs

/-- Every `.proj` node in `t` selects a field of a single-constructor inductive that is in
range. -/
def ProjsDeclared (Γ : GlobalDeclarations) (t : LBTerm) : Prop :=
  ∀ p e, SubTerm (.proj p e) t →
    ∃ oib cb, inductiveBody Γ p.indType = some oib ∧ oib.ctors = [cb] ∧ p.fieldIdx < cb.nargs

/-- Every `.fix` definition in `t` has a λ-headed body. -/
def FixLambda (t : LBTerm) : Prop :=
  ∀ defs i, SubTerm (.fix defs i) t → ∀ fd ∈ defs, ∃ nm b, fd.body = .lambda nm b

/-- A binder name the λ□ printer can emit: `Basic.cleanIdent`'s character class. -/
def AsciiBinderName : BinderName → Prop
  | .named s => ∀ c ∈ s.toList, c.isAlphanum ∨ c = '_'
  | .anon => True

/-- Every binder name in `t` is printable. -/
def AsciiBinders (t : LBTerm) : Prop :=
  (∀ nm b, SubTerm (.lambda nm b) t → AsciiBinderName nm) ∧
  (∀ nm v b, SubTerm (.letIn nm v b) t → AsciiBinderName nm) ∧
  (∀ info discr alts ns b, SubTerm (.case info discr alts) t → (ns, b) ∈ alts →
    ∀ nm ∈ ns, AsciiBinderName nm) ∧
  (∀ defs i fd, SubTerm (.fix defs i) t → fd ∈ defs → AsciiBinderName fd.name)

/-- A clause holding of the emitted term and of every constant body of the emitted
environment — the env+term split `expanded_eprogram_cstrs` makes. -/
def OnProgram (Γ : GlobalDeclarations) (t : LBTerm) (P : LBTerm → Prop) : Prop :=
  P t ∧ ∀ kn b, LBTerm.envLookup Γ kn = some (.constantDecl ⟨some b⟩) → P b

/-! ## The output predicate -/

/-- What `untyped_transform_pipeline` needs from the emitted program `(Γ, t)`, on the emitted
program alone. Everything but `etaCtorsEnv`/`etaCtorsTm` is `peregrine validate`'s check; those
two are the constructor-saturation invariant `validate` omits and
`remove_params_optimization` consumes. Fixpoint η is **not** claimed — see `LBExpandedFix`. -/
structure LBWfPeregrine (Γ : GlobalDeclarations) (t : LBTerm) : Prop where
  /-- No kername is declared twice. -/
  keys : (Γ.map Prod.fst).Pairwise (fun a b => Kername.beq a b = false)
  /-- Every inductive declaration has at least one body, and every body at least one
      constructor. -/
  declsWf : ∀ kn body, LBTerm.envLookup Γ kn = some (.inductiveDecl body) →
    body.bodies ≠ [] ∧ ∀ oib ∈ body.bodies, oib.ctors ≠ []
  /-- Every term of the program is closed. -/
  closed : OnProgram Γ t (LBClosed · 0)
  /-- Every constant reference resolves. -/
  constsOk : OnProgram Γ t (NoDangling Γ)
  /-- Constructors are in applied form: no `.construct` node carries arguments. -/
  ctorApplied : OnProgram Γ t NoBlock
  /-- Every constructor used is declared. -/
  ctorDecl : OnProgram Γ t (CtorsDeclared Γ)
  /-- Every `.case` is exhaustive at its inductive. -/
  casesExh : OnProgram Γ t (CasesExhaustive Γ)
  /-- Every `.fix` definition has a λ-headed body. -/
  fixLambda : OnProgram Γ t FixLambda
  /-- Every projection is a declared field of a single-constructor inductive. -/
  projDecl : OnProgram Γ t (ProjsDeclared Γ)
  /-- Constructor saturation, environment half: every constructor spine in a constant body
      carries at least the constructor's declared arity. -/
  etaCtorsEnv : ∀ kn b iid k n, LBTerm.envLookup Γ kn = some (.constantDecl ⟨some b⟩) →
    ConstructSpine b iid k n → ∀ a, constructorArity Γ iid k = some a → a ≤ n
  /-- Constructor saturation, term half. Vacuous on an `#erase` of a constant, whose emitted
      term is a bare `.const`; the environment half carries the invariant. -/
  etaCtorsTm : ∀ iid k n, ConstructSpine t iid k n →
    ∀ a, constructorArity Γ iid k = some a → a ≤ n
  /-- Every binder name is printable. -/
  asciiNames : OnProgram Γ t AsciiBinders

/-- The fix-clause of MetaRocq's `EEtaExpandedFix.expanded`, over environment and term: every
`.fix` occurs applied, to a non-empty argument list longer than its principal argument index. -/
def LBExpandedFix (Γ : GlobalDeclarations) (t : LBTerm) : Prop :=
  OnProgram Γ t fun u => ∀ defs i n, FixSpine u defs i n →
    n ≠ 0 ∧ ∀ fd, defs[i]? = some fd → fd.principalArgIdx < n

/-- What peregrine's first pass actually requires of its input. `LBWfPeregrine` is strictly
weaker, and the difference is exactly `LBExpandedFix`, which is false on emitted output: the
erasure emits bare `tFix` constant bodies. This is **not** concluded by the capstone. -/
def PeregrinePre (Γ : GlobalDeclarations) (t : LBTerm) : Prop :=
  LBWfPeregrine Γ t ∧ LBExpandedFix Γ t

/-! ## Reachable axioms -/

/-- Is `kn` in `l`? -/
def kernameElem (kn : Kername) (l : List Kername) : Bool := l.any (Kername.beq kn)

/-- Add the names of `ks` not already in `acc`. -/
def addNames : List Kername → List Kername → List Kername
  | [], acc => acc
  | k :: ks, acc => addNames ks (if kernameElem k acc then acc else k :: acc)

/-! The constants a term names. Four mutually recursive functions rather than `List.map`:
the structural-recursion checker does not see through `map` for the nested `List` occurrences
of `LBTerm`, the same factoring `Semantics.shift` uses. -/
mutual
/-- Every constant `t` names. -/
def constRefs : LBTerm → List Kername
  | .const kn => [kn]
  | .lambda _ b => constRefs b
  | .letIn _ v b => constRefs v ++ constRefs b
  | .app f a => constRefs f ++ constRefs a
  | .construct _ _ args => constRefsArgs args
  | .case _ discr alts => constRefs discr ++ constRefsAlts alts
  | .proj _ e => constRefs e
  | .fix defs _ => constRefsDefs defs
  | .box | .bvar _ | .fvar _ | .prim _ => []

/-- `constRefs` over a constructor's arguments. -/
def constRefsArgs : List LBTerm → List Kername
  | [] => []
  | t :: rest => constRefs t ++ constRefsArgs rest

/-- `constRefs` over case alternatives. -/
def constRefsAlts : List (List BinderName × LBTerm) → List Kername
  | [] => []
  | (_, b) :: rest => constRefs b ++ constRefsAlts rest

/-- `constRefs` over the definitions of a `.fix` block. -/
def constRefsDefs : List (@FixDef LBTerm) → List Kername
  | [] => []
  | fd :: rest => constRefs fd.body ++ constRefsDefs rest
end

/-- One δ-step of the reachability closure: add the constants named by the bodies of the
constants seen so far. -/
def expandRefs (Γ : GlobalDeclarations) (seen : List Kername) : List Kername :=
  seen.foldl (fun acc kn =>
    match LBTerm.envLookup Γ kn with
    | some (.constantDecl ⟨some b⟩) => addNames (constRefs b) acc
    | _ => acc) seen

/-- The reachability closure, unfolded `n` times from `t`'s own constants. -/
def reachRefs (Γ : GlobalDeclarations) (t : LBTerm) : Nat → List Kername
  | 0 => constRefs t
  | n + 1 => expandRefs Γ (reachRefs Γ t n)

/-- `kn` is reachable from `t` through the constant bodies of `Γ`. Computed by the
list-bounded closure — `Γ` declares finitely many constants, so `Γ.length` δ-steps saturate —
so the predicate is decidable by construction. It over-approximates nothing a shorter closure
would miss, and as a *hypothesis* of the capstone the over-approximating direction is the safe
one: more names must have realizers, not fewer. -/
def ReachableFrom (Γ : GlobalDeclarations) (t : LBTerm) (kn : Kername) : Prop :=
  kernameElem kn (reachRefs Γ t Γ.length) = true

instance (Γ : GlobalDeclarations) (t : LBTerm) (kn : Kername) :
    Decidable (ReachableFrom Γ t kn) := by
  unfold ReachableFrom; infer_instance

/-- Is this declaration a body-less constant — the shape the erasure emits for an axiom? -/
def isBodylessConst : Option GlobalDecl → Bool
  | some (.constantDecl ⟨none⟩) => true
  | _ => false

/-- The kernames for which the consumer is assumed to supply a realizer. One row per audited
name: `Eq.rec` and `False.rec` are the two the erasure emits as body-less axioms and the
backends realize by hand. -/
def axiomRealizerNames : List Kername := [toKername ``Eq.rec, toKername ``False.rec]

/-- Decision procedure for `AxiomRealizer`. -/
def axiomRealizerB (kn : Kername) : Bool := kernameElem kn axiomRealizerNames

/-- `kn` names a body-less constant the consumer realizes. Each constructor is one audited
row, and each is an assumption about the consumer, not a fact about the frontend. -/
inductive AxiomRealizer : Kername → Prop
  /-- Lean's `Eq.rec`, realized by a hand-written identity on the target side. -/
  | eqRec {kn} (h : Kername.beq kn (toKername ``Eq.rec) = true) : AxiomRealizer kn
  /-- Lean's `False.rec`, realized by an unreachable-abort on the target side. -/
  | falseRec {kn} (h : Kername.beq kn (toKername ``False.rec) = true) : AxiomRealizer kn

/-- `AxiomRealizer` is exactly its decision procedure. -/
theorem axiomRealizer_iff {kn : Kername} : AxiomRealizer kn ↔ axiomRealizerB kn = true := by
  constructor
  · rintro (h | h) <;> simp [axiomRealizerB, kernameElem, axiomRealizerNames, h]
  · intro h
    simp [axiomRealizerB, kernameElem, axiomRealizerNames] at h
    rcases h with h | h
    · exact .eqRec h
    · exact .falseRec h

instance (kn : Kername) : Decidable (AxiomRealizer kn) :=
  decidable_of_iff _ axiomRealizer_iff.symm

/-- The reachability form of `axiom_free`: every body-less constant of `Γ` that the emitted
program can reach has a realizer. A `Prop`-typed axiom is erasable, hence boxed, hence not
reachable, which is why the naive "no axioms" form is uninhabited on real output. This is a
hypothesis of the capstone, decidable on the emitted program. -/
def ErasableAxioms (Γ : GlobalDeclarations) (t : LBTerm) : Prop :=
  ∀ kn ∈ Γ.map Prod.fst, ReachableFrom Γ t kn →
    isBodylessConst (LBTerm.envLookup Γ kn) = true → AxiomRealizer kn

instance (Γ : GlobalDeclarations) (t : LBTerm) : Decidable (ErasableAxioms Γ t) := by
  unfold ErasableAxioms; infer_instance

end LeanToLambdaBox
