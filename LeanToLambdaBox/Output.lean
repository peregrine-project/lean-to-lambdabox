import LeanToLambdaBox.OutputShape
import LeanToLambdaBox.Closed
import LeanToLambdaBox.Semantics.Env

/-!
# The output boundary — what the emitted program satisfies

`LBWfPeregrine` is what peregrine's `untyped_transform_pipeline` needs from the emitted
program: the well-formedness `peregrine validate` checks, plus the constructor-saturation
invariant `remove_params_optimization` consumes and `validate` omits. Every clause is stated
over the environment **and** the term, mirroring MetaRocq's `expanded_eprogram_cstrs`.

Fixpoint η — MetaRocq's `expanded_tFix` — is the `expandedFix` clause: `LBExpandedFix` for the
spine, `FixLambda` for the member bodies and `LBFixSelfApplied` for the self-references, folded
as `LBExpandedTFix`. It matters because `guarded_to_unguarded_fix` is the identity on terms and
discharges its whole evaluation-preservation obligation from that clause. The remaining content
of `EEtaExpandedFix.expanded` — that a de Bruijn index resolves at all, and that a constructor
spine is saturated — is `closed` and `etaCtorsEnv`/`etaCtorsTm`, so `LBWfPeregrine` is the
precondition entire and no separate `PeregrinePre` is stated.

`NoBodylessRefs` is `axiom_free` at the emitted environment: no constant the program reaches
is declared without a body. It is decidable, and it is the capstone's premise — a run that
reaches a body-less constant is stuck at its `delta` step, so without the premise such a rung
would be vacuously green.

`ReachableFrom` is the reachability the two conditions read, computed by a fuel-bounded fold
over the constant bodies; its threading lemmas move a program's reachable set to a subterm, to
a δ-unfolded body and to a substitution instance.
-/

namespace LeanToLambdaBox

open Lean (Name FVarId)

/-! ## Kername equality

`Kername.beq` is the comparison `LBTerm.envLookup` and the reachability closure use; these
are its reflexivity and its adequacy, which a concrete environment's lookups are computed
with.
-/

theorem ModPath.eq_of_beq : ∀ {mp mp' : ModPath}, ModPath.beq mp mp' = true → mp = mp'
  | .MPfile _, .MPfile _, h => by simp [ModPath.beq] at h; simp [h]
  | .MPdot mp _, .MPdot mp' _, h => by
      simp [ModPath.beq] at h
      rw [ModPath.eq_of_beq h.1, h.2]
  | .MPfile _, .MPdot _ _, h | .MPdot _ _, .MPfile _, h => by simp [ModPath.beq] at h

theorem ModPath.beq_self : ∀ mp : ModPath, ModPath.beq mp mp = true
  | .MPfile _ => by simp [ModPath.beq]
  | .MPdot mp _ => by simp [ModPath.beq, ModPath.beq_self mp]

theorem Kername.eq_of_beq {k k' : Kername} (h : Kername.beq k k' = true) : k = k' := by
  simp only [Kername.beq, Bool.and_eq_true] at h
  obtain ⟨hmp, hid⟩ := h
  cases k; cases k'
  simp_all only [Kername.mk.injEq]
  exact ⟨ModPath.eq_of_beq hmp, by simpa using hid⟩

theorem Kername.beq_self (k : Kername) : Kername.beq k k = true := by
  simp [Kername.beq, ModPath.beq_self]

theorem Kername.beq_iff {k k' : Kername} : Kername.beq k k' = true ↔ k = k' :=
  ⟨Kername.eq_of_beq, fun h => h ▸ Kername.beq_self k⟩

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

/-- A binder name the λ□ printer can emit. `Printing.lean`'s `quote_atom` wraps the name in
`"…"` and escapes nothing, and peregrine's `Deserialize_ident` accepts any `Str` atom, so the
condition is that the name contains neither of the two characters that would close or escape
the atom. `Basic.cleanIdent`'s alphanumeric class is a condition on **kername identifiers**,
which `toKername` establishes by construction; on a binder name it is false — the eraser emits
`x._@.Init.Prelude.1822880135._hygCtx._hyg.3` at three rungs and thirty-two such names at two
more. -/
def PrintableBinderName : BinderName → Prop
  | .named s => ∀ c ∈ s.toList, c ≠ '"' ∧ c ≠ '\\'
  | .anon => True

/-- Every binder name in `t` is printable. -/
def PrintableBinders (t : LBTerm) : Prop :=
  (∀ nm b, SubTerm (.lambda nm b) t → PrintableBinderName nm) ∧
  (∀ nm v b, SubTerm (.letIn nm v b) t → PrintableBinderName nm) ∧
  (∀ info discr alts ns b, SubTerm (.case info discr alts) t → (ns, b) ∈ alts →
    ∀ nm ∈ ns, PrintableBinderName nm) ∧
  (∀ defs i fd, SubTerm (.fix defs i) t → fd ∈ defs → PrintableBinderName fd.name)

/-- The refutation the printability condition answers: the character class `Basic.cleanIdent`
establishes on a kername identifier is false at a binder name the eraser emits. -/
theorem hygienic_binder_not_alphanum :
    ¬ ∀ c ∈ "x._@.Init.Prelude.1822880135._hygCtx._hyg.3".toList, c.isAlphanum ∨ c = '_' := by
  decide

/-- A clause holding of the emitted term and of every constant body of the emitted
environment — the env+term split `expanded_eprogram_cstrs` makes. -/
def OnProgram (Γ : GlobalDeclarations) (t : LBTerm) (P : LBTerm → Prop) : Prop :=
  P t ∧ ∀ kn b, LBTerm.envLookup Γ kn = some (.constantDecl ⟨some b⟩) → P b

/-- Every `.fix` node in the subterm closure of an `OnProgram`-satisfying program is itself
λ-headed at every member: the projection that feeds one `LowerBlock.hfl` obligation at the
block a `visitMutual` run emits. A block stored in `Γ` rather than reached from the term is
read through the environment half first — `⟨h.2 kn b hb, h.2⟩ : OnProgram Γ b FixLambda`. -/
theorem FixLambda.of_onProgram {Γ : GlobalDeclarations} {prog sub : LBTerm}
    (h : OnProgram Γ prog FixLambda) (hsub : SubTerm sub prog)
    {defs : List (@FixDef LBTerm)} {j : Nat} (heq : sub = .fix defs j) :
    ∀ i, i < defs.length → isLambda (defs[i]!).body = true := by
  intro i hi
  obtain ⟨nm, b, hb⟩ :=
    h.1 defs j (heq ▸ hsub) defs[i]! (by rw [getElem!_pos defs i hi]; exact List.getElem_mem hi)
  rw [hb]; rfl

/-! ## Fixpoint η

`expanded_tFix` (`../metarocq/erasure/theories/EEtaExpandedFix.v:46-54`) is the one clause of
`EEtaExpandedFix.expanded` that constrains a `.fix` node. Read on λ□ it splits three ways:
the node occurs under a spine long enough (`LBExpandedFix`), every member body is λ-headed
(`FixLambda`), and every self-reference inside a member body is itself applied past its own
principal argument (`LBFixSelfApplied`). `LBExpandedTFix` is the three together.
-/

/-- The fix-clause of MetaRocq's `EEtaExpandedFix.expanded`, over environment and term: every
`.fix` occurs applied, to a non-empty argument list longer than its principal argument index.
`expanded_tFix`'s `args <> []`, `nth_error mfix idx = Some d` and `#|args| > d.(rarg)`
(`EEtaExpandedFix.v:51-53`). -/
def LBExpandedFix (Γ : GlobalDeclarations) (t : LBTerm) : Prop :=
  OnProgram Γ t fun u => ∀ defs i n, FixSpine u defs i n →
    n ≠ 0 ∧ ∀ fd, defs[i]? = some fd → fd.principalArgIdx < n

/-- The spine length each enclosing binder demands of a de Bruijn index resolving to it —
MetaRocq's `Γ : list nat` (`EEtaExpandedFix.v:33`) at a `.fix` block's own binders,
`rev_map (fun d => 1 + d.(rarg)) mfix` (`:48`). Index `0` is the block's last member. Every
other binder demands nothing and contributes `0`. -/
def fixDemands (defs : List (@FixDef LBTerm)) : List Nat :=
  (defs.map fun d => 1 + d.principalArgIdx).reverse

/-- A de Bruijn occurrence located. `BVarDemand ctx k t m k'` says: reading `t` under the
binder demands `ctx`, with `t` itself applied to `k` arguments, some maximal application spine
inside `t` is headed by an index that its own context resolves to the demand `m`, and that
spine carries `k'` arguments. These are the two premises of MetaRocq's `expanded_tRel_app`
(`EEtaExpandedFix.v:34`) — `nth_error Γ n = Some m` and `#|args|` — located at the occurrence
instead of read at the root, so that the demand is checked against the spine that actually
carries it. An index `ctx` does not resolve is no occurrence at all: that `expanded` admits no
such index is `LBWfPeregrine.closed`, not this. -/
inductive BVarDemand : List Nat → Nat → LBTerm → Nat → Nat → Prop
  | bvar {ctx k n m} : ctx[n]? = some m → BVarDemand ctx k (.bvar n) m k
  | appFn {ctx k f a m k'} : BVarDemand ctx (k + 1) f m k' → BVarDemand ctx k (.app f a) m k'
  | appArg {ctx k f a m k'} : BVarDemand ctx 0 a m k' → BVarDemand ctx k (.app f a) m k'
  | lambda {ctx k nm b m k'} : BVarDemand (0 :: ctx) 0 b m k' →
      BVarDemand ctx k (.lambda nm b) m k'
  | letInVal {ctx k nm v b m k'} : BVarDemand ctx 0 v m k' →
      BVarDemand ctx k (.letIn nm v b) m k'
  | letInBody {ctx k nm v b m k'} : BVarDemand (0 :: ctx) 0 b m k' →
      BVarDemand ctx k (.letIn nm v b) m k'
  | constructArg {ctx k iid c args x m k'} : x ∈ args → BVarDemand ctx 0 x m k' →
      BVarDemand ctx k (.construct iid c args) m k'
  | caseDiscr {ctx k info discr alts m k'} : BVarDemand ctx 0 discr m k' →
      BVarDemand ctx k (.case info discr alts) m k'
  | caseAlt {ctx k info discr alts ns b m k'} : (ns, b) ∈ alts →
      BVarDemand (List.replicate ns.length 0 ++ ctx) 0 b m k' →
      BVarDemand ctx k (.case info discr alts) m k'
  | proj {ctx k p e m k'} : BVarDemand ctx 0 e m k' → BVarDemand ctx k (.proj p e) m k'
  | fixBody {ctx k defs j fd m k'} : fd ∈ defs →
      BVarDemand (fixDemands defs ++ ctx) 0 fd.body m k' →
      BVarDemand ctx k (.fix defs j) m k'

/-- Every de Bruijn spine in `t` carries what its binder demands: in particular an index
resolving into an enclosing `.fix` block's own binder region heads a spine of at least
`1 + rarg` arguments. This is `expanded (ctx ++ Γ) d.(dbody)` inside `expanded_tFix`
(`EEtaExpandedFix.v:48-49`) read through `expanded_tRel_app`'s `m <= #|args|` (`:34`). -/
def FixSelfApplied (t : LBTerm) : Prop := ∀ m k, BVarDemand [] 0 t m k → m ≤ k

/-- `FixSelfApplied` over environment and term. -/
def LBFixSelfApplied (Γ : GlobalDeclarations) (t : LBTerm) : Prop :=
  OnProgram Γ t FixSelfApplied

/-- MetaRocq's `expanded_tFix` (`EEtaExpandedFix.v:46-54`) on the emitted program, all three
of its term-level conjuncts: the spine (`LBExpandedFix`), the λ-headed member bodies
(`FixLambda`, the clause's `isLambda d.(dbody)`, `:47`) and the applied self-references
(`LBFixSelfApplied`). The clause's remaining premise, `Forall (expanded Γ) args` (`:50`), is
the ambient recursion, carried here by every clause being read on the whole program; the
`nth_error Γ n = Some m` that `expanded_tRel_app` needs of an index is `closed`. -/
def LBExpandedTFix (Γ : GlobalDeclarations) (t : LBTerm) : Prop :=
  LBExpandedFix Γ t ∧ OnProgram Γ t FixLambda ∧ LBFixSelfApplied Γ t

/-! ## The output predicate -/

/-- What `untyped_transform_pipeline` needs from the emitted program `(Γ, t)`, on the emitted
program alone. Everything but `etaCtorsEnv`/`etaCtorsTm` and `printableNames` is `peregrine
validate`'s check; those two are the constructor-saturation invariant `validate` omits and
`remove_params_optimization` consumes, and `printableNames` is what the printer's quoted atoms
need of a binder name. `expandedFix` is the fixpoint-η precondition
`guarded_to_unguarded_fix` reads, which the emitted program satisfies since the registration
point η-expands (`Erasure.etaExpandFix`). -/
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
  /-- Fixpoint η: MetaRocq's `expanded_tFix`, all three of its term-level conjuncts. -/
  expandedFix : LBExpandedTFix Γ t
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
  printableNames : OnProgram Γ t PrintableBinders

/-- `expanded_tFix`'s λ-headedness conjunct, projected out of the folded clause: what
`FixLambda.of_onProgram` and `LowerBlock.hfl` read. -/
theorem LBWfPeregrine.fixLambda {Γ : GlobalDeclarations} {t : LBTerm}
    (h : LBWfPeregrine Γ t) : OnProgram Γ t FixLambda := h.expandedFix.2.1

/-! ## Reachability -/

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
/-- Every kername `t` names: the constants it references, and the **inductive block** every
`.construct`, `.case` and `.proj` node reads — `constructorArity` and
`isPropositionalInductive` answer from that declaration, so a program that reaches such a
node reaches its block. -/
def constRefs : LBTerm → List Kername
  | .const kn => [kn]
  | .lambda _ b => constRefs b
  | .letIn _ v b => constRefs v ++ constRefs b
  | .app f a => constRefs f ++ constRefs a
  | .construct iid _ args => iid.mutualBlockName :: constRefsArgs args
  | .case ip discr alts => ip.1.mutualBlockName :: (constRefs discr ++ constRefsAlts alts)
  | .proj p e => p.indType.mutualBlockName :: constRefs e
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

/-- The accumulator step of `expandRefs`: a seen constant contributes the kernames of its
body, if it has one. -/
def expandStep (Γ : GlobalDeclarations) (acc : List Kername) (kn : Kername) : List Kername :=
  match LBTerm.envLookup Γ kn with
  | some (.constantDecl ⟨some b⟩) => addNames (constRefs b) acc
  | _ => acc

/-- One δ-step of the reachability closure: add the constants named by the bodies of the
constants seen so far. -/
def expandRefs (Γ : GlobalDeclarations) (seen : List Kername) : List Kername :=
  seen.foldl (expandStep Γ) seen

/-- A seed closed under `n` δ-steps. -/
def reachFrom (Γ : GlobalDeclarations) (seen : List Kername) : Nat → List Kername
  | 0 => seen
  | n + 1 => expandRefs Γ (reachFrom Γ seen n)

/-- The reachability closure, unfolded `n` times from `t`'s own kernames. -/
def reachRefs (Γ : GlobalDeclarations) (t : LBTerm) (n : Nat) : List Kername :=
  reachFrom Γ (constRefs t) n

/-- `kn` is reachable from `t` through the constant bodies of `Γ`. Computed by the
list-bounded closure, so the predicate is decidable by construction; `Γ.length` δ-steps do
saturate it (`reachFrom_saturated`), which is what makes it compose. -/
def ReachableFrom (Γ : GlobalDeclarations) (t : LBTerm) (kn : Kername) : Prop :=
  kernameElem kn (reachRefs Γ t Γ.length) = true

instance (Γ : GlobalDeclarations) (t : LBTerm) (kn : Kername) :
    Decidable (ReachableFrom Γ t kn) := by
  unfold ReachableFrom; infer_instance

/-- Is this declaration a body-less constant — the shape the erasure emits for an axiom? -/
def isBodylessConst : Option GlobalDecl → Bool
  | some (.constantDecl ⟨none⟩) => true
  | _ => false

/-! ## The reachability closure, as a set of kernames

`kernameElem` is `Kername.beq` membership, which is membership; the closure's three
operations — one accumulation, one δ-step, the iteration — are characterised by it, and the
threading lemmas of the next section are read off those characterisations.
-/

/-- `Kername.beq` membership is membership. -/
theorem kernameElem_iff {kn : Kername} {l : List Kername} :
    kernameElem kn l = true ↔ kn ∈ l := by
  simp only [kernameElem, List.any_eq_true]
  exact ⟨fun ⟨x, hx, hb⟩ => Kername.eq_of_beq hb ▸ hx,
    fun h => ⟨kn, h, Kername.beq_self kn⟩⟩

/-- `addNames` is union. -/
theorem mem_addNames {kn : Kername} : ∀ {ks acc : List Kername},
    kn ∈ addNames ks acc ↔ kn ∈ ks ∨ kn ∈ acc
  | [], acc => by simp [addNames]
  | k :: ks, acc => by
      rw [addNames, mem_addNames (kn := kn) (ks := ks)]
      by_cases hk : kernameElem k acc = true
      · rw [if_pos hk]
        have : k ∈ acc := kernameElem_iff.1 hk
        constructor
        · rintro (h | h) <;> simp_all
        · rintro (h | h)
          · rcases List.mem_cons.1 h with rfl | h
            · exact .inr this
            · exact .inl h
          · exact .inr h
      · rw [if_neg hk]
        simp only [List.mem_cons]
        constructor
        · rintro (h | h | h)
          · exact .inl (.inr h)
          · exact .inl (.inl h)
          · exact .inr h
        · rintro ((h | h) | h)
          · exact .inr (.inl h)
          · exact .inl h
          · exact .inr (.inr h)

/-- What one δ-step accumulates: the seed, plus the kernames named by the bodies of the
constants folded over. -/
theorem mem_foldl_expandStep {Γ : GlobalDeclarations} {kn : Kername} :
    ∀ {l acc : List Kername}, kn ∈ l.foldl (expandStep Γ) acc ↔
      kn ∈ acc ∨ ∃ k ∈ l, ∃ b, LBTerm.envLookup Γ k = some (.constantDecl ⟨some b⟩) ∧
        kn ∈ constRefs b
  | [], acc => by simp
  | k :: ks, acc => by
      rw [List.foldl_cons, mem_foldl_expandStep (Γ := Γ) (kn := kn) (l := ks)]
      unfold expandStep
      split
      · rename_i b hb
        simp only [mem_addNames, List.mem_cons]
        constructor
        · rintro ((h | h) | ⟨k', hk', hb'⟩)
          · exact .inr ⟨k, .inl rfl, b, hb, h⟩
          · exact .inl h
          · exact .inr ⟨k', .inr hk', hb'⟩
        · rintro (h | ⟨k', rfl | hk', b', hb', h⟩)
          · exact .inl (.inr h)
          · rw [hb] at hb'; cases hb'; exact .inl (.inl h)
          · exact .inr ⟨k', hk', b', hb', h⟩
      · rename_i hb
        simp only [List.mem_cons]
        constructor
        · rintro (h | ⟨k', hk', hb'⟩)
          · exact .inl h
          · exact .inr ⟨k', .inr hk', hb'⟩
        · rintro (h | ⟨k', rfl | hk', b', hb', h⟩)
          · exact .inl h
          · exact absurd hb' (by simpa using hb b')
          · exact .inr ⟨k', hk', b', hb', h⟩

/-- What one δ-step adds: the bodies of the constants already seen. -/
theorem mem_expandRefs {Γ : GlobalDeclarations} {kn : Kername} {seen : List Kername} :
    kn ∈ expandRefs Γ seen ↔ kn ∈ seen ∨ ∃ k ∈ seen, ∃ b,
      LBTerm.envLookup Γ k = some (.constantDecl ⟨some b⟩) ∧ kn ∈ constRefs b :=
  mem_foldl_expandStep

/-- A δ-step only adds. -/
theorem subset_expandRefs {Γ : GlobalDeclarations} {seen : List Kername} :
    seen ⊆ expandRefs Γ seen := fun _ h => mem_expandRefs.2 (.inl h)

/-- A δ-step is monotone in its seed. -/
theorem expandRefs_mono {Γ : GlobalDeclarations} {s₁ s₂ : List Kername} (h : s₁ ⊆ s₂) :
    expandRefs Γ s₁ ⊆ expandRefs Γ s₂ := by
  intro kn hkn
  rcases mem_expandRefs.1 hkn with hk | ⟨k, hk, b, hb, hcb⟩
  · exact mem_expandRefs.2 (.inl (h hk))
  · exact mem_expandRefs.2 (.inr ⟨k, h hk, b, hb, hcb⟩)

/-- The closure is monotone in its seed. -/
theorem reachFrom_mono {Γ : GlobalDeclarations} {s₁ s₂ : List Kername} (h : s₁ ⊆ s₂) :
    ∀ n, reachFrom Γ s₁ n ⊆ reachFrom Γ s₂ n
  | 0 => h
  | n + 1 => expandRefs_mono (reachFrom_mono h n)

/-- The closure only adds. -/
theorem subset_reachFrom {Γ : GlobalDeclarations} {seen : List Kername} :
    ∀ n, seen ⊆ reachFrom Γ seen n
  | 0 => fun _ h => h
  | n + 1 => fun _ h => subset_expandRefs (subset_reachFrom n h)

/-- The empty seed reaches nothing. -/
theorem reachFrom_nil {Γ : GlobalDeclarations} : ∀ n, reachFrom Γ [] n = []
  | 0 => rfl
  | n + 1 => by rw [reachFrom, reachFrom_nil n]; rfl

/-- The closure of a union is the union of the closures. -/
theorem reachFrom_append {Γ : GlobalDeclarations} {A B : List Kername} {kn : Kername} :
    ∀ n, kn ∈ reachFrom Γ (A ++ B) n → kn ∈ reachFrom Γ A n ∨ kn ∈ reachFrom Γ B n
  | 0, h => List.mem_append.1 h
  | n + 1, h => by
      rcases mem_expandRefs.1 h with hk | ⟨k, hk, b, hb, hcb⟩
      · exact (reachFrom_append n hk).imp (fun hA => subset_expandRefs hA)
          (fun hB => subset_expandRefs hB)
      · exact (reachFrom_append n hk).imp
          (fun hA => mem_expandRefs.2 (.inr ⟨k, hA, b, hb, hcb⟩))
          (fun hB => mem_expandRefs.2 (.inr ⟨k, hB, b, hb, hcb⟩))

/-! ## Threading the reachable set

`ErasesEnv`'s `deps` and `defns` clauses are universally quantified over what a program
reaches, so the simulation's induction consumes them at a subterm, at a δ-unfolded body and
at an ι reduct. Each lemma below moves reachability from the part to the whole, which is the
direction that consumption needs.
-/

/-- `constRefsArgs` is `constRefs` over the arguments. -/
theorem constRefsArgs_eq : ∀ l : List LBTerm, constRefsArgs l = l.flatMap constRefs
  | [] => rfl
  | t :: rest => by simp [constRefsArgs, constRefsArgs_eq rest]

/-- `constRefsAlts` is `constRefs` over the branch bodies. -/
theorem constRefsAlts_eq : ∀ l : List (List BinderName × LBTerm),
    constRefsAlts l = l.flatMap fun a => constRefs a.2
  | [] => rfl
  | (_, b) :: rest => by simp [constRefsAlts, constRefsAlts_eq rest]

/-- `constRefsDefs` is `constRefs` over the block's bodies. -/
theorem constRefsDefs_eq : ∀ l : List (@FixDef LBTerm),
    constRefsDefs l = l.flatMap fun d => constRefs d.body
  | [] => rfl
  | fd :: rest => by simp [constRefsDefs, constRefsDefs_eq rest]

/-- The kernames of a spine are the head's and the arguments'. -/
theorem constRefs_mkApps : ∀ (l : List LBTerm) (f : LBTerm),
    constRefs (LBTerm.mkApps f l) = constRefs f ++ l.flatMap constRefs
  | [], f => by simp
  | a :: l, f => by
      rw [LBTerm.mkApps, constRefs_mkApps l (.app f a)]
      simp [constRefs, List.append_assoc]

/-- Membership in the arguments' kernames. -/
theorem mem_constRefsArgs {kn : Kername} {l : List LBTerm} :
    kn ∈ constRefsArgs l ↔ ∃ x ∈ l, kn ∈ constRefs x := by
  rw [constRefsArgs_eq]; simp

/-- Membership in the branch bodies' kernames. -/
theorem mem_constRefsAlts {kn : Kername} {l : List (List BinderName × LBTerm)} :
    kn ∈ constRefsAlts l ↔ ∃ a ∈ l, kn ∈ constRefs a.2 := by
  rw [constRefsAlts_eq]; simp

/-- Membership in a block's kernames. -/
theorem mem_constRefsDefs {kn : Kername} {l : List (@FixDef LBTerm)} :
    kn ∈ constRefsDefs l ↔ ∃ d ∈ l, kn ∈ constRefs d.body := by
  rw [constRefsDefs_eq]; simp

/-- A subterm names no kername the whole term does not. -/
theorem SubTerm.constRefs_subset {d t : LBTerm} (h : SubTerm d t) :
    constRefs d ⊆ constRefs t := by
  induction h with
  | refl => exact fun _ h => h
  | lambda _ ih => exact ih
  | letInVal _ ih => exact fun _ h => List.mem_append.2 (.inl (ih h))
  | letInBody _ ih => exact fun _ h => List.mem_append.2 (.inr (ih h))
  | appFn _ ih => exact fun _ h => List.mem_append.2 (.inl (ih h))
  | appArg _ ih => exact fun _ h => List.mem_append.2 (.inr (ih h))
  | constructArg hx _ ih =>
      exact fun _ h => List.mem_cons_of_mem _ (mem_constRefsArgs.2 ⟨_, hx, ih h⟩)
  | caseDiscr _ ih =>
      exact fun _ h => List.mem_cons_of_mem _ (List.mem_append.2 (.inl (ih h)))
  | caseAlt ha _ ih =>
      exact fun _ h => List.mem_cons_of_mem _
        (List.mem_append.2 (.inr (mem_constRefsAlts.2 ⟨_, ha, ih h⟩)))
  | proj _ ih => exact fun _ h => List.mem_cons_of_mem _ (ih h)
  | fixBody hd _ ih => exact fun _ h => mem_constRefsDefs.2 ⟨_, hd, ih h⟩

/-- What a subterm reaches, the whole term reaches. -/
theorem ReachableFrom.subterm {Γ : GlobalDeclarations} {d t : LBTerm} {kn : Kername}
    (hs : SubTerm d t) (h : ReachableFrom Γ d kn) : ReachableFrom Γ t kn :=
  kernameElem_iff.2 (reachFrom_mono hs.constRefs_subset _ (kernameElem_iff.1 h))

/-- What either side of an application reaches, the application reaches. -/
theorem ReachableFrom.app {Γ : GlobalDeclarations} {f a : LBTerm} {kn : Kername}
    (h : ReachableFrom Γ f kn ∨ ReachableFrom Γ a kn) : ReachableFrom Γ (.app f a) kn :=
  h.elim (ReachableFrom.subterm (.appFn .refl)) (ReachableFrom.subterm (.appArg .refl))

/-- What a branch body reaches, the `.case` node reaches. -/
theorem ReachableFrom.alt {Γ : GlobalDeclarations} {ip : InductiveId × Nat}
    {discr b : LBTerm} {ns : List BinderName} {alts : List (List BinderName × LBTerm)}
    {kn : Kername} (hm : (ns, b) ∈ alts) (h : ReachableFrom Γ b kn) :
    ReachableFrom Γ (.case ip discr alts) kn :=
  ReachableFrom.subterm (.caseAlt hm .refl) h

/-- Shifting names no new kername. -/
theorem mem_constRefs_shift {kn : Kername} : ∀ (t : LBTerm) (d c : Nat),
    kn ∈ constRefs (LBTerm.shift d c t) → kn ∈ constRefs t := by
  intro t
  induction t using LBTerm.recData with
  | hbox | hfvar | hprim => intro d c h; exact h
  | hbvar i => intro d c h; unfold LBTerm.shift at h; split at h <;> exact h
  | hconst kn' => intro d c h; exact h
  | hlam n b ih => intro d c h; exact ih d (c + 1) h
  | hletIn n v b ihv ihb =>
      intro d c h
      exact List.mem_append.2 ((List.mem_append.1 h).imp (ihv d c) (ihb d (c + 1)))
  | happ f a ihf iha =>
      intro d c h
      exact List.mem_append.2 ((List.mem_append.1 h).imp (ihf d c) (iha d c))
  | hconstruct iid k args ih =>
      intro d c h
      rcases List.mem_cons.1 h with rfl | h
      · exact List.mem_cons_self ..
      · rw [LBTerm.shiftArgs_eq_map, mem_constRefsArgs] at h
        obtain ⟨x, hx, hkn⟩ := h
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        exact List.mem_cons_of_mem _ (mem_constRefsArgs.2 ⟨y, hy, ih y hy d c hkn⟩)
  | hcase info discr alts ihd iha =>
      intro d c h
      rcases List.mem_cons.1 h with rfl | h
      · exact List.mem_cons_self ..
      refine List.mem_cons_of_mem _ (List.mem_append.2 ?_)
      rcases List.mem_append.1 h with h | h
      · exact .inl (ihd d c h)
      · rw [LBTerm.shiftAlts_eq_map, mem_constRefsAlts] at h
        obtain ⟨a, ha, hkn⟩ := h
        obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
        exact .inr (mem_constRefsAlts.2 ⟨b, hb, iha b hb d (c + b.1.length) hkn⟩)
  | hproj p e ih =>
      intro d c h
      rcases List.mem_cons.1 h with rfl | h
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih d c h)
  | hfix defs i ih =>
      intro d c h
      rw [LBTerm.shift, constRefs, LBTerm.shiftDefs_eq_map, mem_constRefsDefs] at h
      obtain ⟨fd, hfd, hkn⟩ := h
      obtain ⟨fd', hfd', rfl⟩ := List.mem_map.1 hfd
      exact mem_constRefsDefs.2 ⟨fd', hfd', ih fd' hfd' d (c + defs.length) hkn⟩

/-- Substitution names no kername the term and the substituend do not. -/
theorem mem_constRefs_subst {kn : Kername} {s : LBTerm} : ∀ (t : LBTerm) (d : Nat),
    kn ∈ constRefs (LBTerm.subst s d t) → kn ∈ constRefs t ∨ kn ∈ constRefs s := by
  intro t
  induction t using LBTerm.recData with
  | hbox | hfvar | hprim => intro d h; exact .inl h
  | hbvar i =>
      intro d h
      unfold LBTerm.subst at h
      split at h
      · exact .inl h
      · split at h
        · exact .inr (mem_constRefs_shift s d 0 h)
        · exact .inl h
  | hconst kn' => intro d h; exact .inl h
  | hlam n b ih => intro d h; exact ih (d + 1) h
  | hletIn n v b ihv ihb =>
      intro d h
      rcases List.mem_append.1 h with h | h
      · exact (ihv d h).imp (fun h => List.mem_append.2 (.inl h)) id
      · exact (ihb (d + 1) h).imp (fun h => List.mem_append.2 (.inr h)) id
  | happ f a ihf iha =>
      intro d h
      rcases List.mem_append.1 h with h | h
      · exact (ihf d h).imp (fun h => List.mem_append.2 (.inl h)) id
      · exact (iha d h).imp (fun h => List.mem_append.2 (.inr h)) id
  | hconstruct iid k args ih =>
      intro d h
      rcases List.mem_cons.1 h with rfl | h
      · exact .inl (List.mem_cons_self ..)
      · rw [LBTerm.substArgs_eq_map, mem_constRefsArgs] at h
        obtain ⟨x, hx, hkn⟩ := h
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        exact (ih y hy d hkn).imp
          (fun h => List.mem_cons_of_mem _ (mem_constRefsArgs.2 ⟨y, hy, h⟩)) id
  | hcase info discr alts ihd iha =>
      intro d h
      rcases List.mem_cons.1 h with rfl | h
      · exact .inl (List.mem_cons_self ..)
      rcases List.mem_append.1 h with h | h
      · exact (ihd d h).imp
          (fun h => List.mem_cons_of_mem _ (List.mem_append.2 (.inl h))) id
      · rw [LBTerm.substAlts_eq_map, mem_constRefsAlts] at h
        obtain ⟨a, ha, hkn⟩ := h
        obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
        exact (iha b hb (d + b.1.length) hkn).imp
          (fun h => List.mem_cons_of_mem _
            (List.mem_append.2 (.inr (mem_constRefsAlts.2 ⟨b, hb, h⟩)))) id
  | hproj p e ih =>
      intro d h
      rcases List.mem_cons.1 h with rfl | h
      · exact .inl (List.mem_cons_self ..)
      · exact (ih d h).imp (fun h => List.mem_cons_of_mem _ h) id
  | hfix defs i ih =>
      intro d h
      rw [LBTerm.subst, constRefs, LBTerm.substDefs_eq_map, mem_constRefsDefs] at h
      obtain ⟨fd, hfd, hkn⟩ := h
      obtain ⟨fd', hfd', rfl⟩ := List.mem_map.1 hfd
      exact (ih fd' hfd' (d + defs.length) hkn).imp
        (fun h => mem_constRefsDefs.2 ⟨fd', hfd', h⟩) id

/-- A simultaneous substitution names no kername the term and the substituends do not. -/
theorem mem_constRefs_substList {kn : Kername} : ∀ (l : List LBTerm) (t : LBTerm),
    kn ∈ constRefs (LBTerm.substList l t) →
      kn ∈ constRefs t ∨ ∃ x ∈ l, kn ∈ constRefs x
  | [], t, h => .inl h
  | x :: l, t, h => by
      rw [LBTerm.substList, List.foldl_cons] at h
      rcases mem_constRefs_substList l _ h with h | ⟨y, hy, hkn⟩
      · exact (mem_constRefs_subst t 0 h).imp id fun h => ⟨x, List.mem_cons_self .., h⟩
      · exact .inr ⟨y, List.mem_cons_of_mem _ hy, hkn⟩

/-! ## Saturation

`Γ.length` δ-steps saturate the closure. A step that unfolds no body the previous step had
not already unfolded is a fixed point, and every other step consumes a distinct key of `Γ`:
there are `Γ.length` of those. Saturation is what makes reachability compositional, which is
what `through_body` needs.
-/

/-- `kn` is declared in `Γ` with a body. -/
def HasBody (Γ : GlobalDeclarations) (kn : Kername) : Prop :=
  ∃ b, LBTerm.envLookup Γ kn = some (.constantDecl ⟨some b⟩)

/-- A successful lookup exhibits the entry it answered with. -/
theorem envLookup_mem : ∀ {Γ : GlobalDeclarations} {kn : Kername} {d : GlobalDecl},
    LBTerm.envLookup Γ kn = some d → (kn, d) ∈ Γ
  | [], _, _, h => by simp [LBTerm.envLookup] at h
  | (k, e) :: rest, kn, d, h => by
      rw [LBTerm.envLookup] at h
      split at h
      · rename_i hb
        cases h
        rw [← Kername.eq_of_beq hb]
        exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (envLookup_mem h)

/-- A key of an entry is a key the lookup answers. -/
theorem envLookup_isSome_of_mem : ∀ {Γ : GlobalDeclarations} {p : Kername × GlobalDecl},
    p ∈ Γ → (LBTerm.envLookup Γ p.1).isSome
  | (k, d) :: rest, p, h => by
      rw [LBTerm.envLookup]
      split
      · rfl
      · rename_i hb
        rcases List.mem_cons.1 h with rfl | h
        · exact absurd (Kername.beq_self k) hb
        · exact envLookup_isSome_of_mem h

/-- A declared key is a key of the environment. -/
theorem HasBody.mem_keys {Γ : GlobalDeclarations} {kn : Kername} (h : HasBody Γ kn) :
    kn ∈ Γ.map Prod.fst :=
  List.mem_map.2 ⟨_, envLookup_mem h.choose_spec, rfl⟩

/-- A δ-step that unfolds no body the previous step had not is a fixed point. -/
theorem expandRefs_stall {Γ : GlobalDeclarations} {seen : List Kername}
    (h : ∀ k, HasBody Γ k → k ∈ expandRefs Γ seen → k ∈ seen) :
    expandRefs Γ (expandRefs Γ seen) ⊆ expandRefs Γ seen := by
  intro kn hkn
  rcases mem_expandRefs.1 hkn with h' | ⟨k, hk, b, hb, hcb⟩
  · exact h'
  · exact mem_expandRefs.2 (.inr ⟨k, h k ⟨b, hb⟩ hk, b, hb, hcb⟩)

/-- The closure is monotone in its fuel. -/
theorem reachFrom_le_add {Γ : GlobalDeclarations} {s : List Kername} {m : Nat} :
    ∀ k : Nat, reachFrom Γ s m ⊆ reachFrom Γ s (m + k)
  | 0 => fun _ h => h
  | k + 1 => fun _ h => subset_expandRefs (reachFrom_le_add k h)

/-- The closure is monotone in its fuel. -/
theorem reachFrom_le {Γ : GlobalDeclarations} {s : List Kername} {m j : Nat} (h : m ≤ j) :
    reachFrom Γ s m ⊆ reachFrom Γ s j := by
  obtain ⟨k, rfl⟩ := Nat.le.dest h
  exact reachFrom_le_add k

/-- A fixed point stays one. -/
theorem reachFrom_stall_add {Γ : GlobalDeclarations} {s : List Kername} {m : Nat}
    (h : reachFrom Γ s (m + 1) ⊆ reachFrom Γ s m) :
    ∀ k : Nat, reachFrom Γ s (m + k) ⊆ reachFrom Γ s m
  | 0 => fun _ h => h
  | k + 1 => fun _ hkn => h (expandRefs_mono (reachFrom_stall_add h k) hkn)

/-- A fixed point stays one. -/
theorem reachFrom_stall {Γ : GlobalDeclarations} {s : List Kername} {m j : Nat}
    (h : reachFrom Γ s (m + 1) ⊆ reachFrom Γ s m) (hj : m ≤ j) :
    reachFrom Γ s j ⊆ reachFrom Γ s m := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hj
  exact reachFrom_stall_add h k

/-- Some step at or below `n + rem.length + 1` is a fixed point, given that every key with a
body not yet reached at step `n` is listed in `rem`. Each step that is not already a fixed
point consumes one entry of `rem`, so `f` bounds the search. -/
theorem find_stall {Γ : GlobalDeclarations} {s : List Kername} :
    ∀ (f : Nat) (rem : List Kername) (n : Nat), rem.length ≤ f →
      (∀ k, HasBody Γ k → k ∉ reachFrom Γ s n → k ∈ rem) →
      ∃ m, m ≤ n + rem.length + 1 ∧ reachFrom Γ s (m + 1) ⊆ reachFrom Γ s m := by
  have _ : DecidableEq Kername := fun _ _ => Classical.propDecidable _
  intro f
  induction f with
  | zero =>
      intro rem n hf hinv
      have hnil : rem = [] := by
        cases rem with
        | nil => rfl
        | cons a l => simp at hf
      refine ⟨n + 1, by omega, expandRefs_stall ?_⟩
      intro k hb _
      by_cases hk : k ∈ reachFrom Γ s n
      · exact hk
      · exact absurd (hinv k hb hk) (by rw [hnil]; simp)
  | succ f ih =>
      intro rem n hf hinv
      by_cases hc : ∀ k, HasBody Γ k → k ∈ reachFrom Γ s (n + 1) → k ∈ reachFrom Γ s n
      · exact ⟨n + 1, by omega, expandRefs_stall hc⟩
      · have hex : ∃ k, HasBody Γ k ∧ k ∈ reachFrom Γ s (n + 1) ∧
            k ∉ reachFrom Γ s n :=
          Classical.byContradiction fun hno =>
            hc fun k hb hin =>
              Classical.byContradiction fun hout => hno ⟨k, hb, hin, hout⟩
        obtain ⟨k₀, hbody, hin, hout⟩ := hex
        have hk₀ : k₀ ∈ rem := hinv k₀ hbody hout
        have hpos : 0 < rem.length := List.length_pos_of_mem hk₀
        have hlen : (rem.erase k₀).length ≤ f := by
          rw [List.length_erase_of_mem hk₀]; omega
        obtain ⟨m, hm, hstall⟩ := ih (rem.erase k₀) (n + 1) hlen (by
          intro k hb hnot
          have hne : k ≠ k₀ := fun h => hnot (h ▸ hin)
          exact (List.mem_erase_of_ne hne).2
            (hinv k hb fun h => hnot (reachFrom_le (Nat.le_succ n) h)))
        refine ⟨m, ?_, hstall⟩
        rw [List.length_erase_of_mem hk₀] at hm
        omega

/-- `Γ.length` δ-steps saturate the closure of any seed. -/
theorem reachFrom_saturated {Γ : GlobalDeclarations} {s : List Kername} {j : Nat}
    (hj : Γ.length ≤ j) : reachFrom Γ s j ⊆ reachFrom Γ s Γ.length := by
  have _ : DecidableEq Kername := fun _ _ => Classical.propDecidable _
  by_cases hs : ∃ k, HasBody Γ k ∧ k ∈ s
  · obtain ⟨k₀, hbody, hmem⟩ := hs
    have hk₀ : k₀ ∈ Γ.map Prod.fst := hbody.mem_keys
    obtain ⟨m, hm, hstall⟩ :=
      find_stall (Γ := Γ) (s := s) Γ.length ((Γ.map Prod.fst).erase k₀) 0
        (by rw [List.length_erase_of_mem hk₀, List.length_map]; omega) (by
        intro k hb hnot
        have hne : k ≠ k₀ := fun h => hnot (h ▸ hmem)
        exact (List.mem_erase_of_ne hne).2 hb.mem_keys)
    have hpos : 0 < Γ.length := by
      have := List.length_pos_of_mem hk₀
      rw [List.length_map] at this; omega
    have hmL : m ≤ Γ.length := by
      rw [List.length_erase_of_mem hk₀, List.length_map] at hm; omega
    exact fun kn hkn => reachFrom_le hmL (reachFrom_stall hstall (Nat.le_trans hmL hj) hkn)
  · have hs' : ∀ k, HasBody Γ k → k ∉ s := fun k hb hm => hs ⟨k, hb, hm⟩
    have hstall : reachFrom Γ s (0 + 1) ⊆ reachFrom Γ s 0 := by
      intro kn hkn
      rcases mem_expandRefs.1 hkn with h' | ⟨k, hk, b, hb, _⟩
      · exact h'
      · exact absurd hk (hs' k ⟨b, hb⟩)
    exact fun kn hkn =>
      reachFrom_le (Nat.zero_le _) (reachFrom_stall hstall (Nat.zero_le j) hkn)

/-- Two runs of the closure compose. -/
theorem reachFrom_add {Γ : GlobalDeclarations} {s : List Kername} :
    ∀ (a c : Nat), reachFrom Γ (reachFrom Γ s a) c = reachFrom Γ s (c + a)
  | a, 0 => by rw [Nat.zero_add]; rfl
  | a, c + 1 => by
      show expandRefs Γ (reachFrom Γ (reachFrom Γ s a) c) = reachFrom Γ s (c + 1 + a)
      rw [reachFrom_add a c]
      have h : c + 1 + a = (c + a) + 1 := by omega
      rw [h]
      rfl

/-- A kername reached from a list of terms' kernames is reached from one of them. -/
theorem mem_reachFrom_flatMap {Γ : GlobalDeclarations} {kn : Kername} :
    ∀ l : List LBTerm, kn ∈ reachFrom Γ (l.flatMap constRefs) Γ.length →
      ∃ x ∈ l, ReachableFrom Γ x kn
  | [], h => by rw [List.flatMap_nil, reachFrom_nil] at h; exact absurd h (by simp)
  | x :: l, h => by
      rw [List.flatMap_cons] at h
      rcases reachFrom_append _ h with h | h
      · exact ⟨x, List.mem_cons_self .., kernameElem_iff.2 h⟩
      · obtain ⟨y, hy, hky⟩ := mem_reachFrom_flatMap l h
        exact ⟨y, List.mem_cons_of_mem _ hy, hky⟩

/-- What a δ-unfolded body reaches, the program reaches: the closure composes, because
`Γ.length` steps saturate it. -/
theorem ReachableFrom.through_body {Γ : GlobalDeclarations} {t b : LBTerm}
    {kn kn' : Kername} (hk : ReachableFrom Γ t kn')
    (hb : LBTerm.envLookup Γ kn' = some (.constantDecl ⟨some b⟩))
    (h : ReachableFrom Γ b kn) : ReachableFrom Γ t kn := by
  have hsub : constRefs b ⊆ reachFrom Γ (constRefs t) (Γ.length + 1) := fun _ hx =>
    mem_expandRefs.2 (.inr ⟨kn', kernameElem_iff.1 hk, b, hb, hx⟩)
  have h2 := reachFrom_mono hsub Γ.length (kernameElem_iff.1 h)
  rw [reachFrom_add] at h2
  exact kernameElem_iff.2 (reachFrom_saturated (by omega) h2)

/-- What an ι reduct or a β contractum reaches, the term and the substituends reach: a
substitution instance names no new kername. -/
theorem ReachableFrom.substList {Γ : GlobalDeclarations} {l : List LBTerm} {t : LBTerm}
    {kn : Kername} (h : ReachableFrom Γ (LBTerm.substList l t) kn) :
    ReachableFrom Γ t kn ∨ ∃ x ∈ l, ReachableFrom Γ x kn := by
  rw [ReachableFrom, kernameElem_iff, reachRefs] at h
  have hsub : constRefs (LBTerm.substList l t) ⊆ constRefs t ++ l.flatMap constRefs := by
    intro kn' hkn'
    rcases mem_constRefs_substList l t hkn' with h' | ⟨x, hx, h'⟩
    · exact List.mem_append.2 (.inl h')
    · exact List.mem_append.2 (.inr (List.mem_flatMap.2 ⟨x, hx, h'⟩))
  rcases reachFrom_append _ (reachFrom_mono hsub _ h) with h | h
  · exact .inl (kernameElem_iff.2 h)
  · exact .inr (mem_reachFrom_flatMap l h)

/-! ## `axiom_free` at the emitted environment -/

/-- `[S §7.3]`'s `axiom_free Σ`, with no realizer whitelist: no constant reachable from `t`
is declared without a body. Decidable, hence `by decide +kernel` per rung; false exactly
where the target is stuck at a `delta` step. The capstone's premise, and nothing else's —
the source semantics gives a body-less constant no value, so the simulation needs none. -/
def NoBodylessRefs (Γ : GlobalDeclarations) (t : LBTerm) : Prop :=
  ∀ kn, ReachableFrom Γ t kn → isBodylessConst (LBTerm.envLookup Γ kn) = false

/-- Decision procedure for `NoBodylessRefs`: the closure is a list. -/
def noBodylessRefsB (Γ : GlobalDeclarations) (t : LBTerm) : Bool :=
  (reachRefs Γ t Γ.length).all fun kn => !isBodylessConst (LBTerm.envLookup Γ kn)

/-- `NoBodylessRefs` is exactly its decision procedure. -/
theorem noBodylessRefs_iff {Γ : GlobalDeclarations} {t : LBTerm} :
    NoBodylessRefs Γ t ↔ noBodylessRefsB Γ t = true := by
  simp only [NoBodylessRefs, noBodylessRefsB, ReachableFrom, List.all_eq_true,
    Bool.not_eq_true', kernameElem_iff]

instance (Γ : GlobalDeclarations) (t : LBTerm) : Decidable (NoBodylessRefs Γ t) :=
  decidable_of_iff _ noBodylessRefs_iff.symm

end LeanToLambdaBox
