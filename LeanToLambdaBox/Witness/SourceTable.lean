import Lean
import Lean4Lean.Std.ToExpr
import LeanToLambdaBox.Erasure

/-!
# `SourceTable` — a reified slice of the elaboration environment

A `SourceTable` holds the data the verification reads out of `Lean.Environment`: the
`Erasure.prepare_erasure`d compiler bodies of a dependency closure (`SourceTable.decls`) and
the inductive metadata with constructor arities (`SourceTable.inds`). There is no oracle column —
relevance is discharged, not tabled — and no configuration column: the table is built under
`reifyConfig`, and a rung states its configuration obligation separately.

The table is produced by the `reify%` term elaborator, which reads the environment of the
elaboration it runs in. There is therefore no committed artifact to ingest, no parser in the
trust base, and no regenerate-and-diff step: what a `by rfl` or `by decide` discharge sees is a
literal copied out of the live environment by `reify%`. No term denotes the ambient environment,
so `SourceTableAdequate` — the statement that the copy is faithful — is not itself decidable; it
is carried as a named hypothesis, and `lake exe reify --check` re-compares a table against the
live environment field by field (`SourceTable.check`).
-/

open Lean

namespace LeanToLambdaBox.Witness

/-! ## The table -/

/-- One constructor of a reified inductive type: its name, its type, its position in the
declaration and the parameter/field split of its arity. -/
structure ReifiedCtor where
  name : Name
  type : Expr
  cidx : Nat
  numParams : Nat
  numFields : Nat
  deriving Inhabited, Repr, ToExpr

/-- A reified inductive type: the block data shared with its mutual companions (`all`,
`numParams`, `numIndices`) together with its own type and constructors. -/
structure ReifiedInduct where
  levelParams : List Name
  type : Expr
  numParams : Nat
  numIndices : Nat
  all : List Name
  ctors : List ReifiedCtor
  deriving Inhabited, Repr, ToExpr

/-- A reified constant: its level parameters and type, read off the kernel constant, and — for
a definition or an opaque constant the eraser δ-unfolds — the body the eraser reads, which is
the *compiler* body (`compilerValue?`) run through `Erasure.prepare_erasure`. `body?` is `none`
for a constant whose body the eraser never traverses (`erasesBody`): axioms, theorems,
quotient primitives, constructors, recursors, and the `casesOn`-like constants that
`Erasure.visitConstApp` eliminates with rather than unfolds. -/
structure ReifiedDecl where
  levelParams : List Name
  type : Expr
  body? : Option Expr
  deriving Inhabited, Repr, ToExpr

/-- The reified slice: the prepared bodies of a dependency closure and the inductive metadata
of every inductive type that closure mentions. -/
structure SourceTable where
  decls : List (Name × ReifiedDecl)
  inds : List (Name × ReifiedInduct)
  deriving Inhabited, Repr, ToExpr

/-- The reified constant of a name, if the table holds one. -/
def SourceTable.decl? (tbl : SourceTable) (n : Name) : Option ReifiedDecl :=
  tbl.decls.lookup n

/-- The reified inductive type of a name, if the table holds one. -/
def SourceTable.ind? (tbl : SourceTable) (n : Name) : Option ReifiedInduct :=
  tbl.inds.lookup n

/-- The tabled body of a name — the δ-column read by the source-side evaluation and by the
environment-erasure relation. -/
def SourceTable.body? (tbl : SourceTable) : Name → Option Expr :=
  fun n => (tbl.decl? n).bind (·.body?)

/-- The level-parameter column, beside `body?`: `cst_universes` of the declaration
(`../metarocq/erasure/theories/Extract.v:264`), which is the scope the eraser erases the
declaration's body at. An untabled name answers `[]`. -/
def SourceTable.levels? (tbl : SourceTable) (n : Name) : List Name :=
  ((tbl.decl? n).map (·.levelParams)).getD []

/-- A successful `List.lookup` finds a member of the list. -/
theorem mem_of_lookup {α : Type} {n : Name} {a : α} :
    ∀ {l : List (Name × α)}, l.lookup n = some a → (n, a) ∈ l
  | [], h => by simp [List.lookup] at h
  | (k, v) :: l, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i hk
      have hk : n = k := by simpa using hk
      subst hk
      simp_all
    · exact List.mem_cons_of_mem _ (mem_of_lookup h)

/-! ## The compiler's view of a declaration

The eraser does not read the kernel body of a definition. `Erasure.visitMutual` opens a
declaration with `Lean.Compiler.LCNF.getDeclInfo?`, which prefers the `_unsafe_rec` companion
the elaborator emits for a recursive definition, and takes that constant's value with
`allowOpaque := true`. For a definition by structural recursion the kernel body eliminates with
`brecOn` while the compiler body calls itself directly, so the two differ and only the second
is erased. -/

/-- The `Lean.ConstantInfo` the code generator reads for `n`: the `_unsafe_rec` companion when
the elaborator emitted one, and `n` itself otherwise. A pure reading of the environment, equal
to `Lean.Compiler.LCNF.getDeclInfo?` run at that environment (`compilerInfo?_eq`). -/
def compilerInfo? (lenv : Environment) (n : Name) : Option ConstantInfo :=
  lenv.find? (Compiler.mkUnsafeRecName n) <|> lenv.find? n

/-- The value the eraser erases for `n`, before `Erasure.prepare_erasure`: the value of
`compilerInfo?`, taken with `allowOpaque := true` as `Erasure.visitMutual` takes it. `none` is
the case `Erasure.visitMutual` emits an axiom for. -/
def compilerValue? (lenv : Environment) (n : Name) : Option Expr :=
  (compilerInfo? lenv n).bind (·.value? (allowOpaque := true))

/-- The block `Erasure.visitMutual` installs a fixvar map for at `n`, and `none` when it takes
its non-recursive exit or emits an axiom. Mirrors the gate at `Erasure.visitMutual`, read off
`compilerInfo?`, which is `Lean.Compiler.LCNF.getDeclInfo?` at the ambient environment
(`compilerInfo?_eq`). The members are the block's names after the `_unsafe_rec` stripping the
run applies. -/
def fixBlock? (lenv : Environment) (n : Name) : Option (List Name) :=
  match compilerInfo? lenv n, compilerValue? lenv n with
  | some ci, some v =>
    if ci.all.length == 1 && !Erasure.name_occurs n v then none
    else some (ci.all.map Erasure.remove_unsafe_rec)
  | _, _ => none

/-- Does the table carry a body for a constant of this kind? Definitions and opaque constants
do — they are the kinds `Erasure.visitMutual` opens. Axioms, theorems, quotient primitives,
constructors and recursors do not, and the eraser reads none of their bodies: a proof is boxed
by `Erasure.visitExpr` before `Erasure.visitConst` sees its head, and the other three kinds have
no value at all. -/
def reifiesBody : ConstantInfo → Bool
  | .defnInfo _ | .opaqueInfo _ => true
  | _ => false

/-- Does the eraser read `n`'s body? `Erasure.visitConstApp` sends a `casesOn`-like head to
`Erasure.visitCasesEta` and a constructor head to `Erasure.visitCtorEta`; only the remaining
heads reach `Erasure.visitConst`, hence `Erasure.visitMutual` and its δ-step. Constructors have
their own arm in `Reify.visit`, so the test left here is `Lean.getCasesInfo?`, on top of the kind
test `reifiesBody`. -/
def erasesBody (n : Name) (ci : ConstantInfo) : CoreM Bool := do
  if !reifiesBody ci then return false
  return (← getCasesInfo? n).isNone

/-- The value the table records a prepared form of, for the constant `ci` of name `n`:
`compilerValue?` where the eraser reads a body, and `none` where it does not. `Reify.visit`
fills the column with it and `checkDecl` re-derives the column from it. -/
def erasedValue? (n : Name) (ci : ConstantInfo) : CoreM (Option Expr) := do
  if ← erasesBody n ci then return compilerValue? (← getEnv) n else return none

/-- `compilerInfo?` is `Lean.Compiler.LCNF.getDeclInfo?` read off the ambient environment. -/
theorem compilerInfo?_eq (n : Name) :
    (Compiler.LCNF.getDeclInfo? n : CoreM (Option ConstantInfo))
      = do return compilerInfo? (← getEnv) n := rfl

/-! ## Adequacy -/

/-- The per-declaration pin: `lenv` knows `n`, with the level parameters and the type the table
records for it. -/
def ReifiedDecl.Pinned (lenv : Environment) (n : Name) (d : ReifiedDecl) : Prop :=
  ∃ ci, lenv.find? n = some ci ∧ ci.levelParams = d.levelParams ∧ ci.type = d.type

/-- α-equivalence of `Lean.Expr`: structural equality ignoring binder names and binder info,
and nothing else. There is no `mdata`-blind arm, so `.mdata d e` and `e` stay unrelated: the
source semantics has no `mdata` rule, and a relation identifying them makes an α-transport of
that semantics false. Extensionally `Lean.Expr.eqv`, which is `@[extern]` and opaque, so no
theorem connects the two; `Expr.alphaEqB` is this relation arm for arm, and the `--check` verb
of the `reify` executable reports a disagreement between it and `Lean.Expr.eqv`. -/
inductive Expr.AlphaEq : Expr → Expr → Prop
  | bvar {i} : AlphaEq (.bvar i) (.bvar i)
  | fvar {x} : AlphaEq (.fvar x) (.fvar x)
  | mvar {x} : AlphaEq (.mvar x) (.mvar x)
  | sort {u} : AlphaEq (.sort u) (.sort u)
  | const {c us} : AlphaEq (.const c us) (.const c us)
  | lit {l} : AlphaEq (.lit l) (.lit l)
  | app {f a g b} : AlphaEq f g → AlphaEq a b → AlphaEq (.app f a) (.app g b)
  | lam {n n' t t' b b' bi bi'} : AlphaEq t t' → AlphaEq b b' →
      AlphaEq (.lam n t b bi) (.lam n' t' b' bi')
  | forallE {n n' t t' b b' bi bi'} : AlphaEq t t' → AlphaEq b b' →
      AlphaEq (.forallE n t b bi) (.forallE n' t' b' bi')
  | letE {n n' t t' v v' b b' nd nd'} : AlphaEq t t' → AlphaEq v v' → AlphaEq b b' →
      AlphaEq (.letE n t v b nd) (.letE n' t' v' b' nd')
  | proj {s i e e'} : AlphaEq e e' → AlphaEq (.proj s i e) (.proj s i e')
  | mdata {d e e'} : AlphaEq e e' → AlphaEq (.mdata d e) (.mdata d e')

/-- The run clause for the one column that is not a `Lean.Environment.find?` output: the code
generator reads a value for `n` in `lenv`, and every successful run of
`Erasure.prepare_erasure` on that value, under a configuration with `csimp` off, returns the
tabled body up to `Expr.AlphaEq`. The value is `compilerValue?`'s — for a recursive definition
the `_unsafe_rec` companion's body, not the kernel's — and preparation is monadic, so this is a
statement about runs. On equality in place of α the clause is uninhabited wherever
`Lean.Compiler.LCNF.inlineMatchers` fires, `Nat.add` included; the price is that a consumer of
a tabled body owes an α-transport. -/
def ReifiedDecl.Prepared (lenv : Environment) (n : Name) (d : ReifiedDecl) : Prop :=
  ∀ b, d.body? = some b →
    ∃ ci v, compilerInfo? lenv n = some ci ∧ ci.value? (allowOpaque := true) = some v ∧
      ∀ (s s' : Erasure.ErasureState) (ctx : Erasure.ErasureContext) (cctx : Core.Context)
        (ref : ST.Ref IO.RealWorld Core.State) (w w' : Void IO.RealWorld) (b' : Expr),
        ctx.config.csimp = false →
        Erasure.prepare_erasure v s ctx cctx ref w = .ok (b', s') w' → Expr.AlphaEq b' b

/-- The per-inductive pin: `lenv` knows `n` as an inductive type of that name, listed in its
own block, with the block data the table records, and each tabled constructor is `lenv`'s
constructor of `n` at its position in the tabled list, with that type, index, parameter count
and field count. The positional clauses are the kernel's own indexing invariants; they are what
carries the table's arithmetic to `ErasureSpec.KernelFields`. -/
def ReifiedInduct.Pinned (lenv : Environment) (n : Name) (I : ReifiedInduct) : Prop :=
  ∃ iv, lenv.find? n = some (.inductInfo iv) ∧ iv.name = n ∧
    iv.levelParams = I.levelParams ∧ iv.type = I.type ∧
    iv.numParams = I.numParams ∧ iv.numIndices = I.numIndices ∧
    iv.all = I.all ∧ n ∈ I.all ∧ iv.ctors = I.ctors.map (·.name) ∧
    ∀ (j : Nat) (c : ReifiedCtor), I.ctors[j]? = some c →
      ∃ cv, lenv.find? c.name = some (.ctorInfo cv) ∧
        cv.type = c.type ∧ cv.cidx = c.cidx ∧ c.cidx = j ∧
        cv.numParams = c.numParams ∧ c.numParams = I.numParams ∧
        cv.numFields = c.numFields ∧ cv.induct = n

/-- The table is a faithful copy of the slice of `lenv` it claims: every tabled constant is
pinned and its tabled body is what `Erasure.prepare_erasure` computes from the constant's
compiler value, and every tabled inductive type is pinned. Not decidable — no term denotes the
ambient environment — so this is a named hypothesis of every theorem that reads a table,
mechanised outside the kernel by `lake exe reify --check`. -/
structure SourceTableAdequate (lenv : Environment) (tbl : SourceTable) : Prop where
  decls : ∀ n d, (n, d) ∈ tbl.decls →
    ReifiedDecl.Pinned lenv n d ∧ ReifiedDecl.Prepared lenv n d
  inds : ∀ n I, (n, I) ∈ tbl.inds → ReifiedInduct.Pinned lenv n I
  /-- The **compiler** declaration carries the kernel declaration's level parameters. A
      property of `Lean.Compiler.LCNF.getDeclInfo?` — `compilerInfo?` at the ambient
      environment (`compilerInfo?_eq`) — and the one column of it the run reads that
      `ReifiedDecl.Pinned` does not pin: `Erasure.visitMutual` opens a declaration with
      `getDeclInfo?`, which answers the `_unsafe_rec` companion where the elaborator emitted
      one, and installs `lparams := ci.levelParams` from *that* constant
      (`Erasure.lean:889`, `:912`), while `SourceTable.levels?` and `CompilerBodies` read
      `lenv.find?`. Without this the two scopes are unrelated and the erasure a run records
      is at a scope no specification names. Spent by U7's `RegContent.defns`, which reads
      the tabled body at `tbl.levels? n` against a run that erased it at the companion's
      column. Class **D**, like the two clauses beside it, and checked per table by
      `lake exe reify --check` (`TableMismatch.compilerLevels`). -/
  compilerLevels : ∀ n d, (n, d) ∈ tbl.decls →
    ∀ ci, compilerInfo? lenv n = some ci → ci.levelParams = d.levelParams

/-- Adequacy transported to the lookup interface: a tabled body is the prepared body of the
value the code generator reads for that name, up to `Expr.AlphaEq`. -/
theorem SourceTableAdequate.body?_prepared {lenv : Environment} {tbl : SourceTable} {n : Name}
    {b : Expr} (h : SourceTableAdequate lenv tbl) (hb : tbl.body? n = some b) :
    ∃ ci v, compilerInfo? lenv n = some ci ∧ ci.value? (allowOpaque := true) = some v ∧
      ∀ (s s' : Erasure.ErasureState) (ctx : Erasure.ErasureContext) (cctx : Core.Context)
        (ref : ST.Ref IO.RealWorld Core.State) (w w' : Void IO.RealWorld) (b' : Expr),
        ctx.config.csimp = false →
        Erasure.prepare_erasure v s ctx cctx ref w = .ok (b', s') w' → Expr.AlphaEq b' b := by
  cases hd : tbl.decls.lookup n with
  | none =>
    rw [SourceTable.body?, SourceTable.decl?, hd] at hb
    nomatch (show (none : Option Expr) = some b from hb)
  | some d =>
    rw [SourceTable.body?, SourceTable.decl?, hd] at hb
    exact (h.decls n d (mem_of_lookup hd)).2 b hb

/-- Adequacy at the level column: a tabled name's level scope is the one `lenv` declares it
with. `ReifiedDecl.Pinned`'s `levelParams` conjunct, read through the lookup interface. -/
theorem SourceTableAdequate.levels?_eq {lenv : Environment} {tbl : SourceTable} {n : Name}
    {ci : ConstantInfo} (h : SourceTableAdequate lenv tbl) (hd : (tbl.decl? n).isSome)
    (hci : lenv.find? n = some ci) : tbl.levels? n = ci.levelParams := by
  cases hl : tbl.decls.lookup n with
  | none => rw [SourceTable.decl?, hl] at hd; simp at hd
  | some d =>
    obtain ⟨ci', hci', hlp, -⟩ := (h.decls n d (mem_of_lookup hl)).1
    obtain rfl : ci' = ci := Option.some.inj (hci'.symm.trans hci)
    rw [SourceTable.levels?, SourceTable.decl?, hl]
    exact hlp.symm

/-- Adequacy at the level column the **run** installs: the scope `Erasure.visitMutual` enters
a declaration's body under (`Erasure.lean:889`, `:912`) is the table's own column, so the
erasure a run records and the erasure `ErasesEnv.defns` asks for are at the same scope.
`SourceTableAdequate.compilerLevels` read through the lookup interface. -/
theorem SourceTableAdequate.compilerLevels?_eq {lenv : Environment} {tbl : SourceTable}
    {n : Name} {ci : ConstantInfo} (h : SourceTableAdequate lenv tbl)
    (hd : (tbl.decl? n).isSome) (hci : compilerInfo? lenv n = some ci) :
    tbl.levels? n = ci.levelParams := by
  cases hl : tbl.decls.lookup n with
  | none => rw [SourceTable.decl?, hl] at hd; simp at hd
  | some d =>
    rw [SourceTable.levels?, SourceTable.decl?, hl]
    exact (h.compilerLevels n d (mem_of_lookup hl) ci hci).symm

/-! ## Reification -/

/-- The configuration `reify%` prepares bodies under. `Erasure.prepare_erasure` reads exactly
one field, `Erasure.ErasureConfig.csimp`, and every correctness statement needs it off: `csimp`
replaces bodies by tail-recursive variants that are not the declaration's own. -/
def reifyConfig : Erasure.ErasureConfig := { csimp := false }

namespace Reify

/-- What the reification worklist has produced so far, and which names it has processed. -/
structure State where
  decls : Array (Name × ReifiedDecl) := #[]
  inds : Array (Name × ReifiedInduct) := #[]
  seen : NameSet := {}

/-- The reification monad: a worklist state over `CoreM`, whose environment is the environment
of the elaboration `reify%` runs in. -/
abbrev M := StateT State CoreM

/-- Record a reified constant. -/
def pushDecl (n : Name) (d : ReifiedDecl) : M Unit :=
  modify fun s => { s with decls := s.decls.push (n, d) }

/-- Record a reified inductive type. -/
def pushInd (n : Name) (I : ReifiedInduct) : M Unit :=
  modify fun s => { s with inds := s.inds.push (n, I) }

/-- Reify one constructor of `n` from the live environment. -/
def reifyCtor (c : Name) : M ReifiedCtor := do
  let .ctorInfo cv ← getConstInfo c | throwError "{c} is not a constructor"
  return { name := c, type := cv.type, cidx := cv.cidx,
           numParams := cv.numParams, numFields := cv.numFields }

/-- Reify `n` and everything its prepared body, or its constructors' types, mention.
A body is `erasedValue?` run through `Erasure.prepare_erasure` under `reifyConfig` — the
expression `Erasure.visitMutual` erases; an inductive type pulls in its whole mutual block.
Terminates because the environment is finite and every name is processed at most once. -/
partial def visit (n : Name) : M Unit := do
  if (← get).seen.contains n then return
  modify fun s => { s with seen := s.seen.insert n }
  let ci ← getConstInfo n
  match ci with
  | .inductInfo iv =>
    -- `n` is marked already; its mutual companions are marked here, as the block is reified.
    for J in iv.all do
      unless J != n && (← get).seen.contains J do
        modify fun s => { s with seen := s.seen.insert J }
        let .inductInfo jv ← getConstInfo J | throwError "{J} is not an inductive type"
        let ctors ← jv.ctors.mapM reifyCtor
        pushInd J { levelParams := jv.levelParams, type := jv.type, numParams := jv.numParams,
                    numIndices := jv.numIndices, all := jv.all, ctors }
        for c in jv.ctors do visit c
        for c in jv.type.getUsedConstants do visit c
  | .ctorInfo cv =>
    pushDecl n { levelParams := cv.levelParams, type := cv.type, body? := none }
    visit cv.induct
    for c in cv.type.getUsedConstants do visit c
  | .recInfo rv =>
    pushDecl n { levelParams := rv.levelParams, type := rv.type, body? := none }
    for I in rv.all do visit I
  | _ =>
    match ← erasedValue? n ci with
    | some v =>
      let (body, _) ← Erasure.run (Erasure.prepare_erasure v) reifyConfig
      pushDecl n { levelParams := ci.levelParams, type := ci.type, body? := some body }
      for c in body.getUsedConstants do visit c
    | none =>
      pushDecl n { levelParams := ci.levelParams, type := ci.type, body? := none }

/-- Reify the dependency closure of `ns` out of the environment of the current elaboration. -/
def table (ns : List Name) : CoreM SourceTable := do
  let (_, s) ← (ns.forM visit).run {}
  let decls := s.decls.qsort (fun a b => toString a.1 < toString b.1)
  let inds := s.inds.qsort (fun a b => toString a.1 < toString b.1)
  return { decls := decls.toList, inds := inds.toList }

end Reify

/-- `reify% c₁, …, cₙ` elaborates to the `SourceTable` of the dependency closure of the named
constants, read out of the environment of this elaboration. -/
syntax (name := reifyTerm) "reify% " ident,+ : term

open Elab Term in
@[term_elab reifyTerm]
def elabReify : TermElab := fun stx expectedType? => do
  let ns ← stx[1].getSepArgs.toList.mapM fun s => realizeGlobalConstNoOverloadWithInfo s
  let tbl ← Reify.table ns
  let e := toExpr tbl
  match expectedType? with
  | some t => ensureHasType t e
  | none => return e

/-! ## Checking a table against the live environment -/

/-- A field-by-field disagreement between a table and the environment checked against. -/
inductive TableMismatch where
  | unknownDecl (n : Name)
  | declLevels (n : Name)
  | compilerLevels (n : Name)
  | declType (n : Name)
  | declBody (n : Name)
  | alphaDisagreement (n : Name)
  | missingBody (n : Name)
  | spuriousBody (n : Name)
  | prepareFailed (n : Name) (msg : String)
  | notInductive (n : Name)
  | indBlock (n : Name)
  | ctorList (n : Name)
  | ctorField (n : Name) (c : Name)
  deriving Inhabited, Repr

/-- One line naming the disagreement and the declaration it is about. -/
def TableMismatch.describe : TableMismatch → String
  | .unknownDecl n => s!"{n}: not in the environment"
  | .declLevels n => s!"{n}: level parameters differ"
  | .compilerLevels n =>
    s!"{n}: the compiler declaration's level parameters differ from the table's"
  | .declType n => s!"{n}: type differs"
  | .declBody n => s!"{n}: tabled body is not the prepared compiler body"
  | .alphaDisagreement n =>
    s!"{n}: Expr.eqv and Expr.alphaEqB disagree on the prepared body"
  | .missingBody n => s!"{n}: a definition or opaque constant, but the table records no body"
  | .spuriousBody n =>
    s!"{n}: the table records a body, but the code generator reads no value for it"
  | .prepareFailed n msg => s!"{n}: prepare_erasure failed: {msg}"
  | .notInductive n => s!"{n}: not an inductive type in the environment"
  | .indBlock n => s!"{n}: block data (levels, type, parameters, indices, block) differ"
  | .ctorList n => s!"{n}: constructor list differs"
  | .ctorField n c => s!"{n}: constructor {c} differs"

/-- An agreement worth printing: the table and the environment match, but not on the nose. -/
inductive TableNote where
  | declBodyAlpha (n : Name)
  deriving Inhabited, Repr

/-- One line naming the agreement and the declaration it is about. -/
def TableNote.describe : TableNote → String
  | .declBodyAlpha n => s!"{n}: tabled body matches up to binder names"

/-- `Expr.AlphaEq` as a Boolean, one arm per constructor of the relation. `partial` because
`Expr` carries computed fields, so a two-argument recursion over it has no structural measure;
nothing in `Prop` reduces this, which is used only inside `checkDecl`, against `Expr.eqv`. -/
partial def Expr.alphaEqB : Expr → Expr → Bool
  | .bvar i, .bvar j => i == j
  | .fvar x, .fvar y => x == y
  | .mvar x, .mvar y => x == y
  | .sort u, .sort v => u == v
  | .const c us, .const c' us' => c == c' && us == us'
  | .lit l, .lit l' => l == l'
  | .app f a, .app g b => alphaEqB f g && alphaEqB a b
  | .lam _ t b _, .lam _ t' b' _ => alphaEqB t t' && alphaEqB b b'
  | .forallE _ t b _, .forallE _ t' b' _ => alphaEqB t t' && alphaEqB b b'
  | .letE _ t v b _, .letE _ t' v' b' _ => alphaEqB t t' && alphaEqB v v' && alphaEqB b b'
  | .proj s i e, .proj s' i' e' => s == s' && i == i' && alphaEqB e e'
  | .mdata d e, .mdata d' e' => d == d' && alphaEqB e e'
  | _, _ => false

/-- Check one tabled constant against the live environment: level parameters and type against
`Lean.Environment.find?`, the level parameters again against `compilerInfo?` — the constant
the run reads its scope from, which is the `_unsafe_rec` companion where there is one — and
the tabled body against a fresh `Erasure.prepare_erasure` run on
the constant's `erasedValue?` — the same column `Reify.visit` fills. Types are compared with
`Lean.Expr.equal`, which is structural; the body is compared with `==`, which is `Lean.Expr.eqv`,
the decision procedure for the relation `ReifiedDecl.Prepared` pins the body up to. A body that
matches only up to binder names is a pass with a note; anything beyond them is `declBody`. The
`@[extern]` `eqv` is checked against `Expr.alphaEqB` on every compared pair, and a disagreement
is itself a mismatch. -/
def checkDecl (n : Name) (d : ReifiedDecl) :
    CoreM (Array TableMismatch × Array TableNote) := do
  let some ci := (← getEnv).find? n | return (#[.unknownDecl n], #[])
  let mut ms := #[]
  let mut ns := #[]
  if ci.levelParams != d.levelParams then ms := ms.push (.declLevels n)
  if let some cci := compilerInfo? (← getEnv) n then
    if cci.levelParams != d.levelParams then ms := ms.push (.compilerLevels n)
  if !ci.type.equal d.type then ms := ms.push (.declType n)
  match d.body?, ← erasedValue? n ci with
  | some b, some v =>
    try
      let (b', _) ← Erasure.run (Erasure.prepare_erasure v) reifyConfig
      let eqv := b' == b
      if eqv != Expr.alphaEqB b' b then ms := ms.push (.alphaDisagreement n)
      if !eqv then ms := ms.push (.declBody n)
      else if !b'.equal b then ns := ns.push (.declBodyAlpha n)
    catch e =>
      ms := ms.push (.prepareFailed n (← e.toMessageData.toString))
  | some _, none => ms := ms.push (.spuriousBody n)
  | none, some _ => ms := ms.push (.missingBody n)
  | none, none => pure ()
  return (ms, ns)

/-- Check one tabled inductive type against the live environment: block data against the
`Lean.InductiveVal` — its name, its membership in its own block included — and every tabled
constructor against its `Lean.ConstructorVal`, at its position in the tabled list. -/
def checkInd (n : Name) (I : ReifiedInduct) : CoreM (Array TableMismatch) := do
  let some (.inductInfo iv) := (← getEnv).find? n | return #[.notInductive n]
  let mut ms := #[]
  if iv.name != n || iv.levelParams != I.levelParams || !iv.type.equal I.type
      || iv.numParams != I.numParams || iv.numIndices != I.numIndices || iv.all != I.all
      || !I.all.contains n then
    ms := ms.push (.indBlock n)
  if iv.ctors != I.ctors.map (·.name) then
    return ms.push (.ctorList n)
  for (c, j) in I.ctors.zipIdx do
    match (← getEnv).find? c.name with
    | some (.ctorInfo cv) =>
      if !cv.type.equal c.type || cv.cidx != c.cidx || c.cidx != j
          || cv.numParams != c.numParams || c.numParams != I.numParams
          || cv.numFields != c.numFields || cv.induct != n then
        ms := ms.push (.ctorField n c.name)
    | _ => ms := ms.push (.ctorField n c.name)
  return ms

/-- Every disagreement between the table and the environment of the current `CoreM` run, and
every body that agrees only up to binder names. An empty mismatch array is the mechanised form
of `SourceTableAdequate` at that environment, modulo the clauses no computation reaches: the
body column is re-derived by running `Erasure.prepare_erasure` once, not quantified over all
runs, and no theorem connects `Lean.Expr.eqv` to `Expr.AlphaEq`. -/
def SourceTable.check (tbl : SourceTable) :
    CoreM (Array TableMismatch × Array TableNote) := do
  let mut ms := #[]
  let mut ns := #[]
  for (n, d) in tbl.decls do
    let (ms', ns') ← checkDecl n d
    ms := ms ++ ms'; ns := ns ++ ns'
  for (n, I) in tbl.inds do ms := ms ++ (← checkInd n I)
  return (ms, ns)

/-! ## Self-test -/

namespace SelfTest

/-- A toy declaration whose prepared body is a two-constructor spine: the subject of this
module's checked examples. -/
def toyTwo : Nat := Nat.succ (Nat.succ Nat.zero)

/-- The reified closure of `LeanToLambdaBox.Witness.SelfTest.toyTwo`: the declaration itself,
`Nat`'s constructors, and `Nat` as a reified inductive type. -/
def toyTable : SourceTable := reify% toyTwo

/-- The tabled body is the constructor spine, field for field. -/
example : toyTable.body? ``toyTwo =
    some (.app (.const ``Nat.succ []) (.app (.const ``Nat.succ []) (.const ``Nat.zero []))) := by
  rfl

/-- The tabled type and level parameters of the toy declaration. -/
example : (toyTable.decl? ``toyTwo).map (fun d => (d.levelParams, d.type)) =
    some ([], .const ``Nat []) := by
  rfl

/-- `Nat` is tabled with its block data and both constructors, field for field. -/
example : toyTable.ind? ``Nat =
    some { levelParams := [], type := .sort (.succ .zero), numParams := 0, numIndices := 0,
           all := [``Nat],
           ctors := [{ name := ``Nat.zero, type := .const ``Nat [],
                       cidx := 0, numParams := 0, numFields := 0 },
                     { name := ``Nat.succ,
                       type := .forallE `n (.const ``Nat []) (.const ``Nat []) .default,
                       cidx := 1, numParams := 0, numFields := 1 }] } := by
  rfl

/-- The constructor arities of the tabled `Nat`, decided on the table. -/
example : (toyTable.ind? ``Nat).map (fun I => I.ctors.map (·.numFields)) = some [0, 1] := by
  decide

/-- A matcher-bearing declaration. Preparing its body inlines the matcher, and the inlined
`let`-binders are named from the name generator, so a fresh preparation agrees with the tabled
body only up to binder names — the case `ReifiedDecl.Prepared` is stated up to `Expr.AlphaEq`
for, and the positive half of the executable's α self-test. -/
def spikeMatch : Nat :=
  match Nat.succ (Nat.succ Nat.zero) with
  | Nat.zero => Nat.zero
  | Nat.succ n => n

/-- The reified closure of `spikeMatch` and of `Nat.add`, the two measured declarations whose
preparation is not binder-name stable. `lake exe reify --check` passes it with one note each. -/
def matchTable : SourceTable := reify% spikeMatch, Nat.add

/-- A deliberately wrong table: it claims `LeanToLambdaBox.Witness.SelfTest.toyTwo` has body
`Nat.zero`. `lake exe reify --check` must reject it — that is the negative half of the
executable's self-test, and it is data, not a claim, so this module stays green. -/
def staleTable : SourceTable :=
  { decls := [(``toyTwo, { levelParams := [], type := .const ``Nat [],
                           body? := some (.const ``Nat.zero []) })],
    inds := [] }

end SelfTest

end LeanToLambdaBox.Witness
