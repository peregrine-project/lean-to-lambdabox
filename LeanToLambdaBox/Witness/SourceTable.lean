import Lean
import Lean4Lean.Std.ToExpr
import LeanToLambdaBox.Erasure

/-!
# `SourceTable` — a reified slice of the elaboration environment

A `SourceTable` holds the data the verification reads out of `Lean.Environment`: the
`Erasure.prepare_erasure`d bodies of a dependency closure (`SourceTable.decls`) and the
inductive metadata with constructor arities (`SourceTable.inds`). There is no oracle column —
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

/-- A reified constant: its level parameters, its type, and — for a definition — the body the
eraser reads, already run through `Erasure.prepare_erasure`. `body?` is `none` for a constant
whose body the eraser never traverses (axioms, theorems, constructors, recursors). -/
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

/-! ## Adequacy -/

/-- The per-declaration pin: `lenv` knows `n`, with the level parameters and the type the table
records for it. -/
def ReifiedDecl.Pinned (lenv : Environment) (n : Name) (d : ReifiedDecl) : Prop :=
  ∃ ci, lenv.find? n = some ci ∧ ci.levelParams = d.levelParams ∧ ci.type = d.type

/-- The run clause for the one column that is not a `Lean.Environment.find?` output: `n` has a
value in `lenv`, and every successful run of `Erasure.prepare_erasure` on that value, in a
context whose configuration has `csimp` off, returns the tabled body.
`Erasure.prepare_erasure` is monadic, so this is a statement about runs, not an equation.
It is inhabited only where preparation is name-stable: `Lean.Compiler.LCNF.inlineMatchers`
draws the `let`-binder names it introduces from the name generator, so a declaration whose
preparation inlines a matcher has prepared bodies that agree across runs only up to binder
names — `lake exe reify --check` reports that case as `TableMismatch.declBodyAlpha`. -/
def ReifiedDecl.Prepared (lenv : Environment) (n : Name) (d : ReifiedDecl) : Prop :=
  ∀ b, d.body? = some b →
    ∃ ci v, lenv.find? n = some ci ∧ ci.value? = some v ∧
      ∀ (s s' : Erasure.ErasureState) (ctx : Erasure.ErasureContext) (cctx : Core.Context)
        (ref : ST.Ref IO.RealWorld Core.State) (w w' : Void IO.RealWorld) (b' : Expr),
        ctx.config.csimp = false →
        Erasure.prepare_erasure v s ctx cctx ref w = .ok (b', s') w' → b' = b

/-- The per-inductive pin: `lenv` knows `n` as an inductive type with the block data the table
records, and each tabled constructor is `lenv`'s constructor of `n` with that type, index and
parameter/field split. -/
def ReifiedInduct.Pinned (lenv : Environment) (n : Name) (I : ReifiedInduct) : Prop :=
  ∃ iv, lenv.find? n = some (.inductInfo iv) ∧
    iv.levelParams = I.levelParams ∧ iv.type = I.type ∧
    iv.numParams = I.numParams ∧ iv.numIndices = I.numIndices ∧
    iv.all = I.all ∧ iv.ctors = I.ctors.map (·.name) ∧
    ∀ c ∈ I.ctors, ∃ cv, lenv.find? c.name = some (.ctorInfo cv) ∧
      cv.type = c.type ∧ cv.cidx = c.cidx ∧
      cv.numParams = c.numParams ∧ cv.numFields = c.numFields ∧ cv.induct = n

/-- The table is a faithful copy of the slice of `lenv` it claims: every tabled constant is
pinned and its tabled body is what `Erasure.prepare_erasure` computes, and every tabled
inductive type is pinned. Not decidable — no term denotes the ambient environment — so this is
a named hypothesis of every theorem that reads a table, mechanised outside the kernel by
`lake exe reify --check`. -/
structure SourceTableAdequate (lenv : Environment) (tbl : SourceTable) : Prop where
  decls : ∀ n d, (n, d) ∈ tbl.decls →
    ReifiedDecl.Pinned lenv n d ∧ ReifiedDecl.Prepared lenv n d
  inds : ∀ n I, (n, I) ∈ tbl.inds → ReifiedInduct.Pinned lenv n I

/-- Adequacy transported to the lookup interface: a tabled body is the prepared body of the
value `lenv` holds for that name. -/
theorem SourceTableAdequate.body?_prepared {lenv : Environment} {tbl : SourceTable} {n : Name}
    {b : Expr} (h : SourceTableAdequate lenv tbl) (hb : tbl.body? n = some b) :
    ∃ ci v, lenv.find? n = some ci ∧ ci.value? = some v ∧
      ∀ (s s' : Erasure.ErasureState) (ctx : Erasure.ErasureContext) (cctx : Core.Context)
        (ref : ST.Ref IO.RealWorld Core.State) (w w' : Void IO.RealWorld) (b' : Expr),
        ctx.config.csimp = false →
        Erasure.prepare_erasure v s ctx cctx ref w = .ok (b', s') w' → b' = b := by
  cases hd : tbl.decls.lookup n with
  | none =>
    rw [SourceTable.body?, SourceTable.decl?, hd] at hb
    nomatch (show (none : Option Expr) = some b from hb)
  | some d =>
    rw [SourceTable.body?, SourceTable.decl?, hd] at hb
    exact (h.decls n d (mem_of_lookup hd)).2 b hb

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
Definition bodies go through `Erasure.prepare_erasure` under `reifyConfig`; an inductive type
pulls in its whole mutual block. Terminates because the environment is finite and every name is
processed at most once. -/
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
  | .defnInfo dv =>
    let (body, _) ← Erasure.run (Erasure.prepare_erasure dv.value) reifyConfig
    pushDecl n { levelParams := dv.levelParams, type := dv.type, body? := some body }
    for c in body.getUsedConstants do visit c
  | _ =>
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
  | declType (n : Name)
  | declBody (n : Name)
  | declBodyAlpha (n : Name)
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
  | .declType n => s!"{n}: type differs"
  | .declBody n => s!"{n}: tabled body is not the prepared body"
  | .declBodyAlpha n => s!"{n}: tabled body is the prepared body only up to binder names"
  | .missingBody n => s!"{n}: a definition, but the table records no body"
  | .spuriousBody n => s!"{n}: the table records a body, but the constant has no value"
  | .prepareFailed n msg => s!"{n}: prepare_erasure failed: {msg}"
  | .notInductive n => s!"{n}: not an inductive type in the environment"
  | .indBlock n => s!"{n}: block data (levels, type, parameters, indices, block) differ"
  | .ctorList n => s!"{n}: constructor list differs"
  | .ctorField n c => s!"{n}: constructor {c} differs"

/-- Check one tabled constant against the live environment: level parameters and type against
`Lean.Environment.find?`, and the tabled body against a fresh `Erasure.prepare_erasure` run on
the environment's own value. Expression comparison is `Lean.Expr.equal`, which is structural —
`==` on `Lean.Expr` is α-equivalence and would accept a table with different binder names. -/
def checkDecl (n : Name) (d : ReifiedDecl) : CoreM (Array TableMismatch) := do
  let some ci := (← getEnv).find? n | return #[.unknownDecl n]
  let mut ms := #[]
  if ci.levelParams != d.levelParams then ms := ms.push (.declLevels n)
  if !ci.type.equal d.type then ms := ms.push (.declType n)
  match d.body?, ci.value? with
  | some b, some v =>
    try
      let (b', _) ← Erasure.run (Erasure.prepare_erasure v) reifyConfig
      if !b'.equal b then
        ms := ms.push (if b' == b then .declBodyAlpha n else .declBody n)
    catch e =>
      ms := ms.push (.prepareFailed n (← e.toMessageData.toString))
  | some _, none => ms := ms.push (.spuriousBody n)
  | none, _ => if ci.isDefinition then ms := ms.push (.missingBody n)
  return ms

/-- Check one tabled inductive type against the live environment: block data against the
`Lean.InductiveVal`, and every tabled constructor against its `Lean.ConstructorVal`. -/
def checkInd (n : Name) (I : ReifiedInduct) : CoreM (Array TableMismatch) := do
  let some (.inductInfo iv) := (← getEnv).find? n | return #[.notInductive n]
  let mut ms := #[]
  if iv.levelParams != I.levelParams || !iv.type.equal I.type || iv.numParams != I.numParams
      || iv.numIndices != I.numIndices || iv.all != I.all then
    ms := ms.push (.indBlock n)
  if iv.ctors != I.ctors.map (·.name) then
    return ms.push (.ctorList n)
  for c in I.ctors do
    match (← getEnv).find? c.name with
    | some (.ctorInfo cv) =>
      if !cv.type.equal c.type || cv.cidx != c.cidx || cv.numParams != c.numParams
          || cv.numFields != c.numFields || cv.induct != n then
        ms := ms.push (.ctorField n c.name)
    | _ => ms := ms.push (.ctorField n c.name)
  return ms

/-- Every disagreement between the table and the environment of the current `CoreM` run. An
empty result is the mechanised form of `SourceTableAdequate` at that environment, modulo the
clauses no computation reaches: the body column is re-derived by running
`Erasure.prepare_erasure` once, not quantified over all runs. -/
def SourceTable.check (tbl : SourceTable) : CoreM (Array TableMismatch) := do
  let mut ms := #[]
  for (n, d) in tbl.decls do ms := ms ++ (← checkDecl n d)
  for (n, I) in tbl.inds do ms := ms ++ (← checkInd n I)
  return ms

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

/-- A deliberately wrong table: it claims `LeanToLambdaBox.Witness.SelfTest.toyTwo` has body
`Nat.zero`. `lake exe reify --check` must reject it — that is the negative half of the
executable's self-test, and it is data, not a claim, so this module stays green. -/
def staleTable : SourceTable :=
  { decls := [(``toyTwo, { levelParams := [], type := .const ``Nat [],
                           body? := some (.const ``Nat.zero []) })],
    inds := [] }

end SelfTest

end LeanToLambdaBox.Witness
