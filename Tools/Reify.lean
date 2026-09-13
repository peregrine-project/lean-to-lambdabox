import LeanToLambdaBox.Witness.SourceTable

/-!
# `reify` — table drift detection

Three verbs, all against the environment `MOD` elaborated in.

`lake exe reify --check MOD NAME…` imports `MOD`, evaluates each named `SourceTable` constant
and compares it, field by field, against the environment `MOD` elaborated in — the same
comparison `LeanToLambdaBox.Witness.SourceTable.check` performs, run outside the kernel.
Nothing is regenerated and diffed: the table under test is the committed one, and it is held
against `Lean.Environment.find?` and a fresh `Erasure.prepare_erasure` run on the value the code
generator reads for the constant (`LeanToLambdaBox.Witness.compilerValue?`, the `_unsafe_rec`
companion's body where the elaborator emitted one) — the column `reify%` fills. Bodies are
compared up to binder names, the relation `LeanToLambdaBox.Witness.ReifiedDecl.Prepared` pins
them up to; such a match is a pass with a `TableNote.declBodyAlpha` note. Exit `0` when every
table matches, `1` on any mismatch or error.

`lake exe reify --blocks MOD NAME…` reads `LeanToLambdaBox.Witness.fixBlock?` — the gate
`Erasure.visitMutual` takes — off the same environment, for every name of each named table, and
checks the two clauses of `LeanToLambdaBox.TableBlocks` a computation reaches: every member of
an installed block is tabled, and every member's tabled body is λ-headed.

`lake exe reify --prepared MOD NAME…` runs `Erasure.prepare_erasure` on `.const NAME []` and
reports whether the result is the subject itself, which is the premise each rung carries about
its own subject.

The negative half of the self-test is
`LeanToLambdaBox.Witness.SelfTest.staleTable`, a deliberately wrong table the tool must reject.
-/

open Lean LeanToLambdaBox.Witness

/-- What this tool does and how to call it. -/
def usage : String :=
  "reify — check a reified SourceTable against the live environment\n\n\
   usage:\n  \
     reify --check MOD NAME…    import MOD, compare each named table against MOD's environment\n  \
     reify --blocks MOD NAME…   check the fix blocks MOD's environment installs for each table\n  \
     reify --prepared MOD NAME… check that prepare_erasure is the identity at each constant\n\n\
   NAME is the fully qualified name of a `SourceTable` constant in MOD, or — for --prepared —\n\
   of any constant. Exit 0 if every check passes, 1 otherwise."

/-- Compare one named table against `env`, printing every mismatch and every note. A body that
matches only up to binder names is a note, not a mismatch, and the summary counts those and the
`Expr.alphaEqB`/`Lean.Expr.eqv` disagreements separately. Returns whether it matched. -/
def checkTable (env : Environment) (tbl : SourceTable) (name : Name) : IO Bool := do
  let ctx : Core.Context := { fileName := "<reify>", fileMap := default, maxHeartbeats := 0 }
  let ((ms, ns), _) ← (tbl.check).toIO ctx { env }
  for m in ms do IO.println s!"  {m.describe}"
  for n in ns do IO.println s!"  note: {n.describe}"
  let alpha := ns.filter (fun n => match n with | .declBodyAlpha _ => true) |>.size
  let disagree := ms.filter (fun m => match m with | .alphaDisagreement _ => true | _ => false)
    |>.size
  IO.println s!"{if ms.isEmpty then "PASS" else "FAIL"} {name} \
    ({tbl.decls.length} decls, {tbl.inds.length} inds, {ms.size} mismatches, \
    {alpha} up to binder names, {disagree} alphaEqB/eqv disagreements)"
  return ms.isEmpty

/-- Check the blocks `Erasure.visitMutual` installs for one table's constants against the
table: `fixBlock?` names the block, and each member must be tabled with a λ-headed body. -/
def checkBlocks (env : Environment) (tbl : SourceTable) (name : Name) : IO Bool := do
  let mut blocks := 0
  let mut singletons := 0
  let mut bad : Array String := #[]
  for (n, _) in tbl.decls do
    if let some nms := fixBlock? env n then
      blocks := blocks + 1
      if nms.length == 1 then singletons := singletons + 1
      for m in nms do
        if (tbl.decl? m).isNone then
          bad := bad.push s!"{n}: block member {m} is not tabled"
        else if let some b := tbl.body? m then
          unless b.isLambda do
            bad := bad.push s!"{n}: block member {m} has a tabled body that is not λ-headed"
  for b in bad do IO.println s!"  {b}"
  IO.println s!"{if bad.isEmpty then "PASS" else "FAIL"} {name} \
    ({blocks} blocks, {singletons} singletons, {bad.size} failures)"
  return bad.isEmpty

/-- Run `Erasure.prepare_erasure` on `.const n []` and report whether it returns its subject. -/
def checkPrepared (env : Environment) (n : Name) : IO Bool := do
  let ctx : Core.Context := { fileName := "<reify>", fileMap := default, maxHeartbeats := 0 }
  let subject : Expr := .const n []
  try
    let ((pe, _), _) ←
      (Erasure.run (Erasure.prepare_erasure subject) reifyConfig).toIO ctx { env }
    let ok := pe == subject
    if ok then IO.println s!"PASS {n} (prepare_erasure is the identity)"
    else IO.println s!"FAIL {n}: prepare_erasure returns {pe}"
    return ok
  catch e =>
    IO.eprintln s!"FAIL {n}: {e}"
    return false

/-- Import `mod` and check the fix blocks its environment installs for each named table. -/
unsafe def blocksModuleUnsafe (mod : Name) (names : List Name) : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := mod }] {} (trustLevel := 1024) (loadExts := true)
  let mut failed := 0
  for name in names do
    match env.evalConstCheck SourceTable {} ``SourceTable name with
    | .error e => IO.eprintln s!"FAIL {name}: {e}"; failed := failed + 1
    | .ok tbl => unless ← checkBlocks env tbl name do failed := failed + 1
  return if failed == 0 then 0 else 1

/-- Import `mod` and check the fix blocks its environment installs for each named table. -/
@[implemented_by blocksModuleUnsafe]
opaque blocksModule (mod : Name) (names : List Name) : IO UInt32

/-- Import `mod` and check that `Erasure.prepare_erasure` is the identity at each name. -/
unsafe def preparedModuleUnsafe (mod : Name) (names : List Name) : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := mod }] {} (trustLevel := 1024) (loadExts := true)
  let mut failed := 0
  for name in names do
    unless ← checkPrepared env name do failed := failed + 1
  return if failed == 0 then 0 else 1

/-- Import `mod` and check that `Erasure.prepare_erasure` is the identity at each name. -/
@[implemented_by preparedModuleUnsafe]
opaque preparedModule (mod : Name) (names : List Name) : IO UInt32

/-- Import `mod` and check each named table against its environment. -/
unsafe def checkModuleUnsafe (mod : Name) (names : List Name) : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  -- `loadExts := true` is load-bearing: with the default the imported environment carries no
  -- environment-extension state, `Lean.Meta.getMatcherInfo?` answers `none` for every matcher,
  -- and `Erasure.prepare_erasure`'s `inlineMatchers` step silently does nothing — so the check
  -- would hold the table against a body prepared differently from the one `reify%` tabled.
  let env ← importModules #[{ module := mod }] {} (trustLevel := 1024) (loadExts := true)
  let mut failed := 0
  for name in names do
    match env.evalConstCheck SourceTable {} ``SourceTable name with
    | .error e => IO.eprintln s!"FAIL {name}: {e}"; failed := failed + 1
    | .ok tbl => unless ← checkTable env tbl name do failed := failed + 1
  return if failed == 0 then 0 else 1

/-- Import `mod` and check each named table against its environment. -/
@[implemented_by checkModuleUnsafe]
opaque checkModule (mod : Name) (names : List Name) : IO UInt32

/-- Entry point of the `reify` executable. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | "--check" :: mod :: names@(_ :: _) =>
    checkModule mod.toName (names.map String.toName)
  | "--blocks" :: mod :: names@(_ :: _) =>
    blocksModule mod.toName (names.map String.toName)
  | "--prepared" :: mod :: names@(_ :: _) =>
    preparedModule mod.toName (names.map String.toName)
  | [] | ["--help"] | ["-h"] => IO.println usage; return 0
  | _ => IO.eprintln usage; return 1
