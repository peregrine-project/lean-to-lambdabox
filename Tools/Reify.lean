import LeanToLambdaBox.Witness.SourceTable

/-!
# `reify` — table drift detection

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

The negative half of the self-test is
`LeanToLambdaBox.Witness.SelfTest.staleTable`, a deliberately wrong table the tool must reject.
-/

open Lean LeanToLambdaBox.Witness

/-- What this tool does and how to call it. -/
def usage : String :=
  "reify — check a reified SourceTable against the live environment\n\n\
   usage:\n  \
     reify --check MOD NAME…   import MOD, compare each named table against MOD's environment\n\n\
   NAME is the fully qualified name of a `SourceTable` constant in MOD.\n\
   Exit 0 if every table matches the environment, 1 otherwise."

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
  | [] | ["--help"] | ["-h"] => IO.println usage; return 0
  | _ => IO.eprintln usage; return 1
