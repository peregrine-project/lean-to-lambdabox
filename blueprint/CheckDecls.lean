import Lean
/-!
Blueprint declaration checker (replacement for `lake exe checkdecls`).

`leanblueprint web` writes `blueprint/lean_decls`, one fully-qualified Lean name per
line, collected from every `\lean{...}` in the blueprint. This script imports the
`LeanToLambdaBox` library root and reports every listed name the environment does
not contain.

Run from the repository root, after `lake build`:

    lake env lean --run blueprint/CheckDecls.lean blueprint/lean_decls

The stock `checkdecls` package cannot be used here: it imports every root of every
`lean_lib` of the workspace, and the `VerifyBench.Src.*` frozen benchmark sources are
not co-importable (`Sieve` and `Quicksort` both declare a root-level `divmod`).
-/
open Lean
/-- The fully qualified names a standalone script declares, read textually: `namespace`/`end`
nesting plus `theorem`/`lemma`/`def`/`abbrev`/`structure`/`inductive` headers. Standalone scripts
(such as `test/Vacuity.lean`) are not modules of the library, so their declarations cannot be
looked up in the imported environment. -/
def scriptNames (path : System.FilePath) : IO (Array String) := do
  let mut ns : Array String := #[]
  let mut out : Array String := #[]
  for line in ← IO.FS.lines path do
    let ws := (line.trimAscii.toString.splitOn " ").filter (· ≠ "")
    match ws with
    | "namespace" :: n :: _ => ns := ns.push n
    | "end" :: _ :: _ => if ns.size > 0 then ns := ns.pop
    | _ =>
      let ws' := if ws.head? == some "private" || ws.head? == some "protected" then ws.drop 1 else ws
      match ws' with
      | kw :: n :: _ =>
        if kw ∈ ["theorem", "lemma", "def", "abbrev", "structure", "inductive"] then
          let short := ((n.splitOn ":").head!.takeWhile (fun c => c != '(' && c != '{')).toString
          out := out.push (String.intercalate "." (ns.toList ++ [short]))
      | _ => pure ()
  return out

unsafe def main (args : List String) : IO UInt32 := do
  let file :: scripts := args
    | IO.eprintln "usage: lake env lean --run blueprint/CheckDecls.lean <lean_decls> [script.lean ...]"; return 2
  unless ← System.FilePath.pathExists file do
    IO.eprintln s!"Could not find declaration list {file}."; return 2
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := `LeanToLambdaBox }] {}
  let mut extra : Array String := #[]
  for sc in scripts do
    extra := extra ++ (← scriptNames sc)
  let mut checked := 0
  let mut missing := 0
  for line in ← IO.FS.lines file do
    let s := line.trimAscii.toString
    if s.isEmpty then continue
    checked := checked + 1
    unless env.contains s.toName || extra.contains s do
      IO.println s!"{s} is missing."
      missing := missing + 1
  IO.println s!"checked {checked} declarations, {missing} missing"
  return if missing == 0 then 0 else 1
