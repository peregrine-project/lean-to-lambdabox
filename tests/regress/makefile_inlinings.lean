import LeanToLambdaBox

/-!
With `INLINING=1`, the benchmark Makefile's rule for `$(build)/%.mlf` runs peregrine with
`--attributes=$(build)/%.ast.inlinings` (register entry S-6), so that file is a prerequisite of the
rule: when it is missing, make regenerates it with `lake lean` before running peregrine. The test
needs `make`, not peregrine or OCaml. It erases `rInl` into a fresh build directory and asks
`make -n` for the commands that build `rInl.mlf` there (peregrine set to `peregrine`, the generated
`rInl.lean` taken as present and old): with every output present, with `rInl.ast.inlinings`
deleted, and with it deleted under `INLINING=0`, where peregrine does not read it. It writes the
three command lists to `mlf_commands.txt`, with the build directory written `$(build)`. Lines
starting with `rm ` are dropped: GNU make 4.3, which lacks `.NOTINTERMEDIATE`, ends the second run
by removing the regenerated file as an intermediate one (R-28), and make 4.4 does not.
-/

run_cmd IO.FS.createDirAll "build"

def rInl (n : Nat) : Nat := n + 1
#erase rInl to "build/rInl.ast" mli "build/rInl.mli"

open Lean Elab Command in
run_cmd do
  let file : System.FilePath := ← getFileName
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "cannot locate the repository root from {file}"
  let build := (← IO.currentDir) / "build"
  let dryRun (inlining : String) : CommandElabM (List String) := do
    let out ← IO.Process.output {
      cmd := "make"
      args := #["-n", "--no-print-directory",
        "-C", (root / "benchmarks" / "via_malfunction").toString, s!"build={build}",
        "PEREGRINE=peregrine", s!"INLINING={inlining}",
        "-o", (build / "rInl.lean").toString, (build / "rInl.mlf").toString]
      env := #[("MAKEFLAGS", none), ("MFLAGS", none), ("MAKELEVEL", none)]
    }
    unless out.exitCode == 0 do
      throwError "make exited with {out.exitCode}: {out.stderr}"
    return (out.stdout.replace build.toString "$(build)").splitOn "\n"
      |>.filter (fun l => l ≠ "" && !l.startsWith "rm ")
  let erase := "lake lean $(build)/rInl.lean"
  let compile := "peregrine compile $(build)/rInl.ast unbox.config"
  let withAttrs := compile ++ " --attributes=$(build)/rInl.ast.inlinings > /dev/null"
  let present ← dryRun "1"
  unless present == [withAttrs] do
    throwError "all outputs present: expected only the peregrine command, got:\n{present}"
  IO.FS.removeFile (build / "rInl.ast.inlinings")
  let missing ← dryRun "1"
  unless missing == [erase, withAttrs] do
    throwError "rInl.ast.inlinings missing: expected the lake lean command before the peregrine \
      command, got:\n{missing}"
  let missing0 ← dryRun "0"
  unless missing0 == [compile ++ " > /dev/null"] do
    throwError "rInl.ast.inlinings missing, INLINING=0: expected only the peregrine command, \
      got:\n{missing0}"
  IO.FS.removeDirAll build
  IO.FS.writeFile "mlf_commands.txt" <| String.intercalate "\n" <|
    ["# all outputs present, INLINING=1"] ++ present ++
    ["# rInl.ast.inlinings missing, INLINING=1"] ++ missing ++
    ["# rInl.ast.inlinings missing, INLINING=0"] ++ missing0 ++ [""]
