import LeanToLambdaBox

/-!
The benchmark Makefile's rule for `$(build)/%.cmi` compiles the `.mli` that `#erase` writes
(register entry S-4). For an `Array` result that `.mli` names `LeanArray`, so the rule must build
`$(build)/LeanArray.cmi` first and pass `-I $(build)`. The test needs `make`, not OCaml: it erases
`rArr` into a fresh build directory, asks `make -n` for the commands that build `rArr.cmi` there
(the compiler command set to `ocamlopt`), and writes them to `cmi_commands.txt`, with the build
directory written `$(build)`.
-/

run_cmd IO.FS.createDirAll "build"

def rArr (n : Nat) : Array Nat := Array.mk [n, n + 1]
#erase rArr to "build/rArr.ast" mli "build/rArr.mli"

open Lean Elab Command in
run_cmd do
  let file : System.FilePath := ← getFileName
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "cannot locate the repository root from {file}"
  let build := (← IO.currentDir) / "build"
  let out ← IO.Process.output {
    cmd := "make"
    args := #["-n", "--no-print-directory", "-C", (root / "benchmarks" / "via_malfunction").toString,
      s!"build={build}", "OCAMLOPT=ocamlopt", "-o", (build / "rArr.mli").toString,
      (build / "rArr.cmi").toString]
    env := #[("MAKEFLAGS", none), ("MFLAGS", none), ("MAKELEVEL", none)]
  }
  unless out.exitCode == 0 do
    throwError "make exited with {out.exitCode}: {out.stderr}"
  IO.FS.removeDirAll build
  let cmds := (out.stdout.replace build.toString "$(build)").splitOn "\n" |>.filter (· ≠ "")
  let some i := cmds.findIdx? (· == "ocamlopt -c $(build)/LeanArray.mli")
    | throwError "LeanArray.cmi is not built before rArr.cmi:\n{out.stdout}"
  let some j := cmds.findIdx? (· == "ocamlopt -I $(build) -c $(build)/rArr.mli")
    | throwError "rArr.mli is not compiled with -I $(build):\n{out.stdout}"
  unless i < j do
    throwError "LeanArray.cmi is built after rArr.cmi:\n{out.stdout}"
  IO.FS.writeFile "cmi_commands.txt" (String.intercalate "\n" cmds ++ "\n")
