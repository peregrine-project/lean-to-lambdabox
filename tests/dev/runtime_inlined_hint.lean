import Lean

/-!
Inlining attributes of the benchmark runtime (register entry S-2, claim C3). The Zarith calls in
`benchmarks/via_malfunction/nat-inline.ml` and `int-inline.ml` carry `[@inlined hint]`, which OCaml
compiles without warning 55 when Zarith provides no inlining information; a bare `[@inlined]` there
makes this test fail. Unlike the other tests, this one reads repository files instead of calling
`#erase`; it writes the attribute counts to `inlined_attributes.txt`.
-/

open Lean Elab Command in
run_cmd do
  let file : System.FilePath := ← getFileName
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "cannot locate the repository root from {file}"
  let mut report := ""
  for name in ["nat-inline.ml", "int-inline.ml"] do
    let src ← IO.FS.readFile (root / "benchmarks" / "via_malfunction" / name)
    let hint := (src.splitOn "[@inlined hint]").length - 1
    let bare := (src.splitOn "[@inlined]").length - 1
    if bare > 0 then
      throwError "{name}: {bare} bare [@inlined] attribute(s)"
    report := report ++ s!"{name}: [@inlined hint] {hint}, [@inlined] {bare}\n"
  IO.FS.writeFile "inlined_attributes.txt" report
