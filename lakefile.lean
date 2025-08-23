import Lake
import Lean.Util.Diff
open System Lake DSL

package leanpy

@[default_target]
lean_lib Py

@[default_target]
lean_lib LeanPy

@[default_target]
lean_exe leanpy where
  root := `Main

@[test_driver]
script test do
  let testFile : FilePath := "tests" / "basic.lean"
  let eOutFile := testFile.withExtension "expected.out"
  let eOut ← (·.crlfToLf) <$> IO.FS.readFile eOutFile
  let out ← IO.Process.output {
    cmd := (← getLean).toString
    args := #[testFile.toString]
    env := ← getAugmentedEnv
  }
  let pOut := out.stderr ++ out.stdout |>.crlfToLf
  let pOutFile := testFile.withExtension "produced.out"
  IO.FS.writeFile pOutFile pOut
  if eOut = pOut then
    IO.eprintln s!"{testFile}: output matched"
    return 0
  else
    IO.eprintln s!"{testFile}: produced output did not match expected output"
    let eLns := eOut.split (· == '\n') |>.toArray
    let pLns := pOut.split (· == '\n') |>.toArray
    let diffs := Lean.Diff.diff eLns pLns
    IO.eprintln <| Lean.Diff.linesToString diffs
    return 1
