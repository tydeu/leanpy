import Lake
import Lean.Util.Diff
open System Lake DSL

package leanpy where
  reservoir := false

@[default_target]
lean_lib LeanPy

@[test_driver]
script test do
  let testFile : FilePath := "tests" / "basic.lean"
  let eOutFile := testFile.withExtension "expected.out"
  let eOut ← IO.FS.readFile eOutFile
  let out ← IO.Process.output {
    cmd := (← getLean).toString
    args := #[testFile.toString]
    env := ← getAugmentedEnv
  }
  let pOut := out.stderr ++ out.stdout
  let pOutFile := testFile.withExtension "produced.out"
  IO.FS.writeFile pOutFile pOut
  if out.exitCode != 0 then
    IO.eprintln s!"{testFile}: Lean exited with code {out.exitCode}"
    IO.eprintln pOut
    return 1
  let pOut := pOut.crlfToLf
  let eOut := eOut.crlfToLf
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
