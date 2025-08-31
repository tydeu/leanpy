import Lake
import Lean.Util.Diff
open System Lake DSL

package leanpy where
  reservoir := false

@[default_target]
lean_lib LeanPy

def testLeanFile (testFile : FilePath) : ScriptM UInt32 := do
  let child ← IO.Process.spawn {
    cmd := (← getLean).toString
    args := #[testFile.toString]
    env := ← getAugmentedEnv
  }
  let rc ← child.wait
  if rc == 0 then
    IO.eprintln s!"{testFile}: completed successfully"
    return 0
  else
    IO.eprintln s!"{testFile}: Lean exited with code {rc}"
    return 1

def testLeanOutput (testFile : FilePath) : ScriptM UInt32 := do
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

@[test_driver]
script test do
  runBuild (← LeanPy.get).leanArts.fetch
  if (← testLeanOutput ("tests" / "syntax.lean")) != 0 then
    return 1
  if (← testLeanFile ("tests" / "eval.lean")) != 0 then
    return 1
  return 0
