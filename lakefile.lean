import Lake
open Lake DSL

package «leanpy»

@[default_target]
lean_lib «Py»

@[default_target]
lean_lib «LeanPy»

@[default_target]
lean_exe «leanpy» where
  root := `Main

script test do
  let testFile : FilePath := "tests" / "basic.lean"
  let eOutFile := testFile.withExtension "expected.out"
  let eOut ← IO.FS.readFile eOutFile
  let out ← IO.Process.output {
    cmd := (← getLean).toString, args := #[testFile.toString], env := ← getAugmentedEnv
  }
  let pOut := out.stderr ++ out.stdout
  let pOutFile := testFile.withExtension "produced.out"
  IO.FS.writeFile pOutFile pOut
  if Lake.crlf2lf eOut = Lake.crlf2lf pOut then
    IO.eprintln s!"{testFile}: output matched"
    return 0
  else
    IO.eprintln s!"{testFile}: produced output did not match expected output"
    let args := #[eOutFile.toString, pOutFile.toString, "--strip-trailing-cr"]
    IO.Process.spawn {cmd := "diff", args} >>= (discard <| ·.wait)
    return 1
