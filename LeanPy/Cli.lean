/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
syntax Authors Mac Malone
-/
import LeanPy.Cli.EvalFile

open Lake

namespace LeanPy

def cli  (args : List String) : IO UInt32 := do
  let [file] := args
    | IO.eprintln "error: missing file name"
      return 1
  let messages ← evalPyFile file
  messages.unreported.forM fun msg => do
    IO.eprint (← mkMessageString msg)
  return if messages.hasErrors then 1 else 0
