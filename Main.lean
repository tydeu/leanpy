/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
syntax Authors Mac Malone
-/
import LeanPy
import LeanPy.Cli
import LeanPy.Cli.BuiltinAttrs

-- Register builtin evaluators for the CLI
open LeanPy.Internal in add_builtin_py_eval%

def main (args : List String) : IO UInt32 :=
  LeanPy.cli args
