/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Object
import LeanPy.Grammar
import LeanPy.ElabUtil

open Lean Elab Command Parser

namespace LeanPy

abbrev PyElabM := CoreM
abbrev PyEvalM := PyElabM
abbrev PyEval := Syntax → PyEvalM Object

initialize pyEvalAttribute : KeyedDeclsAttribute PyEval ←
  unsafe mkElabAttribute _ `builtin_py_eval `py_eval `LeanPy.Grammar ``PyEval "py"

def evalPy (stx : Syntax) : PyEvalM Object :=
  elabSyntaxWith stx fun stx => do
    let k := stx.getKind
    let elabFns := pyEvalAttribute.getEntries (← getEnv) k
    if let some obj ← elabSyntaxUsing? stx elabFns then
      return obj
    else
      withInfoTreeContext (mkInfoTree := mkCommandElabInfoTree `no_elab stx) do
        throwError m!"no python evaluator implemented for `{mkConst k}`"

def runPy (stx : Syntax) : PyElabM Unit :=
  withLogging <| discard <| evalPy stx
