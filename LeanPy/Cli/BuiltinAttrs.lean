/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
syntax Authors Mac Malone
-/
import LeanPy.Elab.Command

open Lean

namespace LeanPy.Internal

/-! ## `@[builtin_py_eval]` Attributes -/

/-- Adds `@[builtin_py_val]` to all declarations with `@[py_eval]` -/
scoped elab "add_builtin_py_eval%" : command => do
  let s := pyEvalAttribute.ext.getState (← getEnv)
  Elab.Command.liftCoreM <| s.table.forM fun k es => es.forM fun e =>
    let val := mkApp5 (mkConst ``KeyedDeclsAttribute.addBuiltin)
      (mkConst ``PyEval) (mkConst ``pyEvalAttribute)
      (toExpr k) (toExpr e.declName) (mkConst e.declName)
    declareBuiltin e.declName val
