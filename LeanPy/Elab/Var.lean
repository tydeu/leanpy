/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Elab.Command

namespace LeanPy

open Grammar Lean

-- TODO: name binding through `global` / `nonlocal`

@[inline] def getLocals [Functor m] [MonadReaderOf PyContext m] : m DictRef :=
  (·.locals) <$> read

@[py_eval identExpr]
def evalIdentExpr : PyEval := fun stx => do
  let `(identExpr| $id:ident) := stx
    | throwError "ill-formed name"
  match id.getId with
  | .str .anonymous var =>
    let some val ← (← getLocals).getByStr? var
      | throwError "name '{var}' is not defined" -- NameError
    return val
  | _ =>
    throwError "non-atomic names are not yet supported"

@[py_eval annotatedRhs]
def evalAnnotatedRhs : PyEval := fun stx => do
  match stx with
  | `(annotatedRhs| $x:yieldExpr) =>
    evalPy x
  | `(annotatedRhs| $x:starExprs) =>
    evalPy x
  | _ =>
    throwError "ill-formed right-hand side of assignment"

@[py_eval assignment]
def evalAssignment : PyEval := fun stx => do
  match stx with
  | `(assignment| $id:ident = $rhs:annotatedRhs) =>
    match id.getId with
    | .str .anonymous var =>
      let val ← evalPy rhs
      (← getLocals).setByStr var val
      return val
    | _ =>
      throwError "non-atomic names are not yet supported"
  | _ =>
    throwError "complex assignment statements are not yet supported"

@[py_eval assignmentExpr]
def evalAssignmentExpr : PyEval := fun stx => do
  match stx with
  | `(assignmentExpr| $id:ident := $x) =>
    match id.getId with
    | .str .anonymous var =>
      let val ← evalPy x
      (← getLocals).setByStr var val
      return val
    | _ =>
      throwError "non-atomic names are not yet supported"
  | _ =>
    throwError "complex assignment statements are not yet supported"
