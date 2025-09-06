/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Elab.Command

namespace LeanPy

open Grammar Lean

-- TODO: name binding through `global` / `nonlocal`

@[inline] def getLocals [Functor m] [MonadReaderOf PyContext m] : m VarDict :=
  (·.locals) <$> read

def VarDict.get? (var : AttrName) (self : VarDict) : BaseIO (Option Object) := do
  return (← self.get)[var]?

def VarDict.set (var : AttrName) (val : Object) (self : VarDict) : BaseIO Unit := do
  self.modify (·.insert var val)

@[py_eval identExpr]
def evalIdentExpr : PyEval := fun stx => do
  let `(identExpr| $id:ident) := stx
    | throwError "ill-formed name"
  match h:id.getId with
  | .str .anonymous _ =>
    let var := AttrName.mk id.getId (by simp [h])
    let some val ← (← getLocals).get? var
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
    match h:id.getId with
    | .str .anonymous _ =>
      let val ← evalPy rhs
      let var := AttrName.mk id.getId (by simp [h])
      (← getLocals).set var val
      return val
    | _ =>
      throwError "non-atomic names are not yet supported"
  | _ =>
    throwError "complex assignment statements are not yet supported"

@[py_eval assignmentExpr]
def evalAssignmentExpr : PyEval := fun stx => do
  match stx with
  | `(assignmentExpr| $id:ident := $x) =>
    match h:id.getId with
    | .str .anonymous _ =>
      let val ← evalPy x
      let var := AttrName.mk id.getId (by simp [h])
      (← getLocals).set var val
      return val
    | _ =>
      throwError "non-atomic names are not yet supported"
  | _ =>
    throwError "complex assignment statements are not yet supported"
