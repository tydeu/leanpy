/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Elab.Command
import LeanPy.Data.None.Object
import LeanPy.Data.Tuple.Object

namespace LeanPy

open Grammar Lean

def evalPySeq (xs : Array Syntax) : PyEvalM Object :=
  xs.foldlM (init := none) fun _ stx => evalPy stx

@[py_eval pyBlock]
def evalBlock : PyEval := fun stx => do
  match stx with
  | `(pyBlock| $[\]* $stmts:pySimpleStmt;*) =>
    evalPySeq stmts.getElems
  | `(pyBlock| $stmts:stmt*) =>
    evalPySeq stmts
  | _ =>
    throwError "ill-formed block"

@[py_eval stmt]
def evalStmt : PyEval := fun stx => do
  match stx with
  | `(stmt| $stmts:pySimpleStmt;*) =>
    evalPySeq stmts.getElems
  | `(stmt| $stmt:pyCompoundStmt) =>
    evalPy stmt
  | _ =>
    throwError "ill-formed statement"

@[py_eval starExpr]
def evalStarExpr : PyEval := fun stx =>
  match stx with
  | `(starExpr| *$_) =>
    throwError "cannot use starred expression here"
  | `(starExpr| $x:pyExpr) => evalPy x
  | _ => throwError "ill-formed star expression"

@[py_eval starExprs]
def evalStarExprs : PyEval := fun stx => do
  let `(starExprs| $xs,*) := stx
    | throwError m!"ill-formed star expressions"
  let vs ← xs.getElems.foldlM (init := #[]) fun vs stx =>
    match stx with
    | `(starExpr| *$x) =>
      throwError "iterable unpacking not yet implemented"
    | `(starExpr| $x:pyExpr) =>
      vs.push <$> evalPy x
    | _ => throwError "ill-formed star expression"
  if h : vs.size = 1 then
    return vs[0]
  else
    mkTupleObject vs

@[py_eval namedExpr]
def evalNamedExpr : PyEval := fun stx => do
  match stx with
  | `(namedExpr| $x:assignmentExpr) =>
    evalPy x -- TODO: perform assignment
  | `(namedExpr| $x:pyExpr) =>
    evalPy x
  | _ =>
    throwError "ill-formed named expression"

@[py_eval groupExpr]
def evalGroupExpr : PyEval := fun stx => do
  let `(groupExpr| ($x)) := stx
    | throwError "ill-formed group expression"
  match x with
  | `(yieldExpr| $x:yieldExpr) =>
    evalPy x
  | `(namedExpr| $x:namedExpr) =>
    evalPy x
  | _ =>
    throwError "ill-formed group expression"
