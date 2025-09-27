/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Elab.Command

namespace LeanPy

open Grammar Lean

/- ## Statement & Expression Combinators -/

def evalPySeq (xs : Array Syntax) : PyEvalM Object :=
  xs.foldlM (init := none) fun _ stx => evalPy stx

@[py_eval block]
def evalBlock : PyEval := fun stx => do
  match stx with
  | `(block| $[\]* $stmts:pySimpleStmt;*) =>
    evalPySeq stmts.getElems
  | `(block| $stmts:stmt*) =>
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
    throwError "tuples not yet implemented"

@[py_eval namedExpr]
def evalNamedExpr : PyEval := fun stx => do
  match stx with
  | `(namedExpr| $x:assignmentExpr) =>
    evalPy x
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

/- ## Basic Statements & Expressions -/

@[py_eval returnStmt]
def evalReturnStmt : PyEval := fun stx => do
  let `(returnStmt| return%$tk $_) := stx
    | throwError "ill-formed return statement"
  throwErrorAt tk "'return' outside function"

@[py_eval yieldExpr]
def evalYieldExpr : PyEval := fun stx => do
  let `(yieldExpr| yield%$tk $_) := stx
    | throwError "ill-formed yield expression"
  throwErrorAt tk "'yield' outside function"

@[py_eval yieldStmt]
def evalYieldStmt : PyEval := fun stx => do
  let `(yieldStmt| yield%$tk $_) := stx
    | throwError "ill-formed yield statement"
  throwErrorAt tk "'yield' outside function"

@[py_eval passStmt]
def evalPassStmt : PyEval := fun _ => do
  return none

@[py_eval noneExpr]
def evalNoneExpr : PyEval := fun _ => do
  return none

@[py_eval numExpr]
def evalNumExpr : PyEval := fun stx => do
  let `(pyExpr| $n:num) := stx
    | throwError "ill-formed numeric expression"
  mkIntObject n.getNat

@[py_eval strings]
def evalStrings : PyEval := fun stx => do
  let `(pyExpr| $ss:str*) := stx
    | throwError "ill-formed strings"
  let s := ss.foldl (init := "") fun s sStx =>
    s ++ sStx.getString
  mkStringObject s

@[py_eval isExpr]
def evalIsExpr : PyEval := fun stx => do
  let `(pyExpr| $a is $b) := stx
    | throwError "ill-formed 'is' expression"
  let a ← evalPy a
  let b ← evalPy b
  return a.id == b.id

@[py_eval isNotExpr]
def evalIsNotExpr : PyEval := fun stx => do
  let `(pyExpr| $a is not $b) := stx
    | throwError "ill-formed 'is not' expression"
  let a ← evalPy a
  let b ← evalPy b
  return a.id != b.id
