/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Elab.Command

namespace LeanPy

open Grammar Lean

/-! ## Literals -/

@[py_eval noneExpr]
def evalNoneExpr : PyEval := fun _ => do
  return none

@[py_eval falseExpr]
def evalFalseExpr : PyEval := fun _ =>
  return false

@[py_eval trueExpr]
def evalTrueExpr : PyEval := fun _ =>
  return true

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

/-! ## Basic Operations -/

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

@[py_eval eq]
def evalEq : PyEval := fun stx => do
  let `(pyExpr| $a == $b) := stx
    | throwError "ill-formed '==' expression"
  let a ← evalPy a
  let b ← evalPy b
  a.eqOpM b

@[py_eval ne]
def evalNe : PyEval := fun stx => do
  let `(pyExpr| $a != $b) := stx
    | throwError "ill-formed '!=' expression"
  let a ← evalPy a
  let b ← evalPy b
  a.neOpM b
