/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Elab.Command

namespace LeanPy

open Grammar Lean

/- ## Basic Statements  -/

@[py_eval passStmt]
def evalPassStmt : PyEval := fun _ => do
  return none

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

/-! ## Conditionals -/

@[py_eval condExpr]
def evalCondExpr : PyEval := fun stx => do
  let `(pyExpr| $t if $c else $e) := stx
    | throwError "ill-formed condition expression"
  let c ← evalPy c
  if (← c.toBoolM) then
    evalPy t
  else
    evalPy e

@[py_eval ifStmt]
def evalCondStmt : PyEval := fun stx => do
  let `(ifStmt| if $c:namedExpr: $t:block $elifs* $[else: $e?:block]?) := stx
    | throwError "ill-formed if statement"
  let c ← evalPy c
  if (← c.toBoolM) then
    evalPy t
  else
    let r? ← elifs.findSomeM? fun stx => withRef stx do
      let `(elifStmt| elif $c:namedExpr: $t:block) := stx
        | throwError "ill-formed elif statment"
      let c ← evalPy c
      if (← c.toBoolM) then
        some <$> evalPy t
      else
        return none
    if let some r := r? then
      return r
    else if let some e := e? then
      evalPy e
    else
      return none
