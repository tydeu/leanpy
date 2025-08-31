import LeanPy

open Lean Elab Command
open LeanPy Grammar

syntax (name := evalPyCmd) withPosition("#eval_py" block) : command

@[command_elab evalPyCmd]
def elabEvalPyCmd : CommandElab := fun stx => do
  let `(#eval_py%$tk $b) := stx
    | throwError "ill-formed `#eval_py` syntax"
  liftCoreM <| withRef tk do
  let v ← evalPy b
  unless v.isNone do
    logInfo (← v.repr)

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

@[py_eval returnStmt]
def evalReturnStmt : PyEval := fun stx => do
  let `(returnStmt| return%$tk $_) := stx
    | throwError "ill-formed return statement"
  throwErrorAt tk "'return' outside function"

/-- error: 'return' outside function -/
#guard_msgs in #eval_py return None

@[py_eval yieldExpr]
def evalYieldExpr : PyEval := fun stx => do
  let `(yieldExpr| yield%$tk $_) := stx
    | throwError "ill-formed yield expression"
  throwErrorAt tk "'yield' outside function"

/-- error: 'yield' outside function -/
#guard_msgs in #eval_py (yield None)

@[py_eval yieldStmt]
def evalYieldStmt : PyEval := fun stx => do
  let `(yieldStmt| yield%$tk $_) := stx
    | throwError "ill-formed yield statement"
  throwErrorAt tk "'yield' outside function"

/-- error: 'yield' outside function -/
#guard_msgs in #eval_py yield None

@[py_eval passStmt]
def evalPassStmt : PyEval := fun _ => do
  return none

#guard_msgs in #eval_py pass

@[py_eval noneExpr]
def evalNoneExpr : PyEval := fun _ => do
  return none

#guard_msgs in #eval_py None
#guard_msgs in #eval_py (None)

@[py_eval falseExpr]
def evalFalseExpr : PyEval := fun _ =>
  return false

/-- info: False -/
#guard_msgs in #eval_py False

@[py_eval trueExpr]
def evalTrueExpr : PyEval := fun _ =>
  return true

/-- info: True -/
#guard_msgs in #eval_py True

#eval_py
  pass
  None

@[py_eval condExpr]
def evalCondExpr : PyEval := fun stx => do
  let `(pyExpr| $t if $c else $e) := stx
    | throwError "ill-formed condition expression"
  let c ← evalPy c
  if (← c.toBool) then
    evalPy t
  else
    evalPy e

/-- info: True -/
#guard_msgs in #eval_py True if True else False

/-- info: False -/
#guard_msgs in #eval_py True if False else False

@[py_eval ifStmt]
def evalCondStmt : PyEval := fun stx => do
  let `(ifStmt| if $c:namedExpr: $t:block $elifs* $[else: $e?:block]?) := stx
    | throwError "ill-formed if statement"
  let c ← evalPy c
  if (← c.toBool) then
    evalPy t
  else
    let r? ← elifs.findSomeM? fun stx => withRef stx do
      let `(elifStmt| elif $c:namedExpr: $t:block) := stx
        | throwError "ill-formed elif statment"
      let c ← evalPy c
      if (← c.toBool) then
        some <$> evalPy t
      else
        return none
    if let some r := r? then
      return r
    else if let some e := e? then
      evalPy e
    else
      return none

#guard_msgs in
#eval_py if False: False

/-- info: True -/
#guard_msgs in
#eval_py if True: True

/-- info: True -/
#guard_msgs in
#eval_py
  if False:
    False
  else:
    True

/-- info: True -/
#guard_msgs in
#eval_py
  if False:
    False
  elif True:
    True
  else:
    False
