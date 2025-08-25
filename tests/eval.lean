import LeanPy

open Lean Elab Command
open LeanPy Grammar

elab tk:"#eval_py" stmts:stmt* : command => liftCoreM <| withRef tk do
  let v ← stmts.foldlM (init := LeanPy.none) fun _ stx =>
    evalPy stx
  logInfo v.ty.name

@[py_eval stmt]
def evalStmt : PyEval := fun stx => do
  match stx with
  | `(stmt| $stmts:pySimpleStmt;*) =>
    stmts.getElems.foldlM (init := none) fun _ stx =>
      evalPy stx
  | `(stmt| $stmt:pyCompoundStmt) =>
    evalPy stmt
  | _ =>
    throwError "ill-formed Python statement"

@[py_eval passStmt]
def evalPassStmt : PyEval := fun _ =>
  return none

@[py_eval noneExpr]
def evalNoneExpr : PyEval := fun _ =>
  return none

@[py_eval starExpr]
def evalStarExpr : PyEval := fun stx =>
  match stx with
  | `(starExpr| *$_) =>
    throwError m!"cannot use starred expression here"
  | `(starExpr| $x:pyExpr) => evalPy x
  | _ => throwError m!"ill-formed Python star expression"

@[py_eval starExprs]
def evalStarExprs : PyEval := fun stx => do
  let `(starExprs| $xs,*) := stx
    | throwError m!"ill-formed Python star expressions"
  let vs ← xs.getElems.foldlM (init := #[]) fun vs stx =>
    match stx with
    | `(starExpr| *$x) =>
      throwError "iterable unpacking not yet implemented"
    | `(starExpr| $x:pyExpr) =>
      vs.push <$> evalPy x
    | _ => throwError m!"ill-formed Python star expression"
  if h : vs.size = 1 then
    return vs[0]
  else
    throwError "tuples not yet implemented"

/-- info: NoneType -/
#guard_msgs in
#eval_py
  pass
  None
