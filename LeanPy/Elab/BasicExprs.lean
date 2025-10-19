/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Elab.Command
import LeanPy.Data.None.Object
import LeanPy.Data.Bool.Object
import LeanPy.Data.Tuple.Object
import LeanPy.Data.Dict.Object
import LeanPy.Data.Str.Object

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
  if s.isEmpty then
    return StrObject.empty
  else
    mkStrObject s

@[py_eval tuple]
def evalTuple : PyEval := fun stx => do
  let `(pyExpr| ($[$body?]?)) := stx
    | throwError "ill-formed tuple"
  let some body := body?
    | return TupleObject.empty
  let `(tupleBody| $init , $items,*) := body
    | throwError "ill-formed tuple"
  let init ← go #[] init
  let data ← items.getElems.foldlM go init
  mkTupleObject data
where go os stx := do
  match stx with
  | `(starNamedExpr| * $_) =>
    throwError "iterable unpacking not yet implemented"
  | `(starNamedExpr| $x:namedExpr) =>
    os.push <$> evalPy x
  | _ =>
    throwError "ill-formed tuple item"

@[py_eval dict]
def evalDict : PyEval := fun stx => do
  let `(pyExpr| { $kvs:doubleStarredKvpair,* }) := stx
    | throwError "ill-formed dict"
  let d : DictRef.Data := ∅
  let d ← kvs.getElems.foldlM (init := d) fun d stx => do
    match stx with
    | `(doubleStarredKvpair| ** $_) =>
      throwError "iterable unpacking not yet implemented"
    | `(doubleStarredKvpair| $k:pyExpr : $v:pyExpr) =>
      let k ← evalPy k
      let v ← evalPy v
      d.set k v
    | _ =>
      throwError "ill-formed dict key-value pairs"
  mkDictObject d

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
  a.beqM b

@[py_eval ne]
def evalNe : PyEval := fun stx => do
  let `(pyExpr| $a != $b) := stx
    | throwError "ill-formed '!=' expression"
  let a ← evalPy a
  let b ← evalPy b
  a.bneM b
