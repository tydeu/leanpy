/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Grammar
import LeanPy.Data.Object.Basic
import LeanPy.Util.Elab

open Lean Elab Command Parser

namespace LeanPy

/-! ## Monad -/

abbrev PyElabM := ReaderT PyContext CoreM
abbrev PyEvalM := PyElabM
abbrev PyEval := Syntax → PyEvalM Object

def PyElabM.liftPyM (x : PyM α) : PyElabM α := fun ctx => do
  match (← x.run ctx |>.toBaseIO) with
  | .ok a => return a
  | .error e => -- TODO: Traceback
    let msg ← id do
      match (← e.toStr.run ctx |>.toBaseIO) with
      | .ok msg =>
        if msg.isEmpty then
          return e.ty.name
        else
          return s!"{e.ty.name}: {msg}"
      | .error _ =>
        return s!"{e.ty.name}: <exception str() failed>"
    throwError msg

instance : MonadLift PyM PyElabM := ⟨PyElabM.liftPyM⟩

/-! ## Elaborator -/

initialize pyEvalAttribute : KeyedDeclsAttribute PyEval ←
  unsafe mkElabAttribute _ `builtin_py_eval `py_eval `LeanPy.Grammar ``PyEval "py"

def evalPy (stx : Syntax) : PyEvalM Object :=
  elabSyntaxWith stx fun stx => do
    let k := stx.getKind
    let elabFns := pyEvalAttribute.getEntries (← getEnv) k
    if let some obj ← elabSyntaxUsing? stx elabFns then
      return obj
    else
      withInfoTreeContext (mkInfoTree := mkCommandElabInfoTree `no_elab stx) do
        throwError m!"no python evaluator implemented for `{mkConst k}`"

def runPy (stx : Syntax) : PyElabM Unit :=
  withLogging <| discard <| evalPy stx

/-! ## Command -/

open Grammar

scoped syntax (name := evalPyCmd) withPosition("#eval_py" block) : command

@[command_elab evalPyCmd]
def elabEvalPyCmd : CommandElab := fun stx => do
  let `(#eval_py%$tk $b) := stx
    | throwError "ill-formed `#eval_py` syntax"
  let go : PyElabM Unit := do
    withRef tk do
    let v ← evalPy b
    unless v.isNone do
      logInfo (← v.repr)
  let globals ← IO.mkRef {}
  let ctx : PyContext := {globals}
  liftCoreM <| ReaderT.run (r := ctx) go
