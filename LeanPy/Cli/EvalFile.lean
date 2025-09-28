/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
syntax Authors Mac Malone
-/
import LeanPy.Elab.Combinators
import LeanPy.ParserCategories
import Lake.Util.Message

open Lean Lake Parser

namespace LeanPy

/-! ## Python File Syntax -/

open Grammar in
syntax file := withPosition(stmt*)
open Internal in compile_parser file

-- force Lean to allow the `builtin_py_eval file` below
run_cmd modifyEnv (addSyntaxNodeKind · `LeanPy.file)

@[builtin_py_eval file]
def evalFile : PyEval := fun stx => do
  let `(file| $stmts*) := stx
    | throwError "ill-formed file syntax"
  evalPySeq stmts

/-! ## Python Evaluator -/

def mkSimpleMessage
  (fileName : String) (data : MessageData) (severity := MessageSeverity.error)
: Message where
  fileName := fileName
  pos := ⟨1, 0⟩
  endPos := none
  severity := severity
  data := data

def evalPyInput
  (ictx : InputContext) (messages : MessageLog := {})
: BaseIO MessageLog := do
  let env ←
    match (← mkEmptyEnvironment.toBaseIO) with
    | .ok env => pure env
    | .error e => return messages.add <| mkSimpleMessage ictx.fileName <|
      m!"failed to initialize Python environment: {e}"
  let env := parserExtension.modifyState env fun s =>
    {s with categories := LeanPy.parserCategories}
  let s := file.parser.fn.run ictx
    { env, options := {} } LeanPy.tokenTable (mkParserState ictx.input)
  if let some errorMsg := s.errorMsg then
    return messages.add <| mkParserErrorMessage ictx s errorMsg
  else if ictx.input.atEnd s.pos then
    let stx := s.stxStack.back
    let globals ← IO.mkRef {}
    let pyCtx : PyContext := {globals}
    let ctx := {fileName := ictx.fileName, fileMap := ictx.fileMap}
    let s := {env, messages}
    match (← evalPy stx |>.run pyCtx |>.run ctx s |>.toBaseIO) with
    | .ok (_, s) => return s.messages
    | .error e =>
      return messages.add <| mkExceptionMessage ictx e
  else
    return messages.add <| mkParserErrorMessage ictx s {expected := ["end of input", "statement"]}

def evalPyFile (path : System.FilePath) : BaseIO MessageLog := do
  let fileName := path.toString
  let input ←
    match (← IO.FS.readFile path |>.toBaseIO) with
    | .ok input => pure input
    | .error e => return MessageLog.empty.add <| mkSimpleMessage fileName <|
      m!"read failed: {e}"
  let ictx := Lean.Parser.mkInputContext input fileName
  evalPyInput ictx {}
