/-
Copyright (c) 2023 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
syntax Authors Mac Malone
-/
import LeanPy.Grammar
import LeanPy.Util.CompileParser

open Lean Parser

namespace LeanPy

open Internal

@[inline] private def mkParserCategories : ParserCategories := {}
@[inline] private def addParserCategory (categories : ParserCategories) (catName : Name) (category : ParserCategory) :=
  categories.insert catName category

private def parserPrios : NameMap Nat :=
  (∅ : NameMap _)
  |>.insert ``Grammar.assignment (eval_prio high)

local elab "compile_py_cats%" : command => do
  let cats := (parserExtension.getState (← getEnv)).categories
  let x := mkConst (``mkParserCategories)
  let x ← cats.foldlM (init := x) fun x catName cat => do
    let .str .anonymous catStr := catName
      | return x
    unless catStr.startsWith "py" do
      return x
    let declName ← compileParserCategory cat parserPrios `LeanPy.Grammar
    return mkApp3 (mkConst ``addParserCategory) x
      (toExpr catName) (mkConst declName)
  addAndCompileConstDef `LeanPy.parserCategories x ``ParserCategories

compile_py_cats%

local elab "mk_token_table%" : term =>
  let tks := mkTokenTableOfCategories parserCategories |>.values
  return tks.foldl (init := mkConst ``mkTokenTable) fun x tk =>
    mkApp2 (mkConst ``addNewToken) x (toExpr tk)

set_option compiler.extract_closed false in
def tokenTable : TokenTable := mk_token_table%
