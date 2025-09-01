/-
Copyright (c) 2023 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
syntax Authors Mac Malone
-/
import Lean.Elab.Command
import Lean.Elab.Syntax
import Lean.Elab.Eval

open Lean Elab Command Parser

namespace LeanPy.Internal

def addAndCompileConstDef
  (declName : Name) (p : Expr) (typeName : Name)
: CommandElabM Unit := do
  liftCoreM <| addAndCompile <| .defnDecl {
    name := declName
    levelParams := []
    type := mkConst typeName
    value := p
    hints := ReducibilityHints.regular (getMaxHeight (← getEnv) p + 1)
    safety := .safe
  }

private def appOptParams (eTy : Expr) (e : Expr) : Expr :=
  match eTy with
  | .forallE _ d b _ =>
    match d.getOptParamDefault? with
    | some defVal => appOptParams b (mkApp e defVal)
    | _ => e
  | _ => e

def parserName (constName : Name) : Name :=
  constName.str "parser"

/- Adapted from `Lean.Parser.compileParserDescr` -/
def compileParserDescr
  (root : Name) (categories : ParserCategories)
  (d : ParserDescr) (withPrefix : Name := .anonymous)
: CommandElabM Expr := do
  go d
where go d := do
  match d with
  | .const n =>
    let {declName, ..} ← getParserAliasInfo n
    let some info := (← getEnv).find? declName
      | throwUnknownConstant declName
    return appOptParams info.type (mkConst declName)
  | .unary n d =>
    let {declName, ..} ← getParserAliasInfo n
    if declName = ``notFollowedBy then
      -- the 2-argument `notFollowedBy` uniquely
      -- registers a 1-argument lambda as its alias
      return mkApp2 (mkConst declName) (← go d) (toExpr "element")
    else
      return mkApp (mkConst declName) (← go d)
  | .binary n d₁ d₂ =>
    let {declName, ..} ← getParserAliasInfo n
    return mkApp2 (mkConst declName) (← go d₁) (← go d₂)
  | .node k prec d =>
    return mkApp3 (mkConst ``leadingNode)
      (toExpr k) (toExpr prec) (← go d)
  | .nodeWithAntiquot n k d =>
    let mkP _ : CommandElabM Expr := do
      return mkApp2 (mkConst ``withCache) (toExpr k) $
        mkApp4 (mkConst ``nodeWithAntiquot) (toExpr n) (toExpr k) (← go d) (toExpr true)
    if (`token).isPrefixOf k then
      -- lone string literals may be wrapped in a `token` kind,
      -- no need to generate separate parser definitions for them
      return ← mkP ()
    let declName := parserName k
    unless (← getEnv).contains declName do
      unless withPrefix.isPrefixOf k do
        throwError m!"{root}: missing compiled parser for `{.ofConstName k}`"
      addAndCompileConstDef declName (← mkP ()) ``Parser
    return mkConst declName
  | .sepBy p sep psep trail =>
    return mkApp4 (mkConst ``sepBy)
      (← go p) (toExpr sep) (← go psep) (toExpr trail)
  | .sepBy1 p sep psep trail =>
    return mkApp4 (mkConst ``sepBy1)
      (← go p) (toExpr sep) (← go psep) (toExpr trail)
  | .trailingNode k prec lhsPrec d =>
    return mkApp4 (mkConst ``trailingNode)
      (toExpr k) (toExpr prec) (toExpr lhsPrec) (← go d)
  | .symbol tk =>
    return mkApp (mkConst ``symbol) (toExpr tk)
  | .nonReservedSymbol tk includeIdent =>
    return mkApp2 (mkConst ``nonReservedSymbol) (toExpr tk) (toExpr includeIdent)
  | .parser constName =>
    return mkConst constName
  | .cat catName prec =>
    if categories.contains catName then
      return mkApp2 (mkConst ``categoryParser) (toExpr catName) (toExpr prec)
    else
      ofExcept <| throwUnknownParserCategory catName

/- Adapted from `Lean.Parser.mkParserOfConstantAux` -/
def compileParser
  (constName : Name) (withPrefix : Name := .anonymous) (warn := false)
: CommandElabM (Bool × Name) := do
  let env ← getEnv
  let opts ← getOptions
  let some info := env.find? constName
    | throwUnknownConstant constName
  match info.type with
  | .const ``ParserDescr _ =>
    let d ← ofExcept (unsafe env.evalConst ParserDescr opts constName)
    compileDescr true ``Parser d
  | .const ``TrailingParserDescr _ =>
    let d ← ofExcept (unsafe env.evalConst TrailingParserDescr opts constName)
    compileDescr false ``TrailingParser d
  | .const ``Parser _ =>
    return (true, constName)
  | .const ``TrailingParser _ =>
    return (false, constName)
  | _ => throwError "\
    unexpected parser type at `{.ofConstName constName}`, \
    expected `ParserDescr` or `TrailingParserDescr`"
where
  compileDescr leading typeName d := do
    let declName := parserName constName
    if let some info := (← getEnv).find? declName then
      if warn then
        logWarning m!"`{.ofConstName declName}` already exists"
      match info.type with
      | .const ``Parser _ =>
        return (true, declName)
      | .const ``TrailingParser _ =>
        return (false, declName)
      | _ => throwError "\
        unexpected parser type at `{.ofConstName declName}`, \
        expected `Parser` or `TrailingParser`"
    let categories := (parserExtension.getState (← getEnv)).categories
    let p ← compileParserDescr constName categories d withPrefix
    unless (← getEnv).contains declName do -- `mkExpr` may create the def
      addAndCompileConstDef declName p typeName
    return (leading, declName)

scoped elab tk:"compile_parser " id:ident : command => withRef tk do
  let constName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  discard <| compileParser constName (warn := true)

/- Copied from `Lean.Parser.Extension` and adapted to `ParserCategory` -/
section

private def addLeadingParser
  (cat : ParserCategory) (declName : Name) (p : Parser) (prio : Nat)
: ParserCategory :=
  let kinds := cat.kinds.insert declName
  let addTokens (tks : List Token) : ParserCategory :=
    let tks    := tks.map Name.mkSimple
    let tables := tks.eraseDups.foldl (init := cat.tables) fun tables tk =>
      { tables with leadingTable := tables.leadingTable.insert tk (p, prio) }
    { cat with kinds, tables }
  match p.info.firstTokens with
  | FirstTokens.tokens tks    => addTokens tks
  | FirstTokens.optTokens tks => addTokens tks
  | _ =>
    let tables := { cat.tables with leadingParsers := (p, prio) :: cat.tables.leadingParsers }
    { cat with kinds, tables }

private def addTrailingParserAux
  (tables : PrattParsingTables) (p : TrailingParser) (prio : Nat)
: PrattParsingTables :=
  let addTokens (tks : List Token) : PrattParsingTables :=
    let tks := tks.map fun tk => Name.mkSimple tk
    tks.eraseDups.foldl (init := tables) fun tables tk =>
      { tables with trailingTable := tables.trailingTable.insert tk (p, prio) }
  match p.info.firstTokens with
  | FirstTokens.tokens tks    => addTokens tks
  | FirstTokens.optTokens tks => addTokens tks
  | _                         => { tables with trailingParsers := (p, prio) :: tables.trailingParsers }

private def addTrailingParser
  (cat : ParserCategory) (declName : Name) (p : TrailingParser) (prio : Nat)
: ParserCategory :=
  let kinds := cat.kinds.insert declName
  let tables := addTrailingParserAux cat.tables p prio
  { cat with kinds, tables }

def addParser
  (category : ParserCategory) (declName : Name)
  (leading : Bool) (p : Parser) (prio : Nat)
: ParserCategory :=
  if leading then
    addLeadingParser category declName p prio
  else
    addTrailingParser category declName p prio

end

def mkParserCategory (declName : Name) (behavior : LeadingIdentBehavior) : ParserCategory :=
  { declName, behavior }

deriving instance ToExpr for LeadingIdentBehavior

def categoryName (declName : Name) : Name :=
  declName.str "category"

def compileParserCategory
  (cat : ParserCategory) (prios : NameMap Nat := {})
  (withPrefix : Name := .anonymous)
: CommandElabM Name := do
  let declName := categoryName cat.declName
  if let some _ := (← getEnv).find? declName then
    logWarning m!"`{.ofConstName declName}` already exists"
    return declName
  let x := mkApp2 (mkConst ``mkParserCategory) (toExpr cat.declName) (toExpr cat.behavior)
  let x ← cat.kinds.foldlM (init := x) fun x kind _ => do
    let (leading, declName) ← compileParser kind withPrefix
    let prio := prios.find? kind |>.getD (eval_prio default)
    return mkApp5 (mkConst ``addParser) x
      (toExpr kind) (toExpr leading) (mkConst declName) (toExpr prio)
  addAndCompileConstDef declName x ``ParserCategory
  return declName

scoped elab tk:"compile_parser_cat " id:ident ps?:(term)? : command => withRef tk do
  let catName := id.getId.eraseMacroScopes
  let cats := (parserExtension.getState (← getEnv)).categories
  let some cat := cats.find? catName
    |  throwErrorAt id "unknown category `{catName}`"
  liftTermElabM <| Lean.Elab.Term.addCategoryInfo id catName
  let prios ←
    if let some ps := ps? then
      let t := mkApp (mkConst ``NameMap) (mkConst ``Nat)
      liftTermElabM <| unsafe Term.evalTerm (NameMap Nat) t ps
    else
      pure {}
  discard <| compileParserCategory cat prios

@[inline] def mkTokenTable : TokenTable := {}

@[inline] def addNewToken (tks : TokenTable) (tk : Token) : TokenTable :=
  tks.insert tk tk

def addToken (tks : TokenTable) (tk : Token) : TokenTable :=
  if let some _ := tks.find? tk then tks else tks.insert tk tk

def addParserTokens (tks : TokenTable) (p : Parser) : TokenTable :=
  let newTokens := p.info.collectTokens []
  newTokens.foldl addToken tks

def addCategoryTokens (tks : TokenTable) (cat : ParserCategory) : TokenTable :=
  let tks := cat.tables.leadingParsers.foldl fromParsers tks
  let tks := cat.tables.leadingTable.fold fromTable tks
  let tks := cat.tables.trailingParsers.foldl fromParsers tks
  let tks := cat.tables.trailingTable.fold fromTable tks
  tks
where
  fromParsers := fun tks (p, _) => addParserTokens tks p
  fromTable := fun tks __ ps => ps.foldl fromParsers tks

def mkTokenTableOfCategories (categories : ParserCategories) : TokenTable :=
  categories.foldl (init := {}) fun tks _ cat =>
    addCategoryTokens tks cat
