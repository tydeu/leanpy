/-
Copyright (c) 2023 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
syntax Authors Mac Malone
-/
import LeanPy.Parser

/-!
# The Python Grammar

This module contains a Lean DSL that encodes the Python grammar.
It uses Python 3's [Full Grammar Specification][1] as a guideline.

[1]: https://docs.python.org/3/reference/grammar.html
-/

namespace Py.Grammar
open LeanPy

/-- Use `[stx]` as an alternative to `(stx)?` following the specification style. -/
local macro "[" xs:stx* "]" : stx => `(stx|($[$xs:stx]*)?)

/-! ## Basic Tokens -/

syntax name := simpleIdent
syntax dottedName := ident -- name ("." name)*
syntax attr := ident -- name ("." name)+
syntax nameOrAttr := ident -- name ("." name)*
syntax lambdaParam := name

/-! ## Expressions -/

declare_syntax_cat pyExpr (behavior := symbol)

syntax typeComment := "# " "type: " pyExpr

syntax exprs := pyExpr,+,?
syntax starredExpr := "*" pyExpr
syntax doubleStarredExpr := "**" pyExpr

syntax starExpr
  | "*" pyExpr:55
  | pyExpr

syntax starExprs := starExpr,+,?

syntax yieldExpr := "yield" (("from" pyExpr) <|> starExpr,*,?)

syntax assignmentExpr := atomic(name " := ") pyExpr

syntax namedExpr
  | assignmentExpr
  | pyExpr !":="

syntax starNamedExpr
  | "*" pyExpr:55
  | namedExpr

/-! ### Logical Expressions -/

syntax (name := condExpr) pyExpr:30 colGt " if " pyExpr:30 colGt " else " pyExpr : pyExpr
syntax:30 (name := disjunction) pyExpr:31 (" or " pyExpr:31)+ : pyExpr
syntax:35 (name := conjunction) pyExpr:36 (" and " pyExpr:36)+ : pyExpr
syntax:38 (name := inversion) "not " pyExpr:40 : pyExpr

/-! ### Comparison Operators -/

syntax:50 (name := eq)    pyExpr:50 " == " pyExpr:51 : pyExpr
syntax:50 (name := ne)    pyExpr:50 " != " pyExpr:51 : pyExpr
syntax:50 (name := le)    pyExpr:50 " <= " pyExpr:51 : pyExpr
syntax:50 (name := lt)    pyExpr:50 " < " pyExpr:51 : pyExpr
syntax:50 (name := ge)    pyExpr:50 " >= " pyExpr:51 : pyExpr
syntax:50 (name := gt)    pyExpr:50 " > " pyExpr:51 : pyExpr
syntax:50 (name := notIn) pyExpr:50 " not " "in " pyExpr:51 : pyExpr
syntax:50 (name := «in»)  pyExpr:50 " in " pyExpr:51 : pyExpr
syntax:50 (name := isNot) pyExpr:50 " is " "not " pyExpr:51 : pyExpr
syntax:50 (name := «is»)  pyExpr:50 " is " pyExpr:51 : pyExpr

/-! ### Bitwise Operators -/

syntax:55 (name := bitwiseOr)  pyExpr:55 " | " pyExpr:56 : pyExpr
syntax:58 (name := bitwiseXor) pyExpr:58 " ^ " pyExpr:59 : pyExpr
syntax:60 (name := bitwiseAnd) pyExpr:60 " & " pyExpr:61 : pyExpr

/- shift_expr -/
syntax:63 (name := shl) pyExpr:63 "<<" pyExpr:65 : pyExpr
syntax:63 (name := shr) pyExpr:63 ">>" pyExpr:65 : pyExpr

/-! ### Arithmetic Operators -/

/- sum -/
syntax:65 (name := add) pyExpr:65 " + " pyExpr:66 : pyExpr
syntax:65 (name := sub) pyExpr:65 " - " pyExpr:66 : pyExpr

/- term -/
syntax:70 (name := mul)     pyExpr:70 " * " pyExpr:71 : pyExpr
syntax:70 (name := tdiv)    pyExpr:70 " / " pyExpr:71 : pyExpr
syntax:70 (name := fdiv)    pyExpr:70 " // " pyExpr:71 : pyExpr
syntax:70 (name := mod)     pyExpr:70 " % " pyExpr:71 : pyExpr
syntax:70 (name := matmul)  pyExpr:70 " @ " pyExpr:71 : pyExpr

/- factor -/
syntax:75 (name := pos) "+" pyExpr:75 : pyExpr
syntax:75 (name := neg) "-" pyExpr:75 : pyExpr
syntax:75 (name := cmp) "~" pyExpr:75 : pyExpr

/- power -/
syntax:75 (name := power) pyExpr:76 "**" pyExpr:75 : pyExpr

/-! ### Primary Elements -/

syntax:100 (name := await) "await " pyExpr:101 : pyExpr

syntax slice
  | assignmentExpr
  | [pyExpr] ":" [pyExpr] [":" [pyExpr]]
  | pyExpr !":="

syntax slices
  | atomic(slice !",")
  | (slice <|> starredExpr),+,?

syntax:arg pyExpr:arg "[" slices "]" : pyExpr

/- Captures both simple names and member accesses of names. -/
syntax:max (name := identExpr) ident : pyExpr

syntax:arg pyExpr:arg "." name : pyExpr

syntax:max (name := trueExpr)   "True" : pyExpr
syntax:max (name := falseExpr)  "False" : pyExpr
syntax:max (name := noneExpr)   "None" : pyExpr
syntax:max (name := numExpr)    num : pyExpr
syntax:max (name := group)      "(" (yieldExpr <|> namedExpr) ")" : pyExpr
syntax:max (name := ellipsis)   "..." : pyExpr

/-! ### Lambda Functions -/

/-
NOTE FROM THE SPECIFICATION:
`lambdaParams` etc. duplicates parameters but without annotations
or type comments, and if there's no comma after a parameter, we expect
a colon, not a close parenthesis.  (For more, see parameters above.)
-/

syntax default := " = " pyExpr

syntax lambdaParamNoDefault :=
  lambdaParam ("," <|> lookahead(":"))

syntax lambdaParamWithDefault :=
  lambdaParam default ("," <|> lookahead(":"))

syntax lambdaParamMaybeDefault :=
  lambdaParam [default] ("," <|> lookahead(":"))

syntax lambdaKwds :=
  "**" lambdaParamNoDefault

syntax lambdaStarEtc
  | atomic("*" ",") lambdaParamMaybeDefault+ [lambdaKwds]
  | "*" lambdaParamNoDefault lambdaParamMaybeDefault* [lambdaKwds]
  | lambdaKwds

syntax lambdaSlashNoDefault
  | lambdaParamNoDefault+ "/" ("," <|> lookahead(":"))

syntax lambdaSlashWithDefault
  | lambdaParamNoDefault* lambdaParamWithDefault+ "/" ("," <|> lookahead(":"))

syntax lambdaParams
  | lambdaSlashNoDefault lambdaParamNoDefault* lambdaParamWithDefault* [lambdaStarEtc]
  | lambdaSlashWithDefault lambdaParamWithDefault* [lambdaStarEtc]
  | lambdaParamNoDefault+ lambdaParamWithDefault* [lambdaStarEtc]
  | lambdaParamWithDefault+ [lambdaStarEtc]
  | lambdaStarEtc

syntax:20 (name := lambdef) "lambda " [lambdaParams] ":" pyExpr : pyExpr

/- ## Literals -/

syntax:max (name := strings) str+ : pyExpr
syntax:max (name := list)   "[" starNamedExpr,*,? "]" : pyExpr
syntax:max (name := tuple)  "(" [starNamedExpr "," starNamedExpr,*,?] ")" : pyExpr
syntax:max (name := set)    "{" starNamedExpr,+,? "}" : pyExpr

/- ### Dicts -/

syntax kvpair := pyExpr ":" pyExpr
syntax doubleStarredKvpair := (("**" pyExpr:55) <|> kvpair)
syntax:max (name := dict) "{" doubleStarredKvpair,*,? "}" : pyExpr

/- ### Comprehensions & Generators -/

declare_syntax_cat pyStarTarget
syntax starTargets := pyStarTarget,+,?

syntax forIfClause :=
  atomic("async "? "for " starTargets " in ") disjunction (" if " disjunction )*

syntax forIfClauses := forIfClause+

syntax:max (name := listcomp) "[" namedExpr forIfClauses "]" : pyExpr
syntax:max (name := setcomp)  "{" namedExpr forIfClauses "}" : pyExpr
syntax:max (name := dictcomp) "{" kvpair forIfClauses "}" : pyExpr

syntax:max (name := genexp)   "(" (assignmentExpr <|> (pyExpr !":=")) forIfClauses ")" : pyExpr
syntax:arg pyExpr:arg genexp : pyExpr

/- ### Function Calls -/

syntax kwarg := atomic(name " = ") pyExpr

syntax kwargs
  | lookahead("**") (doubleStarredExpr <|> kwarg),+,?
  | (starredExpr <|> kwarg),+,? [commaBefore (doubleStarredExpr <|> kwarg),+,?]

syntax args
  | (!("**" <|> kwarg) (starredExpr <|> assignmentExpr <|> (pyExpr !":=")) !"="),+,?
    [commaBefore kwargs]
  | kwargs

syntax arguments := args lookahead(")")
syntax:arg (name := callExpr) pyExpr:arg "(" [arguments] ")" : pyExpr

/-! ## Assignment Targets -/

/-
NOTE FROM THE SPECIFICATION:
Star targets may contain `*bitwiseOr`, targets may not.
-/

syntax tLookahead := "(" <|> "[" <|> "."

declare_syntax_cat pyTPrimary
syntax pyTPrimary "." name lookahead(tLookahead) : pyTPrimary
syntax pyTPrimary "[" slices "]" lookahead(tLookahead) : pyTPrimary
syntax pyTPrimary genexp lookahead(tLookahead) : pyTPrimary
syntax pyTPrimary "(" [arguments] ")" lookahead(tLookahead) : pyTPrimary
syntax pyExpr:max lookahead(tLookahead) : pyTPrimary

syntax singleSubscriptAttributeTarget :=
  pyTPrimary (("." name) <|> ("[" slices "]")) !tLookahead

syntax "*" !"*" pyStarTarget : pyStarTarget
syntax:arg singleSubscriptAttributeTarget : pyStarTarget
syntax:max "(" pyStarTarget,*,? ")" : pyStarTarget
syntax:max "[" pyStarTarget,*,? "]" : pyStarTarget
syntax:max name : pyStarTarget

declare_syntax_cat pySingleTarget
syntax "(" pySingleTarget ")" : pySingleTarget
syntax singleSubscriptAttributeTarget : pySingleTarget
syntax name : pySingleTarget

/-! ### Targets for `del` Statements -/

declare_syntax_cat pyDelTarget
syntax delTargets := pyDelTarget,+,?
syntax singleSubscriptAttributeTarget : pyDelTarget

/- del_t_atom -/
syntax:max name : pyDelTarget
syntax:max "(" pyDelTarget,*,? ")" : pyDelTarget
syntax:max "[" pyDelTarget,*,? "]" : pyDelTarget

/-! ## Typing Elements -/

-- NOTE FROM THE SPECIFICATION:  `typeExprs` allow `*`/`**` but ignore them
syntax typeExprs
  | "**" pyExpr
  | "*" pyExpr ["," "**" pyExpr]
  | pyExpr,+,? [commaBefore "*" pyExpr ("," <|> !"**")] [commaBefore "**" pyExpr]

syntax funcTypeComment
  | linebreak typeComment colGt -- SPEC NOTE: Must be followed by indented block
  | typeComment

/-! ## Statements -/

declare_syntax_cat pySimpleStmt (behavior := symbol)
syntax simpleStmts := withPosition(sepBy1(pySimpleStmt, "; ")) linebreak

declare_syntax_cat pyCompoundStmt (behavior := symbol)
syntax stmt := pyCompoundStmt <|> simpleStmts

syntax stmtNewline
  | pyCompoundStmt linebreak
  | simpleStmts
  | linebreak

/-! ### Simple Statements -/

syntax returnStmt   := "return " starExpr,*,?
syntax raiseStmt    := "raise " [pyExpr ["from" pyExpr]]
syntax passStmt     := "pass"
syntax delStmt      := "del " delTargets lookahead(";" <|> linebreak)
syntax yieldStmt    := yieldExpr
syntax assertStmt   := "assert " pyExpr ["," pyExpr]
syntax breakStmt    := "break"
syntax continueStmt := "continue"
syntax globalStmt   := "global " name,+
syntax nonlocalStmt := "nonlocal " name,+

attribute [pySimpleStmt_parser] returnStmt
attribute [pySimpleStmt_parser] raiseStmt
attribute [pySimpleStmt_parser] passStmt
attribute [pySimpleStmt_parser] delStmt
attribute [pySimpleStmt_parser] yieldStmt
attribute [pySimpleStmt_parser] assertStmt
attribute [pySimpleStmt_parser] breakStmt
attribute [pySimpleStmt_parser] continueStmt
attribute [pySimpleStmt_parser] globalStmt
attribute [pySimpleStmt_parser] nonlocalStmt

/-! ### Assignment Statements -/

syntax augassign
  | "+="
  | "-="
  | "*="
  | "@="
  | "/="
  | "%="
  | "&="
  | "|="
  | "^="
  | "<<="
  | ">>="
  | "**="
  | "//="

syntax annotatedRhs := yieldExpr <|> starExprs

/-
NOTE FROM THE SPECIFICATION:
`annotatedRhs` may start with `yield`; `yieldExpr` must start with `yield`
-/
syntax assignment
  | atomic(name ": ") pyExpr [" = " annotatedRhs]
  | atomic(("(" pySingleTarget ")" <|> singleSubscriptAttributeTarget) ": ")
      pyExpr ["=" annotatedRhs]
  | (atomic(starTargets) "=")+ annotatedRhs !"=" [typeComment]
  | atomic(pySingleTarget augassign) annotatedRhs

/-
NOTE: Assignment MUST be higher priority than expression in the grammar,
otherwise parsing a simple assignment will break (and this is a known feature
of the Python grammar).
-/
attribute [pySimpleStmt_parser] starExprs
attribute [pySimpleStmt_parser high] assignment

/-! ### Import Statements -/

syntax importFromAsName := name ["as" name]
syntax dottedAsName := dottedName ["as" name]
syntax importName := "import " dottedAsName,+

syntax importFromTargets
  | "(" importFromAsName,+,? ")"
  | importFromAsName,+
  | "*"

@[run_parser_attribute_hooks]
def dots := raw <| Lean.Parser.takeWhileFn (· = '.')

syntax importFrom :=
  "from " dots dottedName " import " importFromTargets

attribute [pySimpleStmt_parser] importName
attribute [pySimpleStmt_parser] importFrom

/-! ### Compound Statements -/

syntax block
  | ppSpace ("\\" <|> lineEq) simpleStmts
  | ppIndent(colGt withPosition(many1Indent(ppLine stmt)))

syntax decorator := "@" namedExpr linebreak

/-! ### Class Definitions -/

syntax classDefRaw :=
  "class " name ["(" [arguments] ")"] ":" block

syntax classDef :=
  withPosition(decorator* classDefRaw)

attribute [pyCompoundStmt_parser] classDef

/-! ### Function Definitions -/

/-
NOTE FROM THE SPECIFICATION:

One parameter.  This *includes* a following comma and type comment.

There are three styles:
- No default
- With default
- Maybe with default

There are two alternative forms of each, to deal with type comments:
- Ends in a comma followed by an optional type comment
- No comma, optional type comment, must be followed by close paren
The latter form is for a final parameter without trailing comma.
-/

syntax annotation := ":" pyExpr
syntax param := atomic(name [annotation])
syntax starAnnotation := ":" starExpr
syntax paramStarAnnotation := atomic(name starAnnotation)

syntax paramSep :=
  ("," [typeComment]) <|> ([typeComment] lookahead(")"))

syntax paramNoDefault := param paramSep
syntax paramNoDefaultStarAnnotation := paramStarAnnotation paramSep
syntax paramWithDefault := atomic(param default) paramSep
syntax paramMaybeDefault := param [default] paramSep

syntax slashNoDefault :=
  paramNoDefault+ "/" ("," <|> lookahead(")"))

syntax slashWithDefault :=
  paramNoDefault* paramWithDefault+ "/" ("," <|> lookahead(")"))

syntax kwds :=
  "**" paramNoDefault

syntax starEtc
  | "*" paramNoDefault paramMaybeDefault* [kwds]
  | "*" paramNoDefaultStarAnnotation paramMaybeDefault* [kwds]
  | "*" "," paramMaybeDefault+ [kwds]
  | kwds

syntax params
  | slashNoDefault paramNoDefault* paramWithDefault* [starEtc]
  | slashWithDefault paramWithDefault* [starEtc]
  | paramNoDefault+ paramWithDefault* [starEtc]
  | paramWithDefault+ [starEtc]
  | starEtc

syntax functionDefRaw :=
  "async "? "def " name "(" [params] ")" [" -> " pyExpr] ":" [funcTypeComment] block

syntax functionDef :=
  withPosition(decorator* functionDefRaw)

attribute [pyCompoundStmt_parser] functionDef

/-! ### If Statement -/

syntax elseBlock := "else" ":" block
syntax elifStmt := "elif " namedExpr ":" block

syntax ifStmt := withPosition $
  "if " namedExpr ":" block (colEq elifStmt)* [colEq elseBlock]

attribute [pyCompoundStmt_parser] ifStmt

/-! ### While Statement -/

syntax whileStmt := withPosition $
  "while" namedExpr ":" block [colEq elseBlock]

attribute [pyCompoundStmt_parser] whileStmt

/-! ### For Statement -/

syntax forStmt := withPosition $
  atomic("async "? "for" starTargets "in")
  starExprs ":" [typeComment] block [colEq elseBlock]

attribute [pyCompoundStmt_parser] forStmt

/-! ### With Statement -/

syntax withItem :=
  pyExpr ["as" pyStarTarget lookahead("," <|> ")" <|> ":")]

syntax withSig
  | "(" withItem,+,? ")" ":" block
  | withItem,+ ":" [typeComment] block

syntax withStmt :=
  withPosition("async "? "with " withSig)

attribute [pyCompoundStmt_parser] withStmt

/-! ### Try Statement -/

syntax exceptBlock :=
  "except" (":" <|> (pyExpr ["as" name] ":")) block

syntax exceptStarBlock :=
  atomic("except" "*") pyExpr ["as" name] ":" block

syntax finallyBlock :=
  "finally" ":" block

syntax tryStmt := withPosition $
  "try" ":" block colEq (exceptStarBlock+ <|> exceptBlock+)
    [colEq elseBlock] [colEq finallyBlock]

attribute [pyCompoundStmt_parser] tryStmt

/-! ### Match Statement -/

syntax patternCaptureTarget :=
  name !("." <|> "(" <|> "=")

declare_syntax_cat pyPattern (behavior := symbol)

syntax:20 (name := asPattern) pyPattern:21 "as" patternCaptureTarget : pyPattern
syntax:30 (name := orPattern) sepBy1(pyPattern:max,"|") : pyPattern

syntax literalNum :=
  "-"? num [("+" <|> "-") num]

-- Literal exprs are used to restrict permitted mapping pattern keys
syntax literalExpr
  | literalNum
  | strings
  | "None"
  | "True"
  | "False"

syntax:max (name := literalPattern) literalExpr : pyPattern
syntax:max (name := capturePattern) patternCaptureTarget : pyPattern
syntax:max (name := wildcardPattern) "_" : pyPattern
syntax:max (name := valuePattern) attr !("." <|> "(" <|> "=") : pyPattern
syntax:max (name := groupPattern) "(" pyPattern ")" : pyPattern

syntax starPattern :=
  "*" (wildcardPattern <|> patternCaptureTarget)

syntax maybeStarPattern := starPattern <|> pyPattern

syntax sequencePattern
  | "[" maybeStarPattern,*,? "]"
  | "(" [maybeStarPattern "," maybeStarPattern,*,?] ")"

syntax keyValuePattern :=
  (literalExpr <|> attr) ":" pyPattern

syntax itemsPattern := keyValuePattern,+

syntax doubleStarPattern :=
  "**" patternCaptureTarget

syntax mappingPatternParams
  | doubleStarPattern ","?
  | keyValuePattern,+,?  [commaBefore doubleStarPattern ","?]

syntax:max (name := mappingPattern) "{" [mappingPatternParams] "}" : pyPattern

syntax keywordPattern := atomic(name "=") pyPattern

syntax classPatternParams
  |  keywordPattern,+,?
  |  pyPattern,+,? [commaBefore keywordPattern,+,?]

syntax:max (name := classPattern) nameOrAttr "(" [classPatternParams] ")" : pyPattern

syntax patterns
  | starPattern "," maybeStarPattern,*,?
  | pyPattern ["," maybeStarPattern,*,?]

syntax guard := " if " namedExpr

syntax caseBlock := withPosition $
  "case " patterns [guard] ":" block

syntax subjectExpr
  | "*" pyExpr:55 "," starNamedExpr,*,?
  | namedExpr

syntax matchBlock :=
  ppIndent(colGt withPosition(many1Indent(ppLine stmt)))

syntax matchStmt := withPosition $
  "match " subjectExpr ":" matchBlock

attribute [pyCompoundStmt_parser] matchStmt
