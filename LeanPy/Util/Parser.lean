/-
Copyright (c) 2023 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Parser.Basic
import Lean.Parser.Syntax

/-! # Parser & Syntax Utilities
Additional definitions to help with defining the Python grammar.
-/

open Lean Parser Command PrettyPrinter Formatter Parenthesizer

namespace LeanPy

/--
`$`-style application grouping for the syntax category.

For example, `withPostion $ x` expands to `withPosition(x)`.
-/
macro id:ident " $ " xs:stx*: stx => `(stx| $id:ident($[$xs]*))

/--
A convenient multiline syntax for defining large alternatives. For example,

```
syntax foobar
  | foo
  | bar
  | baz
```

is equivalent to

```
syntax foobar := foo <|> (bar <|> baz)
```
-/
syntax (name := syntaxAbbrevAlts) (docComment)?
"syntax" ident ppIndent(many1Indent(ppLine "| " ppSpace stx+)) : command

macro_rules
| `(syntaxAbbrevAlts| $(doc?)? syntax $id $[| $[$alts:stx]*]*) => do
  let alt0 := ⟨mkNullNode alts.back!⟩
  let stx ← alts[0:alts.size-1].foldrM (init := alt0) fun xs x =>
    `(stx|($[$xs]*) <|> $x)
  `(syntaxAbbrev| $[$doc?:docComment]? syntax $id := $stx)

/-- A `Parser` for `rawFn`. -/
def raw (fn : ParserFn) (trailingWs := false) : Parser where
  fn := rawFn fn trailingWs

@[combinator_formatter raw] def raw.formatter :=
  Formatter.visitAtom Name.anonymous

@[combinator_parenthesizer raw] def raw.parenthesizer :=
  Parenthesizer.visitToken

/--
Check if the topmost atom of the syntax stack matches `f`. If not, error with `msg`.
If the syntax on top of the stack is a node, look at its final argument recursively.
-/
@[run_parser_attribute_hooks] def checkAtomTop (f : String → Bool) (msg : String) :=
  checkStackTop go msg
where
  go
  | .missing => false
  | .ident .. => false
  | .atom (val := val) .. => f val
  | .node (args := args) .. =>
      if h : args.size > 0 then
        go <| args[args.size - 1]'(Nat.sub_succ_lt_self _ _ h)
      else
        false

@[run_parser_attribute_hooks]
def commaBefore := checkAtomTop (· = ",") "expected ',' before"

def simpleIdentFn : ParserFn := fun ctx st =>
  let startPos := st.pos
  let initStackSz := st.stackSize
  let expected := ["simple unqualified identifier"]
  let st := tokenFn expected ctx st
  if st.hasError then
    st
  else
    match st.stxStack.back with
    | Syntax.ident _ _ (.str .anonymous _) _ => st
    | _  => st.mkErrorsAt expected startPos initStackSz

def simpleIdentNoAntiquot : Parser where
  fn   := simpleIdentFn
  info := mkAtomicInfo "ident"

@[combinator_formatter simpleIdentNoAntiquot]
def simpleIdentNoAntiquot.formatter := identNoAntiquot.formatter

@[combinator_parenthesizer simpleIdentNoAntiquot]
def simpleIdentNoAntiquot.parenthesizer := identNoAntiquot.parenthesizer

/--
Parses an identifier that is a simple name (i.e., `Name.mkSimple`).
That is, it parses an identifier without a `.` (an unqualified/atomic identifier).
-/
@[run_parser_attribute_hooks] def simpleIdent : Parser :=
  withAntiquot (mkAntiquot "ident" identKind) simpleIdentNoAntiquot

def skipInsideQuotFn (p : ParserFn) : ParserFn := fun c s =>
  if c.quotDepth > 0 then s else p c s

@[run_parser_attribute_hooks]
def skipInsideQuot (p : Parser) : Parser :=
  withFn skipInsideQuotFn p

initialize
  register_parser_alias skipInsideQuot { stackSz? := none }
