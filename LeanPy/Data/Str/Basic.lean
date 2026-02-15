/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.Hash
import LeanPy.Util.String

namespace LeanPy

/-- Returns the LeanPy hash of a string. -/
@[inline] def strHash (s : String) : Hash :=
  hash s -- TODO: salt hash?

/-- Returns the Python string representation of a `String`. -/
def strRepr (s : String) : String :=
  let q := if s.contains '\'' && !s.contains '"' then '"' else '\''
  go q s.startPos ("".push q) |>.push q
where
  go q p ns : String :=
    if h : p.IsAtEnd then
      ns
    else
      let c := p.get h
      let p' := p.next h
      if c == q then
        go q p' (ns.push '\\' |>.push q)
      else if c == '\\' then
        go q p' (ns.push '\\' |>.push '\\')
      else if c == '\t' then
        go q p' (ns.push '\\' |>.push 't')
      else if c == '\r' then
        go q p' (ns.push '\\' |>.push 'r')
      else if c == '\n' then
        go q p' (ns.push '\\' |>.push 'n')
      else if c.val < 0x20 || c.val == 0x7f then
        go q p' (upperHexUInt8 c.val.toUInt8 (ns.push '\\' |>.push 'x'))
      else if c.val < 0x7f || isPrintableUnicode c then
        go q p' (ns.push c)
      else if c.val < 0x100 then
        go q p' (upperHexUInt8 c.val.toUInt8 (ns.push '\\' |>.push 'x'))
      else if c.val < 0x10000 then
        go q p' (upperHexUInt16 c.val.toUInt16 (ns.push '\\' |>.push 'u'))
      else
        go q p' (upperHexUInt32 c.val (ns.push '\\' |>.push 'U'))
  termination_by p
  @[inline] isPrintableUnicode c :=
    -- TODO: Use unicode definition once Lean has support for it
    Lean.isLetterLike c
