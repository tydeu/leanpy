/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.Object.Basic
import LeanPy.Data.Dict.Basic
import LeanPy.Data.AttrName

namespace LeanPy

abbrev AttrDict := TDict AttrName Object

/-- A Python exception. -/
-- TODO: Derive from `BaseException`
abbrev ErrorObject := Object

/-- A mutable dictionary value at some key.. -/
abbrev DictRef.Cell := MutableRef Object

/-- The stored value of a mutable dictionary. -/
abbrev DictRef.Data := TDict Object Cell

/-- A mutable reference to a dictionary. -/
abbrev DictRef := MutableRef DictRef.Data

/-- Mutable dictionary of variables. -/
abbrev VarDict := MutableRef AttrDict

structure PyContext where
  globals : VarDict
  locals : VarDict := globals

/-- The monad of Python code. -/
abbrev PyM := ReaderT PyContext <| EIO ErrorObject
