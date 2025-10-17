/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.Object.TypeRef

namespace LeanPy

def intType.doc : String := "\
  int([x]) -> integer\n\
  int(x, base=10) -> integer\n\
  \n\
  Convert a number or string to an integer, or return 0 if no arguments\n\
  are given.  If x is a number, return x.__int__().  For floating point\n\
  numbers, this truncates towards zero.\n\
  \n\
  If x is not a number or if base is given, then x must be a string,\n\
  bytes, or bytearray instance representing an integer literal in the\n\
  given base.  The literal can be preceded by '+' or '-' and be surrounded\n\
  by whitespace.  The base defaults to 10.  Valid bases are 0 and 2-36.\n\
  Base 0 means to interpret the base from the string as an integer literal.\n\
  >>> int('0b100', base=0)\n\
  4\
  "

@[reducible] def intType : PyType where
  name := "int"
  doc? := some intType.doc
  isIntSubclass := true
  base? := some objectTypeRef
  IsValidObject _ data :=
    data.kind = typeName IntRef -- TODO: id.isInt

initialize intTypeRef.init : InitTypeRef intType ← initTypeRef

abbrev intTypeRef : TypeRef := intTypeRef.init.toTypeRef
