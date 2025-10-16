/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.IntRef
import LeanPy.Data.StringRef
import LeanPy.Data.MutableRef
import LeanPy.Data.Object.ObjectType

/-!
Built-in types inheriting directly from `object`. These are in a separate
file from their parent due to `initialize` limitations.
-/

namespace LeanPy

/-! ## `NoneType` -/

@[reducible] def noneType : TypeSpec where
  name := "NoneType"
  base? := some objectTypeRef
  IsValidObject id data :=
    id = .none ∧ data = .mk ()

initialize noneTypeRef' : DTypeSpecRef noneType ← mkDTypeSpecRef _

abbrev noneTypeRef : TypeSpecRef := noneTypeRef'.toTypeSpecRef

/-! ## `type` -/

def typeTypeDoc : String := "\
  type(object) -> the object's type\n\
  type(name, bases, dict, **kwds) -> a new type\
  "

@[reducible] def typeType : TypeSpec where
  name := "type"
  doc? := some typeTypeDoc
  isTypeSubclass := true
  base? := some objectTypeRef
  IsValidObject id data :=
    id.isNonScalar ∧ data.kind = typeName TypeSpecRef

initialize typeTypeRef' : DTypeSpecRef typeType ← mkDTypeSpecRef _

abbrev typeTypeRef : TypeSpecRef := typeTypeRef'.toTypeSpecRef

/-! ## `str` -/

def strTypeDoc : String := "\
  str(object='') -> str\n\
  str(bytes_or_buffer[, encoding[, errors]]) -> str\n\
  \n\
  Create a new string object from the given object. If encoding or\n\
  errors is specified, then the object must expose a data buffer\n\
  that will be decoded using the given encoding and error handler.\n\
  Otherwise, returns the result of object.__str__() (if defined)\n\
  or repr(object).\n\
  encoding defaults to sys.getdefaultencoding().\n\
  errors defaults to 'strict'.\
  "

@[reducible] def strType : TypeSpec where
  name := "str"
  doc? := some strTypeDoc
  isStrSubclass := true
  base? := some objectTypeRef
  IsValidObject id data :=
    id.isNonScalar ∧ data.kind = typeName StringRef

initialize strTypeRef' : DTypeSpecRef strType ← mkDTypeSpecRef _

abbrev strTypeRef : TypeSpecRef := strTypeRef'.toTypeSpecRef

/-! ## `int` -/

def intTypeDoc : String := "\
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

@[reducible] def intType : TypeSpec where
  name := "int"
  doc? := some intTypeDoc
  isIntSubclass := true
  base? := some objectTypeRef
  IsValidObject _ data :=
    data.kind = typeName IntRef -- TODO: id.isInt

initialize intTypeRef' : DTypeSpecRef intType ← mkDTypeSpecRef _

abbrev intTypeRef : TypeSpecRef := intTypeRef'.toTypeSpecRef
