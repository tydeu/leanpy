/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.Str.Ref
import LeanPy.Data.Object.TypeRef

namespace LeanPy

def strType.doc : String := "\
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

@[reducible] def strType : PyType where
  name := "str"
  doc? := some strType.doc
  isStrSubclass := true
  base? := some objectTypeRef
  IsValidObject id data :=
    id.isNonScalar ∧ data.kind = typeName StringRef

initialize strTypeRef.init : InitTypeRef strType ← initTypeRef

abbrev strTypeRef : TypeRef := strTypeRef.init.toTypeRef
