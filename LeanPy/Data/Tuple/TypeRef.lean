/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.Object.TypeRef

namespace LeanPy

def tupleType.doc : String := "\
  Built-in immutable sequence.\n\
  \n\
  If no argument is given, the constructor returns an empty tuple.\n\
  If iterable is specified the tuple is initialized from iterable's items.\n\
  \n\
  If the argument is a tuple, the return value is the same object.\
  "

def tupleDataKind : DataKind := `LeanPy.TupleRef

@[reducible] def tupleType : PyType where
  name := "tuple"
  doc? := some tupleType.doc
  base? := some objectTypeRef
  isTupleSubclass := true
  IsValidObject id data := id.isNonScalar ∧ data.kind = tupleDataKind

initialize tupleTypeRef.init : InitTypeRef tupleType ← initTypeRef

abbrev tupleTypeRef : TypeRef := tupleTypeRef.init.toTypeRef
