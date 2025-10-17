/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.Object.TypeRef

namespace LeanPy

def typeType.doc : String := "\
  type(object) -> the object's type\n\
  type(name, bases, dict, **kwds) -> a new type\
  "

@[reducible] def typeType : PyType where
  name := "type"
  doc? := some typeType.doc
  isTypeSubclass := true
  base? := some objectTypeRef
  IsValidObject id data :=
    id.isNonScalar ∧ data.kind = typeName RawTypeRef

initialize typeTypeRef.init : InitTypeRef typeType ← initTypeRef

abbrev typeTypeRef : TypeRef := typeTypeRef.init.toTypeRef
