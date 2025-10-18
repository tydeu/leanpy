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
  -- NOTE: Validity of the data of the object
  -- is shown through `Object.lawful_ty_data`
  IsValidObject id _ := id.isNonScalar

initialize typeTypeRef.init : InitTypeRef typeType ← initTypeRef

abbrev typeTypeRef : TypeRef := typeTypeRef.init.toTypeRef
