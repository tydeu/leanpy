/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.Object.InitTypeRef

namespace LeanPy

def objectType.doc : String := "\
  The base class of the class hierarchy.\n\
  \n\
  When called, it accepts no arguments and returns a new featureless\n\
  instance that has no instance attributes and cannot be given any.\n\
  "

@[reducible] def objectType : PyType where
  name := "object"
  doc? := some objectType.doc

initialize objectTypeRef.init : InitTypeRef objectType ← initTypeRef

abbrev objectTypeRef : TypeRef := objectTypeRef.init.toTypeRef
