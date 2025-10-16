/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.Object.Type

namespace LeanPy

def objectTypeDoc : String := "\
  The base class of the class hierarchy.\n\
  \n\
  When called, it accepts no arguments and returns a new featureless\n\
  instance that has no instance attributes and cannot be given any.\n\
  "

@[reducible] def objectType : TypeSpec where
  name := "object"
  doc? := some objectTypeDoc

initialize objectTypeRef' : DTypeSpecRef objectType ← mkDTypeSpecRef _

abbrev objectTypeRef : TypeSpecRef := objectTypeRef'.toTypeSpecRef
