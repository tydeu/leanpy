/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.Type.Init
import LeanPy.Data.Type.Mro

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

@[simp] theorem baseMro_objectType :
  objectType.baseMro = []
:= rfl

private initialize objectTypeInitRef : InitTypeRef objectType ← initTypeRef

@[inline] def objectTypeRawRef : RawTypeRef := objectTypeInitRef.toRawTypeRef

@[simp] theorem isNonScalar_addr_objectTypeRawRef : objectTypeRawRef.addr.isNonScalar :=
  objectTypeInitRef.isNonScalar_addr

@[simp] theorem data_objectTypeRawRef : objectTypeRawRef.data = objectType :=
  objectTypeInitRef.data_toRawTypeRef
