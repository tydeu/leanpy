/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.Object.TypeRef

namespace LeanPy

def dictType.doc : String := "\
  dict() -> new empty dictionary\n\
  dict(mapping) -> new dictionary initialized from a mapping object's\n\
      (key, value) pairs\n\
  dict(iterable) -> new dictionary initialized as if via:\n\
      d = {}\n\
      for k, v in iterable:\n\
          d[k] = v\n\
  dict(**kwargs) -> new dictionary initialized with the name=value pairs\n\
      in the keyword argument list.  For example:  dict(one=1, two=2)\
  "

def dictDataKind : DataKind := `LeanPy.Dict

@[reducible] def dictType : PyType where
  name := "dict"
  doc? := some dictType.doc
  base? := some objectTypeRawRef
  isDictSubclass := true
  IsValidObject id data := id.isNonScalar ∧ data.kind = dictDataKind

@[simp] theorem baseMro_dictType :
  dictType.baseMro = [objectTypeRawRef]
:= rfl

private initialize dictTypeInitRef : InitTypeRef dictType ← initTypeRef

@[inline] def dictTypeRawRef : RawTypeRef := dictTypeInitRef.toRawTypeRef

@[simp] theorem isNonScalar_addr_dictTypeRawRef : dictTypeRawRef.addr.isNonScalar :=
  dictTypeInitRef.isNonScalar_addr

@[simp] theorem data_dictTypeRawRef : dictTypeRawRef.data = dictType :=
  dictTypeInitRef.data_toRawTypeRef
