/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.Int.TypeRef

namespace LeanPy

def boolType.doc : String := "\
  bool(x) -> bool\n\
  \n\
  Returns True when the argument x is true, False otherwise.\n\
  The builtins True and False are the only two instances of the class bool.\n\
  The class bool is a subclass of the class int, and cannot be subclassed.\
  "

@[reducible] def boolType : PyType where
  name := "bool"
  doc? := some boolType.doc
  base? := some intTypeRawRef
  isIntSubclass := true
  IsValidObject id data :=
    (id = .false ∨ id = .true) ∧
    (id = .false → data.isOf (0 : IntRef)) ∧
    (id = .true → data.isOf (1 : IntRef)) ∧
    -- redundant, but makes `simp_all` work in `LawfulType`
    data.isOfType IntRef

@[simp] theorem baseMro_boolType :
  boolType.baseMro = [intTypeRawRef, objectTypeRawRef]
:= rfl

private initialize boolTypeInitRef : InitTypeRef boolType ← initTypeRef

@[inline] def boolTypeRawRef : RawTypeRef := boolTypeInitRef.toRawTypeRef

@[simp] theorem isNonScalar_addr_boolTypeRawRef : boolTypeRawRef.addr.isNonScalar :=
  boolTypeInitRef.isNonScalar_addr

@[simp] theorem data_boolTypeRawRef : boolTypeRawRef.data = boolType :=
  boolTypeInitRef.data_toRawTypeRef
