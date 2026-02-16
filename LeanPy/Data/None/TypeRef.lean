/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.Object.TypeRef

namespace LeanPy

@[reducible] def noneType : PyType where
  name := "NoneType"
  base? := some objectTypeRawRef
  IsValidObject id data :=
    id = .none ∧ data = .mk ()

@[simp] theorem baseMro_noneType :
  noneType.baseMro = [objectTypeRawRef]
:= rfl

private initialize noneTypeInitRef : InitTypeRef noneType ← initTypeRef

@[inline] def noneTypeRawRef : RawTypeRef := noneTypeInitRef.toRawTypeRef

@[simp] theorem isNonScalar_addr_noneTypeRawRef : noneTypeRawRef.addr.isNonScalar :=
  noneTypeInitRef.isNonScalar_addr

@[simp] theorem data_noneTypeRawRef : noneTypeRawRef.data = noneType :=
  noneTypeInitRef.data_toRawTypeRef
