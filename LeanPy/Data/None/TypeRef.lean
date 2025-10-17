/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.Object.TypeRef

namespace LeanPy

@[reducible] def noneType : PyType where
  name := "NoneType"
  base? := some objectTypeRef
  IsValidObject id data :=
    id = .none ∧ data = .mk ()

initialize noneTypeRef.init : InitTypeRef noneType ← initTypeRef

abbrev noneTypeRef : TypeRef := noneTypeRef.init.toTypeRef
