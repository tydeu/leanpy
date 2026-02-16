/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.Type.Ref

namespace LeanPy

/-! ## Fixed Type Ref -/

/--
A reference to a statically known `PyType`.

This is used to initialize types.
-/
structure InitTypeRef (ty : PyType) extends NonScalarRef PyType where
  data_eq : toNonScalarRef.data = ty

namespace InitTypeRef

attribute [simp] InitTypeRef.data_eq

instance : Nonempty (InitTypeRef ty) := ⟨⟨.null ty, rfl⟩⟩

@[inline] def toRawTypeRef (self : InitTypeRef ty) : RawTypeRef :=
  self.toFrozenRef.cast self.data_eq

@[simp] theorem data_toRawTypeRef {self : InitTypeRef ty} :
  self.toRawTypeRef.data = ty
:= by simp [toRawTypeRef]

@[simp] theorem isNonScalar_addr_toRawTypeRef {self : InitTypeRef ty} :
  self.toRawTypeRef.addr.isNonScalar
:= self.isNonScalar_addr

instance : CoeOut (InitTypeRef ty) RawTypeRef :=
  ⟨InitTypeRef.toRawTypeRef⟩

@[inline] def toTypeRef (self : InitTypeRef ty) : TypeRef :=
  ⟨self.toRawTypeRef⟩

@[simp] theorem data_toTypeRef {self : InitTypeRef ty} :
  self.toTypeRef.data = ty
:= by simp [toTypeRef, TypeRef.data]

@[simp] theorem isNonScalar_addr_toTypeRef {self : InitTypeRef ty} :
  self.toTypeRef.addr.isNonScalar
:= self.isNonScalar_addr

instance : CoeOut (InitTypeRef ty) TypeRef :=
  ⟨InitTypeRef.toTypeRef⟩

end InitTypeRef

@[inline] private unsafe def initTypeRefImpl
  (ty : PyType) : BaseIO (InitTypeRef ty)
:= pure (unsafeCast ty)

@[implemented_by initTypeRefImpl]
opaque initTypeRef {ty : PyType} : BaseIO (InitTypeRef ty) :=
  pure ⟨NonScalarRef.null ty, NonScalarRef.data_null⟩

@[inline] def mkInitTypeRef (ty : PyType) : BaseIO (InitTypeRef ty) := do
  initTypeRef

@[inline] def mkTypeRef (ty : PyType) : BaseIO TypeRef := do
  (·.toTypeRef) <$> mkInitTypeRef ty
