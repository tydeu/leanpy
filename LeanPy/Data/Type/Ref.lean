/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.Type.Basic

namespace LeanPy

/-- A Python type reference. -/
structure TypeRef where
  toRawTypeRef : RawTypeRef
  deriving TypeName, Nonempty

namespace TypeRef

instance : Coe TypeRef RawTypeRef := ⟨TypeRef.toRawTypeRef⟩

@[inline] def addr (self : TypeRef) : Addr :=
  self.toRawTypeRef.addr

@[inline] def data (self : TypeRef) : PyType :=
  self.toRawTypeRef.data

theorem eq_iff : a = b ↔ addr a = addr b ∧ data a = data b := by
  cases a; cases b; simp [addr, data, FrozenRef.eq_iff]

theorem ne_of_data_ne (h : data self ≠ data other) : self ≠ other := by
  simp [eq_iff, h]

abbrev base? (self : TypeRef) : Option TypeRef :=
  self.data.base?.map (⟨·⟩)

@[inherit_doc PyType.name]
abbrev name (self : TypeRef) : String :=
  self.data.name

@[simp, inherit_doc PyType.isBaseType]
abbrev isBaseType (self : TypeRef) : Bool :=
  self.data.isBaseType

@[simp, inherit_doc PyType.isBuiltin]
abbrev isBuiltin (self : TypeRef) : Bool :=
  self.data.isBuiltin

@[simp, inherit_doc PyType.isTypeSubclass]
abbrev isTypeSubclass (self : TypeRef) : Bool :=
  self.data.isTypeSubclass

@[simp, inherit_doc PyType.isIntSubclass]
abbrev isIntSubclass (self : TypeRef) : Bool :=
  self.data.isIntSubclass

@[simp, inherit_doc PyType.isStrSubclass]
abbrev isStrSubclass (self : TypeRef) : Bool :=
  self.data.isStrSubclass

@[simp, inherit_doc PyType.isTupleSubclass]
abbrev isTupleSubclass (self : TypeRef) : Bool :=
  self.data.isTupleSubclass

@[simp, inherit_doc PyType.isDictSubclass]
abbrev isDictSubclass (self : TypeRef) : Bool :=
  self.data.isDictSubclass

@[simp, inherit_doc PyType.IsValidObject]
abbrev IsValidObject (self : TypeRef) : ObjectProp.Raw :=
  self.data.IsValidObject
