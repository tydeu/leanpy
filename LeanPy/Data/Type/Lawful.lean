/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.Type.Mro
import LeanPy.Data.Type.TypeRef
import LeanPy.Data.Object.TypeRef
import LeanPy.Data.Bool.TypeRef
import LeanPy.Data.Int.TypeRef
import LeanPy.Data.None.TypeRef
import LeanPy.Data.Str.TypeRef
import LeanPy.Data.Dict.TypeRef

namespace LeanPy

/-! ## LawfulTypeRef -/

class LawfulType (self : PyType) : Prop where
  objectType_mem_baseMro : objectTypeRef ∈ self.baseMro
  isTypeSubclass_iff :
    self.isTypeSubclass ↔ self = typeTypeRef.data ∨ typeTypeRef ∈ self.baseMro
  isIntSubclass_iff :
    self.isIntSubclass ↔ self = intTypeRef.data ∨ intTypeRef ∈ self.baseMro
  isStrSubclass_iff :
    self.isStrSubclass ↔ self = strTypeRef.data ∨ strTypeRef ∈ self.baseMro
  isDictSubclass_iff :
    self.isDictSubclass ↔ self = dictTypeRef.data ∨ dictTypeRef ∈ self.baseMro
  isValidObject_mro {id data} :
    self.IsValidObject id data → ∀ {ty}, ty ∈ self.baseMro → ty.IsValidObject id data

namespace PyType

export LawfulType (
  objectType_mem_baseMro
  isIntSubclass_iff isTypeSubclass_iff isStrSubclass_iff
  isValidObject_mro
)

end PyType

class LawfulTypeRef (self : TypeRef) : Prop where
  isNonScalar_addr : self.addr % 2 = 0 := by simp
  subset_objectType : self ⊆ objectTypeRef := by
    simp [TypeRef.Subtype.iff_mem_mro, TypeRef.mem_mro_iff, TypeRef.eq_iff]
  isTypeSubclass_iff_subset :
    self.isTypeSubclass ↔ self ⊆ typeTypeRef := by
      simp [TypeRef.Subtype.iff_mem_mro, TypeRef.mem_mro_iff, TypeRef.eq_iff]
  isIntSubclass_iff_subset :
    self.isIntSubclass ↔ self ⊆ intTypeRef := by
      simp [TypeRef.Subtype.iff_mem_mro, TypeRef.mem_mro_iff, TypeRef.eq_iff]
  isStrSubclass_iff_subset :
    self.isStrSubclass ↔ self ⊆ strTypeRef := by
      simp [TypeRef.Subtype.iff_mem_mro, TypeRef.mem_mro_iff, TypeRef.eq_iff]
  isDictSubclass_iff_subset :
    self.isDictSubclass ↔ self ⊆ dictTypeRef := by
      simp [TypeRef.Subtype.iff_mem_mro, TypeRef.mro_eq_cons_baseMro, TypeRef.eq_iff]
  isValidObject_mro {id data} :
    self.IsValidObject id data → ∀ {ty}, self ⊆ ty → ty.IsValidObject id data
  := by simp_all [TypeRef.Subtype.iff_mem_mro, TypeRef.mro_eq_cons_baseMro]

theorem TypeRef.ne_of_data_ne (h : data self ≠ data other) : self ≠ other := by
  simp [TypeRef.eq_iff, h]

namespace TypeRef

export LawfulTypeRef (
  isNonScalar_addr subset_objectType
  isTypeSubclass_iff_subset isIntSubclass_iff_subset
  isStrSubclass_iff_subset isDictSubclass_iff_subset
  isValidObject_mro
)

@[inline] def toNonScalarRef (self : TypeRef) [LawfulTypeRef self] : NonScalarRef PyType :=
  NonScalarRef.mk self.toRawTypeRef isNonScalar_addr

abbrev id (self : TypeRef) [LawfulTypeRef self] : ObjectId :=
  self.toNonScalarRef.id

end TypeRef

@[simp] theorem data_objectTypeRef : objectTypeRef.data = objectType := rfl

@[simp] theorem mro_objectTypeRef :
  objectTypeRef.baseMro = []
:= rfl

@[simp] theorem data_typeTypeRef : typeTypeRef.data = typeType := rfl

@[simp] theorem baseMro_typeTypeRef :
  typeTypeRef.baseMro = [objectTypeRef]
:= rfl

@[simp] theorem data_noneTypeRef : noneTypeRef.data = noneType := rfl

@[simp] theorem baseMro_noneTypeRef :
  noneTypeRef.baseMro = [objectTypeRef]
:= rfl

@[simp] theorem data_strTypeRef : strTypeRef.data = strType := rfl

@[simp] theorem baseMro_strTypeRef :
  strTypeRef.baseMro = [objectTypeRef]
:= rfl

@[simp] theorem data_dictTypeRef : dictTypeRef.data = dictType := rfl

@[simp] theorem baseMro_dictTypeRef :
  dictTypeRef.baseMro = [objectTypeRef]
:= rfl

@[simp] theorem data_intTypeRef : intTypeRef.data = intType := rfl

@[simp] theorem baseMro_intTypeRef :
  intTypeRef.baseMro = [objectTypeRef]
:= rfl

@[simp] theorem data_boolTypeRef : boolTypeRef.data = boolType := rfl

@[simp] theorem baseMro_boolTypeRef :
  boolTypeRef.baseMro = [intTypeRef, objectTypeRef]
:= rfl

instance : LawfulTypeRef objectTypeRef where
instance : LawfulTypeRef typeTypeRef where
instance : LawfulTypeRef noneTypeRef where
instance : LawfulTypeRef strTypeRef where
instance : LawfulTypeRef dictTypeRef where
instance : LawfulTypeRef intTypeRef where
instance : LawfulTypeRef boolTypeRef where

theorem LawfulTypeRef.ofLawfulType {ty : TypeRef}
  [LawfulType ty.data] (h_addr : ty.addr % 2 = 0) (h_user : ¬ty.isBuiltin)
: LawfulTypeRef ty where
  isNonScalar_addr := h_addr
  subset_objectType := by
    grind [TypeRef.Subtype.iff_mem_mro, TypeRef.mro_eq_cons_baseMro,
      TypeRef.baseMro_eq_data_baseMro, LawfulType.objectType_mem_baseMro]
  isTypeSubclass_iff_subset := by
    have data_ne : ty.data ≠ typeType := by
      match h:ty.data with | .mk .. => grind
    have ty_ne : typeTypeRef ≠ ty := TypeRef.ne_of_data_ne data_ne.symm
    simp [data_ne, ty_ne, TypeRef.Subtype.iff_mem_mro, TypeRef.mem_mro_iff,
      LawfulType.isTypeSubclass_iff, TypeRef.baseMro_eq_data_baseMro]
  isIntSubclass_iff_subset := by
    have data_ne : ty.data ≠ intType := by
      match h:ty.data with | .mk .. => grind
    have ty_ne : intTypeRef ≠ ty := TypeRef.ne_of_data_ne data_ne.symm
    simp [data_ne, ty_ne, TypeRef.Subtype.iff_mem_mro, TypeRef.mem_mro_iff,
      LawfulType.isIntSubclass_iff, TypeRef.baseMro_eq_data_baseMro]
  isDictSubclass_iff_subset := by
    have data_ne : ty.data ≠ dictType := by
      match h:ty.data with | .mk .. => grind
    have ty_ne : dictTypeRef ≠ ty := TypeRef.ne_of_data_ne data_ne.symm
    simp [data_ne, ty_ne,TypeRef.Subtype.iff_mem_mro, TypeRef.mem_mro_iff,
      LawfulType.isDictSubclass_iff, TypeRef.baseMro_eq_data_baseMro]
  isStrSubclass_iff_subset := by
    have data_ne : ty.data ≠ strType := by
      match h:ty.data with | .mk .. => grind
    have ty_ne : strTypeRef ≠ ty := TypeRef.ne_of_data_ne data_ne.symm
    simp [data_ne, ty_ne,TypeRef.Subtype.iff_mem_mro, TypeRef.mem_mro_iff,
      LawfulType.isStrSubclass_iff, TypeRef.baseMro_eq_data_baseMro]
  isValidObject_mro := by
    intro id data
    simp only [
      TypeRef.IsValidObject,
      TypeRef.Subtype.iff_mem_mro, TypeRef.mem_mro_iff,
      TypeRef.baseMro_eq_data_baseMro, forall_eq_or_imp]
    intro h
    apply And.intro h
    apply LawfulType.isValidObject_mro
    exact h
