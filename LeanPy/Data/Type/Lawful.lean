/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.Type.Ref
import LeanPy.Data.Object.ObjectTypes2

namespace LeanPy

/-! ## LawfulTypeRef -/

class LawfulTypeRef (self : TypeRef) : Prop where
  isNonScalar_addr : self.addr % 2 = 0 := by simp
  subset_objectType : self ⊆ objectTypeRef := by
    simp [TypeRef.subset_iff_mem_mro, TypeRef.mro_eq_cons_baseMro, TypeRef.eq_iff]
  isTypeSubclass_iff_subset :
    self.isTypeSubclass ↔ self ⊆ typeTypeRef := by
      simp [TypeRef.subset_iff_mem_mro, TypeRef.mro_eq_cons_baseMro, TypeRef.eq_iff]
  isIntSubclass_iff_subset :
    self.isIntSubclass ↔ self ⊆ intTypeRef := by
      simp [TypeRef.subset_iff_mem_mro, TypeRef.mro_eq_cons_baseMro, TypeRef.eq_iff]
  isStrSubclass_iff_subset :
    self.isStrSubclass ↔ self ⊆ strTypeRef := by
      simp [TypeRef.subset_iff_mem_mro, TypeRef.mro_eq_cons_baseMro, TypeRef.eq_iff]
  isValidObject_mro {id data} :
    self.IsValidObject id data → ∀ {ty}, self ⊆ ty → ty.IsValidObject id data
  := by simp_all [TypeRef.subset_iff_mem_mro, TypeRef.mro_eq_cons_baseMro]

namespace TypeRef

export LawfulTypeRef (
  isNonScalar_addr subset_objectType
  isTypeSubclass_iff_subset isIntSubclass_iff_subset isStrSubclass_iff_subset
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
instance : LawfulTypeRef intTypeRef where
instance : LawfulTypeRef boolTypeRef where
