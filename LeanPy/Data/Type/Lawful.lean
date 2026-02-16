/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.Type.Mro
import LeanPy.Data.Type.TypeRef
import LeanPy.Data.Object.TypeRef
import LeanPy.Data.Int.TypeRef
import LeanPy.Data.Bool.TypeRef
import LeanPy.Data.None.TypeRef
import LeanPy.Data.Str.TypeRef
import LeanPy.Data.Tuple.TypeRef
import LeanPy.Data.Dict.TypeRef

namespace LeanPy

abbrev objectTypeRef : TypeRef := ⟨objectTypeRawRef⟩
abbrev typeTypeRef : TypeRef := ⟨typeTypeRawRef⟩
abbrev intTypeRef : TypeRef := ⟨intTypeRawRef⟩
abbrev boolTypeRef : TypeRef := ⟨boolTypeRawRef⟩
abbrev noneTypeRef : TypeRef := ⟨noneTypeRawRef⟩
abbrev strTypeRef : TypeRef := ⟨strTypeRawRef⟩
abbrev tupleTypeRef : TypeRef := ⟨tupleTypeRawRef⟩
abbrev dictTypeRef : TypeRef := ⟨dictTypeRawRef⟩

/-! ## LawfulTypeRef -/

class LawfulType (self : PyType) : Prop where
  eq_objectType_or_objectTypeRef_mem_baseMro :
    self = objectType ∨ objectTypeRawRef ∈ self.baseMro := by simp
  isTypeSubclass_iff : self.isTypeSubclass ↔
    self = typeType ∨ typeTypeRawRef ∈ self.baseMro := by simp [FrozenRef.eq_iff]
  isIntSubclass_iff : self.isIntSubclass ↔
    self = intType ∨ intTypeRawRef ∈ self.baseMro := by simp [FrozenRef.eq_iff]
  isStrSubclass_iff : self.isStrSubclass ↔
    self = strType ∨ strTypeRawRef ∈ self.baseMro := by simp [FrozenRef.eq_iff]
  isTupleSubclass_iff : self.isTupleSubclass ↔
    self = tupleType ∨ tupleTypeRawRef ∈ self.baseMro := by simp [FrozenRef.eq_iff]
  isDictSubclass_iff : self.isDictSubclass ↔
    self = dictType ∨ dictTypeRawRef ∈ self.baseMro := by simp [FrozenRef.eq_iff]
  isValidObject_mro {id data} : self.IsValidObject id data →
    ∀ {ty}, ty ∈ self.baseMro → ty.data.IsValidObject id data := by simp

namespace PyType

export LawfulType (
  eq_objectType_or_objectTypeRef_mem_baseMro
  isIntSubclass_iff isTypeSubclass_iff isStrSubclass_iff
  isTupleSubclass_iff isDictSubclass_iff
  isValidObject_mro
)

end PyType

class LawfulTypeRef (self : TypeRef) : Prop where
  isNonScalar_addr : self.addr.isNonScalar := by simp
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
  isTupleSubclass_iff_subset :
    self.isTupleSubclass ↔ self ⊆ tupleTypeRef := by
      simp [TypeRef.Subtype.iff_mem_mro, TypeRef.mro_eq_cons, TypeRef.eq_iff]
  isDictSubclass_iff_subset :
    self.isDictSubclass ↔ self ⊆ dictTypeRef := by
      simp [TypeRef.Subtype.iff_mem_mro, TypeRef.mro_eq_cons, TypeRef.eq_iff]
  isValidObject_mro {id data} :
    self.IsValidObject id data → ∀ {ty}, self ⊆ ty → ty.IsValidObject id data
  := by simp_all [TypeRef.Subtype.iff_mem_mro, TypeRef.mro_eq_cons]

namespace TypeRef

export LawfulTypeRef (
  isNonScalar_addr subset_objectType
  isTypeSubclass_iff_subset isIntSubclass_iff_subset isStrSubclass_iff_subset
  isTupleSubclass_iff_subset isDictSubclass_iff_subset
  isValidObject_mro
)

@[inline] def toNonScalarRef (self : TypeRef) [LawfulTypeRef self] : NonScalarRef PyType :=
  NonScalarRef.mk self.toRawTypeRef isNonScalar_addr

abbrev id (self : TypeRef) [LawfulTypeRef self] : ObjectId :=
  self.toNonScalarRef.id

end TypeRef

@[simp] theorem baseMro_objectTypeRef :
  objectTypeRef.baseMro = []
:= rfl

@[simp] theorem baseMro_typeTypeRef :
  typeTypeRef.baseMro = [objectTypeRef]
:= rfl

@[simp] theorem baseMro_noneTypeRef :
  noneTypeRef.baseMro = [objectTypeRef]
:= rfl

@[simp] theorem baseMro_strTypeRef :
  strTypeRef.baseMro = [objectTypeRef]
:= rfl

@[simp] theorem baseMro_tupleTypeRef :
  tupleTypeRef.baseMro = [objectTypeRef]
:= rfl

@[simp] theorem baseMro_dictTypeRef :
  dictTypeRef.baseMro = [objectTypeRef]
:= rfl

@[simp] theorem baseMro_intTypeRef :
  intTypeRef.baseMro = [objectTypeRef]
:= rfl

@[simp] theorem baseMro_boolTypeRef :
  boolTypeRef.baseMro = [intTypeRef, objectTypeRef]
:= rfl

instance : LawfulType objectType where
instance : LawfulType typeType where
instance : LawfulType noneType where
instance : LawfulType tupleType where
instance : LawfulType dictType where
instance : LawfulType intType where
instance : LawfulType boolType where

instance : LawfulTypeRef objectTypeRef where
instance : LawfulTypeRef typeTypeRef where
instance : LawfulTypeRef noneTypeRef where
instance : LawfulTypeRef strTypeRef where
instance : LawfulTypeRef tupleTypeRef where
instance : LawfulTypeRef dictTypeRef where
instance : LawfulTypeRef intTypeRef where
instance : LawfulTypeRef boolTypeRef where

theorem LawfulTypeRef.ofLawfulType {ty : TypeRef}
  [LawfulType ty.data] (h_addr : ty.addr.isNonScalar) (h_user : ¬ty.isBuiltin)
: LawfulTypeRef ty where
  isNonScalar_addr := h_addr
  subset_objectType := by
    grind [
      TypeRef.Subtype.iff_mem_mro, TypeRef.mro_eq_cons,
      TypeRef.mem_baseMro_iff_mem_data_baseMro,
      LawfulType.eq_objectType_or_objectTypeRef_mem_baseMro]
  isTypeSubclass_iff_subset := by
    have data_ne : ty.data ≠ typeType := by
      match h:ty.data with | .mk .. => grind
    have ty_ne : typeTypeRef ≠ ty := TypeRef.ne_of_data_ne data_ne.symm
    simp [data_ne, ty_ne, TypeRef.Subtype.iff_mem_mro, TypeRef.mem_mro_iff,
      LawfulType.isTypeSubclass_iff, TypeRef.mem_baseMro_iff_mem_data_baseMro]
  isIntSubclass_iff_subset := by
    have data_ne : ty.data ≠ intType := by
      match h:ty.data with | .mk .. => grind
    have ty_ne : intTypeRef ≠ ty := TypeRef.ne_of_data_ne data_ne.symm
    simp [data_ne, ty_ne, TypeRef.Subtype.iff_mem_mro, TypeRef.mem_mro_iff,
      LawfulType.isIntSubclass_iff, TypeRef.mem_baseMro_iff_mem_data_baseMro]
  isTupleSubclass_iff_subset := by
    have data_ne : ty.data ≠ tupleType := by
      match h:ty.data with | .mk .. => grind
    have ty_ne : tupleTypeRef ≠ ty := TypeRef.ne_of_data_ne data_ne.symm
    simp [data_ne, ty_ne, TypeRef.Subtype.iff_mem_mro, TypeRef.mem_mro_iff,
      LawfulType.isTupleSubclass_iff, TypeRef.mem_baseMro_iff_mem_data_baseMro]
  isDictSubclass_iff_subset := by
    have data_ne : ty.data ≠ dictType := by
      match h:ty.data with | .mk .. => grind
    have ty_ne : dictTypeRef ≠ ty := TypeRef.ne_of_data_ne data_ne.symm
    simp [data_ne, ty_ne,TypeRef.Subtype.iff_mem_mro, TypeRef.mem_mro_iff,
      LawfulType.isDictSubclass_iff, TypeRef.mem_baseMro_iff_mem_data_baseMro]
  isStrSubclass_iff_subset := by
    have data_ne : ty.data ≠ strType := by
      match h:ty.data with | .mk .. => grind
    have ty_ne : strTypeRef ≠ ty := TypeRef.ne_of_data_ne data_ne.symm
    simp [data_ne, ty_ne, TypeRef.Subtype.iff_mem_mro, TypeRef.mem_mro_iff,
      LawfulType.isStrSubclass_iff, TypeRef.mem_baseMro_iff_mem_data_baseMro]
  isValidObject_mro := by
    intro id data
    simp only [
      TypeRef.IsValidObject,
      TypeRef.Subtype.iff_mem_mro, TypeRef.mem_mro_iff,
      TypeRef.mem_baseMro_iff_mem_data_baseMro, forall_eq_or_imp]
    intro h
    apply And.intro h
    intro _ h_mem
    exact ty.data.isValidObject_mro h h_mem
