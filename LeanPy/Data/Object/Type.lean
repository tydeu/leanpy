/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.Object.Id
import LeanPy.Data.Object.Data

namespace LeanPy

/-! ## Object Type -/

/-- A Python type. -/
-- The `Py` prefix to avoids a clash with the Lean `Type` keyword.
structure PyType where
  /-- The type's name -/
  name : String
  /-- The type's documentation string or `none` if undefined. -/
  doc? : Option String := none
  /-- The type's parent. -/
  base? : Option (FrozenRef PyType) := none
  /--
  Is this type is a legal base for other types.
  If `false`, this type cannot be legally subtyped.

  Equivalent in functionality to CPython's `Py_TPFLAGS_BASETYPE`.
  -/
  isBaseType : Bool := true
  /--
  Is this a subclass of `type`?

  Equivalent in functionality to CPython's `Py_TPFLAGS_TYPE_SUBCLASS`.
  -/
  isTypeSubclass : Bool := false
  /--
  Is this a subclass of `str`?

  Equivalent in functionality to CPython's `Py_TPFLAGS_UNICODE_SUBCLASS`.
  -/
  isStrSubclass : Bool := false
  /--
  Is this a subclass of `int`?

  Equivalent in functionality to CPython's `Py_TPFLAGS_LONG_SUBCLASS`.
  -/
  isIntSubclass : Bool := false
  /--
  Returns whether the field combination could be a valid object of this type.

  This can be an over-approximation. That is, it may hold for objects
  which are not objects of this type.
  -/
  IsValidObject (id : ObjectId) (data : ObjectData) : Prop := True
  deriving Nonempty

namespace PyType

/-- The type's method resolution order. -/
@[inline] def mro (self : PyType) : List PyType :=
  self :: match self with
    | {base? := none, ..} => []
    | {base? := some base, ..} => mro base.data

@[inline] def baseMro (self : PyType) : List PyType :=
  match self with
  | {base? := none, ..} => []
  | {base? := some base, ..} => mro base.data

theorem mro_def : mro self = self :: baseMro self := by
  unfold mro baseMro; rfl

theorem mem_mro_iff : ty ∈ mro self ↔ ty = self ∨ ty ∈ baseMro self := by
  simp [mro_def]

@[simp] theorem self_mem_mro : self ∈ mro self := by
  simp [mro_def]

@[simp] theorem baseMro_subset_mro : baseMro self ⊆ mro self := by
  simp [mro_def]

theorem mem_mro_of_mem_baseMro : ty ∈ baseMro self → ty ∈ mro self :=
  List.subset_def.mp baseMro_subset_mro

private theorem mem_mro_trans :
  ty₁ ∈ mro ty₂ → ty₂ ∈ mro self → ty₁ ∈ mro self
:= by
  revert ty₂
  let {base?, ..} := self
  cases base? with
  | none =>
    intro ty₂ h₁
    simp only [mro, List.mem_cons, List.not_mem_nil, or_false]
    intro h₂
    simpa [h₂, mro] using h₁
  | some base =>
    intro ty₂ h₁
    simp only [mro, List.mem_cons]
    intro h₂
    cases h₂ with
    | inl h₂ => simpa [h₂, mro] using h₁
    | inr h₂ => exact Or.inr <| mem_mro_trans h₁ h₂

def IsSubtype (self other : PyType) : Prop :=
  other ∈ self.mro

instance : HasSubset PyType := ⟨PyType.IsSubtype⟩

theorem subset_iff_mem_mro : a ⊆ b ↔ b ∈ mro a := Iff.rfl

@[simp] theorem subset_rfl {self : PyType} : self ⊆ self :=  self_mem_mro

theorem subset_trans {a b c : PyType} : a ⊆ b → b ⊆ c → a ⊆ c  := by
  simp only [subset_iff_mem_mro]
  exact fun h₁ h₂ => mem_mro_trans h₂ h₁

end PyType

/-! ## Object Type Ref -/

abbrev TypeRef := FrozenRef PyType

noncomputable instance : SizeOf TypeRef :=
  inferInstanceAs (SizeOf (FrozenRef PyType))

namespace TypeRef

instance : TypeName TypeRef := unsafe (.mk _ ``TypeRef)

/-- The type's method resolution order. -/
@[inline] def mro (self : TypeRef) : List TypeRef :=
  self :: go self.data
where go self :=
  match self with
  | {base? := none, ..} => []
  | {base? := some base, ..} => mro base

@[inline] def baseMro (self : TypeRef) : List TypeRef :=
  match self.data with
  | {base? := none, ..} => []
  | {base? := some base, ..} => mro base

instance : SizeOf TypeRef := ⟨(·.baseMro.length)⟩

@[simp] theorem sizeOf_def {self : TypeRef} :
  sizeOf self = self.baseMro.length
:= rfl

theorem mro_def : mro self = self :: baseMro self := by
  unfold mro baseMro mro.go; simp

@[simp] theorem length_mro : (mro self).length = self.baseMro.length + 1 := by
  simp [mro_def]

theorem mem_mro_iff : ty ∈ mro self ↔ ty = self ∨ ty ∈ baseMro self := by
  simp [mro_def]

@[simp] theorem self_mem_mro : self ∈ mro self := by
  simp [mro_def]

@[simp] theorem baseMro_subset_mro : baseMro self ⊆ mro self := by
  simp [mro_def]

private theorem sup_mem_sub :
  sup ∈ mro sub → ∀ {ty}, ty ∈ mro sup → ty ∈ mro sub
:= by
  simp only [mem_mro_iff]
  match h_sub:sub.data with
  | {base? := none, ..} =>
    simp only [baseMro, h_sub, List.not_mem_nil, or_false]
    intro sup_eq_sub
    intro ty
    simp [sup_eq_sub, h_sub]
  | {base? := some base, ..} =>
    have sub_baseMro : sub.baseMro = mro base := by
      simp [h_sub, baseMro]
    simp only [sub_baseMro]
    intro h ty
    cases h with
    | inl sup_eq_sub =>
      simp [sup_eq_sub, sub_baseMro]
    | inr sup_mem_mro_base =>
      simp only [← mem_mro_iff]
      intro ty_mem
      exact Or.inr <| sup_mem_sub sup_mem_mro_base ty_mem
termination_by sub
decreasing_by simp [sub_baseMro]

def Subtype (self other : TypeRef) : Prop :=
  other ∈ self.mro

instance : HasSubset TypeRef := ⟨TypeRef.Subtype⟩

theorem subset_iff_mem_mro : a ⊆ b ↔ b ∈ mro a := Iff.rfl

theorem subset_iff_eq_or_mem_baseMro : a ⊆ b ↔ (a = b ∨ b ∈ baseMro a) := by
  grind [subset_iff_mem_mro, mro_def]

@[simp] theorem Subtype.rfl {self : TypeRef} : self ⊆ self := self_mem_mro

@[simp] theorem Subtype.refl (self : TypeRef) : self ⊆ self := self_mem_mro

theorem Subtype.trans {a b c : TypeRef} : a ⊆ b → b ⊆ c → a ⊆ c  := by
  simp only [subset_iff_mem_mro]
  exact fun h₁ h₂ => sup_mem_sub h₁ h₂

instance : Trans (Subset : TypeRef → TypeRef → Prop) Subset Subset :=
  ⟨Subtype.trans⟩

@[inherit_doc PyType.name]
abbrev name (self : TypeRef) : String :=
  self.data.name

@[simp, inherit_doc PyType.isTypeSubclass]
abbrev isTypeSubclass (self : TypeRef) : Bool :=
  self.data.isTypeSubclass

@[simp, inherit_doc PyType.isIntSubclass]
abbrev isIntSubclass (self : TypeRef) : Bool :=
  self.data.isIntSubclass

@[simp, inherit_doc PyType.isStrSubclass]
abbrev isStrSubclass (self : TypeRef) : Bool :=
  self.data.isStrSubclass

@[simp, inherit_doc PyType.IsValidObject]
abbrev IsValidObject (self : TypeRef) (id : ObjectId) (data : ObjectData) : Prop :=
  self.data.IsValidObject id data

end TypeRef

structure DTypeRef (ty : PyType) extends NonScalarRef PyType where
  data_eq : toNonScalarRef.data = ty

namespace DTypeRef

attribute [simp] data_eq

instance : Nonempty (DTypeRef ty) := ⟨⟨.null ty, rfl⟩⟩

@[inline] def toTypeRef (self : DTypeRef ty) : TypeRef :=
  self.toFrozenRef.cast self.data_eq

@[simp] theorem isNonScalar_addr_toTypeRef {self : DTypeRef ty} :
  self.toTypeRef.addr % 2 = 0
:= self.addr_mod_two

end DTypeRef

instance : CoeOut (DTypeRef ty) TypeRef :=
  ⟨DTypeRef.toTypeRef⟩

@[inline] private unsafe def mkTypeRefImpl
  (ty : PyType) : BaseIO (DTypeRef ty)
:= pure (unsafeCast ty)

@[implemented_by mkTypeRefImpl]
opaque mkDTypeRef (ty : PyType) : BaseIO (DTypeRef ty) :=
  pure ⟨NonScalarRef.null ty, NonScalarRef.data_null⟩

@[inline] def mkTypeRef (ty : PyType) : BaseIO TypeRef := do
  (·.toTypeRef) <$> mkDTypeRef ty
