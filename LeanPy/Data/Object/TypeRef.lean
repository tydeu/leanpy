/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.Object.Type

namespace LeanPy

structure TypeRef where
  toRawTypeRef : RawTypeRef
  deriving TypeName, Nonempty

namespace TypeRef

instance : Coe TypeRef RawTypeRef := ⟨TypeRef.toRawTypeRef⟩

@[inline] def addr (self : TypeRef) : USize :=
  self.toRawTypeRef.addr

@[inline] def data (self : TypeRef) : PyType :=
  self.toRawTypeRef.data

theorem eq_iff : a = b ↔ addr a = addr b ∧ data a = data b := by
  cases a; cases b; simp [addr, data, FrozenRef.eq_iff]

abbrev base? (self : TypeRef) : Option TypeRef :=
  self.data.base?.map (⟨·⟩)

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
abbrev IsValidObject (self : TypeRef) : ObjectProp.Raw :=
  self.data.IsValidObject

/-- The type's method resolution order. -/
@[inline] def mro (self : TypeRef) : List TypeRef :=
  self :: go self.toRawTypeRef.data
where go self :=
  match self with
  | {base? := none, ..} => []
  | {base? := some base, ..} => ⟨base⟩ :: go base.data
termination_by structural self

@[inline] def baseMro (self : TypeRef) : List TypeRef :=
  self.base?.elim [] mro

theorem baseMro_eq_elim : baseMro self = self.base?.elim [] mro := rfl

theorem mro_eq_cons_baseMro : mro self = self :: baseMro self := by
  unfold mro mro.go
  simp only [baseMro_eq_elim, Option.elim, Option.map, base?, data]
  match self.toRawTypeRef.data with
  | {base? := none, ..} => rfl
  | {base? := some base, ..} => simp only [mro]

instance : SizeOf TypeRef := ⟨(·.baseMro.length)⟩

@[simp] theorem sizeOf_def {self : TypeRef} :
  sizeOf self = self.baseMro.length
:= rfl

@[simp] theorem length_mro : (mro self).length = self.baseMro.length + 1 := by
  simp [mro_eq_cons_baseMro]

theorem mem_mro_iff : ty ∈ mro self ↔ ty = self ∨ ty ∈ baseMro self := by
  simp [mro_eq_cons_baseMro]

@[simp] theorem self_mem_mro : self ∈ mro self := by
  simp [mro_eq_cons_baseMro]

@[simp] theorem baseMro_subset_mro : baseMro self ⊆ mro self := by
  simp [mro_eq_cons_baseMro]

private theorem sup_mem_baseMro_sub :
  sup ∈ baseMro sub → ∀ {ty}, ty ∈ baseMro sup → ty ∈ baseMro sub
:= by
  match h_sub:sub.base? with
  | none =>
    simp only [baseMro_eq_elim, h_sub, Option.elim_none, List.not_mem_nil]
    intro sup_eq_sub
    intro ty
    simp [sup_eq_sub]
  | some base =>
    have sub_baseMro : sub.baseMro = mro base := by
      simp [h_sub, baseMro_eq_elim]
    simp only [sub_baseMro, mem_mro_iff]
    intro h ty
    intro ty_mem
    apply Or.inr
    cases h with
    | inl sup_eq_sub => simpa [sup_eq_sub] using ty_mem
    | inr sup_mem_mro_base => exact sup_mem_baseMro_sub sup_mem_mro_base ty_mem
termination_by sub
decreasing_by simp [sub_baseMro]

private theorem sup_mem_mro_sub :
  sup ∈ mro sub → ∀ {ty}, ty ∈ mro sup → ty ∈ mro sub
:= by
  simp only [mem_mro_iff]
  rintro ⟨_ | _⟩ _ ⟨_ | _⟩
  · simp
  · simp [*]
  · simp [*]
  · apply Or.inr
    next sup_mem ty ty_mem =>
    exact sup_mem_baseMro_sub sup_mem ty_mem

def Subtype (self other : TypeRef) : Prop :=
  other ∈ self.mro

instance : HasSubset TypeRef := ⟨TypeRef.Subtype⟩

theorem subset_iff_mem_mro : a ⊆ b ↔ b ∈ mro a := Iff.rfl

def SSubtype (self other : TypeRef) : Prop :=
  other ∈ self.baseMro

instance : HasSSubset TypeRef := ⟨TypeRef.SSubtype⟩

theorem SSubtype.iff_mem_baseMro : a ⊂ b ↔ b ∈ baseMro a := Iff.rfl

theorem Subtype.iff_eq_or_mem_baseMro : a ⊆ b ↔ (a = b ∨ b ∈ baseMro a) := by
  grind [subset_iff_mem_mro, mem_mro_iff]

theorem Subtype.iff_eq_or_ssubset {a b : TypeRef} : a ⊆ b ↔ (a = b ∨ a ⊂ b) := by
  rw [Subtype.iff_eq_or_mem_baseMro, SSubtype.iff_mem_baseMro]

@[simp] theorem Subtype.rfl {self : TypeRef} : self ⊆ self := self_mem_mro

@[simp] theorem Subtype.refl (self : TypeRef) : self ⊆ self := self_mem_mro

theorem SSubtype.trans {a b c : TypeRef} : a ⊂ b → b ⊂ c → a ⊂ c := by
  simp only [SSubtype.iff_mem_baseMro]
  exact fun h₁ h₂ => sup_mem_baseMro_sub h₁ h₂

instance : Trans (SSubset : TypeRef → TypeRef → Prop) SSubset SSubset :=
  ⟨SSubtype.trans⟩

theorem Subtype.trans {a b c : TypeRef} : a ⊆ b → b ⊆ c → a ⊆ c  := by
  simp only [subset_iff_mem_mro]
  exact fun h₁ h₂ => sup_mem_mro_sub h₁ h₂

instance : Trans (Subset : TypeRef → TypeRef → Prop) Subset Subset :=
  ⟨Subtype.trans⟩

end TypeRef
