/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.Type.Ref

namespace LeanPy

/-- The type's method resolution order (excluding itself). -/
@[inline] def PyType.baseMro (self : PyType) : List RawTypeRef :=
  match self with
  | {base? := none, ..} => []
  | {base? := some base, ..} => base :: baseMro base.data
termination_by structural self

/-- The type's method resolution order (excluding itself). -/
abbrev RawTypeRef.baseMro (self : RawTypeRef) : List RawTypeRef :=
  self.data.baseMro

@[simp] theorem RawTypeRef.baseMro_eq_data_baseMro :
  baseMro self = self.data.baseMro
:= by rfl

/-- The type's method resolution order. -/
@[inline] def RawTypeRef.mro (self : RawTypeRef) : List RawTypeRef :=
  self :: self.data.baseMro

theorem RawTypeRef.mro_eq_cons :
  mro self = self :: self.baseMro := rfl

theorem PyType.baseMro_eq_elim :
  baseMro self = self.base?.elim [] RawTypeRef.mro
:= by
  match self with
  | {base? := none, ..} => rfl
  | {base? := some base, ..} => rfl

/-- The type's method resolution order (excluding itself). -/
@[inline] private def PyType.baseMro' (self : PyType) : List TypeRef :=
  match self with
  | {base? := none, ..} => []
  | {base? := some base, ..} => ⟨base⟩ :: baseMro' base.data
termination_by structural self

/-- The type's method resolution order (excluding itself). -/
private abbrev RawTypeRef.baseMro' (self : RawTypeRef) : List TypeRef :=
  self.data.baseMro'

@[simp] private theorem RawTypeRef.baseMro'_eq_data_baseMro :
  baseMro' self = self.data.baseMro' := rfl

/-- The type's method resolution order. -/
@[inline] private def RawTypeRef.mro' (self : RawTypeRef) : List TypeRef :=
  ⟨self⟩ :: self.baseMro'

private theorem PyType.baseMro'_eq_elim :
  baseMro' self = self.base?.elim [] RawTypeRef.mro'
:= by
  match self with
  | {base? := none, ..} => rfl
  | {base? := some base, ..} => rfl

namespace TypeRef

/-- The type's method resolution order (excluding itself). -/
@[inline] def baseMro (self : TypeRef) : List TypeRef :=
  self.data.baseMro'

/-- The type's method resolution order. -/
@[inline] def mro (self : TypeRef) : List TypeRef :=
  self :: self.baseMro

theorem baseMro_eq_elim : baseMro self = self.base?.elim [] mro := by
  simp only [baseMro, PyType.baseMro'_eq_elim, base?]
  unfold mro RawTypeRef.mro' baseMro RawTypeRef.baseMro'
  cases self.data.base? <;> simp

theorem mro_eq_cons : mro self = self :: baseMro self := by rfl

instance : SizeOf TypeRef := ⟨(·.baseMro.length)⟩

@[simp] theorem sizeOf_def {self : TypeRef} :
  sizeOf self = self.baseMro.length
:= rfl

@[simp] theorem length_mro : (mro self).length = self.baseMro.length + 1 := by
  simp [mro_eq_cons]

theorem mem_mro_iff : ty ∈ mro self ↔ ty = self ∨ ty ∈ baseMro self := by
  simp [mro_eq_cons]

@[simp] theorem self_mem_mro : self ∈ mro self := by
  simp [mro_eq_cons]

@[simp] theorem baseMro_subset_mro : baseMro self ⊆ mro self := by
  simp [mro_eq_cons]

theorem mem_baseMro_iff_mem_data_baseMro :
  ty ∈ baseMro self ↔ ty.toRawTypeRef ∈ self.data.baseMro
:= by
  simp only [baseMro_eq_elim, PyType.baseMro_eq_elim, base?]
  match h:self.data.base? with
  | none => simp
  | some base =>
    have baseMro_self : baseMro self = mro ⟨base⟩ := by
       simp [baseMro_eq_elim, base?, h]
    let ⟨raw⟩ := ty
    let ih := mem_baseMro_iff_mem_data_baseMro (ty := ⟨raw⟩) (self := ⟨base⟩)
    simp [mro_eq_cons, RawTypeRef.mro_eq_cons, ih]
termination_by self
decreasing_by simp [baseMro_self]

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

theorem Subtype.iff_mem_mro : a ⊆ b ↔ b ∈ mro a := Iff.rfl

def SSubtype (self other : TypeRef) : Prop :=
  other ∈ self.baseMro

instance : HasSSubset TypeRef := ⟨TypeRef.SSubtype⟩

theorem SSubtype.iff_mem_baseMro : a ⊂ b ↔ b ∈ baseMro a := Iff.rfl

theorem Subtype.iff_eq_or_mem_baseMro : a ⊆ b ↔ (a = b ∨ b ∈ baseMro a) := by
  grind [Subtype.iff_mem_mro, mem_mro_iff]

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
  simp only [Subtype.iff_mem_mro]
  exact fun h₁ h₂ => sup_mem_mro_sub h₁ h₂

instance : Trans (Subset : TypeRef → TypeRef → Prop) Subset Subset :=
  ⟨Subtype.trans⟩

end TypeRef
