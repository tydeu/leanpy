/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.Object.Slots

namespace LeanPy

/- An instance of type `none`. There is only one: the constant `None`. -/
def NoneObject := SubObject noneTypeRef

namespace NoneObject

instance : Coe NoneObject Object := ⟨PObject.toObject⟩

protected def hash : Hash :=
  hash ObjectId.none

protected def repr : String :=
  "None"

end NoneObject

def noneTypeRef.slots : TObjectSlots NoneObject where
  hash _ := return NoneObject.hash
  beq _ other := return other.isNone
  bne _ other := return other.isNotNone
  call self _ _ := throwNotCallable self.ty.name
  bool _ := return false
  repr _ := return NoneObject.repr

@[instance] initialize noneTypeSlotsRef : TypeSlots noneTypeRef ←
  noneTypeRef.slots.mkRef

namespace Object

protected def none : NoneObject :=
  noneTypeRef.mkObject .none ()

instance : CoeDep (Option α) none Object := ⟨Object.none⟩

instance : Inhabited Object := ⟨none⟩

@[simp] theorem isNone_none : isNone none := rfl
@[simp] theorem id_none : (none : Object).id = .none := rfl
@[simp] theorem ty_none : (none : Object).ty = noneTypeRef := rfl
@[simp] theorem data_none : (none : Object).data = .mk () := rfl

theorem isNone_iff_eq_none : isNone self ↔ self = none := by
  simp only [isNone, id_none, eq_iff, beq_iff_eq, iff_self_and]
  intro id_eq
  have ty_eq := self.lawful_none id_eq
  have data_eq := (ty_eq ▸ self.lawful_object).2
  simp [ty_eq, data_eq]

instance : Inhabited Object := ⟨none⟩

end Object

namespace NoneObject

instance : CoeDep (Option α) none NoneObject := ⟨Object.none⟩

@[simp] theorem eq_none : (self : NoneObject) = none := by
  suffices h : self.isNone by
    simp [← self.toObject_inj, self.isNone_iff_eq_none.mp h]
  simp [Object.isNone, self.lawful_subobject.1]

end NoneObject
