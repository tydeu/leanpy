/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.Int.Object

namespace LeanPy

@[simp] theorem boolTypeRef_subset_intTypeRef : boolTypeRef ⊆ intTypeRef := by
  simp [TypeRef.Subtype.iff_eq_or_mem_baseMro]

/-- An instance of a subclass of `bool` that satisfies `p`. -/
def PBoolObject (p : ObjectProp) := PSubIntObject p boolTypeRef

/-- An instance of a subclass of `bool`. There are only two, `True` and `False`. -/
abbrev BoolObject := PBoolObject .Any

@[inline] def BoolObject.ofSubObject (self : SubObject boolTypeRef) : BoolObject :=
  self.upcast boolTypeRef_subset_intTypeRef

instance : Coe (SubObject boolTypeRef) BoolObject := ⟨.ofSubObject⟩

theorem Object.ty_eq_of_isBool : isBool self → self.ty = boolTypeRef := by
  simp only [isBool, isTrue, isFalse, Bool.or_eq_true, beq_iff_eq]
  intro h
  exact self.lawful_bool h

theorem Object.isBool_iff_subset : isBool self ↔ self.ty ⊆ boolTypeRef := by
  apply Iff.intro
  · intro h
    simp [ty_eq_of_isBool h]
  · simp only [isBool, isTrue, isFalse, Bool.or_eq_true, beq_iff_eq]
    exact fun h => self.lawful_subobject h |>.1

/-- Casts `self` to `BoolObject`. -/
@[inline] def Object.asBool (self : Object) (h : self.isBool) : BoolObject :=
  self.asSubObject (self.isBool_iff_subset.mp h)

/--
Casts `self` to `BoolObject` if `self` is either the `True` or `False` singleton.
Otherwise, returns `none`.
-/
@[inline] def Object.asBool? (self : Object) : Option BoolObject :=
  if h : self.isBool then some (self.asBool h) else none

namespace BoolObject

instance : Coe BoolObject Object := ⟨PObject.toObject⟩

@[inline] def getBool (self : BoolObject) : Bool :=
  self.getInt != 0

def repr (self : BoolObject) : String :=
  if self.getBool then "True" else "False"

end BoolObject

def boolTypeRef.slots : TObjectSlots BoolObject := {
  intTypeRef.slots.downcast boolTypeRef_subset_intTypeRef with
  str self := return self.repr
  repr self := return self.repr
}

@[instance] initialize boolTypeSlotsRef : TypeSlots boolTypeRef ←
  boolTypeRef.slots.stripCast boolTypeRef_subset_intTypeRef |>.mkRef

namespace BoolObject

protected def false : BoolObject :=
  boolTypeRef.mkObject .false (0 : IntRef)

instance : CoeDep Bool false BoolObject := ⟨BoolObject.false⟩

protected def true : BoolObject :=
  boolTypeRef.mkObject .true (1 : IntRef)

instance : CoeDep Bool true BoolObject := ⟨BoolObject.true⟩

def ofBool (b : Bool) : BoolObject :=
  if b then true else false

instance : Coe Bool BoolObject := ⟨ofBool⟩

end BoolObject

namespace Object

@[simp] theorem id_true : (true : Object).id = .true := rfl
@[simp] theorem ty_true : (true : Object).ty = boolTypeRef := rfl
@[simp] theorem data_true : (true : Object).data = .mk (1 : IntRef) := rfl

theorem isTrue_iff_eq_true : isTrue self ↔ self = true := by
  simp only [isTrue, id_true, eq_iff, beq_iff_eq, iff_self_and]
  intro id_eq
  have ty_eq := self.lawful_bool (.inr id_eq)
  have data_eq := (ty_eq ▸ self.lawful_object).2.2.1 id_eq
  simpa [ty_eq] using data_eq

@[simp] theorem id_false : (false : Object).id = .false := rfl
@[simp] theorem ty_false : (false : Object).ty = boolTypeRef := rfl
@[simp] theorem data_false : (false : Object).data = .mk (0 : IntRef) := rfl

theorem isFalse_iff_eq_false : isFalse self ↔ self = false := by
  simp only [isFalse, id_false, eq_iff, beq_iff_eq, iff_self_and]
  intro id_eq
  have ty_eq := self.lawful_bool (.inl id_eq)
  have data_eq := (ty_eq ▸ self.lawful_object).2.1 id_eq
  simpa [ty_eq] using data_eq

end Object
