/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.Object.Slots

namespace LeanPy

/-! ## `int` Objects -/

/- An instance of a subtype of `int` that satisfies `p`. -/
def PIntObject (p : ObjectProp) := PSubObject p intTypeRef

/- An instance of the type `ty` that satisfies `p` and subclasses `int` . -/
abbrev PSubIntObject (p : ObjectProp) (ty : TypeRef) := PIntObject (p.AndInstance ty)

/- An instance of a subclass of `int`. -/
abbrev IntObject := PIntObject .Any

@[inline] def Object.isInt (self : Object) : Bool :=
  self.ty.isIntSubclass

theorem Object.isInt_iff_subset : isInt self ↔ self.ty ⊆ intTypeRef :=
  self.ty.isIntSubclass_iff_subset

@[inline] def Object.asInt (self : Object) (h : self.isInt) : IntObject :=
  self.asSubObject (self.ty.isIntSubclass_iff_subset.mp h)

@[inline] def Object.asInt? (self : Object) : Option IntObject :=
  if h : self.isInt then some (self.asInt h) else none

namespace PIntObject

instance : CoeOut (PIntObject p) Object := ⟨PObject.toObject⟩

theorem ty_subset_intType {self : PIntObject p} : self.ty ⊆ intTypeRef :=
  self.property.2

theorem isInt_toObject (self : PIntObject p) : self.toObject.isInt :=
  self.isInt_iff_subset.mpr self.ty_subset_intType

@[inline] nonrec def asInt (self : PIntObject p) : IntObject :=
  self.asInt self.isInt_toObject

@[inline] def getIntRef (self : PIntObject p) : IntRef :=
  self.getData self.lawful_subobject

@[inline] def getInt (self : PIntObject p) : Int :=
  self.getIntRef.toInt

@[inline] protected def beq (self other : PIntObject p) : Bool :=
  self.getInt == other.getInt

@[inline] protected def bne (self other : PIntObject p) : Bool :=
  self.getInt != other.getInt

@[inline] protected def hash (self : PIntObject p) : Hash :=
  hash self.getInt

@[inline] def toBool (self : PIntObject p) : Bool :=
  self.getInt != 0

@[inline] def repr (self : PIntObject p) : String :=
  toString self.getInt

end PIntObject

def intTypeRef.slots : TObjectSlots IntObject where
  hash self := return self.hash
  beq self other := return other.asInt?.any self.beq
  bne self other := return other.asInt?.all self.bne
  bool self := return self.toBool
  repr self := return self.repr

@[instance] initialize intTypeSlotsRef : TypeSlots intTypeRef ←
  intTypeRef.slots.mkRef

@[inline] def IntObject.ofIntRef (n : IntRef) : IntObject :=
  intTypeRef.mkObject n.id  n

instance : OfNat IntObject 0 := ⟨.ofIntRef 0⟩
instance : Coe IntRef IntObject := ⟨.ofIntRef⟩

theorem IntObject.zero_eq : (0 : IntObject) = .ofIntRef 0 := rfl

@[inline] def mkIntObject (n : Int) : BaseIO IntObject := do
  IntObject.ofIntRef <$> mkIntRef n

instance : OfNat Object 0 := ⟨(0 : IntObject)⟩
