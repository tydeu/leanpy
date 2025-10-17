/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.Object.Object

namespace LeanPy

/-! ## `type` -/

/- An instance of a subclass of `type` that satisfies `p`. -/
abbrev PTypeObject (p : ObjectProp) := PSubObject p typeTypeRef

/- An instance of `type` or one of its subtypes. -/
def TypeObject := PTypeObject .Any

/-- Returns whether this object is an instance of a subtype of `type`. -/
@[inline] def Object.isType (self : Object) : Bool :=
  self.ty.isTypeSubclass

/-- Casts `self` to `TypeObject`. -/
@[inline] def Object.asType (self : Object) (h : self.isType) : TypeObject :=
  self.asSubObject (self.ty.isTypeSubclass_iff_subset.mp h)

/--
Casts `self` to `TypeObject` if `self` is instance of a subtype of `type`.
Otherwise, returns `none`.
-/
@[inline] def Object.asType? (self : Object) : Option TypeObject :=
  if h : self.isType then some (self.asType h) else none

namespace TypeObject

instance : Coe TypeObject Object := ⟨PObject.toObject⟩

theorem isType_toObject (self : TypeObject) : self.toObject.isType :=
  self.ty.isTypeSubclass_iff_subset.mpr self.ty_subset

@[inline] def getTypeRef (self : TypeObject) : TypeRef :=
  ⟨self.getData (self.lawful_subobject : typeType.IsValidObject _ _).2⟩

@[inline] def getType (self : TypeObject) : PyType :=
  self.getTypeRef.data

/--
Returns the name of the type.

This is equivalent to the Python `vars(type)['__name__'].__get__(self)`.
-/
def name (self : TypeObject) : String :=
  self.getType.name

/--
Returns a string representation of the type.

This is equivalent to the Python `type.__repr__(self)`.
-/
def repr (self : TypeObject) : String :=
  s!"<class '{self.name}'>"

end TypeObject

def typeTypeRef.slots : TObjectSlots TypeObject where
  hash self := return self.asObject.hash
  beq self other := return self.asObject.beq other
  bne self other := return self.asObject.bne other
  bool _ := return true
  repr self := return self.repr

@[instance] initialize typeTypeSlotsRef : TypeSlots typeTypeRef ←
  typeTypeRef.slots.mkRef

namespace TypeObject

def ofInitTypeRef (ref : InitTypeRef ty) : TypeObject :=
  typeTypeRef.mkObject ref.id  ref.toTypeRef.toRawTypeRef

instance : CoeOut (InitTypeRef ty) TypeObject := ⟨ofInitTypeRef⟩

def ofTypeRef (ty : TypeRef) [LawfulTypeRef ty] : TypeObject :=
  typeTypeRef.mkObject ty.id  ty.toRawTypeRef

instance [LawfulTypeRef ty] : CoeDep TypeRef ty TypeObject := ⟨ofTypeRef ty⟩
instance [LawfulTypeRef ty] : CoeDep TypeRef ty Object := ⟨ofTypeRef ty⟩

end TypeObject

def mkTypeObject (ty : PyType) : BaseIO TypeObject := do
  -- TODO: figure out how to require lawfulness
  .ofInitTypeRef <$> mkInitTypeRef (ty := ty)
