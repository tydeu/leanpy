/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.Object.Slots
import LeanPy.Data.Str.Basic

namespace LeanPy

/- An instance of a subclass of `str` that satisfies `p`. -/
abbrev PStrObject (p : ObjectProp) := PSubObject p strTypeRef

/- An instance of a subclass of `str`. -/
def StrObject := PStrObject .Any

/-- Returns whether this object is an instance of a subtype of `str`. -/
@[inline] def Object.isStr (self : Object) : Bool :=
 self.ty.isStrSubclass

/-- Casts `self` to `StrObject`. -/
@[inline] def Object.asStr (self : Object) (h : self.isStr) : StrObject :=
  self.asSubObject (self.ty.isStrSubclass_iff_subset.mp h)

/--
Casts `self` to `StrObject` if `self` is instance of a subtype of `str`.
Otherwise, returns `none`.
-/
@[inline] def Object.asStr? (self : Object) : Option StrObject :=
  if h : self.isStr then some (self.asStr h) else none

namespace StrObject

instance : Coe StrObject Object := ⟨PObject.toObject⟩

theorem isStr_toObject (self : StrObject) : self.toObject.isStr :=
  self.ty.isStrSubclass_iff_subset.mpr self.ty_subset

@[inline] def getStrRef (self : StrObject) : StrRef :=
  self.data.get (self.lawful_subobject).2

@[inline] def getString (self : StrObject) : String :=
  self.getStrRef.data

@[inline] protected def toString (self : StrObject) : String :=
  self.getString

@[inline] protected def beq (self other : StrObject) : Bool :=
  self.getString == other.getString

@[inline] protected def bne (self other : StrObject) : Bool :=
  self.getString != other.getString

@[inline] protected def hash (self : StrObject) : Hash :=
  strHash self.getString

@[inline] def length (self : StrObject) : Nat :=
  self.getString.length

@[inline] def toBool (self : StrObject) : Bool :=
  self.length != 0

@[inline] def repr (self : StrObject) : String :=
  strRepr self.getString

end StrObject

def strTypeRef.slots : TObjectSlots StrObject where
  hash self := return self.hash
  beq self other := return other.asStr?.any self.beq
  bne self other := return other.asStr?.all self.bne
  bool self := return self.toBool
  str self := return self.toString
  repr self := return self.repr

@[instance] initialize strTypeSlotsRef : TypeSlots strTypeRef ←
  strTypeRef.slots.mkRef

namespace StrObject

@[inline] def ofStrRef (r : StrRef) : StrObject :=
  strTypeRef.mkObject r.id  r

def empty : StrObject := .ofStrRef .empty

instance : EmptyCollection StrObject := ⟨StrObject.empty⟩

end StrObject

@[inline] def mkStrObject (s : String) : BaseIO StrObject := do
  StrObject.ofStrRef <$> mkStrRef s
