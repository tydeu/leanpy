/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.Dict.Ref
import LeanPy.Data.Object.Slots
import LeanPy.Data.Str.Object

namespace LeanPy

/- An instance of a subclass of `dict` that satisfies `p`. -/
abbrev PDictObject (p : ObjectProp) := PSubObject p dictTypeRef

/- An instance of a subclass of `dict`. -/
def DictObject := PDictObject .Any

/-- Returns whether this object is an instance of a subtype of `dict`. -/
@[inline] def Object.isDict (self : Object) : Bool :=
 self.ty.isDictSubclass

/-- Casts `self` to `DictObject`. -/
@[inline] def Object.asDict (self : Object) (h : self.isDict) : DictObject :=
  self.asSubObject (self.ty.isDictSubclass_iff_subset.mp h)

/--
Casts `self` to `DictObject` if `self` is instance of a subtype of `dict`.
Otherwise, returns `none`.
-/
@[inline] def Object.asDict? (self : Object) : Option DictObject :=
  if h : self.isDict then some (self.asDict h) else none

namespace ObjectData

@[inline] private unsafe def ofDictRefImpl (dict : DictRef) : ObjectData :=
  unsafeCast dict

@[implemented_by ofDictRefImpl]
abbrev ofDictRef (dict : DictRef) : ObjectData := .mkCore dictDataKind dict

opaque getDictRef (self : ObjectData) (h : self.kind = dictDataKind) : DictRef :=
  unsafe unsafeCast self

end ObjectData

namespace DictObject

instance : Coe DictObject Object := ⟨PObject.toObject⟩

theorem isDict_toObject (self : DictObject) : self.toObject.isDict :=
  self.ty.isDictSubclass_iff_subset.mpr self.ty_subset

@[inline] def getDictRef (self : DictObject) : DictRef :=
  self.data.getDictRef (self.lawful_subobject).2

/--
Returns `true` if the two dictionaries are equal.

This is equivalent to the Python `dict.__eq__(self, other)`.
-/
@[inline] protected def beqM (self other : DictObject) : PyM Bool :=
  self.getDictRef.beqM other.getDictRef

/--
Returns `true` if the two dictionaries are not equal.

This is equivalent to the Python `dict.__ne__(self, other)`.
-/
@[inline] protected def bneM (self other : DictObject) : PyM Bool :=
  not <$> self.beqM other

/--
Return the number of items in the dictionary.

This is equivalent to the Python `dict.len(self)`.
-/
@[inline] def lengthM (self : DictObject) : BaseIO Nat :=
  (·.size) <$> self.getDictRef.get

/-- Return `true` unless the dictionary is empty. -/
@[inline] def toBoolM (self : DictObject) : BaseIO Bool :=
  (· != 0) <$> self.lengthM

/--
Return a string representation of the dictionary.

This is equivalent to the Python `dict.__repr__(self)`.
-/
@[inline] def reprM (self : DictObject) : PyM String :=
  self.getDictRef.reprM

end DictObject

def throwUnhashableType (tyName : String) : PyM α := do
  -- TODO: make this a TypeError
  throw ((← mkStrObject s!"unhashable type: '{tyName}'") : ErrorObject)

def dictTypeRef.slots : TObjectSlots DictObject where
  hash _ := throwUnhashableType "dict"
  beq self other :=
    if let some other := other.asDict? then self.beqM other else return false
  bne self other :=
    if let some other := other.asDict? then self.bneM other else return true
  bool self := self.toBoolM
  repr self := self.reprM

@[instance] initialize dictTypeSlotsRef : TypeSlots dictTypeRef ←
  dictTypeRef.slots.mkRef

@[inline] def DictObject.ofDictRef (r : DictRef) : DictObject :=
  dictTypeRef.mkObjectCore r.id  (.ofDictRef r)

instance : Coe DictRef DictObject := ⟨DictObject.ofDictRef⟩

@[inline] def mkDictObject (data : DictRef.Data) : BaseIO DictObject :=
  .ofDictRef <$> mkDictRef data
