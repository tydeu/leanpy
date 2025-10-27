/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.Tuple.Ref
import LeanPy.Data.Object.Slots
import LeanPy.Data.Str.Object

namespace LeanPy

/- An instance of a subclass of `tuple` that satisfies `p`. -/
abbrev PTupleObject (p : ObjectProp) := PSubObject p tupleTypeRef

/- An instance of a subclass of `tuple`. -/
def TupleObject := PTupleObject .Any

/-- Returns whether this object is an instance of a subtype of `tuple`. -/
@[inline] def Object.isTuple (self : Object) : Bool :=
 self.ty.isTupleSubclass

/-- Casts `self` to `TupleObject`. -/
@[inline] def Object.asTuple (self : Object) (h : self.isTuple) : TupleObject :=
  self.asSubObject (self.ty.isTupleSubclass_iff_subset.mp h)

/--
Casts `self` to `TupleObject` if `self` is instance of a subtype of `tuple`.
Otherwise, returns `none`.
-/
@[inline] def Object.asTuple? (self : Object) : Option TupleObject :=
  if h : self.isTuple then some (self.asTuple h) else none

namespace ObjectData

@[inline] private unsafe def ofTupleRefImpl (tuple : TupleRef) : ObjectData :=
  unsafeCast tuple

@[implemented_by ofTupleRefImpl]
abbrev ofTupleRef (tuple : TupleRef) : ObjectData := .mkCore tupleDataKind tuple

opaque getTupleRef (self : ObjectData) (h : self.kind = tupleDataKind) : TupleRef :=
  unsafe unsafeCast self

end ObjectData

namespace TupleObject

instance : Coe TupleObject Object := ⟨PObject.toObject⟩

theorem isTuple_toObject (self : TupleObject) : self.toObject.isTuple :=
  self.ty.isTupleSubclass_iff_subset.mpr self.ty_subset

@[inline] def getTupleRef (self : TupleObject) : TupleRef :=
  self.data.getTupleRef (self.lawful_subobject).2

@[inline] def getTuple (self : TupleObject) : Tuple :=
  self.getTupleRef.data

/--
Returns the hash of the tuple.

This is equivalent to the Python `tuple.__hash__(self)`.
-/
@[inline] protected def hashM (self : TupleObject) : PyM Hash :=
  self.getTuple.hashM


/--
Returns `true` if the two tuples are equal.

This is equivalent to the Python `tuple.__eq__(self, other)`.
-/
@[inline] protected def beqM (self other : TupleObject) : PyM Bool :=
  self.getTuple.beqM other.getTuple

/--
Returns `true` if the two tuples are not equal.

This is equivalent to the Python `tuple.__ne__(self, other)`.
-/
@[inline] protected def bneM (self other : TupleObject) : PyM Bool :=
  not <$> self.beqM other

/--
Return the number of items in the tuple.

This is equivalent to the Python `tuple.len(self)`.
-/
@[inline] def length (self : TupleObject) : Nat :=
  self.getTuple.size

/-- Return `true` unless the tuple is empty. -/
@[inline] def toBool (self : TupleObject) : Bool :=
  self.length != 0

/--
Return a string representation of the tuple.

This is equivalent to the Python `tuple.__repr__(self)`.
-/
@[inline] def reprM (self : TupleObject) : PyM String :=
  self.getTuple.reprM

end TupleObject

def tupleTypeRef.slots : TObjectSlots TupleObject where
  hash self := self.hashM
  beq self other :=
    if let some other := other.asTuple? then self.beqM other else return false
  bne self other :=
    if let some other := other.asTuple? then self.bneM other else return true
  call self _ _ := throwNotCallable self.ty.name
  bool self := return self.toBool
  repr self := self.reprM

@[instance] initialize tupleTypeSlotsRef : TypeSlots tupleTypeRef ←
  tupleTypeRef.slots.mkRef

namespace TupleObject

@[inline] def ofTupleRef (r : TupleRef) : TupleObject :=
  tupleTypeRef.mkObjectCore r.id  (.ofTupleRef r)

instance : Coe TupleRef TupleObject := ⟨TupleObject.ofTupleRef⟩

def empty : TupleObject := .ofTupleRef .empty

instance : EmptyCollection TupleObject := ⟨TupleObject.empty⟩

end TupleObject

@[inline] def mkTupleObject (data : Array Object) : BaseIO TupleObject :=
  .ofTupleRef <$> mkTupleRef data
