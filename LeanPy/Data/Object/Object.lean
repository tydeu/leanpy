/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.VoidRef
import LeanPy.Data.Object.Slots

namespace LeanPy

/- An instance of a subtype of `object` that satisfies `p`. -/
abbrev PObjectObject (p : ObjectProp) := PObject (p.AndInstance objectTypeRef)

/--
An instance of `object` or one of its subtypes interpreted as an `object`.

Pure Lean operations on this type are their `object` variants,
they do not dispatch to the methods on the object's real type.
For example, given `self : ObjectObject`, the Lean `self.hash`
is `object.__hash__(self)` in Python, not `hash(self)`.
-/
def ObjectObject := PObjectObject .Any

/-- Casts `self` to `ObjectObject` (`object`). -/
@[inline] def Object.asObject (self : Object) : ObjectObject :=
  self.asSubObject self.ty.subset_objectType

instance : Coe Object ObjectObject := ⟨Object.asObject⟩

namespace ObjectObject

/--
Returns the hash of the object's id.

This is equivalent to the Python `object.__hash__(self)`.
-/
@[inline] protected def hash (self : ObjectObject) : Hash :=
  hash self.id

/--
Returns whether two objects are identical (have the same id).

This is equivalent to the Python `self is other`.
-/
@[inline] protected def beq (self other : ObjectObject) : Bool :=
  self.id == other.id

/--
Returns whether two objects are not identical (do not have the same id).

This is equivalent to the Python `self is not other`.
-/
@[inline] protected def bne (self other : ObjectObject) : Bool :=
  self.id != other.id

/--
Returns a string representation of the object.

This is equivalent to the Python `object.__repr__(self)`.
-/
protected def repr (self : ObjectObject) : String :=
  s!"<{self.ty.name} object at 0x{self.id.hex}>"

end ObjectObject

instance : ToString Object := ⟨(·.asObject.repr)⟩

def objectTypeRef.slots : TObjectSlots ObjectObject where
  hash self := return self.hash
  beq self other := return self.beq other
  bne self other := return self.bne other
  call self _ _ := throwNotCallable self.ty.name
  bool _ := return true
  repr self := return self.repr

@[instance] initialize objectTypeSlotsRef : TypeSlots objectTypeRef ←
  objectTypeRef.slots.mkRef

def ObjectObject.ofVoidRef (ref : VoidRef) : ObjectObject :=
  objectTypeRef.mkObject ref.id  ref

/--
Returns a new instance of `object`.

This is equivalent to the Python `object()`.
-/
def mkObjectObject : BaseIO ObjectObject := do
  ObjectObject.ofVoidRef <$> mkVoidRef
