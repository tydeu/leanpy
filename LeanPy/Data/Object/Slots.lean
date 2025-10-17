/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.Object.Basic

namespace LeanPy

/-- Slots for an object of Lean type `α`. -/
structure TObjectSlots (α : Type u) where
  /-- The type's `__hash__` slot.  -/
  hash (self : α) : PyM Hash
  /-- The type's `==` slot. Unlike `__eq__`, this returns `Bool`.  -/
  beq (self : α) (other : Object) : PyM Bool
  /-- The type's `!=` slot. Unlike `__ne__`, this returns `Bool`. -/
  bne (self : α) (other : Object) : PyM Bool := Bool.not <$> beq self other
  /-- The type's `__bool__` slot.  -/
  bool (self : α) : PyM Bool
  /-- The type's `__repr__` slot.  -/
  repr (self : α) : PyM String
  /-- The type's `__str__` slot.  -/
  str (self : α) : PyM String := repr self
  deriving Nonempty

/-- Slots compatible with instances of types that satisfy `p`. -/
abbrev PObjectSlots (p : TypeProp) := TObjectSlots (PObject p)

/-- Slots compatible with instances of `ty` or its subtypes. -/
abbrev SubObjectSlots (ty : TypeRef) := TObjectSlots (SubObject ty)

@[inline] private unsafe def TObjectSlots.castImpl
  (_ : ∀ {ty}, q ty → p ty) (slots : PObjectSlots p)
: (PObjectSlots q) := unsafeCast slots

@[implemented_by castImpl]
def TObjectSlots.cast
  (h : ∀ {ty}, q ty → p ty) (slots : PObjectSlots p)
: (PObjectSlots q) where
  hash self := slots.hash (self.cast (h self.property))
  beq self other := slots.beq (self.cast (h self.property)) other
  bne self other := slots.beq (self.cast (h self.property)) other
  bool self := slots.bool (self.cast (h self.property))
  repr self := slots.repr (self.cast (h self.property))
  str self := slots.str (self.cast (h self.property))

@[inline] def TObjectSlots.downcast
  (h : subTy ⊆ superTy) (slots : TObjectSlots (PSubObject p superTy))
: TObjectSlots (PSubSubObject p subTy superTy) :=
  slots.cast (fun hp => hp.property.trans h)

@[inline] def TObjectSlots.stripCast
  (h : subTy ⊆ superTy) (slots : TObjectSlots (PSubSubObject p subTy superTy))
: TObjectSlots (PSubObject p subTy) :=
  slots.cast (fun hp => ⟨hp, .trans hp.ty_subset h⟩)

@[inline] private unsafe def TObjectSlots.mkRefImpl
  (slots : SubObjectSlots ty) :  BaseIO (TypeSlots ty)
:= pure (unsafeCast slots)

@[implemented_by mkRefImpl]
opaque TObjectSlots.mkRef
  (slots : SubObjectSlots ty) : BaseIO (TypeSlots ty)

@[inline] private unsafe def TypeSlotsRef.getImpl
  (self : TypeSlotsRef) : BaseIO (SubObjectSlots self.ty)
:= pure (unsafeCast self)

@[implemented_by getImpl]
opaque TypeSlotsRef.get
  (self : TypeSlotsRef) : BaseIO (SubObjectSlots self.ty)

/-! ## Slot-based Methods -/

@[inline] def Object.getSlots (self : Object) : BaseIO (SubObjectSlots self.ty) :=
  (·.cast (self.lawful_slots ▸ ·)) <$> self.innerSlots.get

@[inline] def Object.hashM (self : Object) : PyM Hash := do
  (← self.getSlots).hash self.toSubObject

@[inline] def Object.beqM (self other : Object) : PyM Bool := do
  (← self.getSlots).beq self.toSubObject other

@[inline] def Object.bneM (self other : Object) : PyM Bool := do
  (← self.getSlots).bne self.toSubObject other

@[inline] def Object.reprM (self : Object) : PyM String := do
  (← self.getSlots).repr self.toSubObject

@[inline] def Object.toStringM (self : Object) : PyM String := do
  (← self.getSlots).str self.toSubObject

@[inline] def Object.toBoolM (self : Object) : PyM Bool := do
  (← self.getSlots).bool self.toSubObject
