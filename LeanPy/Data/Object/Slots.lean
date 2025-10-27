/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.PyM

namespace LeanPy

/-- Slots for an object of Lean type `α`. -/
structure TObjectSlots (α : Type u) where
  /-- The type's `__hash__` slot.  -/
  hash (self : α) : PyM Hash
  /-- The type's `==` slot. Unlike `__eq__`, this returns `Bool`.  -/
  beq (self : α) (other : Object) : PyM Bool
  /-- The type's `!=` slot. Unlike `__ne__`, this returns `Bool`. -/
  bne (self : α) (other : Object) : PyM Bool := Bool.not <$> beq self other
  /-- The type's `__call__` slot. -/
  call (self : α) (args : Tuple) (kws? : Option DictRef) : PyM Object
  /-- The type's `__bool__` slot.  -/
  bool (self : α) : PyM Bool
  /-- The type's `__repr__` slot.  -/
  repr (self : α) : PyM String
  /-- The type's `__str__` slot.  -/
  str (self : α) : PyM String := repr self
  deriving Nonempty

/-- Slots compatible with objects that satisfy `p`. -/
abbrev PObjectSlots (p : ObjectProp) := TObjectSlots (PObject p)

/-- Slots compatible with instances of `ty` or its subtypes. -/
abbrev SubObjectSlots (ty : TypeRef) := TObjectSlots (SubObject ty)

namespace TObjectSlots

@[inline] private unsafe def castImpl
  (_ : ∀ {ty}, q ty → p ty) (slots : PObjectSlots p)
: (PObjectSlots q) := unsafeCast slots

@[implemented_by castImpl]
def cast
  (h : ∀ {ty}, q ty → p ty) (slots : PObjectSlots p)
: PObjectSlots q where
  hash self := slots.hash (self.cast (h self.property))
  beq self := slots.beq (self.cast (h self.property))
  bne self := slots.beq (self.cast (h self.property))
  call self := slots.call (self.cast (h self.property))
  bool self := slots.bool (self.cast (h self.property))
  repr self := slots.repr (self.cast (h self.property))
  str self := slots.str (self.cast (h self.property))

@[inline] def downcast
  (h : subTy ⊆ superTy) (slots : TObjectSlots (PSubObject p superTy))
: TObjectSlots (PSubSubObject p subTy superTy) :=
  slots.cast (fun hp => hp.property.trans h)

@[inline] def stripCast
  (h : subTy ⊆ superTy) (slots : TObjectSlots (PSubSubObject p subTy superTy))
: TObjectSlots (PSubObject p subTy) :=
  slots.cast (fun hp => ⟨hp, .trans hp.ty_subset h⟩)

@[inline] private unsafe def mkRefImpl
  (slots : SubObjectSlots ty) :  BaseIO (TypeSlots ty)
:= pure (unsafeCast slots)

@[implemented_by mkRefImpl] -- TODO: require lawfulness
opaque mkRef (slots : SubObjectSlots ty) : BaseIO (TypeSlots ty)

end TObjectSlots

namespace TypeSlotsRef

private unsafe def getImpl
  (self : TypeSlotsRef) : BaseIO (SubObjectSlots self.ty)
:= pure (unsafeCast self)

@[implemented_by getImpl] -- TODO: produce lawfulness
opaque get (self : TypeSlotsRef) : BaseIO (SubObjectSlots self.ty)

end TypeSlotsRef

/-! ## Slot-based Methods -/

namespace Object

@[inline] private def getSlots (self : Object) : BaseIO (SubObjectSlots self.ty) :=
  (·.cast (self.lawful_slots ▸ ·)) <$> self.innerSlots.get

@[inline] def hashM (self : Object) : PyM Hash := do
  (← self.getSlots).hash self.toSubObject

@[inline] def beqM (self other : Object) : PyM Bool := do
  (← self.getSlots).beq self.toSubObject other

@[inline] def bneM (self other : Object) : PyM Bool := do
  (← self.getSlots).bne self.toSubObject other

@[inline] def call
  (self : Object) (args : Tuple := ∅) (kws? : Option DictRef := none)
: PyM Object := do (← self.getSlots).call self.toSubObject args kws?

@[inline] def reprM (self : Object) : PyM String := do
  (← self.getSlots).repr self.toSubObject

@[inline] def toStringM (self : Object) : PyM String := do
  (← self.getSlots).str self.toSubObject

@[inline] def toBoolM (self : Object) : PyM Bool := do
  (← self.getSlots).bool self.toSubObject

end Object
