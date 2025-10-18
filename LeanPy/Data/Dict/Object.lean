/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
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

namespace ObjectData -- replace with something more sound

@[inline] private unsafe def ofDictImpl (dict : Dict) : ObjectData :=
  unsafeCast dict

@[implemented_by ofDictImpl]
abbrev ofDict (dict : Dict) : ObjectData := .mkCore dictDataKind dict

opaque getDict (self : ObjectData) (h : self.kind = dictDataKind) : Dict :=
  unsafe unsafeCast self

end ObjectData

namespace Dict

/--
Returns `true` if the two dictionaries are equal.

Dictionaries compare equal if and only if they have the same
`(key, value)` pairs (regardless of ordering).
-/
-- Should follow the logic in CPython's `dict_equal`
-- https://github.com/python/cpython/blob/3.11/Objects/dictobject.c#L3155
def beqM (a b : Dict) : PyM Bool := do
  let a ← a.get
  let b ← b.get
  unless a.size == b.size do
    return false
  for entry in a.entries do
    let .some ah ak av := entry
      | continue
    let ⟨bi⟩ ← b.raw.getEntryIdxCoreM ah (.up <$> ak.beqM ·)
    let some (.some _ _ bv) := b.entries[bi]?
      | return false
    let av ← av.get
    let bv ← bv.get
    unless (← av.beqM bv) do
      return false
  return true

/-- Returns a string representation of the dictionary. -/
-- Should follow the logic in CPython's `dict_repr`
-- https://github.com/python/cpython/blob/3.11/Objects/dictobject.c#L2403
def reprM (self : Dict) : PyM String := do
  return (← appendHead "{" 0 (← self.get).entries).push '}'
where
  appendHead s i entries : PyM String := do
    if h : i < entries.size then
      if let .some _ k v := entries[i] then
        appendTail (← append s k v) (i+1) entries
      else appendHead s (i+1) entries
    else return s
  termination_by entries.size - i
  decreasing_by omega
  appendTail s i entries := do
    if h : i < entries.size then
      if let .some _ k v := entries[i] then
        appendTail (← append s!"{s}, " k v) (i+1) entries
      else appendTail s (i+1) entries
    else return s
  termination_by entries.size - i
  decreasing_by all_goals omega
  append s k v := do
    let k ← k.reprM
    let v ← (← v.get).reprM
    return s!"{s}{k}: {v}"

end Dict

namespace DictObject

instance : Coe DictObject Object := ⟨PObject.toObject⟩

theorem isDict_toObject (self : DictObject) : self.toObject.isDict :=
  self.ty.isDictSubclass_iff_subset.mpr self.ty_subset

@[inline] def getDict (self : DictObject) : Dict :=
  self.data.getDict (self.lawful_subobject).2

/--
Returns `true` if the two dictionaries are equal.

This is equivalent to the Python `dict.__eq__(self, other)`.
-/
@[inline] protected def beqM (self other : DictObject) : PyM Bool :=
  self.getDict.beqM other.getDict

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
  (·.size) <$> self.getDict.get

/-- Return `true` unless the dictionary is empty. -/
@[inline] def toBoolM (self : DictObject) : BaseIO Bool :=
  (· != 0) <$> self.lengthM

/--
Return a string representation of the dictionary.

This is equivalent to the Python `dict.__repr__(self)`.
-/
@[inline] def reprM (self : DictObject) : PyM String :=
  self.getDict.reprM

end DictObject

def dictTypeRef.slots : TObjectSlots DictObject where
  hash _ := do -- TODO: make a TypeError & build this into the slot
    throw ((← mkStrObject "unhashable type: 'dict'") : ErrorObject)
  beq self other :=
    if let some other := other.asDict? then self.beqM other else return false
  bne self other :=
    if let some other := other.asDict? then self.beqM other else return true
  bool self := self.toBoolM
  repr self := self.reprM

@[instance] initialize dictTypeSlotsRef : TypeSlots dictTypeRef ←
  dictTypeRef.slots.mkRef

@[inline] def DictObject.ofDict (r : Dict) : DictObject :=
  dictTypeRef.mkObjectCore r.id  (.ofDict r)

instance : Coe Dict DictObject := ⟨DictObject.ofDict⟩
