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

/- An instance of a subclass of `type`. -/
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

theorem isTypeSubclass_ty {self : TypeObject} : self.ty.isTypeSubclass :=
  self.ty.isTypeSubclass_iff_subset.mpr self.ty_subset

theorem isType_toObject {self : TypeObject} : self.toObject.isType :=
  self.isTypeSubclass_ty

@[inline] def getTypeRef (self : TypeObject) : TypeRef :=
  (self.data.get' <| self.lawful_ty_data self.isTypeSubclass_ty).1

instance : LawfulTypeRef (getTypeRef self) :=
  (self.data.get' <| self.lawful_ty_data self.isTypeSubclass_ty).2

@[inline] def getType (self : TypeObject) : PyType :=
  self.getTypeRef.data

/--
Returns the name of the type.

This is equivalent to the Python `vars(type)['__name__'].__get__(self)`.
-/
def name (self : TypeObject) : String :=
  self.getType.name

/--
A function call on a type object.

For `type` itself, it has two forms. With one argument, it returns the type
of the object. With three arguments, it returns a  new type object.

```text
type(object) -> the object's type
type(name, bases, dict, **kws) -> a new type
```

For other instances of `type` (e.g., `object`),
it constructs an new instance of that type.

This is equivalent to the Python `type.__call__(self, *args, **kws)`.
-/
-- Should follow the logic of CPython's `type_call`
-- https://github.com/python/cpython/blob/3.11/Objects/typeobject.c#L1050
def call (self : TypeObject) (args : Tuple) (kws? : Option DictRef) : PyM Object := do
  -- Only `type` itself should support the one-argument form.
  if self.id == typeTypeRef.id then
    if (← noKws kws?) then
      if h : args.size = 1 then
        return ← mkInternalTypeObject args[0].ty
      else if args.size = 3 then
        return ← mkInstance args kws?
    throwInternalTypeError "type() takes 1 or 3 arguments"
  else
    mkInstance args kws?
where mkInstance _ _ :=
  -- TODO: support creating instances
  throwInternalTypeError s!"cannot create '{self.name}' instances"

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
  call self args kwds? := self.call args kwds?
  bool _ := return true
  repr self := return self.repr

@[instance] initialize typeTypeSlotsRef : TypeSlots typeTypeRef ←
  typeTypeRef.slots.mkRef

namespace TypeObject

def ofTypeRef (ty : TypeRef) [LawfulTypeRef ty] : TypeObject :=
  typeTypeRef.mkObject ty.id ty (h_ty_data := fun _ => ⟨ty, by simp_all⟩)

instance [LawfulTypeRef ty] : CoeDep TypeRef ty TypeObject := ⟨ofTypeRef ty⟩
instance [LawfulTypeRef ty] : CoeDep TypeRef ty Object := ⟨ofTypeRef ty⟩

end TypeObject

def mkTypeObject (ty : PyType) [LawfulType ty] (h : ¬ty.isBuiltin) : BaseIO TypeObject := do
  let ref ← mkInitTypeRef (ty := ty)
  have : LawfulType ref.toTypeRef.data := by simp_all
  have : LawfulTypeRef ref.toTypeRef := .ofLawfulType (by simp) h
  return .ofTypeRef ref
