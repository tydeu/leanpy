/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.Type.Slots
import LeanPy.Data.Type.Lawful
import LeanPy.Data.MutableRef
import LeanPy.Data.Dict.Basic
import LeanPy.Data.AttrName

namespace LeanPy

/-! ## Object -/

/-- A raw Python object without validity proofs. -/
structure Object.Raw where mk ::
  /--
  The object's id.

  See `ObjectId` for details on how LeanPy encodes object identities.
  -/
  protected id : ObjectId
  /-- The object's Python type. -/
  protected ty : TypeRef
  /-- The type's slots. Used to optimize magic methods. -/
  innerSlots : TypeSlotsRef := by exact ty.slotsRef
  /-- The object's Lean data. -/
  data : ObjectData

/-- A Python object. -/
structure Object extends raw : Object.Raw where mk' ::
  [lawful_ty : LawfulTypeRef ty]
  lawful_ty_data : ty.isTypeSubclass →
    ∃ (ty : TypeRef), data.isOf ty ∧ LawfulTypeRef ty
  := by simp_all
  lawful_none : id = .none → ty = noneTypeRef := by assumption
  lawful_bool : id = .false ∨ id = .true → ty = boolTypeRef := by assumption
  lawful_slots : innerSlots.ty = ty := by simp
  lawful_object : ty.data.IsValidObject id data := by assumption

instance {self : Object} : LawfulTypeRef self.ty := self.lawful_ty

/-! ## Object Basics -/

namespace Object

theorem eq_iff (self other : Object) :
  self = other ↔
  self.id = other.id ∧ self.ty = other.ty ∧ self.data = other.data
:= by
  let {lawful_slots := h1, ..} := self
  let {lawful_slots := h2, ..} := other
  simp [mk'.injEq, ← TypeSlotsRef.ty_inj, h1, h2]

theorem lawful_subobject
  {self : Object} (h : self.ty ⊆ ty) : ty.IsValidObject self.id self.data
:= self.ty.isValidObject_mro self.lawful_object h


/--
Returns whether this object is the constant `None`.

Equivalent to the Python `self is None`.
-/
@[inline] def isNone (self : Object) : Bool :=
  self.id == .none

/--
Returns whether this object is not the constant `None`.

Equivalent to the Python `self is not None`.
-/
@[inline] def isNotNone (self : Object) : Bool :=
  self.id != .none

/--
Returns whether this object is the `True` singleton.

This is equivalent to the Python `self is True`.
-/
@[inline] def isTrue (self : Object) : Bool :=
  self.id == .true

/--
Returns whether this object is the `False` singleton.

This is equivalent to the Python `self is False`.
-/
@[inline] def isFalse (self : Object) : Bool :=
  self.id == .false

/--
Returns whether this object is the `True` or `False` singleton.

This is equivalent to the Python `self is True or self is False`.
-/
@[inline] def isBool (self : Object) : Bool :=
  self.isFalse || self.isTrue

end Object

/-! ## ObjectProp -/

/--
A predicate about an object.

Alternatively, this can be interpreted as the set of satisfying objects.
-/
abbrev ObjectProp := Object → Prop

namespace ObjectProp

def Any : ObjectProp :=
  fun _ => True

def ofRaw (p : Raw) : ObjectProp :=
  fun self => p self.id self.data

instance : Coe Raw ObjectProp := ⟨.ofRaw⟩

def And (p q : ObjectProp) : ObjectProp :=
  fun self => p self ∧ q self

theorem And.property (h : And p q o) : p o :=
  h.1

/-- Holds if the object satisfying `p` is a non-virtual instance of `ty`. -/
def AndInstance (ty : TypeRef) (p : ObjectProp) : ObjectProp :=
  p.And (·.ty ⊆ ty)

theorem AndInstance.ty_subset (h : AndInstance ty p o) : o.ty ⊆ ty :=
  h.2

theorem AndInstance.trans
  (h : sub ⊆ sup) (h₁ : AndInstance sub p o)
: AndInstance sup p o := ⟨h₁.1, .trans h₁.2 h⟩

end ObjectProp

/-! ## Object Subtypes -/

structure PObject (p : ObjectProp) extends Object where
  inner_property : p toObject

/-- An object which satisfies `p` and whose type is a subtype of `ty`, -/
abbrev PSubObject (p : ObjectProp) (ty : TypeRef) :=
  PObject (p.AndInstance ty)

/--
An object which satisfies `p` and whose type is a subtype of `subTy`,
which is a subtype of `superTy`.
-/
abbrev PSubSubObject (p : ObjectProp) (subTy superTy : TypeRef) :=
  PSubObject (p.AndInstance subTy) superTy

abbrev SubObject (ty : TypeRef) := PSubObject .Any ty

namespace Object

@[inline] def cast (self : Object) (h : p self) : PObject p :=
  ⟨self, h⟩

@[inline] def toPObject (self : Object) : PObject .Any :=
  self.cast .intro

/-- Casts `self` to an instance of `ty`. -/
@[inline] def asSubObject (self : Object) (h : self.ty ⊆ ty) : SubObject ty :=
  self.cast ⟨.intro, h⟩

/-- Casts `self` to an instance of its own type. -/
@[inline] def toSubObject (self : Object) : SubObject self.ty :=
  self.asSubObject .rfl

end Object

namespace PObject

instance : CoeOut (PObject p) Object :=
  ⟨PObject.toObject⟩

theorem property (self : PObject p) : p self :=
  self.inner_property

@[inline] def upcast
  (self : PSubObject p subTy) (h : subTy ⊆ superTy)
: PSubSubObject p subTy superTy :=
  self.cast ⟨self.property, .trans self.property.2 h⟩

theorem ty_subset {self : PSubObject p ty} : self.ty ⊆ ty :=
  self.property.ty_subset

theorem lawful_subobject
  {self : PSubObject p ty} : ty.data.IsValidObject self.id self.data
:= self.toObject.lawful_subobject self.property.ty_subset

theorem toObject_inj {self other : PObject p} :
  self.toObject = other.toObject ↔ self = other
:= by cases self; cases other; simp

theorem eq_iff {self other : PObject p} :
  self = other ↔
  self.id = other.id ∧ self.ty = other.ty ∧ self.data = other.data
:= by simp [← toObject_inj, Object.eq_iff]

end PObject

/-! ## Object Constructor -/

namespace TypeRef

def mkObjectCore
  (id : ObjectId) (data : ObjectData)
  (ty : TypeRef) [LawfulTypeRef ty] [TypeSlots ty]
  (h : ty.IsValidObject id data := by simp)
  (h_none : id = .none → ty = noneTypeRef := by simp)
  (h_bool : id = .false ∨ id = .true → ty = boolTypeRef := by simp)
  (h_ty_data : ty.isTypeSubclass →
    ∃ (ty : TypeRef), data.isOf ty ∧ LawfulTypeRef ty := by simp)
: SubObject ty := Object.toSubObject {id, ty, data}

def mkObject
  [TypeName α] (id : ObjectId) (data : α)
  (ty : TypeRef) [LawfulTypeRef ty] [TypeSlots ty]
  (h : ty.IsValidObject id (.mk data) := by simp)
  (h_none : id = .none → ty = noneTypeRef := by simp)
  (h_bool : id = .false ∨ id = .true → ty = boolTypeRef := by simp)
  (h_ty_data : ty.isTypeSubclass →
    ∃ (ty : TypeRef), (ObjectData.mk data).isOf ty ∧ LawfulTypeRef ty := by simp)
: SubObject ty := Object.toSubObject  {id, ty, data := .mk data}

end TypeRef
