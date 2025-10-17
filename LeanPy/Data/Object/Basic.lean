/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.Object.TypeRef
import LeanPy.Data.Object.TypeSlotsRef
import LeanPy.Data.Object.LawfulTypeRef
import LeanPy.Data.Object.ObjectTypes2
import LeanPy.Data.HashDict
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
  lawful_none : id = .none → ty = noneTypeRef := by simp
  lawful_bool : id = .false ∨ id = .true → ty = boolTypeRef := by simp
  lawful_slots : innerSlots.ty = ty := by simp
  lawful_object : ty.data.IsValidObject id data := by simp

instance {self : Object} : LawfulTypeRef self.ty := self.lawful_ty

/-! ## TypeProp -/

/--
A predicate about a type.
Used to encode Python type relations in Lean types.
-/
abbrev TypeProp := TypeRef → Prop

def TypeProp.Any : TypeProp :=
  fun _ => True

def TypeProp.Subtype (p : TypeProp) (ty : TypeRef) : TypeProp :=
  fun t => p t ∧ t ⊆ ty

theorem TypeProp.Subtype.property (h : Subtype p ty t) : p t :=
  h.1

theorem TypeProp.Subtype.ty_subset (h : Subtype p ty t) : t ⊆ ty :=
  h.2

theorem TypeProp.Subtype.trans (h : ty₁ ⊆ ty₂) (h₁ : Subtype p ty₁ t) : Subtype p ty₂ t :=
  ⟨h₁.1, .trans h₁.2 h⟩

/-! ## Object Subtypes -/

structure PObject (p : TypeProp) extends Object where
  inner_property : p ty

theorem PObject.property (self : PObject p) : p self.ty :=
  self.inner_property

instance : CoeOut (PObject p) Object :=
  ⟨PObject.toObject⟩

@[inline] def Object.cast (self : Object) (h : p self.ty) : PObject p :=
  ⟨self, h⟩

/-- An object whose type satisfies `p` and is a subtype of `ty`, -/
abbrev PSubObject (p : TypeProp) (ty : TypeRef) :=
  PObject (p.Subtype ty)

/--
An object whose type satisfies `p` and is a subtype of `subTy`,
which is a subtype of `superTy`.
-/
abbrev PSubSubObject (p : TypeProp) (subTy superTy : TypeRef) :=
  PSubObject (p.Subtype subTy) superTy

abbrev SubObject (ty : TypeRef) := PSubObject .Any ty

@[inline] def Object.toPObject (self : Object) : PObject .Any :=
  self.cast .intro

@[inline] def Object.downcast (self : Object) (h : self.ty ⊆ ty) : SubObject ty :=
  self.cast ⟨.intro, h⟩

@[inline] def Object.toSubObject (self : Object) : SubObject self.ty :=
  self.downcast .rfl

@[inline] def PObject.upcast
  (self : PSubObject p subTy) (h : subTy ⊆ superTy)
: PSubSubObject p subTy superTy :=
  self.cast ⟨self.property, .trans self.property.2 h⟩

theorem PObject.ty_subset {self : PSubObject p ty} : self.ty ⊆ ty :=
  self.property.ty_subset

theorem Object.lawful_subobject
  {self : Object} (h : self.ty ⊆ ty) : ty.IsValidObject self.id self.data
:= self.ty.isValidObject_mro self.lawful_object h

theorem PObject.lawful_subobject
  {self : PSubObject p ty} : ty.data.IsValidObject self.id self.data
:= self.toObject.lawful_subobject self.property.ty_subset

/-! ## Object Basics -/

def TypeRef.mkObject
  [TypeName α]
  (ty : TypeRef) [LawfulTypeRef ty] [TypeSlots ty]
  (id : ObjectId) (data : α)
  (h : ty.IsValidObject id (.mk data) := by simp)
  (h_none : id = .none → ty = noneTypeRef := by simp)
  (h_bool : id = .false ∨ id = .true → ty = boolTypeRef := by simp)
: SubObject ty := Object.toSubObject {
  id, ty
  data := ObjectData.mk data
  lawful_none := h_none
  lawful_bool := h_bool
  lawful_object := h
}

namespace Object

@[inline] def getData
  [Nonempty α] [TypeName α] (self : Object) (h : self.data.kind = typeName α)
: α := self.data.get h

theorem eq_iff (self other : Object) :
  self = other ↔
  self.id = other.id ∧ self.ty = other.ty ∧ self.data = other.data
:= by
  let {lawful_slots := h1, ..} := self
  let {lawful_slots := h2, ..} := other
  simp [mk'.injEq, ← TypeSlotsRef.ty_inj, h1, h2]

end Object

/-! `PyM` -/

abbrev AttrDict := HashDict AttrName Object

/-- A Python exception. -/
-- TODO: Derive from `BaseException`
abbrev ErrorObject := Object

/-- Mutable dictionary. -/
abbrev Dict := MutableRef (HashDict Object (MutableRef Object))

/-- Mutable dictionary of variables. -/
abbrev VarDict := MutableRef AttrDict

structure PyContext where
  globals : VarDict
  locals : VarDict := globals

/-- The monad of Python code. -/
abbrev PyM := ReaderT PyContext <| EIO ErrorObject
