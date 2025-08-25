/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
syntax Authors Mac Malone
-/
import Std.Data.HashMap

namespace LeanPy

/-- The name of an object's Lean data type. -/
abbrev DataTy := Lean.Name

private opaque ObjectData.nonemptyType (ty : DataTy) : NonemptyType.{0}

/-- Per-type data. -/
def ObjectData (ty : DataTy) : Type := (ObjectData.nonemptyType ty).type

instance ObjectData.instNonempty : Nonempty (ObjectData ty) :=
  (ObjectData.nonemptyType ty).property

open TypeName

set_option linter.unusedVariables.funArgs false in
def ObjectData.mk [TypeName α] (a : α) (h : typeName α = n) : ObjectData n :=
  unsafe unsafeCast a

unsafe def ObjectData.getImpl [Nonempty α] [TypeName α] (self : ObjectData (typeName α)) : α :=
  unsafeCast self

@[implemented_by getImpl]
opaque ObjectData.get [Nonempty α] [TypeName α] (self : ObjectData (typeName α)) : α

/-- A Python type object. -/
-- TODO: Enrich with proper fields
structure TypeObject where
  name : String
  dataTy : DataTy
  deriving Nonempty

/-- A Python type object with a known Lean representation. -/
structure DTypeObject (α : Type u) [TypeName α] extends TypeObject where
  dataTy := typeName α
  dataTy_eq_typeName : dataTy = typeName α := by exact rfl

instance [TypeName α] : CoeOut (DTypeObject α) TypeObject :=
  ⟨DTypeObject.toTypeObject⟩

/-- A Python object. -/
structure Object where
  mk' ::
    ty : TypeObject
    data : ObjectData ty.dataTy

def Object.mk [TypeName α] (ty : DTypeObject α) (data : α) : Object :=
  ⟨ty, ObjectData.mk data ty.dataTy_eq_typeName.symm⟩

@[inline] def Object.dataTy (self : Object) : DataTy :=
  self.ty.dataTy

structure DObject (α : Type u) [TypeName α] extends Object where
  toObject_dataTy_eq_typeName : toObject.dataTy = typeName α

instance [TypeName α] : CoeOut (DObject α) Object :=
  ⟨DObject.toObject⟩

deriving instance TypeName for Unit

def noneType : DTypeObject Unit where
  name := "NoneType"

def none : Object :=
  .mk noneType ()

def Object.isNone (self : Object) : Bool :=
  self.ty.name == noneType.name

deriving instance TypeName for Int

def boolType : DTypeObject Int where
  name := "bool"

protected def Object.false : Object :=
  .mk boolType 0

instance : CoeDep Bool false Object := ⟨Object.false⟩

protected def Object.true : Object :=
  .mk boolType 1

instance : CoeDep Bool true Object := ⟨Object.true⟩
