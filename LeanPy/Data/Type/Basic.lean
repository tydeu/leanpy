/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.Object.Id
import LeanPy.Data.Object.Data

namespace LeanPy

/-! ## Raw Object Prop -/

def ObjectProp.Raw :=
  (id : ObjectId) → (data : ObjectData) → Prop

@[simp] def ObjectProp.Raw.Any : ObjectProp.Raw :=
  fun _ _ => True

instance : Nonempty ObjectProp.Raw := ⟨.Any⟩

/-! ## Type -/

/-- A raw Python type. -/
-- The `Py` prefix to avoids a clash with the Lean `Type` keyword.
structure PyType where
  /-- The type's name -/
  name : String
  /-- The type's documentation string or `none` if undefined. -/
  doc? : Option String := none
  /-- The type's parent. -/
  base? : Option (FrozenRef PyType) := none
  /--
  Is this type is a legal base for other types.
  If `false`, this type cannot be legally subtyped.

  Equivalent in functionality to CPython's `Py_TPFLAGS_BASETYPE`.
  -/
  isBaseType : Bool := true
  /--
  Is this a builtin type?

  This is used to provably distinguish builtin types with special properties
  from user types.
  -/
  /-
  Defaults to `true` because builtin types are explicitly constructed and thus
  the default is convenient whereas user types use a smart constructor that sets
  this to `false`.
  -/
  isBuiltin := true
  /--
  Is this a subclass of `type`?

  Equivalent in functionality to CPython's `Py_TPFLAGS_TYPE_SUBCLASS`.
  -/
  isTypeSubclass : Bool := false
  /--
  Is this a subclass of `str`?

  Equivalent in functionality to CPython's `Py_TPFLAGS_UNICODE_SUBCLASS`.
  -/
  isStrSubclass : Bool := false
  /--
  Is this a subclass of `int`?

  Equivalent in functionality to CPython's `Py_TPFLAGS_LONG_SUBCLASS`.
  -/
  isIntSubclass : Bool := false
  /--
  Returns whether the field combination could be a valid object of this type.

  This can be an over-approximation. That is, it may hold for objects
  which are not objects of this type.
  -/
  IsValidObject : ObjectProp.Raw := .Any
  deriving Nonempty

/-! ## Raw Type Ref -/

/-- A `TypeRef` as represented recursively in `PyType`. -/
abbrev RawTypeRef := FrozenRef PyType

instance : TypeName RawTypeRef := unsafe (.mk _ ``RawTypeRef)
