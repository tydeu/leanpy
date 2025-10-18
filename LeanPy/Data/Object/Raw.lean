/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.Type.Slots
import LeanPy.Data.MutableRef
import LeanPy.Data.HashDict
import LeanPy.Data.AttrName

namespace LeanPy

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

/--
The `Dict` type using raw objects.
This is used in the definition of `dictType` to break cycles.
-/
structure Dict.Raw where
  innerRef : MutableRef (HashDict Object.Raw (MutableRef Object.Raw))
  deriving TypeName
