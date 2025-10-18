/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/

namespace LeanPy

/-- The name of an object's Lean data type. -/
abbrev DataKind := Lean.Name

/-- Dynamic data index by a `DataKind`. -/
structure ObjectData where
  private innerMk ::
    private innerKind : DataKind
    private innerValue : NonScalar
  deriving Nonempty

export TypeName (typeName)

instance : TypeName Unit := unsafe (.mk _ ``Unit)

namespace ObjectData

noncomputable def mkCore (kind : DataKind) (a : α) : ObjectData :=
  {innerKind := kind, innerValue := unsafe unsafeCast a}

@[inline] private unsafe def mkImpl [TypeName α] (a : α) : ObjectData :=
  unsafeCast a

@[implemented_by mkImpl]
abbrev mk [TypeName α] (a : α) : ObjectData := .mkCore (typeName α) a

noncomputable def kind (self : ObjectData) : DataKind :=
  self.innerKind

@[simp] theorem kind_mkCore  [TypeName α] {a : α} : kind (mkCore n a) = n := rfl

@[inline] private unsafe def getImpl
  [Nonempty α] [TypeName α]
  (self : ObjectData) (_ : self.kind = typeName α) : α
:= unsafeCast self

@[implemented_by getImpl]
opaque get [Nonempty α] [TypeName α]
  (self : ObjectData) (h : self.kind = typeName α) : α
