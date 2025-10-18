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

def isOf [TypeName α] (a : α) (self : ObjectData) : Prop :=
  self = .mk a

@[simp] theorem isOf_mk  [TypeName α] {a : α} : (mk a).isOf a := rfl

def isOfType (α) [TypeName α] (self : ObjectData) : Prop :=
  ∃ (a : α), self = .mk a

@[simp] theorem isOfType_mk  [TypeName α] {a : α} : (mk a).isOfType α :=
  ⟨a, rfl⟩

@[inline] private unsafe def getImpl'
  [TypeName α] {p : α → Prop} (self : ObjectData)
  (_ : ∃ (a : α), self.isOf a ∧ p a) : {a : α // p a}
:= unsafeCast self

@[implemented_by getImpl']
opaque get'
  [TypeName α] {p : α → Prop} (self : ObjectData)
  (h : ∃ (a : α), self.isOf a ∧ p a) : {a : α // p a}
:= let ⟨a, ⟨_, h⟩⟩ := Classical.indefiniteDescription _ h; ⟨a, h⟩

@[inline] private unsafe def getImpl
  [TypeName α] (self : ObjectData) (_ : self.isOfType α) : α
:= unsafeCast self

@[implemented_by getImpl]
opaque get
  [TypeName α] (self : ObjectData) (h : self.isOfType α)
: α := Classical.choose h
