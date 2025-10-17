/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.Object.TypeRef

namespace LeanPy

/-- A type-indexed reference to a `TObjectSlots` structure. -/
structure TypeSlotsRef where
  private innerMk ::
    private innerTy : TypeRef
  deriving Nonempty

noncomputable def TypeSlotsRef.ty (self : TypeSlotsRef) : TypeRef :=
  self.innerTy

theorem TypeSlotsRef.ty_inj : ty a = ty b ↔ a = b := by
  cases a; cases b; simp [ty]

/-- Class used to infer the slots for a type. -/
class TypeSlots (ty : TypeRef) where
  slotsRef : TypeSlotsRef
  ty_slotsRef : slotsRef.ty = ty := by rfl

attribute [simp] TypeSlots.ty_slotsRef

instance : Nonempty (TypeSlots ty) := ⟨{slotsRef.innerTy := ty}⟩

namespace TypeRef
export TypeSlots (slotsRef ty_slotsRef)
end TypeRef
