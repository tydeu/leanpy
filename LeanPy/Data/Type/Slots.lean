/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.Type.Ref

namespace LeanPy

/--
A type-indexed reference to a `SubObjectSlots` structure.

While modelled in the logic as the type index, the runtime data for this type
is the `SubObjectSlots` structure.
-/
structure TypeSlotsRef where
  private innerMk ::
    private innerTy : TypeRef
  deriving Nonempty

namespace TypeSlotsRef

noncomputable def mk (ty : TypeRef) : TypeSlotsRef :=
  innerMk ty

protected noncomputable def ty (self : TypeSlotsRef) : TypeRef :=
  self.innerTy

theorem ty_inj {a b : TypeSlotsRef} : a.ty = b.ty ↔ a = b := by
  cases a; cases b; simp [TypeSlotsRef.ty]

end TypeSlotsRef

/-- Class used to infer the slots for a type. -/
class TypeSlots (ty : TypeRef) where mk' ::
  slotsRef : TypeSlotsRef
  ty_slotsRef : slotsRef.ty = ty := by rfl

namespace TypeSlots

attribute [simp] ty_slotsRef

noncomputable def mk {ty : TypeRef} : TypeSlots ty :=
  .mk' (.mk ty)

instance : Nonempty (TypeSlots ty) := ⟨.mk⟩

end TypeSlots

namespace TypeRef
export TypeSlots (slotsRef ty_slotsRef)
end TypeRef
