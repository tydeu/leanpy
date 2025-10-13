/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
syntax Authors Mac Malone
-/

namespace LeanPy

/-- An immutable value equipped with its runtime address. -/
structure FrozenRef (α : Type u) where
  private noncomputableMk ::
    private noncomputableAddr : USize
    private noncomputableData : α
  deriving Nonempty

namespace FrozenRef

noncomputable def mk (addr : USize) (data : α) : FrozenRef α :=
  noncomputableMk addr data

private unsafe def dataImpl (self : FrozenRef α) : α :=
  unsafeCast self

/-- The addressed data. -/
@[implemented_by dataImpl]
def data (self : FrozenRef α) : α :=
  self.noncomputableData

@[simp] theorem data_mk : data (mk n a) = a := by
  simp [mk, data]

@[inline] private unsafe def addrImpl (self : FrozenRef α) : USize :=
  ptrAddrUnsafe self

/-- The address of `data`. In the case of a scalar, this is its boxed value. -/
@[implemented_by addrImpl]
def addr (self : FrozenRef α) : USize :=
  self.noncomputableAddr

@[simp] theorem addr_mk : addr (mk n a) = n := by
  simp [mk, addr]

theorem eq_iff : a = b ↔ addr a = addr b ∧ data a = data b := by
  cases a; cases b; simp [addr, data]

@[simp] theorem mk_addr_data : mk (addr r) (data r) = r := by
  simp [eq_iff]

end FrozenRef

@[noinline] -- prevents compiler from producing incorrect casts
unsafe def frozenRefUnsafe (a : α) : FrozenRef α :=
  unsafeCast a

@[inline] private unsafe def mkFrozenRefImpl (a : α) : BaseIO {r : FrozenRef α // r.data = a} :=
  pure ⟨frozenRefUnsafe a, lcProof⟩

/-- Equip a value with its runtime address. -/
@[implemented_by mkFrozenRefImpl]
opaque mkFrozenRef' (a : α) : BaseIO {r : FrozenRef α // r.data = a} :=
  pure ⟨FrozenRef.mk 0 a, FrozenRef.data_mk⟩

/-- Equip a value with its runtime address. -/
@[inline] def mkFrozenRef (a : α) : BaseIO (FrozenRef α) :=
  (·.val) <$> mkFrozenRef' a
