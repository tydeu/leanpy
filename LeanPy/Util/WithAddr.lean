/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
syntax Authors Mac Malone
-/

namespace LeanPy

/-- A value equipped with its runtime address. -/
structure WithAddr (α : Type u) where
  private _mk ::
    private _addr : USize
    private _data : α
  deriving Nonempty

namespace WithAddr

noncomputable def mk (addr : USize) (data : α) : WithAddr α :=
  _mk addr data

private unsafe def dataImpl (self : WithAddr α) : α :=
  unsafeCast self

/-- The addressed data. -/
@[implemented_by dataImpl]
def data (self : WithAddr α) : α :=
  self._data

@[simp] theorem data_mk : data (mk n a) = a := by
  simp [mk, data]

@[inline] private unsafe def addrImpl (self : WithAddr α) : USize :=
  ptrAddrUnsafe self

/-- The address of `data`. In the case of a scalar, this is its boxed value. -/
@[implemented_by addrImpl]
def addr (self : WithAddr α) : USize :=
  self._addr

@[simp] theorem addr_mk : addr (mk n a) = n := by
  simp [mk, addr]

end WithAddr

unsafe def withAddrImpl (a : α) : BaseIO {r : WithAddr α // r.data = a} :=
  pure (unsafeCast a)

/-- Equip a value with its runtime address. -/
@[implemented_by withAddrImpl]
opaque withAddr' (a : α) : BaseIO {r : WithAddr α // r.data = a} :=
  pure ⟨WithAddr.mk 0 a, WithAddr.data_mk⟩

/-- Equip a value with its runtime address. -/
@[inline] opaque withAddr (a : α) : BaseIO (WithAddr α) :=
  (·.val) <$> withAddr' a
