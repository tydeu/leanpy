/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/

namespace LeanPy

/-- A runtime address. -/
structure Addr where
  private innerMk ::
    private toUSize : USize
  deriving DecidableEq, Hashable

/-- Returns the address of a Lean object. -/
@[inline] unsafe def addrUnsafe (a : α) : Addr :=
  ⟨ptrAddrUnsafe a⟩

namespace Addr

noncomputable def mk (a : USize) : Addr :=
  innerMk a

/-- The null pointer address. The preferred spelling is `0`. -/
def null : Addr := ⟨0⟩

instance : OfNat Addr 0 := ⟨null⟩

theorem null_eq_zero : null = 0 := rfl

instance : Inhabited Addr := ⟨0⟩

/-- Whether this is a possible address of a Lean object pointer. -/
def isNonScalar (a : Addr) : Bool :=
  a.toUSize % 2 == 0

@[simp] theorem isNonScalar_null : isNonScalar 0 := by
  simp [isNonScalar, ← null_eq_zero, null]

@[inline] def toNat (a : Addr) : Nat :=
  a.toUSize.toNat

@[simp] theorem toNat_mk : toNat (mk a) = a.toNat := rfl

theorem toNat_inj : toNat a = toNat b ↔ a = b := by
  cases a; cases b; simp [toNat, ← USize.toNat_inj]

theorem isNonScalar_iff : isNonScalar a ↔ a.toNat % 2 = 0 := by
  simp [isNonScalar, ← USize.toNat_inj, toNat]

@[inline] def toUInt64 (a : Addr) : UInt64 :=
  a.toUSize.toUInt64

@[simp] theorem toNat_toUInt64 : (toUInt64 a).toNat = a.toNat := rfl
