/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.Int.Ref
import LeanPy.Data.NonScalarRef
import LeanPy.Util.String

namespace LeanPy

/--
The type of Python object ids.

Unlike CPython, object identities in LeanPy are not solely derived from
the object's address. Instead, LeanPy uses a mix of methods to determine
the identifier for an object.

For unique constants (e.g., `None`, `False`, `True`, `Ellipsis`,
`NotImplemented`), a fixed constant id is used. For small integers, their
scalar value is used. For big integers and other objects with a non-scalar
Lean representation, their address is used.
-/
structure ObjectId where
  private innerMk ::
    private innerVal : UInt64
  deriving Nonempty, DecidableEq, Hashable

namespace ObjectId

def toNat (self : ObjectId) : Nat :=
  self.innerVal.toNat

@[simp] private theorem toNat_mk : toNat (innerMk n) = n.toNat := rfl

theorem toNat.inj : toNat n = toNat m → n = m := by
  cases n; cases m; simp [toNat, UInt64.toNat_inj]

theorem toNat_inj : toNat n = toNat m ↔ n = m :=
  .intro toNat.inj (congrArg toNat)

@[inline] def hex (self : ObjectId) : String :=
  upperHexUInt64 self.innerVal

instance : ToString ObjectId := ⟨ObjectId.hex⟩

def const (n : UInt8) : ObjectId :=
  ⟨(n.toUInt64 + 1) <<< 33 ||| 1⟩

private theorem toNat_const : toNat (const n) = (n.toNat + 1) * 2 ^ 33 + 1 := by
  have eq_add_one {n : Nat} (h : n % 2 = 0) : n ||| 1 = n + 1 :=
    Nat.eq_of_testBit_eq fun
    | 0 => by simp [Nat.add_mod, h]
    | i+1 => by simp [↓Nat.testBit_or, Nat.testBit_add_one, Nat.add_div, h]
  have n_lt : n.toNat < 256 := n.toNat_lt
  have h1 : n.toNat + 1 < 18446744073709551616 := by omega
  have h2 : (n.toNat + 1) * 8589934592 < 18446744073709551616 := by omega
  have h3 : (n.toNat + 1) * 8589934592 % 2 = 0 := by omega
  simp [const, Nat.mod_eq_of_lt h1, Nat.shiftLeft_eq, Nat.mod_eq_of_lt h2, eq_add_one h3]

@[simp] private theorem toNat_const_mod_two : toNat (const n) % 2 = 1 := by
  simp [const]

private theorem le_toNat_const : 8589934592 ≤ toNat (const n) := by
  simp only [toNat_const, Nat.reducePow, Nat.reduceLeDiff]
  exact Nat.le_trans (by simp) (Nat.le_mul_of_pos_left 8589934592 (by simp))

@[simp] theorem const_inj : const n = const m ↔ n = m := by
  have h : 8589934592 ≠ 0 := by decide
  simp [← toNat_inj, toNat_const, ← UInt8.toNat_inj, Nat.mul_left_inj h]

@[reducible] def none : ObjectId := const 0
@[reducible] def false : ObjectId := const 1
@[reducible] def true : ObjectId := const 2
@[reducible] def ellipsis : ObjectId := const 3
@[reducible] def notImplemented : ObjectId := const 4

@[inline] def isNonScalar (self : ObjectId) : Bool :=
  self.toNat % 2 = 0

end ObjectId

@[inline] def IntRef.id (n : IntRef) : ObjectId :=
  ⟨n.addr.toUInt64⟩

@[simp] theorem IntRef.id_ne_const : id n ≠ .const c := by
  rw [ne_eq, ← ObjectId.toNat_inj]
  if h : n.isSmall then
    refine Nat.ne_of_lt (Nat.lt_of_lt_of_le ?_ ObjectId.le_toNat_const)
    simp [id, IntRef.addr_of_isSmall h, toNat_smallIntAddr_lt]
  else
    intro h_eq
    replace h_eq := congrArg (· % 2) h_eq
    simp [IntRef.toNat_addr_of_not_isSmall h, id] at h_eq

@[inline] def NonScalarRef.id (n : NonScalarRef α) : ObjectId :=
  ⟨n.addr.toUInt64⟩

@[simp] theorem NonScalarRef.id_ne_const : id r ≠ .const c := by
  rw [ne_eq, ← ObjectId.toNat_inj]
  intro h_eq
  replace h_eq := congrArg (· % 2) h_eq
  simp [id] at h_eq

@[simp] theorem NonScalarRef.isNonScalar_id : (id r).isNonScalar := by
  simp [id, ObjectId.isNonScalar]
