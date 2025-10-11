/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
syntax Authors Mac Malone
-/
import LeanPy.Util.WithAddr

namespace LeanPy

/-! ## Small Int -/

def smallIntBits : Nat :=
  if System.Platform.numBits == 64 then 32 else 31

@[inline] unsafe def isScalarUnsafe (a : α) : Bool :=
  ptrAddrUnsafe a &&& 1 == 1

@[inline] private unsafe def isSmallIntImpl (n : Int) : Bool :=
  isScalarUnsafe n

@[implemented_by isSmallIntImpl]
def isSmallInt (n : Int) : Bool :=
  - 2 ^ (smallIntBits - 1) ≤ n ∧ n ≤ 2 ^ (smallIntBits - 1) - 1

theorem isSmallInt_of_lt (h : n.natAbs < 1073741823) : isSmallInt n := by
  simp only [isSmallInt, smallIntBits]
  split <;> grind

theorem isSmallInt_zero : isSmallInt 0 :=
  isSmallInt_of_lt (by decide)

theorem isSmallInt_one : isSmallInt 1 :=
  isSmallInt_of_lt (by decide)

def smallIntAddr (n : Int) : USize :=
  n.toInt32.toUInt32.toUSize <<< 1 ||| 1

theorem toNat_smallIntAddr_lt : (smallIntAddr n).toNat < 8589934592 := by
  have one_mod_numBits : 1 % System.Platform.numBits = 1 :=
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by simp) System.Platform.le_numBits)
  rw [smallIntAddr]
  simp only [USize.toNat_or, USize.toNat_shiftLeft, USize.reduceToNat]
  refine Nat.or_lt_two_pow (n := 33) (Nat.mod_lt_of_lt ?_) (by simp)
  rw [one_mod_numBits, Nat.shiftLeft_eq, Nat.pow_one, UInt32.toNat_toUSize]
  have n_lt := n.toInt32.toUInt32.toNat_lt
  omega

@[simp] theorem toNat_smallIntAddr_mod_two : (smallIntAddr n).toNat % 2 = 1 := by
  simp [smallIntAddr]

@[simp] theorem smallIntAddr_mod_two : smallIntAddr n % 2 = 1 := by
  simp [← USize.toNat_inj, toNat_smallIntAddr_mod_two]

theorem toNat_smallIntAddr_ne_zero : (smallIntAddr n).toNat ≠ 0 := by
  simp only [smallIntAddr, USize.toNat_or, USize.reduceToNat]
  simp only [Nat.ne_zero_iff_zero_lt, Nat.lt_of_succ_le Nat.right_le_or]

theorem smallIntAddr_ne_zero : smallIntAddr n ≠ 0 := by
  rw [ne_eq, ← USize.toNat_inj, ← ne_eq]
  exact toNat_smallIntAddr_ne_zero

/-! ## Int Ref -/

abbrev IntRef.WF (n : WithAddr Int) : Prop :=
  if isSmallInt n.data then n.addr = smallIntAddr n.data else n.addr % 2 = 0

structure IntRef where
  toWithAddr : WithAddr Int
  wf : IntRef.WF toWithAddr
  deriving TypeName

namespace IntRef

@[inline] def addr (n : IntRef) : USize :=
  n.toWithAddr.addr

@[simp] theorem addr_mk : addr (mk v h) = v.addr := rfl

@[inline] def toInt (n : IntRef) : Int :=
  n.toWithAddr.data

instance : Coe IntRef Int := ⟨toInt⟩

@[simp] theorem toInt_mk : toInt (mk n h) = n.data := rfl

@[inline] def isSmall (n : IntRef) : Bool :=
  isSmallInt n.toInt

@[simp] theorem isSmall_mk : isSmall (mk n h) = isSmallInt n.data := rfl

theorem addr_of_isSmall (h : isSmall n) : addr n = smallIntAddr n.toInt := by
  let ⟨n, wf⟩  := n
  simp only [isSmall_mk] at h
  simpa [WF, h] using wf

theorem addr_of_not_isSmall (h : ¬ isSmall n) : addr n % 2 = 0 := by
  let ⟨n, wf⟩  := n
  simp only [isSmall_mk] at h
  simpa [WF, h] using wf

theorem toNat_addr_of_not_isSmall (h : ¬ isSmall n) : (addr n).toNat % 2 = 0 := by
  simpa [← USize.toNat_inj] using addr_of_not_isSmall h

@[inline] private unsafe def ofSmallIntImpl (n : Int) (_ : isSmallInt n) : IntRef :=
  unsafeCast n

@[implemented_by ofSmallIntImpl]
def ofIsSmall (n : Int) (h : isSmallInt n) : IntRef :=
  ⟨.mk (smallIntAddr n) n, by simp [IntRef.WF, h]⟩

instance : OfNat IntRef 0 := ⟨.ofIsSmall 0 isSmallInt_zero⟩
instance : OfNat IntRef 1 := ⟨.ofIsSmall 1 isSmallInt_one⟩

@[simp] theorem toInt_ofIsSmall : (ofIsSmall n h).toInt = n := rfl

instance : Nonempty IntRef := ⟨.ofIsSmall 0 isSmallInt_zero⟩

@[simp] theorem toInt_zero : toInt 0 = 0 := rfl

private noncomputable def null (n : Int) (h : ¬ isSmallInt n) : IntRef :=
  ⟨.mk 0 n, by simp [IntRef.WF, h]⟩

private theorem toInt_null : toInt (null n h) = n := rfl

end IntRef

@[noinline] -- prevents compiler from producing incorrect casts
unsafe def intRefUnsafe (n : Int) : IntRef :=
 unsafeCast n

@[inline] private unsafe def mkIntRefImpl (n : Int) : BaseIO {r : IntRef // r = n} :=
 pure ⟨intRefUnsafe n, lcProof⟩

@[implemented_by mkIntRefImpl]
opaque mkIntRef' (n : Int) : BaseIO {r : IntRef // r = n} := do
  if h : isSmallInt n then
    return ⟨.ofIsSmall n h, IntRef.toInt_ofIsSmall⟩
  else
    return ⟨IntRef.null n h, IntRef.toInt_null⟩

@[inline] def mkIntRef (n : Int) : BaseIO IntRef :=
  (·.val) <$> mkIntRef' n
