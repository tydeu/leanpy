/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.FrozenRef

namespace LeanPy

structure NonScalarRef (α : Type u) where
  toFrozenRef : FrozenRef α
  wf : toFrozenRef.addr.isNonScalar

namespace NonScalarRef

instance : Coe (NonScalarRef α) (FrozenRef α) := ⟨NonScalarRef.toFrozenRef⟩

abbrev addr (n : NonScalarRef α) : Addr :=
  n.toFrozenRef.addr

@[simp] theorem addr_mk : addr (mk a h) = a.addr := rfl

@[simp] theorem isNonScalar_addr : (addr a).isNonScalar := a.wf

@[simp] theorem toNat_addr_mod_two : (addr a).toNat % 2 = 0 :=
  Addr.isNonScalar_iff.mp a.isNonScalar_addr

abbrev data (n : NonScalarRef α) : α :=
  n.toFrozenRef.data

@[simp] theorem data_mk : data (mk a h) = a.data := rfl

instance : CoeOut (NonScalarRef α) α := ⟨data⟩

noncomputable def null (a : α) : NonScalarRef α :=
  ⟨.mk 0 a, by simp⟩

@[simp] theorem data_null : data (null a) = a := rfl

instance [Nonempty α] : Nonempty (NonScalarRef α) :=
  ⟨null Classical.ofNonempty⟩
