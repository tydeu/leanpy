/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
syntax Authors Mac Malone
-/
import LeanPy.Util.WithAddr

namespace LeanPy

structure NonScalarRef (α : Type u) where
  toWithAddr : WithAddr α
  wf : toWithAddr.addr % 2 = 0

namespace NonScalarRef

@[inline] def addr (n : NonScalarRef α) : USize :=
  n.toWithAddr.addr

@[simp] theorem addr_mk : addr (mk a h) = a.addr := rfl

@[simp] theorem addr_mod_two : addr a % 2 = 0 := a.wf

@[simp] theorem toNat_addr_mod_two : (addr a).toNat % 2 = 0 := by
  simpa [← USize.toNat_inj, -addr_mod_two] using addr_mod_two

@[inline] def data (n : NonScalarRef α) : α :=
  n.toWithAddr.data

@[simp] theorem data_mk : data (mk a h) = a.data := rfl

instance : CoeOut (NonScalarRef α) α := ⟨data⟩

noncomputable def null (a : α) : NonScalarRef α :=
  ⟨.mk 0 a, by simp⟩

@[simp] theorem data_null : data (null a) = a := rfl

instance [Nonempty α] : Nonempty (NonScalarRef α) :=
  ⟨null Classical.ofNonempty⟩
