/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/

namespace LeanPy

/-- An immutable value equipped with its runtime address. -/
structure FrozenRef (α : Type u) where
  -- TODO: Not `private` due to https://github.com/leanprover/lean4/issues/10789
  innerMk ::
    private innerAddr : USize
    private innerData : α
  deriving Nonempty

namespace FrozenRef

noncomputable def mk (addr : USize) (data : α) : FrozenRef α :=
  innerMk addr data

attribute [deprecated "Do not use `innerMk` directly." (since := "always")] innerMk

private unsafe def dataImpl (self : FrozenRef α) : α :=
  unsafeCast self

/-- The addressed data. -/
@[implemented_by dataImpl]
def data (self : FrozenRef α) : α :=
  self.innerData

@[simp] theorem data_mk : data (mk n a) = a := by
  simp [mk, data]

instance : CoeOut (FrozenRef α) α := ⟨data⟩

@[inline] private unsafe def addrImpl (self : FrozenRef α) : USize :=
  ptrAddrUnsafe self

/-- The address of `data`. In the case of a scalar, this is its boxed value. -/
@[implemented_by addrImpl]
def addr (self : FrozenRef α) : USize :=
  self.innerAddr

@[simp] theorem addr_mk : addr (mk n a) = n := by
  simp [mk, addr]

theorem eq_iff : a = b ↔ addr a = addr b ∧ data a = data b := by
  cases a; cases b; simp [addr, data]

@[simp] theorem mk_addr_data : mk (addr r) (data r) = r := by
  simp [eq_iff]

@[simp] theorem mk_eq_iff : mk a₁ d₁ = mk a₂ d₂ ↔ a₁ = a₂ ∧ d₁ = d₂ := by
  simp [eq_iff]

noncomputable def null (a : α) : FrozenRef α :=
  .mk 0 a

@[inline] private unsafe def castImpl
  (self : FrozenRef α) (_ : self.data = a)
: FrozenRef α := unsafeCast self

set_option linter.unusedVariables.funArgs false in
/--
Casts the reference's data to equivalent value in the logic.

This can restore definitional equalities for the data
after a reference has been created via an opaque definition.
-/
@[implemented_by castImpl]
abbrev cast
  (self : FrozenRef α) (h : self.data = a)
: FrozenRef α := {self with innerData := a}

@[simp] theorem cast_def : cast self h = self := by
  cases self; simp only [data] at h; simp [cast, h]

@[inline, elab_as_elim, cases_eliminator, induction_eliminator]
def elim
  {α : Type u} {motive : FrozenRef α → Sort v} (self : FrozenRef α)
  (mk : (addr : USize) → (data : α) → motive (mk addr data))
: motive self := mk self.addr self.data

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
