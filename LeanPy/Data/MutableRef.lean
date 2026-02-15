/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.NonScalarRef

namespace LeanPy

/--
A mutable data cell.

Implemented as an `IO.Ref` with address information.
-/
-- TODO: Consider using a mutex
abbrev MutableRef (α : Type) := NonScalarRef (IO.Ref α)

@[inline] private unsafe def mkMutableRefImpl
  [Nonempty α] (a : α) : BaseIO (MutableRef α)
:= unsafeCast (IO.mkRef a)

@[implemented_by mkMutableRefImpl]
opaque mkMutableRef [Nonempty α] (a : α) : BaseIO (MutableRef α)

namespace MutableRef

@[inline] def get (self : MutableRef α) : BaseIO α :=
  self.data.get

@[inline] def getAndMap (f : α → β) (self : MutableRef α) : BaseIO β :=
  self.data.modifyGet fun a => (f a, a)

@[inline] def set (a : α) (self : MutableRef α) : BaseIO Unit :=
  self.data.set a

@[inline] def modify (f : α → α) (self : MutableRef α) : BaseIO Unit :=
  self.data.modify f
