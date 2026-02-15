/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.MutableRef

namespace LeanPy

/-- A fixed runtime address containing no data. -/
abbrev VoidRef := MutableRef Unit

instance : TypeName VoidRef := unsafe (.mk _ ``VoidRef)

@[inline] def mkVoidRef : BaseIO VoidRef := do
  mkMutableRef ()
