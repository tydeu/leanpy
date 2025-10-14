/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
syntax Authors Mac Malone
-/
import LeanPy.Data.MutableRef

namespace LeanPy

/-- A fixed runtime address containing no data. -/
def VoidRef := MutableRef Unit

deriving instance TypeName for VoidRef

@[inline] def mkVoidRef : BaseIO VoidRef := do
  mkMutableRef ()
