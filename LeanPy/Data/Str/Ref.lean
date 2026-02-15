/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.NonScalarRef

namespace LeanPy

/-- An immutable reference to a string. -/
abbrev StrRef := NonScalarRef String

instance : TypeName StrRef := unsafe (.mk _ ``StrRef)

instance : Nonempty {r : StrRef // r.data = data} :=
  ⟨NonScalarRef.null data, NonScalarRef.data_null⟩

@[inline]
opaque mkStrRef' (s : String) : BaseIO {r : StrRef // r.data = s} :=
  pure (unsafe unsafeCast s)

@[inline] def mkStrRef (s : String) : BaseIO StrRef := do
  Subtype.val <$> mkStrRef' s

namespace StrRef

initialize empty' : {r : StrRef // r.data = ""} ← mkStrRef' _

@[inline] def empty : StrRef := empty'.val

@[simp] theorem data_empty : empty.data = "" := empty'.property

instance : EmptyCollection StrRef := ⟨empty⟩
