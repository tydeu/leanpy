/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
syntax Authors Mac Malone
-/
import LeanPy.Data.NonScalarRef

namespace LeanPy

abbrev StringRef := NonScalarRef String

instance : TypeName StringRef := unsafe (.mk _ ``StringRef)

instance : Nonempty {r : StringRef // r.data = data} :=
  ⟨NonScalarRef.null data, NonScalarRef.data_null⟩

@[inline]
opaque mkStringRef' (s : String) : BaseIO {r : StringRef // r.data = s} :=
  pure (unsafe unsafeCast s)

@[inline] def mkStringRef (s : String) : BaseIO StringRef := do
  Subtype.val <$> mkStringRef' s

namespace StringRef

initialize empty' : {r : StringRef // r.data = ""} ← mkStringRef' _

@[inline] def empty : StringRef := empty'.val

@[simp] theorem data_empty : empty.data = "" := empty'.property

instance : EmptyCollection StringRef := ⟨empty⟩
