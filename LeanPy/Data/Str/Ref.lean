/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
syntax Authors Mac Malone
-/
import LeanPy.Data.NonScalarRef

namespace LeanPy

abbrev StringRef := NonScalarRef String

instance : TypeName StringRef := unsafe (.mk _ ``StringRef)

@[inline] private unsafe def mkStringRefImpl
  (s : String) : BaseIO {r : StringRef // r.data = s}
:= pure (unsafeCast s)

@[implemented_by mkStringRefImpl]
opaque mkStringRef' (s : String) : BaseIO {r : StringRef // r.data = s} :=
  pure ⟨NonScalarRef.null s, NonScalarRef.data_null⟩

@[inline] def mkStringRef (s : String) : BaseIO StringRef := do
  Subtype.val <$> mkStringRef' s
