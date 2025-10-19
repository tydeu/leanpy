/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.Tuple.Basic

namespace LeanPy

/- An immutable reference to a tuple. -/
abbrev TupleRef := NonScalarRef Tuple

instance : Nonempty {r : TupleRef // r.data = data} :=
  ⟨NonScalarRef.null data, NonScalarRef.data_null⟩

@[inline] opaque mkTupleRef' (data : Tuple) : BaseIO {r : TupleRef // r.data = data} :=
  pure (unsafe unsafeCast data)

@[inline] def mkTupleRef (data : Tuple) : BaseIO TupleRef := do
  Subtype.val <$> mkTupleRef' data

namespace TupleRef

initialize empty' : {r : TupleRef // r.data = #[]} ← mkTupleRef' _

@[inline] def empty : TupleRef := empty'.val

@[simp] theorem data_empty : empty.data = #[] := empty'.property

instance : EmptyCollection TupleRef := ⟨TupleRef.empty⟩
