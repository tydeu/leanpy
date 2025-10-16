/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.IntRef
import LeanPy.Data.StringRef
import LeanPy.Data.MutableRef
import LeanPy.Data.Object.ObjectTypes

/-!
Built-in types inheriting from a direct subclass of `object`. These are in a
separate file from their parents due to `initialize` limitations.
-/

namespace LeanPy

def boolTypeDoc : String := "\
  bool(x) -> bool\n\
  \n\
  Returns True when the argument x is true, False otherwise.\n\
  The builtins True and False are the only two instances of the class bool.\n\
  The class bool is a subclass of the class int, and cannot be subclassed.\
  "

@[reducible] def boolType : PyType where
  name := "bool"
  doc? := some boolTypeDoc
  base? := some intTypeRef
  isIntSubclass := true
  IsValidObject id data :=
    (id = .false ∨ id = .true) ∧
    (id = .false → data = .mk (0 : IntRef)) ∧
    (id = .true → data = .mk (1 : IntRef)) ∧
    data.kind = typeName IntRef -- redundant, but makes `simp_all` work bellow

initialize boolTypeRef' : DTypeRef boolType ← mkDTypeRef _

abbrev boolTypeRef : TypeRef := boolTypeRef'.toTypeRef
