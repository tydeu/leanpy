/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.MutableRef
import LeanPy.Data.Object.Basic
import LeanPy.Data.Dict.Basic

namespace LeanPy

/-- A Python exception. -/
-- TODO: Derive from `BaseException`
abbrev ErrorObject := Object

/-- A mutable dictionary value at some key.. -/
abbrev DictRef.Cell := MutableRef Object

/-- The stored value of a mutable dictionary. -/
abbrev DictRef.Data := TDict Object Cell

/-- A mutable reference to a dictionary. -/
abbrev DictRef := MutableRef DictRef.Data

/-- A pure Python tuple. -/
abbrev Tuple := Array Object

structure PyContext where
  globals : DictRef
  locals : DictRef := globals
  mkInternalError (msg : String) : BaseIO ErrorObject
  mkInternalTypeObject (ty : TypeRef) [LawfulTypeRef ty] : SubObject typeTypeRef

/-- The monad of Python code. -/
abbrev PyM := ReaderT PyContext <| EIO ErrorObject

@[inline] private def mkInternalError (msg : String) : PyM ErrorObject := do
  (← read).mkInternalError msg

/--
Used internally in places where a type object is needed
but `ofTypeRef` cannot yet be defined (e.g., `type(ty)`).
-/
@[inline] def mkInternalTypeObject
  (ty : TypeRef) [LawfulTypeRef ty] : PyM (SubObject typeTypeRef)
:= return (← read).mkInternalTypeObject ty

@[inline] def throwInternalTypeError (msg : String) : PyM α := do
  -- TODO: make this a real TypeError
  throw (← mkInternalError msg)

@[inline] def throwUnhashableType (tyName : String) : PyM α := do
  throwInternalTypeError s!"unhashable type: '{tyName}'"

@[inline] def throwNotCallable (tyName : String) : PyM α := do
  throwInternalTypeError s!"'{tyName}' object is not callable"

/-- Returns `true` if `kws?` is `none` or empty. -/
def noKws (kws? : Option DictRef) : BaseIO Bool :=
  if let some kws := kws? then kws.getAndMap (·.isEmpty) else return true
