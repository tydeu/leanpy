/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
syntax Authors Mac Malone
-/
import LeanPy.Util.String

namespace LeanPy

/--
The type of Python object ids.

Unlike CPython, object identities in LeanPy are not derived from the object's
address. Instead, LeanPy uses a mix of methods to determine an identifier for
an object.

For unique constants (e.g., `None`, `False`, `True`, `Ellipsis`,
`NoteImplemented`), a fixed id is used. For small integers, their
scalar value is used. For big integers and other objects with a non-scalar
Lean representation, their address is used.
-/
structure ObjectId where
  val : UInt64
  deriving Nonempty, BEq

namespace ObjectId

def hex (self : ObjectId) : String :=
  upperHexUInt64 self.val

def none : ObjectId := .mk 0
def false : ObjectId := .mk <| 2 ^ 32
def true : ObjectId := .mk <| 2 ^ 32 + 1
def ellipsis : ObjectId := .mk <| 2 ^ 32 + 2
def notImplemented : ObjectId := .mk <| 2 ^ 32 + 3

def int (n : Int) : ObjectId :=
  .mk <| (unsafe ptrAddrUnsafe n).toUInt64

def nonScalar (n : NonScalar) : ObjectId :=
  .mk <| (unsafe ptrAddrUnsafe n).toUInt64
