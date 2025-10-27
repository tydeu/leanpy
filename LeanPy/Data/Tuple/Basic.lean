/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.Object.Slots

namespace LeanPy.Tuple

/-- Returns the hash of the tuple. -/
-- Should follow the logic in CPython's `tuplehash`
-- https://github.com/python/cpython/blob/3.11/Objects/tupleobject.c#L321
-- adjusted to Lean's hashing algorithm (but maybe should use CPython's?)
def hashM (self : Tuple) : PyM Hash := do
  let baseHash := 7 -- base hash used by `Array`
  self.foldlM (init := baseHash) fun hash obj => do
    return mixHash hash (← obj.hashM)

/--
Returns `true` if the two tuples are equal.

Tuples compare equal if and only if their elements compare equal.
-/
-- Should follow the logic in CPython's `tuplerichcompare`
-- https://github.com/python/cpython/blob/3.11/Objects/tupleobject.c#L628
def beqM (self other : Tuple) : PyM Bool := do
  if h : self.size = other.size then
    self.size.anyM fun i h => self[i].beqM other[i]
  else
    return false

/--
Returns a string representation of the tuple.

Tuples compare equal if and only if their elements compare equal.
-/
-- Should follow the logic in CPython's `tuplerepr`
-- https://github.com/python/cpython/blob/3.11/Objects/tupleobject.c#L219
def reprM (self : Tuple) : PyM String := do
  -- NOTE: CPython does a recursion check here, but likely we don't need it?
  if h0 : self.size = 0 then
    return "()"
  else if h1 : self.size = 1 then
    return s!"({← self[0].reprM},)"
  else
    let init := s!"({← self[0].reprM}, {← self[1].reprM}"
    let s ← self.foldlM (init := init) (start := 2) fun s obj =>
      return s!"{s}, {← obj.reprM}"
    return s.push ')'
