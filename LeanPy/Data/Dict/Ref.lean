/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import LeanPy.Data.None.Object
import LeanPy.Data.Str.Object
import LeanPy.Data.Object.Slots

namespace LeanPy

@[inline] def mkDictRef (data : DictRef.Data) : BaseIO DictRef :=
  mkMutableRef data

namespace DictRef

@[inline] private def mkCell (data : Object) : BaseIO DictRef.Cell :=
  mkMutableRef data

namespace Data

def pushByStr (k : String) (v : Object) (self : Data) : BaseIO Data := do
  return self.pushCore (strHash k) (← mkStrObject k) (← mkCell v)

-- TODO: support `str` subclasses that override `__beq__`?
def getCellByStr? (k : String) (self : Data) : Option Cell :=
  let i := ULift.down.{0} <| Id.run <| self.getEntryIdxCoreM (strHash k) fun k' =>
    pure <| ULift.up <| k'.asStr?.any (·.getString == k)
  if h : i < self.entries.size then
    self.entries[i].value?
  else none

def setByStr (k : String) (v : Object) (self : Data) : PyM Data := do
  self.insertCoreM (strHash k) (← mkStrObject k) (← mkCell v) fun k' =>
    pure <| ULift.up <| k'.asStr?.any (·.getString == k)

def set (k : Object) (v : Object) (self : Data) : PyM Data := do
  self.insertCoreM (← k.hashM) k (← mkCell v) (.up <$> ·.beqM k)

end Data

def getByStr? (k : String) (self : DictRef) : BaseIO (Option Object) := do
  let some cell ← self.getAndMap (·.getCellByStr? k)
    | return none
  cell.get

def setByStr (k : String) (v : Object) (self : DictRef) : PyM Unit := do
  -- thread-safe path where a cell already exists
  if let some cell ← self.getAndMap (·.getCellByStr? k) then
    cell.set v
  else -- TODO: consider mutex here (when multi-threading leanpy)
    let data ← self.get
    let data ← data.pushByStr k v
    self.set data

/--
Returns `true` if the two dictionaries are equal.

Dictionaries compare equal if and only if they have the same
`(key, value)` pairs (regardless of ordering).
-/
-- Should follow the logic in CPython's `dict_equal`
-- https://github.com/python/cpython/blob/3.11/Objects/dictobject.c#L3155
def beqM (a b : DictRef) : PyM Bool := do
  let a ← a.get
  let b ← b.get
  unless a.size == b.size do
    return false
  for entry in a.entries do
    let .some ah ak av := entry
      | continue
    let ⟨bi⟩ ← b.getEntryIdxCoreM ah (.up <$> ak.beqM ·)
    let some (.some _ _ bv) := b.entries[bi]?
      | return false
    let av ← av.get
    let bv ← bv.get
    unless (← av.beqM bv) do
      return false
  return true

/-- Returns a string representation of the dictionary. -/
-- Should follow the logic in CPython's `dict_repr`
-- https://github.com/python/cpython/blob/3.11/Objects/dictobject.c#L2403
def reprM (self : DictRef) : PyM String := do
  let es ← self.getAndMap (·.entries)
  return (← appendHead "{" 0 es).push '}'
where
  appendHead s i entries : PyM String := do
    if h : i < entries.size then
      if let .some _ k v := entries[i] then
        appendTail (← append s k v) (i+1) entries
      else appendHead s (i+1) entries
    else return s
  termination_by entries.size - i
  decreasing_by omega
  appendTail s i entries := do
    if h : i < entries.size then
      if let .some _ k v := entries[i] then
        appendTail (← append s!"{s}, " k v) (i+1) entries
      else appendTail s (i+1) entries
    else return s
  termination_by entries.size - i
  decreasing_by all_goals omega
  append s k v := do
    let k ← k.reprM
    let v ← (← v.get).reprM
    return s!"{s}{k}: {v}"
