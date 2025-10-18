/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
syntax Authors Mac Malone
-/
import Std.Data.DHashMap.Internal.Index

namespace LeanPy

abbrev Hash := UInt64

namespace TDict

inductive Entry (α : Type u) (β : Type v) where
| protected none
| protected some (hash : Hash) (k : α) (v : β)

namespace Entry

@[inline] def key? (e : Entry α β) : Option α :=
  match e with
  | .none => none
  | .some _ k _ => some k

@[inline] def value? (e : Entry α β) : Option β :=
  match e with
  | .none => none
  | .some _ _ v => some v

@[inline] def toOption  (e : Entry α β) : Option (α × β) :=
  match e with
  | .none => none
  | .some _ k v => some (k, v)

@[inline] def isSome  (e : Entry α β) : Bool :=
  match e with
  | .none => false
  | .some .. => true

@[inline] def key  (e : Entry α β) (h : isSome e) : α :=
  match e with
  | .some _ k _ => k

@[inline] def value  (e : Entry α β) (h : isSome e) : β :=
  match e with
  | .some _ _ v => v

end Entry

def Internal.mkBucketIdx
  (size : Nat) (h : 0 < size) (hash : Hash)
: {u : USize // u.toNat < size} := Std.DHashMap.Internal.mkIdx size h hash

@[inline] def Internal.numBucketsForCapacity (capacity : Nat) : Nat :=
  -- a "load factor" of 0.75 is the usual standard for hash maps
  capacity * 4 / 3

structure Bucket where
  private ofList ::
    toList : List Nat
    deriving Nonempty

namespace Bucket

@[match_pattern, inline] def nil : Bucket := ⟨.nil⟩

@[inline] def push (i : Nat) (self : Bucket) : Bucket :=
 ⟨.cons i self.toList⟩

end Bucket

@[specialize] def Internal.findEntryIdxM [Monad m]
  (bucket : Bucket) (entries : Array (Entry α β))  (isBEq : α → m (ULift Bool))
: m (ULift Nat) :=
  go bucket.toList
where go bucket := do
  match bucket with
  | .nil => return .up entries.size
  | .cons i t =>
    if h' : i < entries.size then
      if let .some _ k _ := entries[i] then
        if (← isBEq k).down then
          return .up i
        else go t
      else go t
    else go t

structure Buckets where
  toArray : Array Bucket
  size_toArray_pos : 0 < toArray.size

namespace Buckets

@[inline] def size (self : Buckets) : Nat :=
  self.toArray.size

theorem size_pos : 0 < size self := self.size_toArray_pos

/-- Create an set of empty buckets to store at most `capacity` elements. -/
@[inline] def emptyWithCapacity (capacity : Nat) : Buckets where
  toArray := Array.replicate (Internal.numBucketsForCapacity capacity).nextPowerOfTwo .nil
  size_toArray_pos := by simpa using Nat.pos_of_isPowerOfTwo (Nat.isPowerOfTwo_nextPowerOfTwo _)

instance : Nonempty Buckets := ⟨.emptyWithCapacity 0⟩

/-- Create an set of empty buckets that is double the size of `self`. -/
@[inline] def emptyAndExpand (self : Buckets) : Buckets where
  toArray := Array.replicate (self.size * 2) .nil
  size_toArray_pos := by simpa using Nat.mul_pos self.size_pos Nat.two_pos

structure Idx (self : Buckets) where
  toUSize : USize
  toUSize_lt : toUSize.toNat < self.size

@[inline] def getIdx (hash : Hash) (self : Buckets) : self.Idx :=
  let ⟨i, h⟩ := Internal.mkBucketIdx self.size self.size_pos hash
  ⟨i, h⟩

@[inline] def getByIdx (self : Buckets) (i : self.Idx) : Bucket :=
  self.toArray.uget (Idx.toUSize i) (Idx.toUSize_lt i)

@[inline] def get (hash : Hash) (self : Buckets) : Bucket :=
  let ⟨data, hd⟩ := self
  let ⟨i, h⟩ := Internal.mkBucketIdx data.size hd hash
  data.uget i h

@[inline] def set (self : Buckets) (i : self.Idx) (bucket : Bucket) : Buckets :=
  ⟨self.toArray.uset (Idx.toUSize i) bucket (Idx.toUSize_lt i), by simpa using self.size_pos⟩

def push (hash : Hash) (entryIdx : Nat) (self : Buckets) : Buckets :=
  let ⟨data, hd⟩ := self
  let ⟨i, h⟩ := Internal.mkBucketIdx data.size hd hash
  ⟨data.uset i (data[i].push entryIdx) h, by simpa⟩

end Buckets

end TDict

/-- A pure insertion-ordered dictionary of Lean-typed key-value pairs. -/
structure TDict (α : Type u) (β : Type v) where
  size : Nat
  buckets : TDict.Buckets
  entries : Array (TDict.Entry α β)
  deriving Nonempty

namespace TDict

def emptyWithCapacity (capacity : Nat) : TDict α β where
  size := 0
  buckets := .emptyWithCapacity capacity
  entries := .emptyWithCapacity capacity

def empty : TDict α β :=
  emptyWithCapacity 8

instance : EmptyCollection (TDict α β) := ⟨empty⟩
instance : Nonempty (TDict α β) := ⟨empty⟩

@[inline] def isEmpty (self : TDict α β) : Bool :=
  self.size == 0

def items (self : TDict α β) : Array (α × β) :=
  self.entries.filterMap (·.toOption)

def keys (self : TDict α β) : Array α :=
  self.entries.filterMap (·.key?)

def values (self : TDict α β) : Array β :=
  self.entries.filterMap (·.value?)

/-- Copies all the entries from `es` into `self` (which should be a new dictionary). -/
def reinsert (es : Array (Entry α β)) (self : TDict α β)  : TDict α β :=
  es.foldl (init := self) fun self e =>
    match e with
    | .none => self
    | e@(.some hash _ _) =>
      let {size, buckets, entries} := self
      let buckets := buckets.push hash entries.size
      let entries := entries.push e
      ⟨size, buckets, entries⟩

/-- Remove erased entries from the dictionary. -/
def compress (self : TDict α β) : TDict α β :=
  let {size, buckets := _, entries} := self
  reinsert entries {
    size
    buckets := .emptyWithCapacity size
    entries := .emptyWithCapacity size.nextPowerOfTwo
  }

/-- Copies all the entries from `self` into a new dictionary with a larger capacity. -/
def expand {α β} (self : TDict α β) : TDict α β :=
  let {size, buckets, entries} := self
  reinsert entries {
    size
    buckets := buckets.emptyAndExpand
    entries := .emptyWithCapacity size.nextPowerOfTwo
  }

@[inline] def expandIfNecessary (self : TDict α β) : TDict α β :=
  if Internal.numBucketsForCapacity self.size ≤ self.buckets.size then
    self
  else
    self.expand

def pushCore (hash : Hash) (k : α) (v : β) (self : TDict α β) : TDict α β :=
  let {size, buckets, entries} := self
  let buckets := buckets.push hash entries.size
  let entries := entries.push (.some hash k v)
  expandIfNecessary ⟨size + 1, buckets, entries⟩

/--
Looks for the first entry in the bucket identified by `hash`
whose key satisfies `isBEq`. If none, insert a `k => v` mapping into
the dictionary. Otherwise, set that entry said mapping.
-/
@[specialize] def insertCoreM [Monad m]
  (hash : Hash) (k : α) (v : β) (self : TDict α β) (isBEq : α → m (ULift Bool))
: m (TDict α β) := do
  let {size, buckets, entries} := self
  let i := buckets.getIdx hash
  let bucket := buckets.getByIdx i
  let ⟨entryIdx⟩ ← Internal.findEntryIdxM bucket entries isBEq
  if h' : entryIdx < entries.size then
    let entries := entries.set entryIdx (.some hash k v)
    return {size, buckets, entries}
  else
    let buckets := buckets.set i (bucket.push entries.size)
    let entries := entries.push (.some hash k v)
    return expandIfNecessary {size := size + 1, buckets, entries}

/--
Finds the first entry in the bucket identified by `hash`
whose key satisfies `isBEq` (if any) and erases it from the dictionary.

This is done by setting the matching entry to `Entry.none`.
It does not remove the entry index from the bucket.
-/
@[specialize] def eraseCoreM [Monad m]
  (hash : Hash) (self : TDict α β) (isBEq : α → m (ULift Bool))
: m (TDict α β) := do
  let {size, buckets, entries} := self
  let ⟨entryIdx⟩ ← Internal.findEntryIdxM (buckets.get hash) entries isBEq
  if h' : entryIdx < entries.size then
    let entries := entries.set entryIdx .none
    return {size := size - 1, buckets, entries}
  else
    return {size, buckets, entries}

/-! ## Operations for dictionaries with pure keys -/

@[inline] def push [Hashable α] (self : TDict α β)  (k : α) (v : β) : TDict α β :=
  self.pushCore (hash k) k v

@[inline] def Internal.isBEqM [Pure m] [BEq α] (k₁ k₂ : α) : m (ULift Bool) :=
  pure <| .up <| k₁ == k₂

@[inline] def insert
  [Hashable α] [BEq α] (self : TDict α β) (k : α) (v : β)
: TDict α β := Id.run <| self.insertCoreM (hash k) k v (Internal.isBEqM k)

@[specialize] def ofArray [Hashable α] [BEq α] (items : Array (α × β)) : TDict α β :=
  items.foldl (init := emptyWithCapacity items.size) fun d (k, v) =>
    d.insert k v

@[inline] def erase
  [Hashable α] [BEq α] (self : TDict α β) (k : α)
: TDict α β := Id.run <| self.eraseCoreM (hash k) (Internal.isBEqM k)

@[inline] def getEntryIdxCoreM [Monad m]
  (hash : Hash) (self : TDict α β) (isBEq : α → m (ULift Bool))
: m (ULift Nat) :=
  let {buckets, entries, ..} := self
  Internal.findEntryIdxM (buckets.get hash) entries isBEq

@[inline] def getEntryIdx
  [Hashable α] [BEq α] (k : α) (self : TDict α β)
: Nat := ULift.down.{0,0} <| Id.run do
  self.getEntryIdxCoreM (hash k) (Internal.isBEqM k)

@[inline] def contains
  [Hashable α] [BEq α] (k : α) (self : TDict α β)
: Bool :=
  let i := self.getEntryIdx k
  if h : i < self.entries.size then
    self.entries[i].isSome
  else false

@[inline] def get?
  [Hashable α] [BEq α] (k : α) (self : TDict α β)
: Option β :=
  let i := self.getEntryIdx k
  if h : i < self.entries.size then
    self.entries[i].value?
  else none

@[inline] def getEntryIdx?
  [Hashable α] [BEq α] (k : α) (self : TDict α β)
: Option (Fin self.entries.size) :=
  let i := self.getEntryIdx k
  if h : i < self.entries.size then some ⟨i, h⟩ else none

@[inline] def getEntry
  [Hashable α] [BEq α] (k : α) (self : TDict α β)
: Entry α β :=
  let i := self.getEntryIdx k
  if h : i < self.entries.size then self.entries[i] else .none

structure Mem [Hashable α] [BEq α] (self : TDict α β) (k : α)  where
  getEntryIdx_lt : self.getEntryIdx k < self.entries.size
  isSome_getElem_entries : self.entries[self.getEntryIdx k].isSome

instance [Hashable α] [BEq α] : Membership α (TDict α β) :=
  ⟨fun d a => contains a d⟩

@[simp] theorem contains_iff_mem
  [Hashable α] [BEq α] {self : TDict α β} :
  contains k self ↔ k ∈ self
:= Iff.intro id id

theorem mem_iff_mem
  [Hashable α] [BEq α] {self : TDict α β} :
  k ∈ self ↔ self.Mem k
:= by
  simp only [← contains_iff_mem, contains, TDict.contains]
  apply Iff.intro
  · intro h
    split at h
    · next h_lt => exact ⟨h_lt, h⟩
    · simp at h
  · intro ⟨h_lt, h_isSome⟩
    simp [h_lt, h_isSome]

theorem getEntryIdx_lt_of_mem
  [Hashable α] [BEq α] {self : TDict α β}
  (h : k ∈ self) : self.getEntryIdx k < self.entries.size
:= Mem.getEntryIdx_lt (mem_iff_mem.mp h)

macro_rules
| `(tactic|get_elem_tactic_extensible) =>
  `(tactic|with_reducible apply getEntryIdx_lt_of_mem; get_elem_tactic_extensible; done)

theorem isSome_getElem_entries_of_mem
  [Hashable α] [BEq α] {self : TDict α β}
  (h : k ∈ self) : self.entries[self.getEntryIdx k].isSome
:= Mem.isSome_getElem_entries (mem_iff_mem.mp h)

@[inline] def get
  [Hashable α] [BEq α] (k : α) (self : TDict α β) (h : k ∈ self)
: β := self.entries[self.getEntryIdx k].value (isSome_getElem_entries_of_mem h)

instance [Hashable α] [BEq α] : GetElem? (TDict α β) α β (fun d k => k ∈ d) where
  getElem d k h := get k d h
  getElem? d k := get? k d
