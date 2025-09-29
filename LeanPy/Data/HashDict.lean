/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
syntax Authors Mac Malone
-/
import Std.Data.DHashMap.Internal.Index

namespace LeanPy

abbrev Hash := UInt64

namespace HashDict

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

@[inline] def Internal.isBEqM [Pure m] [BEq α] (k₁ k₂ : α) : m (ULift Bool) :=
  pure <| .up <| k₁ == k₂

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

/-- Implementation detail of `HashDict`. -/
structure Raw (α : Type u) (β : Type v) where
  size : Nat
  buckets : Buckets
  entries : Array (Entry α β)
  deriving Nonempty

namespace Raw

def emptyWithCapacity (capacity : Nat) : Raw α β where
  size := 0
  buckets := .emptyWithCapacity capacity
  entries := .emptyWithCapacity capacity

/-- Copies all the entries from `es` into `self` (which should be a new dictionary). -/
def reinsert (es : Array (Entry α β)) (self : Raw α β)  : Raw α β :=
  es.foldl (init := self) fun self e =>
    match e with
    | .none => self
    | e@(.some hash _ _) =>
      let {size, buckets, entries} := self
      let buckets := buckets.push hash entries.size
      let entries := entries.push e
      ⟨size, buckets, entries⟩

/-- Remove erased entries from the dictionary. -/
def compress (self : Raw α β) : Raw α β :=
  let {size, buckets := _, entries} := self
  reinsert entries {
    size
    buckets := .emptyWithCapacity size
    entries := .emptyWithCapacity size.nextPowerOfTwo
  }

/-- Copies all the entries from `self` into a new dictionary with a larger capacity. -/
def expand {α β} (self : Raw α β) : Raw α β :=
  let {size, buckets, entries} := self
  reinsert entries {
    size
    buckets := buckets.emptyAndExpand
    entries := .emptyWithCapacity size.nextPowerOfTwo
  }

@[inline] def expandIfNecessary (self : Raw α β) : Raw α β :=
  if Internal.numBucketsForCapacity self.size ≤ self.buckets.size then
    self
  else
    self.expand

def pushCore (hash : Hash) (k : α) (v : β) (self : Raw α β) : Raw α β :=
  let {size, buckets, entries} := self
  let buckets := buckets.push hash entries.size
  let entries := entries.push (.some hash k v)
  expandIfNecessary ⟨size + 1, buckets, entries⟩

@[inline] def push [Hashable α] (k : α) (v : β) (self : Raw α β) : Raw α β :=
  self.pushCore (hash k) k v

/--
Looks for the first entry in the bucket identified by `hash`
whose key satisfies `isBEq`. If none, insert a `k => v` mapping into
the dictionary. Otherwise, set that entry said mapping.
-/
@[specialize] def insertCoreM [Monad m]
  (hash : Hash) (k : α) (v : β) (self : Raw α β) (isBEq : α → m (ULift Bool))
: m (Raw α β) := do
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

@[inline] def insert
  [Hashable α] [BEq α] (k : α) (v : β) (self : Raw α β)
: Raw α β := Id.run <| self.insertCoreM (hash k) k v (Internal.isBEqM k)

/--
Finds the first entry in the bucket identified by `hash`
whose key satisfies `isBEq` (if any) and erases it from the dictionary.

This is done by setting the matching entry to `Entry.none`.
It does not remove the entry index from the bucket.
-/
@[specialize] def eraseCoreM [Monad m]
  (hash : Hash) (self : Raw α β) (isBEq : α → m (ULift Bool))
: m (Raw α β) := do
  let {size, buckets, entries} := self
  let ⟨entryIdx⟩ ← Internal.findEntryIdxM (buckets.get hash) entries isBEq
  if h' : entryIdx < entries.size then
    let entries := entries.set entryIdx .none
    return {size := size - 1, buckets, entries}
  else
    return {size, buckets, entries}

@[inline] def erase
  [Hashable α] [BEq α] (k : α) (self : Raw α β)
: Raw α β := Id.run <| self.eraseCoreM (hash k) (Internal.isBEqM k)

@[inline] def getEntryIdxCoreM [Monad m]
  (hash : Hash) (self : Raw α β) (isBEq : α → m (ULift Bool))
: m (ULift Nat) :=
  let {buckets, entries, ..} := self
  Internal.findEntryIdxM (buckets.get hash) entries isBEq

@[inline] def getEntryIdx
  [Hashable α] [BEq α] (k : α) (self : Raw α β)
: Nat := ULift.down.{0,0} <| Id.run do
  self.getEntryIdxCoreM (hash k) (Internal.isBEqM k)

@[inline] def contains
  [Hashable α] [BEq α] (k : α) (self : Raw α β)
: Bool :=
  let i := self.getEntryIdx k
  if h : i < self.entries.size then
    self.entries[i].isSome
  else false

@[inline] def get?
  [Hashable α] [BEq α] (k : α) (self : Raw α β)
: Option β :=
  let i := self.getEntryIdx k
  if h : i < self.entries.size then
    self.entries[i].value?
  else none

end Raw
end HashDict

/-- An insertion-ordered dictionary backed by a `Std.HashMap`. -/
structure HashDict (α : Type u) (β : Type v) where
  raw : HashDict.Raw α β

namespace HashDict

def emptyWithCapacity (capacity : Nat) : HashDict α β where
  raw := .emptyWithCapacity capacity

def empty : HashDict α β :=
  emptyWithCapacity 8

instance : EmptyCollection (HashDict α β) := ⟨empty⟩
instance : Nonempty (HashDict α β) := ⟨empty⟩

@[inline] def size (self : HashDict α β) : Nat :=
  self.raw.size

@[inline] def entries (self : HashDict α β) : Array (Entry α β) :=
  self.raw.entries

def items (self : HashDict α β) : Array (α × β) :=
  self.entries.filterMap (·.toOption)

@[inline] protected def beq
  [BEq (α × β)] (self other : HashDict α β)
: Bool := self.items == other.items

instance [BEq (α × β)] : BEq (HashDict α β) := ⟨HashDict.beq⟩

@[inline] def isEmpty (self : HashDict α β) : Bool :=
  self.size == 0

def keys (self : HashDict α β) : Array α :=
  self.entries.filterMap (·.key?)

def values (self : HashDict α β) : Array β :=
  self.entries.filterMap (·.value?)

@[inline] def getEntryIdx [Hashable α] [BEq α] (k : α) (self : HashDict α β) : Nat :=
  self.raw.getEntryIdx k

@[inline] def getEntryIdx?
  [Hashable α] [BEq α] (k : α) (self : HashDict α β)
: Option (Fin self.entries.size) :=
  let i := self.getEntryIdx k
  if h : i < self.entries.size then some ⟨i, h⟩ else none

@[inline] def getEntry
  [Hashable α] [BEq α] (k : α) (self : HashDict α β)
: Entry α β :=
  let i := self.getEntryIdx k
  if h : i < self.entries.size then self.entries[i] else .none

@[inline] def contains [Hashable α] [BEq α] (k : α) (self : HashDict α β) : Bool :=
  self.raw.contains k

structure Mem [Hashable α] [BEq α] (self : HashDict α β) (k : α)  where
  getEntryIdx_lt : self.getEntryIdx k < self.entries.size
  isSome_getElem_entries : self.entries[self.getEntryIdx k].isSome

instance [Hashable α] [BEq α] : Membership α (HashDict α β) :=
  ⟨fun d a => contains a d⟩

@[simp] theorem contains_iff_mem
  [Hashable α] [BEq α] {self : HashDict α β} :
  contains k self ↔ k ∈ self
:= Iff.intro id id

theorem mem_iff_mem
  [Hashable α] [BEq α] {self : HashDict α β} :
  k ∈ self ↔ self.Mem k
:= by
  simp only [← contains_iff_mem, contains, Raw.contains]
  apply Iff.intro
  · intro h
    split at h
    · next h_lt => exact ⟨h_lt, h⟩
    · simp at h
  · intro h
    have ⟨h_lt, h_isSome⟩ := h
    simp only [getEntryIdx, entries] at h_lt h_isSome
    simp [h_lt, h_isSome]

theorem getEntryIdx_lt_of_mem
  [Hashable α] [BEq α] {self : HashDict α β}
  (h : k ∈ self) : self.getEntryIdx k < self.entries.size
:= Mem.getEntryIdx_lt (mem_iff_mem.mp h)

macro_rules
| `(tactic|get_elem_tactic_extensible) =>
  `(tactic|with_reducible apply getEntryIdx_lt_of_mem; get_elem_tactic_extensible; done)

theorem isSome_getElem_entries_of_mem
  [Hashable α] [BEq α] {self : HashDict α β}
  (h : k ∈ self) : self.entries[self.getEntryIdx k].isSome
:= Mem.isSome_getElem_entries (mem_iff_mem.mp h)

@[inline] def get
  [Hashable α] [BEq α] (k : α) (self : HashDict α β) (h : k ∈ self)
: β := self.entries[self.getEntryIdx k].value (isSome_getElem_entries_of_mem h)

@[inline] def get?
  [Hashable α] [BEq α] (k : α) (self : HashDict α β)
: Option β := self.getEntry k |>.value?

instance [Hashable α] [BEq α] : GetElem? (HashDict α β) α β (fun d k => k ∈ d) where
  getElem d k h := get k d h
  getElem? d k := get? k d

@[inline] def insert
  [Hashable α] [BEq α] (k : α) (v : β) (self : HashDict α β)
: HashDict α β := ⟨self.raw.insert k v⟩

@[specialize] def ofArray [Hashable α] [BEq α] (items : Array (α × β)) : HashDict α β :=
  items.foldl (init := emptyWithCapacity items.size) fun d (k, v) =>
    d.insert k v

@[inline] def erase
  [Hashable α] [BEq α] (k : α) (self : HashDict α β)
: HashDict α β := ⟨self.raw.erase k⟩

/-- Remove erased entries from the dictionary. -/
@[inline] def compress (self : HashDict α β) : HashDict α β :=
  ⟨self.raw.compress⟩
