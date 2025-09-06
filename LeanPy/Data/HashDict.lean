/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
syntax Authors Mac Malone
-/
import Std.Data.HashMap
import Std.Data.HashMap.RawLemmas

namespace LeanPy

inductive DictEntry (α : Type u) (β : Type v) where
| protected none
| protected some (k : α) (v : β)

namespace DictEntry

@[inline] def key? (e : DictEntry α β) : Option α :=
  match e with
  | .none => none
  | .some k _ => some k

@[inline] def value? (e : DictEntry α β) : Option β :=
  match e with
  | .none => none
  | .some _ v => some v

@[inline] def toOption  (e : DictEntry α β) : Option (α × β) :=
  match e with
  | .none => none
  | .some k v => some (k, v)

@[inline] def isSome  (e : DictEntry α β) : Bool :=
  match e with
  | .none => false
  | .some .. => true

@[inline] def key  (e : DictEntry α β) (h : isSome e) : α :=
  match e with
  | .some k _ => k

@[inline] def value  (e : DictEntry α β) (h : isSome e) : β :=
  match e with
  | .some _ v => v

end DictEntry

/-- Implementation detail of `HashDict`. -/
structure HashDict.Raw (α : Type u) (β : Type v) where
  size : Nat
  indices : Std.HashMap.Raw α Nat
  entries : Array (DictEntry α β)
  deriving Nonempty

/-- An insertion-ordered dictionary backed by a `Std.HashMap`. -/
structure HashDict (α : Type u) [BEq α] [Hashable α] (β : Type v) where
  raw : HashDict.Raw α β
  indices_raw_wf : raw.indices.WF

namespace HashDict
variable {α : Type u} [BEq α] [Hashable α] {β : Type v}

def Raw.emptyWithCapacity (capacity : Nat) : HashDict.Raw α β where
  size := 0
  indices := .emptyWithCapacity capacity
  entries := .emptyWithCapacity capacity

def emptyWithCapacity (capacity : Nat) : HashDict α β where
  raw := .emptyWithCapacity capacity
  indices_raw_wf := .emptyWithCapacity

def empty : HashDict α β :=
  emptyWithCapacity 8

instance : EmptyCollection (HashDict α β) := ⟨empty⟩
instance : Nonempty (HashDict α β) := ⟨empty⟩

@[inline] def size (self : HashDict α β) : Nat :=
  self.raw.size

@[inline] def entries (self : HashDict α β) : Array (DictEntry α β) :=
  self.raw.entries

@[inline] def indices (self : HashDict α β) : Std.HashMap α Nat :=
  ⟨⟨self.raw.indices.inner, self.indices_raw_wf.out⟩⟩

def items (self : HashDict α β) : Array (α × β) :=
  self.entries.filterMap (·.toOption)

@[specialize] protected def beq [BEq (α × β)] (self other : HashDict α β) : Bool :=
  self.items == other.items

instance [BEq (α × β)] : BEq (HashDict α β) := ⟨HashDict.beq⟩

@[inline] def isEmpty (self : HashDict α β) : Bool :=
  self.size == 0

def keys (self : HashDict α β) : Array α :=
  self.entries.filterMap (·.key?)

def values (self : HashDict α β) : Array β :=
  self.entries.filterMap (·.value?)

@[specialize] def contains (k : α) (self : HashDict α β) : Bool :=
  self.indices.contains k

structure Mem (self : HashDict α β) (k : α) : Prop where
  mem_indices : k ∈ self.indices
  getElem_indices_lt : self.indices[k] < self.entries.size
  isSome_getElem_entries : self.entries[self.indices[k]].isSome

instance : Membership α (HashDict α β) := ⟨Mem⟩

theorem mem_indices_of_mem {self : HashDict α β}
  (h : k ∈ self) : k ∈ self.indices
:= Mem.mem_indices h

macro_rules
| `(tactic|get_elem_tactic_extensible) =>
  `(tactic|with_reducible apply mem_indices_of_mem; get_elem_tactic_extensible; done)

theorem getElem_indices_lt_of_mem {self : HashDict α β}
  (h : k ∈ self) : self.indices[k] < self.entries.size
:= Mem.getElem_indices_lt h

macro_rules
| `(tactic|get_elem_tactic_extensible) =>
  `(tactic|with_reducible apply getElem_indices_lt_of_mem; get_elem_tactic_extensible; done)

theorem isSome_getElem_entries_of_mem {self : HashDict α β}
  (h : k ∈ self) : self.entries[self.indices[k]].isSome
:= Mem.isSome_getElem_entries h

private theorem indices_insert_eq_insert_raw_erase {self : HashDict α β} :
  ⟨self.indices.insert k v |>.inner.inner⟩ = (raw self).indices.insert k v
:= by
  simp only [HashDict.indices]
  simp only [Std.HashMap.insert, Std.DHashMap.insert]
  simp only [Std.HashMap.Raw.insert, Std.DHashMap.Raw.insert]
  simp [self.indices_raw_wf.out.size_buckets_pos]

@[specialize] def get (a : α) (self : HashDict α β) (h : a ∈ self) : β :=
  let i := self.indices[a]
  self.entries[i].value (isSome_getElem_entries_of_mem h)

@[inline] def getEntryIdx (k : α) (self : HashDict α β) : Nat :=
  go self.indices k self.entries.size
where @[specialize] go indices k defVal : Nat :=
  indices.getD k defVal -- specializes `getD`

@[inline] def getEntryIdx? (k : α) (self : HashDict α β) : Option (Fin self.entries.size) :=
  let i := self.getEntryIdx k
  if h : i < self.entries.size then some ⟨i, h⟩ else none

@[inline] def getEntry (k : α) (self : HashDict α β) : DictEntry α β :=
  let i := self.getEntryIdx k
  if h : i < self.entries.size then self.entries[i] else .none

@[inline] def get? (k : α) (self : HashDict α β) : Option β :=
  self.getEntry k |>.value?

instance : GetElem? (HashDict α β) α β (fun d k => k ∈ d) where
  getElem d k h := get k d h
  getElem? d k := get? k d

@[specialize] def push (k : α) (v : β) (self : HashDict α β) : HashDict α β where
  raw.size := self.raw.size + 1
  raw.entries := self.entries.push <| .some k v
  raw.indices := ⟨self.indices.insert k self.entries.size |>.inner.inner⟩
  indices_raw_wf := self.indices_insert_eq_insert_raw_erase ▸
    .insert self.indices_raw_wf

@[specialize] def ofArray (items : Array (α × β)) : HashDict α β :=
  items.foldl (init := emptyWithCapacity items.size) fun d (k, v) =>
    d.push k v

@[specialize] def insert (k : α) (v : β) (self : HashDict α β) : HashDict α β :=
  if let some i := self.getEntryIdx? k then
    let size := if self.entries[i].isSome then self.size else self.size + 1
    {self with
      raw.size := size,
      raw.entries := self.entries.set i (.some k v)
    }
  else
    self.push k v

private theorem indices_erase_eq_indices_raw_erase {self : HashDict α β} :
  ⟨self.indices.erase k |>.inner.inner⟩ = (raw self).indices.erase k
:= by
  simp only [HashDict.indices]
  simp only [Std.HashMap.erase, Std.DHashMap.erase]
  simp only [Std.HashMap.Raw.erase, Std.DHashMap.Raw.erase]
  simp [self.indices_raw_wf.out.size_buckets_pos]

@[specialize] def erase (k : α) (self : HashDict α β) : HashDict α β :=
  if let some i := self.getEntryIdx? k then
    if self.entries[i].isSome then
      {self with
        raw.size := self.raw.size - 1
        raw.indices := ⟨self.indices.erase k |>.inner.inner⟩
        raw.entries := self.raw.entries.set i .none i.isLt
        indices_raw_wf := self.indices_erase_eq_indices_raw_erase ▸
          .erase self.indices_raw_wf
      }
    else
      self
  else
    self

/-- Remove erased entries from the dictionary. -/
@[inline] def compress (self : HashDict α β) : HashDict α β :=
  self.entries.foldl (init := .emptyWithCapacity self.size) fun d e =>
    match e with | .none => d | .some k v => d.push k v
