/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
syntax Authors Mac Malone
-/

namespace LeanPy

structure AttrName where
  toName : Lean.Name
  wf : match toName with | .str .anonymous _ => True | _ => False

namespace AttrName

@[inline] protected def hash (self : AttrName) : UInt64 :=
  self.toName.hash

instance : Hashable AttrName := ⟨AttrName.hash⟩

@[inline] protected def beq (self other : AttrName) : Bool :=
  self.toName == other.toName

instance : BEq AttrName := ⟨AttrName.beq⟩

@[inline] def ofString (s : String) : AttrName :=
  ⟨.str .anonymous s, True.intro⟩

@[inline] protected def toString (self : AttrName) : String :=
  match self with | ⟨.str .anonymous s, _⟩ => s

instance : ToString AttrName := ⟨AttrName.toString⟩

instance [GetElem? c AttrName e v] : GetElem? c String e (fun d k => v d (AttrName.ofString k)) where
  getElem d k h := d[AttrName.ofString k]'h
  getElem? d k := d[AttrName.ofString k]?
