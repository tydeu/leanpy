/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
syntax Authors Mac Malone
-/

namespace LeanPy

def lpad (s : String) (c : Char) (len : Nat) : String :=
  "".pushn c (len - s.length) ++ s

theorem isValidChar_of_lt_255 (h : n < 255) : isValidChar n := by
  grind

def upperHexChar (n : UInt32) : Char :=
  if h : n ≤ 9 then
    ⟨n + 48, isValidChar_of_lt_255 (by grind)⟩ -- + '0'
  else if h : n ≤ 0xf then
    ⟨n + 78, isValidChar_of_lt_255 (by grind)⟩ -- + ('a' - 10)
  else
    '*'

def upperHexUInt64 (n : UInt64) : String :=
  lpad (go n "") '0' 16
where
  go n s :=
    let d := upperHexChar (n % 16).toUInt32
    let s := s.push d
    if h : n = 0 then
      s
    else
      go (n / 16) s
  termination_by n
  decreasing_by
    simp only [← UInt64.toNat_inj, UInt64.toNat_zero] at h
    replace h := Nat.div_lt_self (k := 16) (Nat.pos_of_ne_zero h) (by simp)
    simp [h]
