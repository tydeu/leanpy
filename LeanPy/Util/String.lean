/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
syntax Authors Mac Malone
-/

namespace LeanPy

theorem isValidChar_of_lt_255 (h : n < 255) : isValidChar n := by
  grind

def upperHexChar (n : UInt32) : Char :=
  if h : n ≤ 9 then
    ⟨n + 48, isValidChar_of_lt_255 (by grind)⟩ -- + '0'
  else if h : n ≤ 0xf then
    ⟨n + 55, isValidChar_of_lt_255 (by grind)⟩ -- + ('A' - 10)
  else
    '*'

-- sanity check
example : "FEDCBA9876543210" =
  (String.mk <| (16).fold (init := []) fun i _ s =>
    upperHexChar i.toUInt32 :: s)
:= by decide

set_option linter.unusedVariables false in
def upperHexUInt64 (n : UInt64) : String :=
  .mk <| (go n []).leftpad 16 '0'
where
  go n s :=
    let d := upperHexChar (n % 16).toUInt32
    let s := d :: s
    let n' := n / 16
    if h : n' = 0 then
      s
    else
      go n' s
  termination_by n.toNat
  decreasing_by
    simp only [UInt64.toNat_div, UInt64.reduceToNat]
    refine Nat.div_lt_self (k := 16) ?_ (by simp)
    simp only [← UInt64.toNat_inj, UInt64.toNat_zero] at h
    exact Nat.pos_of_div_pos (Nat.pos_of_ne_zero h)
