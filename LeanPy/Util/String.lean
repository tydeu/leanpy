/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
syntax Authors Mac Malone
-/

namespace LeanPy

def upperHexByte (n : UInt8) : UInt8 :=
  if n ≤ 9 then
    n + 48 -- + '0'
  else
    n + 55 -- + ('A' - 10)

theorem isValidChar_of_lt_256 (h : n < 256) : isValidChar n := by
  grind

def upperHexChar (n : UInt8) : Char :=
  ⟨upperHexByte n |>.toUInt32, isValidChar_of_lt_256 <| by
    simp [UInt32.lt_iff_toNat_lt, (upperHexByte n).toNat_lt]⟩

-- sanity check
example : "FEDCBA9876543210" =
  (String.mk <| (16).fold (init := []) fun i _ s =>
    upperHexChar i.toUInt8 :: s)
:= by decide

def upperHexUInt8 (n : UInt8) (init := "") : String :=
  init
  |>.push (upperHexChar (n >>> 4))
  |>.push (upperHexChar (n &&& 0xf))

def upperHexUInt16 (n : UInt16) (init := "") : String :=
  init
  |>.push (upperHexChar (n >>> 4 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n >>> 8 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n >>> 12).toUInt8)
  |>.push (upperHexChar (n &&& 0xf).toUInt8)

def upperHexUInt32 (n : UInt32) (init := "") : String :=
  init
  |>.push (upperHexChar (n >>> 4 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n >>> 8 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n >>> 12 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n >>> 16 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n >>> 20 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n >>> 24 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n >>> 28).toUInt8)
  |>.push (upperHexChar (n &&& 0xf).toUInt8)

def upperHexUInt64 (n : UInt64) (init := "") : String :=
  init
  |>.push (upperHexChar (n >>> 4 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n >>> 8 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n >>> 12 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n >>> 16 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n >>> 20 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n >>> 24 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n >>> 28 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n >>> 32 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n >>> 36 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n >>> 40 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n >>> 44 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n >>> 48 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n >>> 52 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n >>> 56 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n >>> 60).toUInt8)
  |>.push (upperHexChar (n &&& 0xf).toUInt8)
