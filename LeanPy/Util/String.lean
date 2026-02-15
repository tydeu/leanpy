/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
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
#guard "0123456789ABCDEF" =
  (String.ofList <| (0...(16 : UInt8)).toList.map upperHexChar)

def upperHexUInt8 (n : UInt8) (init := "") : String :=
  init
  |>.push (upperHexChar (n >>> 4))
  |>.push (upperHexChar (n &&& 0xf))

-- sanity check
#guard "01" = upperHexUInt8 0x01

def upperHexUInt16 (n : UInt16) (init := "") : String :=
  init
  |>.push (upperHexChar (n >>> 12).toUInt8)
  |>.push (upperHexChar (n >>> 8 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n >>> 4 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n &&& 0xf).toUInt8)

-- sanity check
#guard "0123" = upperHexUInt16 0x0123

def upperHexUInt32 (n : UInt32) (init := "") : String :=
  init
  |>.push (upperHexChar (n >>> 28).toUInt8)
  |>.push (upperHexChar (n >>> 24 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n >>> 20 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n >>> 16 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n >>> 12 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n >>> 8 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n >>> 4 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n &&& 0xf).toUInt8)

-- sanity check
#guard "01234567" = upperHexUInt32 0x01234567

def upperHexUInt64 (n : UInt64) (init := "") : String :=
  init
  |>.push (upperHexChar (n >>> 60 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n >>> 56 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n >>> 52 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n >>> 48 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n >>> 44 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n >>> 40 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n >>> 36 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n >>> 32 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n >>> 28 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n >>> 24 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n >>> 20 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n >>> 16 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n >>> 12 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n >>> 8 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n >>> 4 &&& 0xf).toUInt8)
  |>.push (upperHexChar (n &&& 0xf).toUInt8)

-- sanity check
#guard "0123456789ABCDEF" = upperHexUInt64 0x0123456789ABCDEF
