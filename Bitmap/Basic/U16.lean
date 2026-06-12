import Mathlib.Data.Nat.Basic
import Init.Data.ByteArray

namespace Bitmaps

@[inline] def u16HighByte (x : UInt16) : UInt8 :=
  UInt8.ofNat (x.toNat / 256)

@[inline] def u16LowByte (x : UInt16) : UInt8 :=
  UInt8.ofNat x.toNat

def readU16BEAt (data : ByteArray) (base : Nat)
    (h : base + 1 < data.size) : UInt16 := by
  have h0 : base < data.size := by omega
  exact UInt16.ofNat ((data.get base h0).toNat * 256 + (data.get (base + 1) h).toNat)

def writeU16BEAt (data : ByteArray) (base : Nat)
    (h : base + 1 < data.size) (x : UInt16) : ByteArray := by
  have h0 : base < data.size := by omega
  let data1 := data.set base (u16HighByte x) h0
  have hsize1 : data1.size = data.size := by
    cases data with
    | mk arr =>
        simp [data1, ByteArray.set, ByteArray.size, Array.size_set]
  have h1 : base + 1 < data1.size := by
    simpa [hsize1] using h
  exact data1.set (base + 1) (u16LowByte x) h1

end Bitmaps
