import Bitmap.Basic.U16
import Init.Data.Array.Lemmas

namespace Bitmaps

namespace Lemmas

/-- Splitting a `UInt16` into big-endian bytes and reading it back is identity.
This is the arithmetic core reused by 16-bit pixel layout proofs. -/
lemma u16_from_be_bytes (x : UInt16) :
    UInt16.ofNat ((u16HighByte x).toNat * 256 + (u16LowByte x).toNat) = x := by
  unfold u16HighByte u16LowByte
  rw [UInt8.toNat_ofNat', UInt8.toNat_ofNat']
  have hx : x.toNat < 2 ^ 16 := UInt16.toNat_lt x
  have hdivLt : x.toNat / 256 < 256 := by omega
  rw [Nat.mod_eq_of_lt hdivLt]
  have hrec : x.toNat / 256 * 256 + x.toNat % 256 = x.toNat := by
    have h := Nat.div_add_mod x.toNat 256
    omega
  rw [hrec]
  exact UInt16.ofNat_toNat

/-- Converting an 8-bit byte to `UInt16` preserves its numeric value.
This lets byte reconstruction proofs survive UInt normalization. -/
lemma u8_toUInt16_toNat (x : UInt8) : x.toUInt16.toNat = x.toNat := by
  cases x
  simp [UInt8.toUInt16, UInt8.toNat, UInt16.toNat]

/-- The same reconstruction fact after Lean normalizes `UInt16.ofNat`.
It closes goals produced by simplifying big-endian byte reads. -/
lemma u16_from_be_bytes_uint16 (x : UInt16) :
    (u16HighByte x).toUInt16 * 256 + (u16LowByte x).toUInt16 = x := by
  apply UInt16.toNat_inj.mp
  simp [UInt16.toNat_add, UInt16.toNat_mul, UInt16.toNat_ofNat]
  unfold u16HighByte u16LowByte
  rw [UInt8.toNat_ofNat', UInt8.toNat_ofNat']
  have hx : x.toNat < 2 ^ 16 := UInt16.toNat_lt x
  have hdivLt : x.toNat / 256 < 256 := by omega
  rw [Nat.mod_eq_of_lt hdivLt]
  have hrec : x.toNat / 256 * 256 + x.toNat % 256 = x.toNat := by
    have h := Nat.div_add_mod x.toNat 256
    omega
  rw [hrec]
  omega

/-- Setting one byte keeps the byte array size.
This is the byte-array side condition for multi-byte pixel proofs. -/
lemma byteArray_set_size {bs : ByteArray} {i : Nat} (hi : i < bs.size) {v : UInt8} :
    (bs.set i v hi).size = bs.size := by
  cases bs with
  | mk arr =>
      simp [ByteArray.set, ByteArray.size, Array.size_set]

/-- A byte write at another index does not affect a read.
This packages the array-level `set_ne` fact for multi-byte pixel proofs. -/
lemma byteArray_get_set_ne {bs : ByteArray} {i j : Nat}
    (hi : i < bs.size) (hj : j < bs.size) (hij : i ≠ j) {v : UInt8}
    (h' : j < (bs.set i v hi).size) :
    (bs.set i v hi).get j h' = bs.get j hj := by
  cases bs with
  | mk arr =>
      simpa [ByteArray.set, ByteArray.get] using
        (Array.getElem_set_ne (xs := arr) (i := i) (j := j) (h' := hi) (pj := hj)
          (h := hij))

/-- Writing a big-endian `UInt16` sample preserves the byte buffer size.
It is the size side condition used by 16-bit pixel instances. -/
lemma writeU16BEAt_size
    (data : ByteArray) (base : Nat) (h : base + 1 < data.size) (x : UInt16) :
    (writeU16BEAt data base h x).size = data.size := by
  unfold writeU16BEAt
  simp [byteArray_set_size]

/-- Reading the same two-byte slot just written returns the written `UInt16`.
This is the sample-level read/write law lifted to 16-bit pixels. -/
lemma readU16BEAt_write_same
    (data : ByteArray) (base : Nat) (h : base + 1 < data.size) (x : UInt16) :
    readU16BEAt (writeU16BEAt data base h x) base
      (by simpa [writeU16BEAt_size (data := data) (base := base) (h := h) (x := x)] using h) = x := by
  have h0 : base < data.size := by omega
  let data1 := data.set base (u16HighByte x) h0
  have hsize1 : data1.size = data.size := by
    simpa [data1] using (byteArray_set_size (bs := data) (i := base) (hi := h0)
      (v := u16HighByte x))
  have h1 : base + 1 < data1.size := by
    simpa [hsize1] using h
  let data2 := data1.set (base + 1) (u16LowByte x) h1
  have hsize2 : data2.size = data.size := by
    have hsize2' : data2.size = data1.size := by
      simpa [data2] using (byteArray_set_size (bs := data1) (i := base + 1)
        (hi := h1) (v := u16LowByte x))
    simpa [hsize1] using hsize2'
  have h0d1 : base < data1.size := by
    simpa [hsize1] using h0
  have h0d2 : base < data2.size := by
    simpa [hsize2] using h0
  have h1d2 : base + 1 < data2.size := by
    simpa [hsize2] using h
  have hhi : data2.get base h0d2 = u16HighByte x := by
    have hkeep : data2.get base h0d2 = data1.get base h0d1 := by
      simpa [data2] using
        (byteArray_get_set_ne (bs := data1) (i := base + 1) (j := base)
          (hi := h1) (hj := h0d1) (hij := by omega) (v := u16LowByte x)
          (h' := h0d2))
    have hset : data1.get base h0d1 = u16HighByte x := by
      simp [data1, ByteArray.set, ByteArray.get]
    simp [hkeep, hset]
  have hlo : data2.get (base + 1) h1d2 = u16LowByte x := by
    simp [data2, ByteArray.set, ByteArray.get]
  unfold readU16BEAt writeU16BEAt
  simp [data1, data2, hhi, hlo, u16_from_be_bytes_uint16]

/-- A later non-overlapping two-byte write preserves an earlier `UInt16` read.
This keeps RGB/RGBA component proofs small when writing several samples. -/
lemma readU16BEAt_write_after
    (data : ByteArray) (readBase writeBase : Nat)
    (hread : readBase + 1 < data.size) (hwrite : writeBase + 1 < data.size)
    (x : UInt16) (hbefore : readBase + 1 < writeBase) :
    readU16BEAt (writeU16BEAt data writeBase hwrite x) readBase
      (by simpa [writeU16BEAt_size (data := data) (base := writeBase) (h := hwrite) (x := x)] using hread) =
    readU16BEAt data readBase hread := by
  have hr0 : readBase < data.size := by omega
  have hw0 : writeBase < data.size := by omega
  let data1 := data.set writeBase (u16HighByte x) hw0
  have hsize1 : data1.size = data.size := by
    simpa [data1] using (byteArray_set_size (bs := data) (i := writeBase)
      (hi := hw0) (v := u16HighByte x))
  have hw1 : writeBase + 1 < data1.size := by
    simpa [hsize1] using hwrite
  let data2 := data1.set (writeBase + 1) (u16LowByte x) hw1
  have hsize2 : data2.size = data.size := by
    have hsize2' : data2.size = data1.size := by
      simpa [data2] using (byteArray_set_size (bs := data1) (i := writeBase + 1)
        (hi := hw1) (v := u16LowByte x))
    simpa [hsize1] using hsize2'
  have hr0d1 : readBase < data1.size := by simpa [hsize1] using hr0
  have hr1d1 : readBase + 1 < data1.size := by simpa [hsize1] using hread
  have hr0d2 : readBase < data2.size := by simpa [hsize2] using hr0
  have hr1d2 : readBase + 1 < data2.size := by simpa [hsize2] using hread
  have h0keep : data2.get readBase hr0d2 = data.get readBase hr0 := by
    have h2 : data2.get readBase hr0d2 = data1.get readBase hr0d1 := by
      simpa [data2] using
        (byteArray_get_set_ne (bs := data1) (i := writeBase + 1) (j := readBase)
          (hi := hw1) (hj := hr0d1) (hij := by omega) (v := u16LowByte x)
          (h' := hr0d2))
    have h1 : data1.get readBase hr0d1 = data.get readBase hr0 := by
      simpa [data1] using
        (byteArray_get_set_ne (bs := data) (i := writeBase) (j := readBase)
          (hi := hw0) (hj := hr0) (hij := by omega) (v := u16HighByte x)
          (h' := hr0d1))
    simp [h2, h1]
  have h1keep : data2.get (readBase + 1) hr1d2 = data.get (readBase + 1) hread := by
    have h2 : data2.get (readBase + 1) hr1d2 = data1.get (readBase + 1) hr1d1 := by
      simpa [data2] using
        (byteArray_get_set_ne (bs := data1) (i := writeBase + 1) (j := readBase + 1)
          (hi := hw1) (hj := hr1d1) (hij := by omega) (v := u16LowByte x)
          (h' := hr1d2))
    have h1 : data1.get (readBase + 1) hr1d1 = data.get (readBase + 1) hread := by
      simpa [data1] using
        (byteArray_get_set_ne (bs := data) (i := writeBase) (j := readBase + 1)
          (hi := hw0) (hj := hread) (hij := by omega) (v := u16HighByte x)
          (h' := hr1d1))
    simp [h2, h1]
  unfold readU16BEAt writeU16BEAt
  simp [data1, data2, h0keep, h1keep]

/-- An earlier non-overlapping two-byte write preserves a later `UInt16` read.
This is the symmetric preservation fact for multi-component 16-bit pixels. -/
lemma readU16BEAt_write_before
    (data : ByteArray) (readBase writeBase : Nat)
    (hread : readBase + 1 < data.size) (hwrite : writeBase + 1 < data.size)
    (x : UInt16) (hbefore : writeBase + 1 < readBase) :
    readU16BEAt (writeU16BEAt data writeBase hwrite x) readBase
      (by simpa [writeU16BEAt_size (data := data) (base := writeBase) (h := hwrite) (x := x)] using hread) =
    readU16BEAt data readBase hread := by
  have hr0 : readBase < data.size := by omega
  have hw0 : writeBase < data.size := by omega
  let data1 := data.set writeBase (u16HighByte x) hw0
  have hsize1 : data1.size = data.size := by
    simpa [data1] using (byteArray_set_size (bs := data) (i := writeBase)
      (hi := hw0) (v := u16HighByte x))
  have hw1 : writeBase + 1 < data1.size := by
    simpa [hsize1] using hwrite
  let data2 := data1.set (writeBase + 1) (u16LowByte x) hw1
  have hsize2 : data2.size = data.size := by
    have hsize2' : data2.size = data1.size := by
      simpa [data2] using (byteArray_set_size (bs := data1) (i := writeBase + 1)
        (hi := hw1) (v := u16LowByte x))
    simpa [hsize1] using hsize2'
  have hr0d1 : readBase < data1.size := by simpa [hsize1] using hr0
  have hr1d1 : readBase + 1 < data1.size := by simpa [hsize1] using hread
  have hr0d2 : readBase < data2.size := by simpa [hsize2] using hr0
  have hr1d2 : readBase + 1 < data2.size := by simpa [hsize2] using hread
  have h0keep : data2.get readBase hr0d2 = data.get readBase hr0 := by
    have h2 : data2.get readBase hr0d2 = data1.get readBase hr0d1 := by
      simpa [data2] using
        (byteArray_get_set_ne (bs := data1) (i := writeBase + 1) (j := readBase)
          (hi := hw1) (hj := hr0d1) (hij := by omega) (v := u16LowByte x)
          (h' := hr0d2))
    have h1 : data1.get readBase hr0d1 = data.get readBase hr0 := by
      simpa [data1] using
        (byteArray_get_set_ne (bs := data) (i := writeBase) (j := readBase)
          (hi := hw0) (hj := hr0) (hij := by omega) (v := u16HighByte x)
          (h' := hr0d1))
    simp [h2, h1]
  have h1keep : data2.get (readBase + 1) hr1d2 = data.get (readBase + 1) hread := by
    have h2 : data2.get (readBase + 1) hr1d2 = data1.get (readBase + 1) hr1d1 := by
      simpa [data2] using
        (byteArray_get_set_ne (bs := data1) (i := writeBase + 1) (j := readBase + 1)
          (hi := hw1) (hj := hr1d1) (hij := by omega) (v := u16LowByte x)
          (h' := hr1d2))
    have h1 : data1.get (readBase + 1) hr1d1 = data.get (readBase + 1) hread := by
      simpa [data1] using
        (byteArray_get_set_ne (bs := data) (i := writeBase) (j := readBase + 1)
          (hi := hw0) (hj := hread) (hij := by omega) (v := u16HighByte x)
          (h' := hr1d1))
    simp [h2, h1]
  unfold readU16BEAt writeU16BEAt
  simp [data1, data2, h0keep, h1keep]

end Lemmas

end Bitmaps
