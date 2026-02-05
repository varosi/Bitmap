import Bitmap.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Data.ByteArray.Lemmas
import Init.Data.UInt.Lemmas
import Batteries.Data.ByteArray

namespace Bitmaps

-- Setting a byte does not change the ByteArray size.
lemma byteArray_size_set {bs : ByteArray} {i : Nat} {h : i < bs.size} {b : UInt8} :
    (bs.set i b h).size = bs.size := by
  cases bs with
  | mk data =>
      simp [ByteArray.set, ByteArray.size, Array.size_set]


namespace Png

-- Reading one bit advances the bit index by one.
-- Re-export: reading one bit advances the bit index by one.
lemma bitIndex_readBit (br : BitReader) (h : br.bytePos < br.data.size) :
    (BitReader.readBit br).2.bitIndex = br.bitIndex + 1 := by
  unfold BitReader.readBit BitReader.bitIndex
  have hne : br.bytePos ≠ br.data.size := ne_of_lt h
  by_cases hnext : br.bitPos + 1 = 8
  · calc
      (BitReader.readBit br).2.bitIndex
          = (br.bytePos + 1) * 8 := by
              simp [BitReader.readBit, BitReader.bitIndex, hne, hnext]
      _ = br.bytePos * 8 + (br.bitPos + 1) := by
              simp [Nat.add_mul, hnext, Nat.add_comm]
      _ = br.bitIndex + 1 := by
              simp [BitReader.bitIndex, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  · simp [hne, hnext, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

-- Reading a bit does not mutate the underlying data buffer.
-- Re-export: reading a bit does not change the underlying data.
lemma readBit_data (br : BitReader) (h : br.bytePos < br.data.size) :
    (br.readBit).2.data = br.data := by
  unfold BitReader.readBit
  have hne : br.bytePos ≠ br.data.size := ne_of_lt h
  by_cases hnext : br.bitPos + 1 = 8 <;> simp [hne, hnext]

-- Static Huffman length base table size.
lemma lengthBases_size : lengthBases.size = 29 := by decide
-- Static Huffman length extra table size.
lemma lengthExtra_size : lengthExtra.size = 29 := by decide
-- Static Huffman distance base table size.
lemma distBases_size : distBases.size = 30 := by decide
-- Static Huffman distance extra table size.
lemma distExtra_size : distExtra.size = 30 := by decide

end Png

namespace Lemmas

-- Linear index from (x,y) is within bounds for Nat coordinates.
lemma arrayCoordSize_nat
    {i x y w h : Nat}
    (hx : x < w) (hy : y < h) (hi : i = x + y * w) :
    i < w * h := by
  subst hi
  have hx' : x + y * w < w + y * w := Nat.add_lt_add_right hx _
  have hx'' : x + y * w < w * (y + 1) := by
    simpa [Nat.mul_comm, Nat.mul_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hx'
  have hy' : w * (y + 1) ≤ w * h := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hy)
  exact lt_of_lt_of_le hx'' hy'

-- Linear index from (x,y) is within bounds for UInt32 coordinates.
lemma arrayCoordSize_u32
    {i w h : Nat} {x y : UInt32}
    (hx : x.toNat < w)
    (hy : y.toNat < h)
    (hi : i = x.toNat + y.toNat * w) :
    i < w * h := by
  have hlt : x.toNat + y.toNat * w < w * h :=
    arrayCoordSize_nat (i := x.toNat + y.toNat * w) hx hy rfl
  simpa [hi] using hlt

-- Getting the byte just set yields the new value.
@[simp] lemma byteArray_get_set_self
    {bs : ByteArray} {i : Nat} (h : i < bs.size) {v : UInt8} :
    (bs.set i v h).get i (by simpa [byteArray_size_set] using h) = v := by
  cases bs with
  | mk arr =>
      simp [ByteArray.set, ByteArray.get]

-- Getting the byte just set yields the new value (alternate proof of bounds).
@[simp] lemma byteArray_get_set_self'
    {bs : ByteArray} {i : Nat} (h : i < bs.size) {v : UInt8}
    {h' : i < (bs.set i v h).size} :
    (bs.set i v h).get i h' = v := by
  simp [byteArray_get_set_self (bs := bs) (i := i) (h := h) (v := v)]

-- Setting one index does not affect other indices.
lemma byteArray_get_set_ne
    {bs : ByteArray} {i j : Nat} (hi : i < bs.size) (hj : j < bs.size)
    (hij : i ≠ j) {v : UInt8} :
    (bs.set i v hi).get j (by simpa [byteArray_size_set] using hj) = bs.get j hj := by
  cases bs with
  | mk arr =>
      simpa [ByteArray.set, ByteArray.get] using
        (Array.getElem_set_ne (xs := arr) (i := i) (j := j) (h' := hi) (pj := hj) (h := hij))

-- Setting one index does not affect other indices (alternate proof of bounds).
lemma byteArray_get_set_ne'
    {bs : ByteArray} {i j : Nat} (hi : i < bs.size) (hj : j < bs.size)
    (hij : i ≠ j) {v : UInt8} {h' : j < (bs.set i v hi).size} :
    (bs.set i v hi).get j h' = bs.get j hj := by
  simpa using (byteArray_get_set_ne (bs := bs) (i := i) (j := j) (hi := hi) (hj := hj) (hij := hij) (v := v))

-- `getElem` is proof-irrelevant for ByteArrays.
@[simp] lemma byteArray_getElem_eq {bs : ByteArray} {i : Nat} (h1 h2 : i < bs.size) :
    bs[i]'h1 = bs[i]'h2 := by
  rfl


 

-- Writing a pixel then reading it back yields the same pixel.
lemma getPixel_putPixel_eq
    (img : Bitmap) (x y : Nat) (pixel : PixelRGB8)
    (hx : x < img.size.width) (hy : y < img.size.height) :
    getPixel (putPixel img x y pixel hx hy) x y
      (by simpa using hx) (by simpa using hy) = pixel := by
  cases pixel with
  | mk r g b =>
      let pixIdx := x + y * img.size.width
      have hPix : pixIdx < img.size.width * img.size.height := by
        simpa [pixIdx] using
          (arrayCoordSize_nat (i := pixIdx) (w := img.size.width) (h := img.size.height)
            (x := x) (y := y) hx hy rfl)

      let base := pixIdx * bytesPerPixel
      have h2 : base + 2 < img.data.size := by
        have : pixIdx * bytesPerPixel + 2 < img.size.width * img.size.height * bytesPerPixel := by
          have hPix' := hPix
          simp [bytesPerPixel] at hPix' ⊢
          omega
        simpa [base, img.valid] using this
      have h1 : base + 1 < img.data.size := by omega
      have h0 : base < img.data.size := by omega

      let data1 := img.data.set base r h0
      have h1d1 : base + 1 < data1.size := by
        simpa [data1, byteArray_size_set] using h1
      let data2 := data1.set (base + 1) g h1d1
      have h2d2 : base + 2 < data2.size := by
        simpa [data2, data1, byteArray_size_set] using h2
      let data3 := data2.set (base + 2) b h2d2

      have h0d1 : base < data1.size := by
        simpa [data1, byteArray_size_set] using h0
      have h0d2 : base < data2.size := by
        simpa [data2, data1, byteArray_size_set] using h0
      have h0d3 : base < data3.size := by
        simpa [data3, data2, data1, byteArray_size_set] using h0
      have h1d2 : base + 1 < data2.size := by
        simpa [data2, data1, byteArray_size_set] using h1
      have h1d3 : base + 1 < data3.size := by
        simpa [data3, data2, data1, byteArray_size_set] using h1
      have h2d3 : base + 2 < data3.size := by
        simpa [data3, data2, data1, byteArray_size_set] using h2

      have hr : data3.get base h0d3 = r := by
        simp [data3, data2, data1, byteArray_get_set_ne', h0d2, h0d1]

      have hg : data3.get (base + 1) h1d3 = g := by
        simp [data3, data2, data1, byteArray_get_set_ne', h1d2]

      have hb : data3.get (base + 2) h2d3 = b := by
        simp [data3, data2, data1]

      -- Now unfold putPixel/getPixel and rewrite with computed fields.
      simp [getPixel, putPixel, pixIdx, base, data1, data2, data3, hr, hg, hb]

open Png

-- Little-endian 16-bit encoding has length 2.
lemma u16le_size (n : Nat) : (u16le n).size = 2 := by
  have h : (u16le n).data.size = 2 := by
    simp [u16le]
  simpa [ByteArray.size_data] using h

-- Big-endian 32-bit encoding has length 4.
lemma u32be_size (n : Nat) : (u32be n).size = 4 := by
  have h : (u32be n).data.size = 4 := by
    simp [u32be]
  simpa [ByteArray.size_data] using h


-- Reading a u16le-encoded value returns the original number (in range).
@[simp] lemma readU16LE_u16le (n : Nat) (hn : n < 2 ^ 16) :
    readU16LE (u16le n) 0 (by simp [u16le_size]) = n := by
  have hpow : (2 ^ 16 : Nat) = 256 * 256 := by decide
  have hdiv : n / 256 < 256 := by
    apply Nat.div_lt_of_lt_mul
    simpa [hpow, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hn
  have hmod : n % 256 < 256 := Nat.mod_lt _ (by decide : 0 < (256:Nat))
  -- Evaluate the two bytes.
  have hb0 : (u16le n).get 0 (by
      simp [u16le_size]) = u8 (n % 256) := by
    rfl
  have hb1 : (u16le n).get 1 (by
      simp [u16le_size]) = u8 ((n / 256) % 256) := by
    rfl
  have hdiv' : (n / 256) % 256 = n / 256 := Nat.mod_eq_of_lt hdiv
  -- Now unfold readU16LE.
  simp [readU16LE, hb0, hb1, hdiv', u8,
    UInt8.toNat_ofNat_of_lt' (by simpa [UInt8.size] using hmod),
    UInt8.toNat_ofNat_of_lt' (by simpa [UInt8.size] using hdiv),
    Nat.shiftLeft_eq, Nat.mul_comm] at *
  -- normalize to mod/div identity
  have : n % 256 + 256 * (n / 256) = n := by
    simpa [Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using (Nat.mod_add_div n 256)
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this

-- Reading a u32be-encoded value returns the original number (in range).
lemma readU32BE_u32be (n : Nat) (hn : n < 2 ^ 32) :
    readU32BE (u32be n) 0 (by simp [u32be_size]) = n := by
  -- Helper: each byte is in range.
  have h0 : (n / 2 ^ 24) % 256 < UInt8.size := by
    have hlt : (n / 2 ^ 24) % 256 < 256 := Nat.mod_lt _ (by decide : 0 < (256:Nat))
    simpa [UInt8.size] using hlt
  have h1 : (n / 2 ^ 16) % 256 < UInt8.size := by
    have hlt : (n / 2 ^ 16) % 256 < 256 := Nat.mod_lt _ (by decide : 0 < (256:Nat))
    simpa [UInt8.size] using hlt
  have h2 : (n / 2 ^ 8) % 256 < UInt8.size := by
    have hlt : (n / 2 ^ 8) % 256 < 256 := Nat.mod_lt _ (by decide : 0 < (256:Nat))
    simpa [UInt8.size] using hlt
  have h3 : n % 256 < UInt8.size := by
    have hlt : n % 256 < 256 := Nat.mod_lt _ (by decide : 0 < (256:Nat))
    simpa [UInt8.size] using hlt
  -- Evaluate the bytes directly.
  have hb0 : (u32be n).get 0 (by
      simp [u32be_size]) =
      u8 ((n / 2 ^ 24) % 256) := by
    rfl
  have hb1 : (u32be n).get 1 (by
      simp [u32be_size]) =
      u8 ((n / 2 ^ 16) % 256) := by
    rfl
  have hb2 : (u32be n).get 2 (by
      simp [u32be_size]) =
      u8 ((n / 2 ^ 8) % 256) := by
    rfl
  have hb3 : (u32be n).get 3 (by
      simp [u32be_size]) =
      u8 (n % 256) := by
    rfl
  have hread :
      readU32BE (u32be n) 0 (by simp [u32be_size]) =
        ((n / 2 ^ 24) % 256) * 2 ^ 24 +
        ((n / 2 ^ 16) % 256) * 2 ^ 16 +
        ((n / 2 ^ 8) % 256) * 2 ^ 8 + n % 256 := by
    simp [readU32BE, hb0, hb1, hb2, hb3, u8,
      UInt8.toNat_ofNat_of_lt' h0, UInt8.toNat_ofNat_of_lt' h1,
      UInt8.toNat_ofNat_of_lt' h2, UInt8.toNat_ofNat_of_lt' h3,
      Nat.shiftLeft_eq, Nat.mul_comm]
  -- Base-2^8 decomposition.
  have h256 : (2 ^ 8 : Nat) = 256 := by decide
  have hpow : (2 ^ 24 : Nat) * 2 ^ 8 = 2 ^ 32 := by decide
  have h24lt : n / 2 ^ 24 < 2 ^ 8 := by
    apply Nat.div_lt_of_lt_mul
    simpa [hpow, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hn
  have h24mod : (n / 2 ^ 24) % 256 = n / 2 ^ 24 := by
    have : n / 2 ^ 24 < 256 := by simpa [h256] using h24lt
    exact Nat.mod_eq_of_lt this
  have h08 : n = (n / 2 ^ 8) * 2 ^ 8 + n % 2 ^ 8 := by
    simpa [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (Nat.div_add_mod n (2 ^ 8)).symm
  have h16 : n / 2 ^ 8 = (n / 2 ^ 8 / 2 ^ 8) * 2 ^ 8 + (n / 2 ^ 8) % 2 ^ 8 := by
    simpa [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (Nat.div_add_mod (n / 2 ^ 8) (2 ^ 8)).symm
  have h24 : n / 2 ^ 16 = (n / 2 ^ 16 / 2 ^ 8) * 2 ^ 8 + (n / 2 ^ 16) % 2 ^ 8 := by
    simpa [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (Nat.div_add_mod (n / 2 ^ 16) (2 ^ 8)).symm
  have hpow8 : (2 ^ 8 : Nat) * 2 ^ 8 = 2 ^ 16 := by decide
  have hpow16 : (2 ^ 8 : Nat) * 2 ^ 16 = 2 ^ 24 := by decide
  have hpow16' : (2 ^ 16 : Nat) * 2 ^ 8 = 2 ^ 24 := by decide
  have hpow8_num : (256:Nat) * 256 = 65536 := by decide
  have hpow16_num : (256:Nat) * 65536 = 16777216 := by decide
  have hmul_pow8 (a b : Nat) :
      (a * 2 ^ 8 + b) * 2 ^ 8 = a * 2 ^ 16 + b * 2 ^ 8 := by
    calc
      (a * 2 ^ 8 + b) * 2 ^ 8 = a * 2 ^ 8 * 2 ^ 8 + b * 2 ^ 8 := by
        simp [Nat.add_mul, Nat.mul_assoc]
      _ = a * 2 ^ 16 + b * 2 ^ 8 := by
        simp [Nat.mul_comm, Nat.mul_left_comm, hpow8]
  have hmul_pow16 (a b : Nat) :
      (a * 2 ^ 8 + b) * 2 ^ 16 = a * 2 ^ 24 + b * 2 ^ 16 := by
    calc
      (a * 2 ^ 8 + b) * 2 ^ 16 = a * 2 ^ 8 * 2 ^ 16 + b * 2 ^ 16 := by
        simp [Nat.add_mul, Nat.mul_assoc]
      _ = a * 2 ^ 24 + b * 2 ^ 16 := by
        simp [Nat.mul_assoc, hpow16]
  have hdiv16 : n / 2 ^ 8 / 2 ^ 8 = n / 2 ^ 16 := by
    simp [Nat.div_div_eq_div_mul, hpow8]
  have hdiv24 : n / 2 ^ 16 / 2 ^ 8 = n / 2 ^ 24 := by
    simp [Nat.div_div_eq_div_mul, hpow16']
  have hdecomp :
      (n / 2 ^ 24) * 2 ^ 24 +
        (n / 2 ^ 16 % 2 ^ 8) * 2 ^ 16 +
        (n / 2 ^ 8 % 2 ^ 8) * 2 ^ 8 + n % 2 ^ 8 = n := by
    symm
    -- Start from the right-hand side using base-2^8 expansion.
    have h16' :
        (n / 2 ^ 8) * 2 ^ 8 + n % 2 ^ 8 =
          ((n / 2 ^ 8 / 2 ^ 8) * 2 ^ 8 + (n / 2 ^ 8) % 2 ^ 8) * 2 ^ 8 + n % 2 ^ 8 := by
      exact congrArg (fun t => t * 2 ^ 8 + n % 2 ^ 8) h16
    have h24' :
        (n / 2 ^ 16) * 2 ^ 16 +
            (n / 2 ^ 8 % 2 ^ 8) * 2 ^ 8 + n % 2 ^ 8 =
          ((n / 2 ^ 16 / 2 ^ 8) * 2 ^ 8 + (n / 2 ^ 16) % 2 ^ 8) * 2 ^ 16 +
            (n / 2 ^ 8 % 2 ^ 8) * 2 ^ 8 + n % 2 ^ 8 := by
      exact congrArg (fun t => t * 2 ^ 16 + (n / 2 ^ 8 % 2 ^ 8) * 2 ^ 8 + n % 2 ^ 8) h24
    calc
      n = (n / 2 ^ 8) * 2 ^ 8 + n % 2 ^ 8 := h08
      _ = ((n / 2 ^ 8 / 2 ^ 8) * 2 ^ 8 + (n / 2 ^ 8) % 2 ^ 8) * 2 ^ 8 + n % 2 ^ 8 := by
        rw [h16']
      _ = ((n / 2 ^ 16) * 2 ^ 8 + (n / 2 ^ 8) % 2 ^ 8) * 2 ^ 8 + n % 2 ^ 8 := by
        simp [hdiv16]
      _ = (n / 2 ^ 16) * 2 ^ 16 +
            (n / 2 ^ 8 % 2 ^ 8) * 2 ^ 8 + n % 2 ^ 8 := by
        -- distribute
        exact
          congrArg (fun t => t + n % 2 ^ 8)
            (hmul_pow8 (n / 2 ^ 16) (n / 2 ^ 8 % 2 ^ 8))
      _ = ((n / 2 ^ 16 / 2 ^ 8) * 2 ^ 8 + (n / 2 ^ 16) % 2 ^ 8) * 2 ^ 16 +
            (n / 2 ^ 8 % 2 ^ 8) * 2 ^ 8 + n % 2 ^ 8 := by
        rw [h24']
      _ = ((n / 2 ^ 24) * 2 ^ 8 + (n / 2 ^ 16) % 2 ^ 8) * 2 ^ 16 +
            (n / 2 ^ 8 % 2 ^ 8) * 2 ^ 8 + n % 2 ^ 8 := by
        simp [hdiv24]
      _ = (n / 2 ^ 24) * 2 ^ 24 +
            (n / 2 ^ 16 % 2 ^ 8) * 2 ^ 16 +
            (n / 2 ^ 8 % 2 ^ 8) * 2 ^ 8 + n % 2 ^ 8 := by
        -- distribute and rewrite 2^8 * 2^16
        exact
          congrArg (fun t => t + (n / 2 ^ 8 % 2 ^ 8) * 2 ^ 8 + n % 2 ^ 8)
            (hmul_pow16 (n / 2 ^ 24) (n / 2 ^ 16 % 2 ^ 8))
  -- Finish by rewriting mod 2^8 to mod 256 and top-byte reduction.
  have hdecomp' :
      ((n / 2 ^ 24) % 256) * 2 ^ 24 +
        ((n / 2 ^ 16) % 256) * 2 ^ 16 +
        ((n / 2 ^ 8) % 256) * 2 ^ 8 + n % 256 = n := by
    simpa [h256, h24mod] using hdecomp
  simpa [hread] using hdecomp'

-- Reading a 32-bit value depends only on the extracted 4-byte slice.
lemma readU32BE_extract (bytes : ByteArray) (pos : Nat) (h : pos + 3 < bytes.size) :
    readU32BE bytes pos h =
      readU32BE (bytes.extract pos (pos + 4)) 0 (by
        have hle : pos + 4 ≤ bytes.size := Nat.succ_le_of_lt h
        simp [ByteArray.size_extract, Nat.min_eq_left hle, Nat.add_sub_cancel_left]) := by
  cases bytes with
  | mk data =>
      simp [readU32BE, ByteArray.extract, ByteArray.get]

-- `readU32BE` is proof-irrelevant in its bounds argument.
lemma readU32BE_proof_irrel {bytes : ByteArray} {pos : Nat}
    (h1 h2 : pos + 3 < bytes.size) :
    readU32BE bytes pos h1 = readU32BE bytes pos h2 := by
  rfl

-- Reading a 32-bit value from a slice that equals `u32be n` yields `n`.
lemma readU32BE_of_extract_eq (bytes : ByteArray) (pos n : Nat)
    (h : pos + 3 < bytes.size)
    (hextract : bytes.extract pos (pos + 4) = u32be n)
    (hn : n < 2 ^ 32) :
    readU32BE bytes pos h = n := by
  have h' := readU32BE_extract (bytes := bytes) (pos := pos) h
  have hcanon : readU32BE (u32be n) 0 (by simp [u32be_size]) = n :=
    readU32BE_u32be n hn
  have h'' :
      readU32BE (bytes.extract pos (pos + 4)) 0 (by
        have hle : pos + 4 ≤ bytes.size := Nat.succ_le_of_lt h
        simp [ByteArray.size_extract, Nat.min_eq_left hle]) = n := by
    simpa [hextract, readU32BE_proof_irrel] using hcanon
  exact h'.trans h''

-- PNG signature is 8 bytes.
lemma pngSignature_size : pngSignature.size = 8 := by
  have h : pngSignature.data.size = 8 := by
    simp [pngSignature]
  simpa [ByteArray.size_data] using h

-- Chunk size = payload + type tag + length field + CRC field.
lemma mkChunk_size (typ : String) (data : ByteArray) :
    (mkChunk typ data).size = data.size + typ.utf8ByteSize + 8 := by
  calc
    (mkChunk typ data).size = data.size + typ.utf8ByteSize + 4 + 4 := by
      simp [mkChunk, u32be_size, Nat.add_left_comm, Nat.add_comm]
    _ = data.size + typ.utf8ByteSize + (4 + 4) := by
      simp [Nat.add_assoc]
    _ = data.size + typ.utf8ByteSize + 8 := by
      simp

-- Extracting a prefix from an append only depends on the left chunk.
lemma byteArray_extract_append_prefix (a b : ByteArray) (n : Nat) (hn : n ≤ a.size) :
    (a ++ b).extract 0 n = a.extract 0 n := by
  have := (ByteArray.extract_append (as := a) (bs := b) (i := 0) (j := n))
  -- The right extract is empty since `n ≤ a.size`.
  simpa [Nat.sub_eq_zero_of_le hn] using this

-- Extracting a slice that lies entirely in the left chunk ignores the right chunk.
lemma byteArray_extract_append_left (a b : ByteArray) (i j : Nat)
    (hi : i ≤ a.size) (hj : j ≤ a.size) :
    (a ++ b).extract i j = a.extract i j := by
  have := (ByteArray.extract_append (as := a) (bs := b) (i := i) (j := j))
  -- Both subtractions are zero since the slice stays within `a`.
  simpa [Nat.sub_eq_zero_of_le hi, Nat.sub_eq_zero_of_le hj] using this

-- The zlib stored-compression header bytes are fixed.
lemma zlibCompressStored_header (raw : ByteArray) :
    (zlibCompressStored raw).extract 0 2 = ByteArray.mk #[u8 0x78, u8 0x01] := by
  let header : ByteArray := ByteArray.mk #[u8 0x78, u8 0x01]
  let deflated := deflateStored raw
  let adler := u32be (adler32 raw).toNat
  have hsize : header.size = 2 := by decide
  have hprefix :
      (header ++ deflated ++ adler).extract 0 2 = header.extract 0 2 := by
    apply byteArray_extract_append_prefix (a := header) (b := deflated ++ adler) (n := 2)
    simp [hsize]
  have hheader : header.extract 0 2 = header := by
    rw [← hsize, ByteArray.extract_zero_size]
  simp [zlibCompressStored, header, deflated, adler, hprefix, hheader]

-- Size of zlib stored-compression output (header + deflate + adler32).
lemma zlibCompressStored_size (raw : ByteArray) :
    (zlibCompressStored raw).size = (deflateStored raw).size + 6 := by
  unfold zlibCompressStored
  have hheader : (ByteArray.mk #[u8 0x78, u8 0x01]).size = 2 := by decide
  simp [ByteArray.size_append, u32be_size, hheader]
  omega


-- IHDR payload is always 13 bytes.
lemma ihdr_payload_size (w h : Nat) :
    (u32be w ++ u32be h ++ ByteArray.mk #[u8 8, u8 2, u8 0, u8 0, u8 0]).size = 13 := by
  have hbytes : (ByteArray.mk #[u8 8, u8 2, u8 0, u8 0, u8 0]).size = 5 := by
    decide
  simp [ByteArray.size_append, u32be_size, hbytes]

-- Fixed tail bytes in the IHDR payload (bit depth, color type, and flags).
def ihdrTail : ByteArray :=
  ByteArray.mk #[u8 8, u8 2, u8 0, u8 0, u8 0]

-- IHDR payload width slice is the encoded width.
lemma ihdr_payload_extract_width (w h : Nat) :
    (u32be w ++ u32be h ++ ByteArray.mk #[u8 8, u8 2, u8 0, u8 0, u8 0]).extract 0 4 =
      u32be w := by
  let tail := ByteArray.mk #[u8 8, u8 2, u8 0, u8 0, u8 0]
  let ihdr := u32be w ++ u32be h ++ tail
  ext i hi
  · -- size goal
    have hle : 0 + 4 ≤ ihdr.size := by
      have : ihdr.size = 13 := by
        simpa [ihdr, tail] using ihdr_payload_size w h
      omega
    have hsize : (ihdr.extract 0 4).size = 4 := by
      simp [ByteArray.size_extract, Nat.min_eq_left hle]
    simp [ByteArray.size_data, u32be_size]
  · -- element goal
    have hle : 0 + 4 ≤ ihdr.size := by
      have : ihdr.size = 13 := by
        simpa [ihdr, tail] using ihdr_payload_size w h
      omega
    have hsize : (ihdr.extract 0 4).size = 4 := by
      simp [ByteArray.size_extract, Nat.min_eq_left hle]
    have hi4 : i < 4 := by
      simpa [hsize] using hi
    have hiw : i < (u32be w).size := by
      simpa [u32be_size] using hi4
    have hi_ihdr : i < ihdr.size := lt_of_lt_of_le hi4 hle
    have hget : ihdr[i]'hi_ihdr = (u32be w)[i]'hiw := by
      have h :=
        (ByteArray.get_append_left (a := u32be w) (b := u32be h ++ tail) (i := i) hiw)
      simpa [ihdr, tail, ByteArray.append_assoc] using h
    have hget' : (ihdr.extract 0 4)[i] = ihdr[i]'hi_ihdr := by
      simp
    calc
      (ihdr.extract 0 4)[i] = ihdr[i]'hi_ihdr := hget'
      _ = (u32be w)[i]'hiw := hget

-- IHDR payload height slice is the encoded height.
lemma ihdr_payload_extract_height (w h : Nat) :
    (u32be w ++ u32be h ++ ByteArray.mk #[u8 8, u8 2, u8 0, u8 0, u8 0]).extract 4 8 =
      u32be h := by
  let tail := ByteArray.mk #[u8 8, u8 2, u8 0, u8 0, u8 0]
  let ihdr := u32be w ++ u32be h ++ tail
  ext i hi
  · -- size goal
    have hle : 4 + 4 ≤ ihdr.size := by
      have : ihdr.size = 13 := by
        simpa [ihdr, tail] using ihdr_payload_size w h
      omega
    have hsize : (ihdr.extract 4 8).size = 4 := by
      simp [ByteArray.size_extract, Nat.min_eq_left hle]
    simp [ByteArray.size_data, u32be_size]
  · -- element goal
    have hle : 4 + 4 ≤ ihdr.size := by
      have : ihdr.size = 13 := by
        simpa [ihdr, tail] using ihdr_payload_size w h
      omega
    have hsize : (ihdr.extract 4 8).size = 4 := by
      simp [ByteArray.size_extract, Nat.min_eq_left hle]
    have hi4 : i < 4 := by
      simpa [hsize] using hi
    have hih : i < (u32be h).size := by
      simpa [u32be_size] using hi4
    have hright : ihdr[4 + i]'(by
        have : ihdr.size = 13 := by
          simpa [ihdr, tail] using ihdr_payload_size w h
        omega) = (u32be h ++ tail)[i]'(by
          have : i < (u32be h ++ tail).size := by
            have : (u32be h).size = 4 := u32be_size h
            have h' : i < 4 := by simpa [u32be_size] using hi4
            simpa [ByteArray.size_append, this] using
              (Nat.lt_of_lt_of_le h' (Nat.le_add_right _ _))
          simpa using this) := by
      have hle' : (u32be w).size ≤ 4 + i := by
        simp [u32be_size]
      have hlt' : 4 + i < ihdr.size := by
        have : ihdr.size = 13 := by
          simpa [ihdr, tail] using ihdr_payload_size w h
        omega
      have h := ByteArray.get_append_right (a := u32be w) (b := u32be h ++ tail)
        (i := 4 + i) hle' (by simpa [ihdr, tail, ByteArray.append_assoc] using hlt')
      simpa [ihdr, tail, u32be_size, Nat.add_sub_cancel_left, ByteArray.append_assoc] using h
    have hleft : (u32be h ++ tail)[i]'(by
        have : i < (u32be h ++ tail).size := by
          have : (u32be h).size = 4 := u32be_size h
          have h' : i < 4 := by simpa [u32be_size] using hi4
          simpa [ByteArray.size_append, this] using
            (Nat.lt_of_lt_of_le h' (Nat.le_add_right _ _))
        simpa using this) = (u32be h)[i]'hih := by
      have h :=
        (ByteArray.get_append_left (a := u32be h) (b := tail) (i := i) hih)
      simpa [tail] using h
    have hget' : (ihdr.extract 4 8)[i] = ihdr[4 + i]'(by
        have : ihdr.size = 13 := by
          simpa [ihdr, tail] using ihdr_payload_size w h
        omega) := by
      simp
    calc
      (ihdr.extract 4 8)[i] = ihdr[4 + i]'(by
        have : ihdr.size = 13 := by
          simpa [ihdr, tail] using ihdr_payload_size w h
        omega) := hget'
      _ = (u32be h ++ tail)[i]'(by
        have : i < (u32be h ++ tail).size := by
          have : (u32be h).size = 4 := u32be_size h
          have h' : i < 4 := by simpa [u32be_size] using hi4
          simpa [ByteArray.size_append, this] using
            (Nat.lt_of_lt_of_le h' (Nat.le_add_right _ _))
        simpa using this) := hright
      _ = (u32be h)[i]'hih := hleft

-- Reading the width from an IHDR payload yields the original width.
lemma readU32BE_ihdr_width (w h : Nat) (hw : w < 2 ^ 32) :
    readU32BE (u32be w ++ u32be h ++ ihdrTail) 0 (by
      have : (u32be w ++ u32be h ++ ihdrTail).size = 13 := by
        simpa [ihdrTail] using ihdr_payload_size w h
      omega) = w := by
  have hpos : 0 + 3 < (u32be w ++ u32be h ++ ihdrTail).size := by
    have : (u32be w ++ u32be h ++ ihdrTail).size = 13 := by
      simpa [ihdrTail] using ihdr_payload_size w h
    omega
  have hread :=
    readU32BE_extract (bytes := u32be w ++ u32be h ++ ihdrTail) (pos := 0) hpos
  have hwidth : (u32be w ++ u32be h ++ ihdrTail).extract 0 4 = u32be w := by
    simpa [ihdrTail] using ihdr_payload_extract_width w h
  have htotal : (u32be w ++ u32be h ++ ihdrTail).size = 13 := by
    simpa [ihdrTail] using ihdr_payload_size w h
  have hsize : ((u32be w ++ u32be h ++ ihdrTail).extract 0 4).size = 4 := by
    simp [ByteArray.size_extract, htotal]
  have hpos' : 0 + 3 < ((u32be w ++ u32be h ++ ihdrTail).extract 0 4).size := by
    simp [hsize]
  have hread' :
      readU32BE ((u32be w ++ u32be h ++ ihdrTail).extract 0 4) 0 hpos' = w := by
    simpa [hwidth] using readU32BE_u32be w hw
  simp [hread'] at hread
  exact hread

-- Reading the height from an IHDR payload yields the original height.
lemma readU32BE_ihdr_height (w h : Nat) (hh : h < 2 ^ 32) :
    readU32BE (u32be w ++ u32be h ++ ihdrTail) 4 (by
      have : (u32be w ++ u32be h ++ ihdrTail).size = 13 := by
        simpa [ihdrTail] using ihdr_payload_size w h
      omega) = h := by
  have hpos : 4 + 3 < (u32be w ++ u32be h ++ ihdrTail).size := by
    have : (u32be w ++ u32be h ++ ihdrTail).size = 13 := by
      simpa [ihdrTail] using ihdr_payload_size w h
    omega
  have hread :=
    readU32BE_extract (bytes := u32be w ++ u32be h ++ ihdrTail) (pos := 4) hpos
  have hheight : (u32be w ++ u32be h ++ ihdrTail).extract 4 8 = u32be h := by
    simpa [ihdrTail] using ihdr_payload_extract_height w h
  have htotal : (u32be w ++ u32be h ++ ihdrTail).size = 13 := by
    simpa [ihdrTail] using ihdr_payload_size w h
  have hsize : ((u32be w ++ u32be h ++ ihdrTail).extract 4 8).size = 4 := by
    simp [ByteArray.size_extract, htotal]
  have hpos' : 0 + 3 < ((u32be w ++ u32be h ++ ihdrTail).extract 4 8).size := by
    simp [hsize]
  have hread' :
      readU32BE ((u32be w ++ u32be h ++ ihdrTail).extract 4 8) 0 hpos' = h := by
    simpa [hheight] using readU32BE_u32be h hh
  simp [hread'] at hread
  exact hread

-- The fixed IHDR tail bytes are present.
lemma ihdr_payload_extract_tail (w h : Nat) :
    (u32be w ++ u32be h ++ ihdrTail).extract 8 13 = ihdrTail := by
  have hsize : (u32be w ++ u32be h).size = 8 := by
    simp [ByteArray.size_append, u32be_size]
  have hshift :
      (u32be w ++ u32be h ++ ihdrTail).extract 8 13 = ihdrTail.extract 0 5 := by
    simpa [ByteArray.append_assoc, hsize] using
      (ByteArray.extract_append_size_add
        (a := u32be w ++ u32be h)
        (b := ihdrTail)
        (i := 0) (j := 5))
  have htail : ihdrTail.extract 0 5 = ihdrTail := by
    decide
  simpa [htail] using hshift

-- IHDR tag is 4 bytes in UTF-8.
lemma ihdr_utf8_size : ("IHDR".toUTF8).size = 4 := by decide
-- IDAT tag is 4 bytes in UTF-8.
lemma idat_utf8_size : ("IDAT".toUTF8).size = 4 := by decide
-- IEND tag is 4 bytes in UTF-8.
lemma iend_utf8_size : ("IEND".toUTF8).size = 4 := by decide
-- IHDR tag is 4 bytes in UTF-8 (byte-size form).
lemma ihdr_utf8ByteSize : ("IHDR".utf8ByteSize) = 4 := by decide
-- IDAT tag is 4 bytes in UTF-8 (byte-size form).
lemma idat_utf8ByteSize : ("IDAT".utf8ByteSize) = 4 := by decide
-- IEND tag is 4 bytes in UTF-8 (byte-size form).
lemma iend_utf8ByteSize : ("IEND".utf8ByteSize) = 4 := by decide

-- Encoded PNG starts with the PNG signature.
lemma encodeBitmap_signature (bmp : BitmapRGB8) :
    (encodeBitmap bmp).extract 0 8 = pngSignature := by
  have hsig : pngSignature.size = 8 := pngSignature_size
  simpa [encodeBitmap, hsig, ByteArray.append_assoc] using
    (ByteArray.extract_append_eq_left
      (a := pngSignature)
      (b := mkChunk "IHDR"
            (u32be bmp.size.width ++ u32be bmp.size.height ++
              ByteArray.mk #[u8 8, u8 2, u8 0, u8 0, u8 0]) ++
          mkChunk "IDAT" (zlibCompressStored (encodeRaw bmp)) ++
          mkChunk "IEND" ByteArray.empty)
      (i := pngSignature.size) rfl)

-- The first 4 bytes of a chunk encode the payload length.
lemma mkChunk_extract_len (typ : String) (data : ByteArray) :
    (mkChunk typ data).extract 0 4 = u32be data.size := by
  have hlen : (u32be data.size).size = 4 := u32be_size _
  simpa [mkChunk, hlen] using
    (ByteArray.extract_append_eq_left
      (a := u32be data.size)
      (b := typ.toUTF8 ++ data ++ u32be (crc32 (typ.toUTF8 ++ data)).toNat)
      (i := (u32be data.size).size) rfl)

-- The next 4 bytes of a chunk encode the type tag.
lemma mkChunk_extract_type (typ : String) (data : ByteArray) (htyp : typ.utf8ByteSize = 4) :
    (mkChunk typ data).extract 4 8 = typ.toUTF8 := by
  have hlen : (u32be data.size).size = 4 := u32be_size _
  have htyp' : typ.toUTF8.size = 4 := by
    simpa [String.toUTF8_eq_toByteArray, String.size_toByteArray] using htyp
  have h1 :
      (mkChunk typ data).extract 4 8 =
        (typ.toUTF8 ++ data ++ u32be (crc32 (typ.toUTF8 ++ data)).toNat).extract 0 4 := by
    simpa [mkChunk, hlen, ByteArray.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (ByteArray.extract_append_size_add
        (a := u32be data.size)
        (b := typ.toUTF8 ++ data ++ u32be (crc32 (typ.toUTF8 ++ data)).toNat)
        (i := 0) (j := 4))
  have h2' :
      (typ.toUTF8 ++ data ++ u32be (crc32 (typ.toUTF8 ++ data)).toNat).extract 0
          typ.toUTF8.size = typ.toUTF8 := by
    simpa [ByteArray.append_assoc] using
      (ByteArray.extract_append_eq_left
        (a := typ.toUTF8)
        (b := data ++ u32be (crc32 (typ.toUTF8 ++ data)).toNat)
        (i := typ.toUTF8.size) rfl)
  have h2 :
      (typ.toUTF8 ++ data ++ u32be (crc32 (typ.toUTF8 ++ data)).toNat).extract 0 4 = typ.toUTF8 := by
    simpa [String.toUTF8_eq_toByteArray, String.size_toByteArray, htyp] using h2'
  simpa [h1, h2]

-- The payload bytes of a chunk can be extracted by offset.
lemma mkChunk_extract_data (typ : String) (data : ByteArray) (htyp : typ.utf8ByteSize = 4) :
    (mkChunk typ data).extract 8 (8 + data.size) = data := by
  have hlen : (u32be data.size).size = 4 := u32be_size _
  have htyp' : typ.toUTF8.size = 4 := by
    simpa [String.toUTF8_eq_toByteArray, String.size_toByteArray] using htyp
  have hprefix : (u32be data.size ++ typ.toUTF8).size = 8 := by
    simp [ByteArray.size_append, hlen, String.toUTF8_eq_toByteArray, String.size_toByteArray, htyp]
  have h1 :
      (mkChunk typ data).extract 8 (8 + data.size) =
        (data ++ u32be (crc32 (typ.toUTF8 ++ data)).toNat).extract 0 data.size := by
    simpa [mkChunk, hprefix, ByteArray.append_assoc, String.toUTF8_eq_toByteArray,
      String.size_toByteArray, htyp, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (ByteArray.extract_append_size_add
        (a := u32be data.size ++ typ.toUTF8)
        (b := data ++ u32be (crc32 (typ.toUTF8 ++ data)).toNat)
        (i := 0) (j := data.size))
  have h2 :
      (data ++ u32be (crc32 (typ.toUTF8 ++ data)).toNat).extract 0 data.size = data := by
    simpa using
      (ByteArray.extract_append_eq_left
        (a := data)
        (b := u32be (crc32 (typ.toUTF8 ++ data)).toNat)
        (i := data.size) rfl)
  simpa [h1, h2]

-- The IHDR length field in the encoded PNG is 13.
lemma encodeBitmap_extract_ihdr_len (bmp : BitmapRGB8) :
    (encodeBitmap bmp).extract 8 12 = u32be 13 := by
  let ihdr :=
    u32be bmp.size.width ++ u32be bmp.size.height ++ ByteArray.mk #[u8 8, u8 2, u8 0, u8 0, u8 0]
  let idat := zlibCompressStored (encodeRaw bmp)
  have hsig : pngSignature.size = 8 := pngSignature_size
  have hihdr : ihdr.size = 13 := by
    simpa [ihdr] using ihdr_payload_size bmp.size.width bmp.size.height
  have hchunk_ge : 4 ≤ (mkChunk "IHDR" ihdr).size := by
    have hsize : (mkChunk "IHDR" ihdr).size = ihdr.size + "IHDR".utf8ByteSize + 8 :=
      mkChunk_size _ _
    calc
      4 ≤ ihdr.size + "IHDR".utf8ByteSize + 8 := by omega
      _ = (mkChunk "IHDR" ihdr).size := by
        simp [hsize]
  have hshift :
      (encodeBitmap bmp).extract 8 12 =
        (mkChunk "IHDR" ihdr ++ mkChunk "IDAT" idat ++ mkChunk "IEND" ByteArray.empty).extract 0 4 := by
    simpa [encodeBitmap, hsig] using
      (ByteArray.extract_append_size_add
        (a := pngSignature)
        (b := mkChunk "IHDR" ihdr ++ mkChunk "IDAT" idat ++ mkChunk "IEND" ByteArray.empty)
        (i := 0) (j := 4))
  have hprefix :
      (mkChunk "IHDR" ihdr ++ mkChunk "IDAT" idat ++ mkChunk "IEND" ByteArray.empty).extract 0 4 =
        (mkChunk "IHDR" ihdr).extract 0 4 := by
    simpa using
      (byteArray_extract_append_prefix
        (a := mkChunk "IHDR" ihdr)
        (b := mkChunk "IDAT" idat ++ mkChunk "IEND" ByteArray.empty)
        (n := 4) hchunk_ge)
  have hlen : (mkChunk "IHDR" ihdr).extract 0 4 = u32be ihdr.size :=
    mkChunk_extract_len _ _
  simp [hshift, hprefix, hlen, hihdr]

-- Reading the IHDR length from the encoded PNG yields 13.
lemma readU32BE_encodeBitmap_ihdr_len (bmp : BitmapRGB8)
    (h : 8 + 3 < (encodeBitmap bmp).size) :
    readU32BE (encodeBitmap bmp) 8 h = 13 := by
  exact readU32BE_of_extract_eq (bytes := encodeBitmap bmp) (pos := 8) (n := 13) h
    (encodeBitmap_extract_ihdr_len bmp) (by decide)

-- The IHDR type field in the encoded PNG is "IHDR".
lemma encodeBitmap_extract_ihdr_type (bmp : BitmapRGB8) :
    (encodeBitmap bmp).extract 12 16 = "IHDR".toUTF8 := by
  let ihdr :=
    u32be bmp.size.width ++ u32be bmp.size.height ++ ByteArray.mk #[u8 8, u8 2, u8 0, u8 0, u8 0]
  let idat := zlibCompressStored (encodeRaw bmp)
  have hsig : pngSignature.size = 8 := pngSignature_size
  have hchunk_ge : 8 ≤ (mkChunk "IHDR" ihdr).size := by
    have hsize : (mkChunk "IHDR" ihdr).size = ihdr.size + "IHDR".utf8ByteSize + 8 :=
      mkChunk_size _ _
    calc
      8 ≤ ihdr.size + "IHDR".utf8ByteSize + 8 := by omega
      _ = (mkChunk "IHDR" ihdr).size := by
        simp [hsize]
  have hshift :
      (encodeBitmap bmp).extract 12 16 =
        (mkChunk "IHDR" ihdr ++ mkChunk "IDAT" idat ++ mkChunk "IEND" ByteArray.empty).extract 4 8 := by
    simpa [encodeBitmap, hsig] using
      (ByteArray.extract_append_size_add
        (a := pngSignature)
        (b := mkChunk "IHDR" ihdr ++ mkChunk "IDAT" idat ++ mkChunk "IEND" ByteArray.empty)
        (i := 4) (j := 8))
  have hleft :
      (mkChunk "IHDR" ihdr ++ mkChunk "IDAT" idat ++ mkChunk "IEND" ByteArray.empty).extract 4 8 =
        (mkChunk "IHDR" ihdr).extract 4 8 := by
    simpa using
      (byteArray_extract_append_left
        (a := mkChunk "IHDR" ihdr)
        (b := mkChunk "IDAT" idat ++ mkChunk "IEND" ByteArray.empty)
        (i := 4) (j := 8)
        (hi := by omega) (hj := hchunk_ge))
  have htyp : (mkChunk "IHDR" ihdr).extract 4 8 = "IHDR".toUTF8 := by
    simpa using mkChunk_extract_type "IHDR" ihdr ihdr_utf8ByteSize
  simp [hshift, hleft, htyp]

-- The IHDR payload bytes in the encoded PNG match the constructed IHDR payload.
lemma encodeBitmap_extract_ihdr_data (bmp : BitmapRGB8) :
    (encodeBitmap bmp).extract 16 29 =
      (u32be bmp.size.width ++ u32be bmp.size.height ++
        ByteArray.mk #[u8 8, u8 2, u8 0, u8 0, u8 0]) := by
  let ihdr :=
    u32be bmp.size.width ++ u32be bmp.size.height ++ ByteArray.mk #[u8 8, u8 2, u8 0, u8 0, u8 0]
  let idat := zlibCompressStored (encodeRaw bmp)
  have hsig : pngSignature.size = 8 := pngSignature_size
  have hihdr : ihdr.size = 13 := by
    simpa [ihdr] using ihdr_payload_size bmp.size.width bmp.size.height
  have hchunk_ge : 21 ≤ (mkChunk "IHDR" ihdr).size := by
    have hsize : (mkChunk "IHDR" ihdr).size = ihdr.size + "IHDR".utf8ByteSize + 8 :=
      mkChunk_size _ _
    calc
      21 ≤ 13 + "IHDR".utf8ByteSize + 8 := by omega
      _ = (mkChunk "IHDR" ihdr).size := by
        simp [hsize, hihdr]
  have hshift :
      (encodeBitmap bmp).extract 16 29 =
        (mkChunk "IHDR" ihdr ++ mkChunk "IDAT" idat ++ mkChunk "IEND" ByteArray.empty).extract 8 21 := by
    simpa [encodeBitmap, hsig] using
      (ByteArray.extract_append_size_add
        (a := pngSignature)
        (b := mkChunk "IHDR" ihdr ++ mkChunk "IDAT" idat ++ mkChunk "IEND" ByteArray.empty)
        (i := 8) (j := 21))
  have hleft :
      (mkChunk "IHDR" ihdr ++ mkChunk "IDAT" idat ++ mkChunk "IEND" ByteArray.empty).extract 8 21 =
        (mkChunk "IHDR" ihdr).extract 8 21 := by
    simpa using
      (byteArray_extract_append_left
        (a := mkChunk "IHDR" ihdr)
        (b := mkChunk "IDAT" idat ++ mkChunk "IEND" ByteArray.empty)
        (i := 8) (j := 21)
        (hi := by omega) (hj := hchunk_ge))
  have hdata : (mkChunk "IHDR" ihdr).extract 8 21 = ihdr := by
    have : (mkChunk "IHDR" ihdr).extract 8 (8 + ihdr.size) = ihdr :=
      mkChunk_extract_data "IHDR" ihdr ihdr_utf8ByteSize
    simpa using this
  simp [hshift, hleft, hdata, ihdr]

-- Size of the PNG signature plus the IHDR chunk in the encoded PNG.
lemma encodeBitmap_sig_ihdr_size (bmp : BitmapRGB8) :
    (pngSignature ++
        mkChunk "IHDR"
          (u32be bmp.size.width ++ u32be bmp.size.height ++
            ByteArray.mk #[u8 8, u8 2, u8 0, u8 0, u8 0])).size = 33 := by
  let ihdr :=
    u32be bmp.size.width ++ u32be bmp.size.height ++
      ByteArray.mk #[u8 8, u8 2, u8 0, u8 0, u8 0]
  have hihdr : ihdr.size = 13 := by
    simpa [ihdr] using ihdr_payload_size bmp.size.width bmp.size.height
  calc
    (pngSignature ++ mkChunk "IHDR" ihdr).size
        = pngSignature.size + (mkChunk "IHDR" ihdr).size := by
            simp [ByteArray.size_append]
    _ = 8 + (ihdr.size + "IHDR".utf8ByteSize + 8) := by
            simp [pngSignature_size, mkChunk_size]
    _ = 33 := by
            simp [hihdr, ihdr_utf8ByteSize, Nat.add_comm]

-- The IDAT length field in the encoded PNG matches the compressed payload size.
lemma encodeBitmap_extract_idat_len (bmp : BitmapRGB8) :
    (encodeBitmap bmp).extract 33 37 =
      u32be (zlibCompressStored (encodeRaw bmp)).size := by
  let ihdr :=
    u32be bmp.size.width ++ u32be bmp.size.height ++ ByteArray.mk #[u8 8, u8 2, u8 0, u8 0, u8 0]
  let idat := zlibCompressStored (encodeRaw bmp)
  have hsig : (pngSignature ++ mkChunk "IHDR" ihdr).size = 33 := by
    simpa [ihdr] using encodeBitmap_sig_ihdr_size bmp
  have hshift :
      (encodeBitmap bmp).extract 33 37 =
        (mkChunk "IDAT" idat ++ mkChunk "IEND" ByteArray.empty).extract 0 4 := by
    simpa [encodeBitmap, hsig, ByteArray.append_assoc] using
      (ByteArray.extract_append_size_add
        (a := pngSignature ++ mkChunk "IHDR" ihdr)
        (b := mkChunk "IDAT" idat ++ mkChunk "IEND" ByteArray.empty)
        (i := 0) (j := 4))
  have hprefix :
      (mkChunk "IDAT" idat ++ mkChunk "IEND" ByteArray.empty).extract 0 4 =
        (mkChunk "IDAT" idat).extract 0 4 := by
    have hchunk_ge : 4 ≤ (mkChunk "IDAT" idat).size := by
      have hsize : (mkChunk "IDAT" idat).size = idat.size + "IDAT".utf8ByteSize + 8 :=
        mkChunk_size _ _
      calc
        4 ≤ idat.size + "IDAT".utf8ByteSize + 8 := by omega
        _ = (mkChunk "IDAT" idat).size := by
          simp [hsize]
    simpa using
      (byteArray_extract_append_prefix
        (a := mkChunk "IDAT" idat)
        (b := mkChunk "IEND" ByteArray.empty)
        (n := 4) hchunk_ge)
  have hlen : (mkChunk "IDAT" idat).extract 0 4 = u32be idat.size :=
    mkChunk_extract_len _ _
  simp [hshift, hprefix, hlen, idat]

-- Reading the IDAT length from the encoded PNG yields the compressed payload size.
lemma readU32BE_encodeBitmap_idat_len (bmp : BitmapRGB8)
    (h : 33 + 3 < (encodeBitmap bmp).size)
    (hidat : (zlibCompressStored (encodeRaw bmp)).size < 2 ^ 32) :
    readU32BE (encodeBitmap bmp) 33 h =
      (zlibCompressStored (encodeRaw bmp)).size := by
  let idat := zlibCompressStored (encodeRaw bmp)
  have hextract : (encodeBitmap bmp).extract 33 37 = u32be idat.size := by
    simpa [idat] using encodeBitmap_extract_idat_len bmp
  exact readU32BE_of_extract_eq (bytes := encodeBitmap bmp) (pos := 33) (n := idat.size) h
    hextract hidat

-- The IDAT type field in the encoded PNG is "IDAT".
lemma encodeBitmap_extract_idat_type (bmp : BitmapRGB8) :
    (encodeBitmap bmp).extract 37 41 = "IDAT".toUTF8 := by
  let ihdr :=
    u32be bmp.size.width ++ u32be bmp.size.height ++ ByteArray.mk #[u8 8, u8 2, u8 0, u8 0, u8 0]
  let idat := zlibCompressStored (encodeRaw bmp)
  have hsig : (pngSignature ++ mkChunk "IHDR" ihdr).size = 33 := by
    simpa [ihdr] using encodeBitmap_sig_ihdr_size bmp
  have hshift :
      (encodeBitmap bmp).extract 37 41 =
        (mkChunk "IDAT" idat ++ mkChunk "IEND" ByteArray.empty).extract 4 8 := by
    simpa [encodeBitmap, hsig, ByteArray.append_assoc] using
      (ByteArray.extract_append_size_add
        (a := pngSignature ++ mkChunk "IHDR" ihdr)
        (b := mkChunk "IDAT" idat ++ mkChunk "IEND" ByteArray.empty)
        (i := 4) (j := 8))
  have hleft :
      (mkChunk "IDAT" idat ++ mkChunk "IEND" ByteArray.empty).extract 4 8 =
        (mkChunk "IDAT" idat).extract 4 8 := by
    have hchunk_ge : 8 ≤ (mkChunk "IDAT" idat).size := by
      have hsize : (mkChunk "IDAT" idat).size = idat.size + "IDAT".utf8ByteSize + 8 :=
        mkChunk_size _ _
      calc
        8 ≤ idat.size + "IDAT".utf8ByteSize + 8 := by omega
        _ = (mkChunk "IDAT" idat).size := by
          simp [hsize]
    simpa using
      (byteArray_extract_append_left
        (a := mkChunk "IDAT" idat)
        (b := mkChunk "IEND" ByteArray.empty)
        (i := 4) (j := 8)
        (hi := by omega) (hj := hchunk_ge))
  have htyp : (mkChunk "IDAT" idat).extract 4 8 = "IDAT".toUTF8 := by
    simpa using mkChunk_extract_type "IDAT" idat idat_utf8ByteSize
  simp [hshift, hleft, htyp]

-- The IDAT payload bytes in the encoded PNG are the compressed bitmap bytes.
lemma encodeBitmap_extract_idat_data (bmp : BitmapRGB8) :
    (encodeBitmap bmp).extract 41 (41 + (zlibCompressStored (encodeRaw bmp)).size) =
      zlibCompressStored (encodeRaw bmp) := by
  let ihdr :=
    u32be bmp.size.width ++ u32be bmp.size.height ++ ByteArray.mk #[u8 8, u8 2, u8 0, u8 0, u8 0]
  let idat := zlibCompressStored (encodeRaw bmp)
  let sigIhdr := pngSignature ++ mkChunk "IHDR" ihdr
  let tail := mkChunk "IDAT" idat ++ mkChunk "IEND" ByteArray.empty
  have hsig : sigIhdr.size = 33 := by
    simpa [sigIhdr, ihdr] using encodeBitmap_sig_ihdr_size bmp
  have hdef : encodeBitmap bmp = sigIhdr ++ tail := by
    simp [encodeBitmap, sigIhdr, tail, ihdr, idat, ByteArray.append_assoc, Id.run]
  have hshift' :
      (encodeBitmap bmp).extract (sigIhdr.size + 8) (sigIhdr.size + (8 + idat.size)) =
        tail.extract 8 (8 + idat.size) := by
    simpa [hdef] using
      (ByteArray.extract_append_size_add
        (a := sigIhdr)
        (b := tail)
        (i := 8) (j := 8 + idat.size))
  have h41 : sigIhdr.size + 8 = 41 := by
    omega
  have h41' : sigIhdr.size + (8 + idat.size) = 41 + idat.size := by
    omega
  have hshift :
      (encodeBitmap bmp).extract 41 (41 + idat.size) =
        tail.extract 8 (8 + idat.size) := by
    simpa [h41, h41'] using hshift'
  have hleft :
      tail.extract 8 (8 + idat.size) =
        (mkChunk "IDAT" idat).extract 8 (8 + idat.size) := by
    have hchunk_ge : 8 + idat.size ≤ (mkChunk "IDAT" idat).size := by
      have hsize : (mkChunk "IDAT" idat).size = idat.size + "IDAT".utf8ByteSize + 8 :=
        mkChunk_size _ _
      calc
        8 + idat.size ≤ idat.size + "IDAT".utf8ByteSize + 8 := by omega
        _ = (mkChunk "IDAT" idat).size := by
          simp [hsize, Nat.add_comm]
    simpa using
      (byteArray_extract_append_left
        (a := mkChunk "IDAT" idat)
        (b := mkChunk "IEND" ByteArray.empty)
        (i := 8) (j := 8 + idat.size)
        (hi := by omega) (hj := hchunk_ge))
  have hdata : (mkChunk "IDAT" idat).extract 8 (8 + idat.size) = idat := by
    simpa using mkChunk_extract_data "IDAT" idat idat_utf8ByteSize
  calc
    (encodeBitmap bmp).extract 41 (41 + idat.size)
        = tail.extract 8 (8 + idat.size) := hshift
    _ = (mkChunk "IDAT" idat).extract 8 (8 + idat.size) := hleft
    _ = idat := hdata

-- The IEND length field in the encoded PNG is zero.
lemma encodeBitmap_extract_iend_len (bmp : BitmapRGB8) :
    (encodeBitmap bmp).extract
        (45 + (zlibCompressStored (encodeRaw bmp)).size)
        (49 + (zlibCompressStored (encodeRaw bmp)).size) = u32be 0 := by
  let ihdr :=
    u32be bmp.size.width ++ u32be bmp.size.height ++ ByteArray.mk #[u8 8, u8 2, u8 0, u8 0, u8 0]
  let idat := zlibCompressStored (encodeRaw bmp)
  let sigIhdr := pngSignature ++ mkChunk "IHDR" ihdr
  let tail := mkChunk "IDAT" idat ++ mkChunk "IEND" ByteArray.empty
  have hsig : sigIhdr.size = 33 := by
    simpa [sigIhdr, ihdr] using encodeBitmap_sig_ihdr_size bmp
  have hidat : (mkChunk "IDAT" idat).size = idat.size + 12 := by
    have hsize : (mkChunk "IDAT" idat).size = idat.size + "IDAT".utf8ByteSize + 8 :=
      mkChunk_size _ _
    calc
      (mkChunk "IDAT" idat).size
          = idat.size + "IDAT".utf8ByteSize + 8 := hsize
      _ = idat.size + 12 := by
          simp [idat_utf8ByteSize]
  have hdef : encodeBitmap bmp = sigIhdr ++ tail := by
    simp [encodeBitmap, sigIhdr, tail, ihdr, idat, ByteArray.append_assoc, Id.run]
  have hshift' :
      (encodeBitmap bmp).extract
          (sigIhdr.size + (mkChunk "IDAT" idat).size)
          (sigIhdr.size + (mkChunk "IDAT" idat).size + 4) =
        tail.extract (mkChunk "IDAT" idat).size ((mkChunk "IDAT" idat).size + 4) := by
    simpa [hdef] using
      (ByteArray.extract_append_size_add
        (a := sigIhdr)
        (b := tail)
        (i := (mkChunk "IDAT" idat).size)
        (j := (mkChunk "IDAT" idat).size + 4))
  have hpos : sigIhdr.size + (mkChunk "IDAT" idat).size = 45 + idat.size := by
    omega
  have hpos' : sigIhdr.size + (mkChunk "IDAT" idat).size + 4 = 49 + idat.size := by
    omega
  have hshift :
      (encodeBitmap bmp).extract (45 + idat.size) (49 + idat.size) =
        tail.extract (mkChunk "IDAT" idat).size ((mkChunk "IDAT" idat).size + 4) := by
    have hshift := hshift'
    rw [hpos', hpos] at hshift
    exact hshift
  have hleft :
      tail.extract (mkChunk "IDAT" idat).size ((mkChunk "IDAT" idat).size + 4) =
        (mkChunk "IEND" ByteArray.empty).extract 0 4 := by
    simpa using
      (ByteArray.extract_append_size_add
        (a := mkChunk "IDAT" idat)
        (b := mkChunk "IEND" ByteArray.empty)
        (i := 0) (j := 4))
  have hlen : (mkChunk "IEND" ByteArray.empty).extract 0 4 = u32be 0 :=
    mkChunk_extract_len _ _
  calc
    (encodeBitmap bmp).extract (45 + idat.size) (49 + idat.size)
        = tail.extract (mkChunk "IDAT" idat).size ((mkChunk "IDAT" idat).size + 4) := hshift
    _ = (mkChunk "IEND" ByteArray.empty).extract 0 4 := hleft
    _ = u32be 0 := hlen

-- Reading the IEND length from the encoded PNG yields zero.
set_option maxHeartbeats 1000000 in
lemma readU32BE_encodeBitmap_iend_len (bmp : BitmapRGB8)
    (h : 45 + (zlibCompressStored (encodeRaw bmp)).size + 3 < (encodeBitmap bmp).size) :
    readU32BE (encodeBitmap bmp) (45 + (zlibCompressStored (encodeRaw bmp)).size) h = 0 := by
  let idat := zlibCompressStored (encodeRaw bmp)
  have hpos : 45 + idat.size + 3 < (encodeBitmap bmp).size := by
    simpa [idat] using h
  have hextract :
      (encodeBitmap bmp).extract (45 + idat.size) (45 + idat.size + 4) = u32be 0 := by
    have hshift : 45 + idat.size + 4 = 49 + idat.size := by omega
    simpa [idat, hshift] using encodeBitmap_extract_iend_len bmp
  exact readU32BE_of_extract_eq (bytes := encodeBitmap bmp) (pos := 45 + idat.size) (n := 0) hpos
    hextract (by decide)

-- The IEND type field in the encoded PNG is "IEND".
lemma encodeBitmap_extract_iend_type (bmp : BitmapRGB8) :
    (encodeBitmap bmp).extract
        (49 + (zlibCompressStored (encodeRaw bmp)).size)
        (53 + (zlibCompressStored (encodeRaw bmp)).size) = "IEND".toUTF8 := by
  let ihdr :=
    u32be bmp.size.width ++ u32be bmp.size.height ++ ByteArray.mk #[u8 8, u8 2, u8 0, u8 0, u8 0]
  let idat := zlibCompressStored (encodeRaw bmp)
  let sigIhdr := pngSignature ++ mkChunk "IHDR" ihdr
  let tail := mkChunk "IDAT" idat ++ mkChunk "IEND" ByteArray.empty
  have hsig : sigIhdr.size = 33 := by
    simpa [sigIhdr, ihdr] using encodeBitmap_sig_ihdr_size bmp
  have hidat : (mkChunk "IDAT" idat).size = idat.size + 12 := by
    have hsize : (mkChunk "IDAT" idat).size = idat.size + "IDAT".utf8ByteSize + 8 :=
      mkChunk_size _ _
    calc
      (mkChunk "IDAT" idat).size
          = idat.size + "IDAT".utf8ByteSize + 8 := hsize
      _ = idat.size + 12 := by
          simp [idat_utf8ByteSize]
  have hdef : encodeBitmap bmp = sigIhdr ++ tail := by
    simp [encodeBitmap, sigIhdr, tail, ihdr, idat, ByteArray.append_assoc, Id.run]
  have hshift' :
      (encodeBitmap bmp).extract
          (sigIhdr.size + (mkChunk "IDAT" idat).size + 4)
          (sigIhdr.size + (mkChunk "IDAT" idat).size + 8) =
        tail.extract ((mkChunk "IDAT" idat).size + 4) ((mkChunk "IDAT" idat).size + 8) := by
    rw [hdef]
    simpa [Nat.add_assoc] using
      (ByteArray.extract_append_size_add
        (a := sigIhdr)
        (b := tail)
        (i := (mkChunk "IDAT" idat).size + 4)
        (j := (mkChunk "IDAT" idat).size + 8))
  have hpos : sigIhdr.size + (mkChunk "IDAT" idat).size + 4 = 49 + idat.size := by
    have : 33 + (idat.size + 12) + 4 = 49 + idat.size := by
      omega
    simpa [hsig, hidat, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
  have hpos' : sigIhdr.size + (mkChunk "IDAT" idat).size + 8 = 53 + idat.size := by
    have : 33 + (idat.size + 12) + 8 = 53 + idat.size := by
      omega
    simpa [hsig, hidat, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
  have hshift :
      (encodeBitmap bmp).extract (49 + idat.size) (53 + idat.size) =
        tail.extract ((mkChunk "IDAT" idat).size + 4) ((mkChunk "IDAT" idat).size + 8) := by
    have hshift := hshift'
    rw [hpos', hpos] at hshift
    exact hshift
  have hleft :
      tail.extract ((mkChunk "IDAT" idat).size + 4) ((mkChunk "IDAT" idat).size + 8) =
        (mkChunk "IEND" ByteArray.empty).extract 4 8 := by
    simpa using
      (ByteArray.extract_append_size_add
        (a := mkChunk "IDAT" idat)
        (b := mkChunk "IEND" ByteArray.empty)
        (i := 4) (j := 8))
  have htyp : (mkChunk "IEND" ByteArray.empty).extract 4 8 = "IEND".toUTF8 := by
    simpa using mkChunk_extract_type "IEND" ByteArray.empty iend_utf8ByteSize
  calc
    (encodeBitmap bmp).extract (49 + idat.size) (53 + idat.size)
        = tail.extract ((mkChunk "IDAT" idat).size + 4) ((mkChunk "IDAT" idat).size + 8) := hshift
    _ = (mkChunk "IEND" ByteArray.empty).extract 4 8 := hleft
    _ = "IEND".toUTF8 := htyp

-- Closed-form size of PNG produced by encodeBitmap.
lemma encodeBitmap_size (bmp : BitmapRGB8) :
    (encodeBitmap bmp).size = (zlibCompressStored (encodeRaw bmp)).size + 57 := by
  unfold encodeBitmap
  have hihdr :
      (u32be bmp.size.width ++ u32be bmp.size.height ++
          ByteArray.mk #[u8 8, u8 2, u8 0, u8 0, u8 0]).size = 13 := by
    simpa using ihdr_payload_size bmp.size.width bmp.size.height
  simp [Id.run, ByteArray.size_append, mkChunk_size, pngSignature_size, hihdr,
    ihdr_utf8ByteSize, idat_utf8ByteSize, iend_utf8ByteSize, Nat.add_left_comm, Nat.add_comm]
  omega

-- Reading the IHDR chunk from an encoded bitmap yields its header payload.
lemma readChunk_encodeBitmap_ihdr (bmp : BitmapRGB8) :
    readChunk (encodeBitmap bmp) 8 =
      some ("IHDR".toUTF8,
        u32be bmp.size.width ++ u32be bmp.size.height ++
          ByteArray.mk #[u8 8, u8 2, u8 0, u8 0, u8 0],
        33) := by
  let ihdr :=
    u32be bmp.size.width ++ u32be bmp.size.height ++
      ByteArray.mk #[u8 8, u8 2, u8 0, u8 0, u8 0]
  let idat := zlibCompressStored (encodeRaw bmp)
  have hsize : (encodeBitmap bmp).size = idat.size + 57 := by
    simpa [idat] using encodeBitmap_size bmp
  have hlen : 8 + 3 < (encodeBitmap bmp).size := by
    simp [hsize]
  have hcrc : ¬ (33 > (encodeBitmap bmp).size) := by
    have hsz : 33 ≤ (encodeBitmap bmp).size := by
      simp [hsize]
    exact not_lt_of_ge hsz
  unfold readChunk
  simp [hlen, hcrc,
    readU32BE_encodeBitmap_ihdr_len (bmp := bmp) (h := hlen),
    encodeBitmap_extract_ihdr_type, encodeBitmap_extract_ihdr_data]

-- Reading the IDAT chunk from an encoded bitmap yields the compressed payload.
lemma readChunk_encodeBitmap_idat (bmp : BitmapRGB8)
    (hidat : (zlibCompressStored (encodeRaw bmp)).size < 2 ^ 32) :
    readChunk (encodeBitmap bmp) 33 =
      some ("IDAT".toUTF8, zlibCompressStored (encodeRaw bmp),
        45 + (zlibCompressStored (encodeRaw bmp)).size) := by
  let idat := zlibCompressStored (encodeRaw bmp)
  have hsize : (encodeBitmap bmp).size = idat.size + 57 := by
    simpa [idat] using encodeBitmap_size bmp
  have hlen : 33 + 3 < (encodeBitmap bmp).size := by
    simp [hsize]
  have hlenval : readU32BE (encodeBitmap bmp) 33 hlen = idat.size := by
    simpa [idat] using
      (readU32BE_encodeBitmap_idat_len (bmp := bmp) (h := hlen) (hidat := hidat))
  have htype : 33 + 4 = 37 := by omega
  have hdataStart : 33 + 8 = 41 := by omega
  have hcrcEnd : 41 + idat.size + 4 = 45 + idat.size := by omega
  have hcrc : ¬ (45 + idat.size > (encodeBitmap bmp).size) := by
    have hsz : 45 + idat.size ≤ (encodeBitmap bmp).size := by
      simp [hsize]; omega
    exact not_lt_of_ge hsz
  unfold readChunk
  simp [hlen, hlenval, hcrc, htype, hdataStart, hcrcEnd,
    encodeBitmap_extract_idat_type, encodeBitmap_extract_idat_data, idat]

-- Reading the IEND chunk from an encoded bitmap yields an empty payload.
lemma readChunk_encodeBitmap_iend (bmp : BitmapRGB8) :
    readChunk (encodeBitmap bmp)
        (45 + (zlibCompressStored (encodeRaw bmp)).size) =
      some ("IEND".toUTF8, ByteArray.empty,
        57 + (zlibCompressStored (encodeRaw bmp)).size) := by
  let idat := zlibCompressStored (encodeRaw bmp)
  have hsize : (encodeBitmap bmp).size = idat.size + 57 := by
    simpa [idat] using encodeBitmap_size bmp
  have hlen : 45 + idat.size + 3 < (encodeBitmap bmp).size := by
    simp [hsize]; omega
  have hlenval : readU32BE (encodeBitmap bmp) (45 + idat.size) hlen = 0 := by
    simpa [idat, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (readU32BE_encodeBitmap_iend_len (bmp := bmp) (h := hlen))
  have htype : 45 + idat.size + 4 = 49 + idat.size := by omega
  have htypeEnd : 49 + idat.size + 4 = 53 + idat.size := by omega
  have hdataStart : 45 + idat.size + 8 = 53 + idat.size := by omega
  have hcrcEnd : 53 + idat.size + 4 = 57 + idat.size := by omega
  have hcrc : ¬ (53 + idat.size + 4 > (encodeBitmap bmp).size) := by
    have hsz : 53 + idat.size + 4 ≤ (encodeBitmap bmp).size := by
      simp [hsize]; omega
    exact not_lt_of_ge hsz
  have hpos : 57 + idat.size ≤ (encodeBitmap bmp).size := by
    simp [hsize]; omega
  unfold readChunk
  simp [hlen, hlenval, hcrcEnd, htype, htypeEnd, hdataStart,
    encodeBitmap_extract_iend_type, idat, hpos]

-- Parsing an encoded bitmap with the simple PNG parser recovers the header and payload.
set_option maxHeartbeats 1000000 in
lemma parsePngSimple_encodeBitmap (bmp : BitmapRGB8)
    (hw : bmp.size.width < 2 ^ 32) (hh : bmp.size.height < 2 ^ 32)
    (hidat : (zlibCompressStored (encodeRaw bmp)).size < 2 ^ 32)
    (hsize : 8 <= (encodeBitmap bmp).size) :
    parsePngSimple (encodeBitmap bmp) hsize =
      some ({ width := bmp.size.width, height := bmp.size.height
            , colorType := 2, bitDepth := 8 },
            zlibCompressStored (encodeRaw bmp)) := by
  let w := bmp.size.width
  let h := bmp.size.height
  let ihdr := u32be w ++ u32be h ++ ihdrTail
  let idat := zlibCompressStored (encodeRaw bmp)
  have hlen' : ihdr.size = 13 := by
    simpa [ihdr, ihdrTail] using ihdr_payload_size w h
  have hsigNe : (pngSignature != pngSignature) = false := by
    exact bne_self_eq_false' (a := pngSignature)
  have hihdrNe : ("IHDR".toUTF8 != "IHDR".toUTF8) = false := by
    exact bne_self_eq_false' (a := "IHDR".toUTF8)
  have hidatNe : ("IDAT".toUTF8 != "IDAT".toUTF8) = false := by
    exact bne_self_eq_false' (a := "IDAT".toUTF8)
  have hiendNe : ("IEND".toUTF8 != "IEND".toUTF8) = false := by
    exact bne_self_eq_false' (a := "IEND".toUTF8)
  have htailEq : ihdr.extract 8 13 = ihdrTail := by
    simpa [ihdr, ihdrTail] using ihdr_payload_extract_tail w h
  have htailNe : (ihdr.extract 8 13 != ihdrTail) = false := by
    rw [htailEq]
    exact bne_self_eq_false' (a := ihdrTail)
  have hpos0 : 0 + 3 < ihdr.size := by
    have : ihdr.size = 13 := hlen'
    omega
  have hpos4 : 4 + 3 < ihdr.size := by
    have : ihdr.size = 13 := hlen'
    omega
  have hwidth0 : readU32BE ihdr 0 hpos0 = w := by
    have hextract : ihdr.extract 0 4 = u32be w := by
      simpa [ihdr, ihdrTail] using ihdr_payload_extract_width w h
    exact readU32BE_of_extract_eq ihdr 0 w hpos0 hextract hw
  have hheight0 : readU32BE ihdr 4 hpos4 = h := by
    have hextract : ihdr.extract 4 8 = u32be h := by
      simpa [ihdr, ihdrTail] using ihdr_payload_extract_height w h
    exact readU32BE_of_extract_eq ihdr 4 h hpos4 hextract hh
  have hwidth : readU32BE ihdr 0 (by simp [hlen']) = w := by
    have hproof :=
      readU32BE_proof_irrel (bytes := ihdr) (pos := 0)
        (h1 := by simp [hlen']) (h2 := hpos0)
    exact hproof.trans hwidth0
  have hheight : readU32BE ihdr 4 (by simp [hlen']) = h := by
    have hproof :=
      readU32BE_proof_irrel (bytes := ihdr) (pos := 4)
        (h1 := by simp [hlen']) (h2 := hpos4)
    exact hproof.trans hheight0
  -- Unfold and simplify the parser using the chunk-level lemmas.
  unfold parsePngSimple
  simp [encodeBitmap_signature,
    readChunk_encodeBitmap_ihdr,
    readChunk_encodeBitmap_idat (bmp := bmp) (hidat := hidat),
    readChunk_encodeBitmap_iend]
  refine And.intro hsigNe ?_
  refine And.intro hihdrNe ?_
  refine And.intro htailNe ?_
  refine And.intro hidatNe ?_
  refine And.intro hiendNe ?_
  exact ⟨hlen', hwidth, hheight⟩

-- Parsing an encoded bitmap with the full PNG parser yields the header and payload.
lemma parsePng_encodeBitmap (bmp : BitmapRGB8)
    (hw : bmp.size.width < 2 ^ 32) (hh : bmp.size.height < 2 ^ 32)
    (hidat : (zlibCompressStored (encodeRaw bmp)).size < 2 ^ 32)
    (hsize : 8 <= (encodeBitmap bmp).size) :
    parsePng (encodeBitmap bmp) hsize =
      some ({ width := bmp.size.width, height := bmp.size.height
            , colorType := 2, bitDepth := 8 },
            zlibCompressStored (encodeRaw bmp)) := by
  have hsimple := parsePngSimple_encodeBitmap bmp hw hh hidat hsize
  unfold parsePng
  simp [hsimple]

lemma bitIndex_readBit (br : BitReader) (h : br.bytePos < br.data.size) :
    (BitReader.readBit br).2.bitIndex = br.bitIndex + 1 :=
  Png.bitIndex_readBit br h

lemma readBit_data (br : BitReader) (h : br.bytePos < br.data.size) :
    (br.readBit).2.data = br.data :=
  Png.readBit_data br h

-- Re-export: static Huffman length base table size.
lemma lengthBases_size : lengthBases.size = 29 := Png.lengthBases_size
-- Re-export: static Huffman length extra table size.
lemma lengthExtra_size : lengthExtra.size = 29 := Png.lengthExtra_size
-- Re-export: static Huffman distance base table size.
lemma distBases_size : distBases.size = 30 := Png.distBases_size
-- Re-export: static Huffman distance extra table size.
lemma distExtra_size : distExtra.size = 30 := Png.distExtra_size

end Lemmas
end Bitmaps
