import Bitmap.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Data.ByteArray.Lemmas
import Init.Data.UInt.Lemmas

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

-- IHDR payload is always 13 bytes.
lemma ihdr_payload_size (w h : Nat) :
    (u32be w ++ u32be h ++ ByteArray.mk #[u8 8, u8 2, u8 0, u8 0, u8 0]).size = 13 := by
  have hbytes : (ByteArray.mk #[u8 8, u8 2, u8 0, u8 0, u8 0]).size = 5 := by
    decide
  simp [ByteArray.size_append, u32be_size, hbytes]

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
