import Bitmap.Basic

namespace Bitmaps

lemma byteArray_size_set {bs : ByteArray} {i : Nat} {h : i < bs.size} {b : UInt8} :
    (bs.set i b h).size = bs.size := by
  cases bs with
  | mk data =>
      simp [ByteArray.set, ByteArray.size, Array.size_set]

namespace Png

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

lemma readBit_data (br : BitReader) (h : br.bytePos < br.data.size) :
    (br.readBit).2.data = br.data := by
  unfold BitReader.readBit
  have hne : br.bytePos ≠ br.data.size := ne_of_lt h
  by_cases hnext : br.bitPos + 1 = 8 <;> simp [hne, hnext]

lemma lengthBases_size : lengthBases.size = 29 := by decide
lemma lengthExtra_size : lengthExtra.size = 29 := by decide
lemma distBases_size : distBases.size = 30 := by decide
lemma distExtra_size : distExtra.size = 30 := by decide

end Png

namespace Lemmas

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

lemma arrayCoordSize_u32
    {i w h : Nat} {x y : UInt32}
    (hx : x.toNat < w)
    (hy : y.toNat < h)
    (hi : i = x.toNat + y.toNat * w) :
    i < w * h := by
  have hlt : x.toNat + y.toNat * w < w * h :=
    arrayCoordSize_nat (i := x.toNat + y.toNat * w) hx hy rfl
  simpa [hi] using hlt

@[simp] lemma byteArray_get_set_self
    {bs : ByteArray} {i : Nat} (h : i < bs.size) {v : UInt8} :
    (bs.set i v h).get i (by simpa [byteArray_size_set] using h) = v := by
  cases bs with
  | mk arr =>
      simp [ByteArray.set, ByteArray.get]

@[simp] lemma byteArray_get_set_self'
    {bs : ByteArray} {i : Nat} (h : i < bs.size) {v : UInt8}
    {h' : i < (bs.set i v h).size} :
    (bs.set i v h).get i h' = v := by
  simp [byteArray_get_set_self (bs := bs) (i := i) (h := h) (v := v)]

lemma byteArray_get_set_ne
    {bs : ByteArray} {i j : Nat} (hi : i < bs.size) (hj : j < bs.size)
    (hij : i ≠ j) {v : UInt8} :
    (bs.set i v hi).get j (by simpa [byteArray_size_set] using hj) = bs.get j hj := by
  cases bs with
  | mk arr =>
      simpa [ByteArray.set, ByteArray.get] using
        (Array.getElem_set_ne (xs := arr) (i := i) (j := j) (h' := hi) (pj := hj) (h := hij))

lemma byteArray_get_set_ne'
    {bs : ByteArray} {i j : Nat} (hi : i < bs.size) (hj : j < bs.size)
    (hij : i ≠ j) {v : UInt8} {h' : j < (bs.set i v hi).size} :
    (bs.set i v hi).get j h' = bs.get j hj := by
  simpa using (byteArray_get_set_ne (bs := bs) (i := i) (j := j) (hi := hi) (hj := hj) (hij := hij) (v := v))

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

lemma u16le_size (n : Nat) : (u16le n).size = 2 := by
  have h : (u16le n).data.size = 2 := by
    simp [u16le]
  simpa [ByteArray.size_data] using h

lemma u32be_size (n : Nat) : (u32be n).size = 4 := by
  have h : (u32be n).data.size = 4 := by
    simp [u32be]
  simpa [ByteArray.size_data] using h

lemma pngSignature_size : pngSignature.size = 8 := by
  have h : pngSignature.data.size = 8 := by
    simp [pngSignature]
  simpa [ByteArray.size_data] using h

lemma mkChunk_size (typ : String) (data : ByteArray) :
    (mkChunk typ data).size = data.size + typ.utf8ByteSize + 8 := by
  calc
    (mkChunk typ data).size = data.size + typ.utf8ByteSize + 4 + 4 := by
      simp [mkChunk, u32be_size, Nat.add_left_comm, Nat.add_comm]
    _ = data.size + typ.utf8ByteSize + (4 + 4) := by
      simp [Nat.add_assoc]
    _ = data.size + typ.utf8ByteSize + 8 := by
      simp

lemma bitIndex_readBit (br : BitReader) (h : br.bytePos < br.data.size) :
    (BitReader.readBit br).2.bitIndex = br.bitIndex + 1 :=
  Png.bitIndex_readBit br h

lemma readBit_data (br : BitReader) (h : br.bytePos < br.data.size) :
    (br.readBit).2.data = br.data :=
  Png.readBit_data br h

lemma lengthBases_size : lengthBases.size = 29 := Png.lengthBases_size
lemma lengthExtra_size : lengthExtra.size = 29 := Png.lengthExtra_size
lemma distBases_size : distBases.size = 30 := Png.distBases_size
lemma distExtra_size : distExtra.size = 30 := Png.distExtra_size

end Lemmas
end Bitmaps
