import Bitmap.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Nat.Bitwise.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.ByteArray.Lemmas
import Init.Data.Range.Lemmas
import Init.Data.UInt.Lemmas
import Batteries.Data.ByteArray
import Bitmap.Lemmas.Png.Core
import Bitmap.Lemmas.Png.FixedLiteral
import Bitmap.Lemmas.Png.FixedBlock

universe u

namespace Bitmaps

namespace Lemmas

open Png
attribute [local simp] Png.byteArray_get_proof_irrel

def encodeBitmapIdat {px : Type u} [Pixel px] [PngPixel px]
    (bmp : Bitmap px) (mode : PngEncodeMode) : ByteArray :=
  match mode with
  | .stored => zlibCompressStored (PngPixel.encodeRaw (α := px) bmp)
  | .fixed => zlibCompressFixed (PngPixel.encodeRaw (α := px) bmp)

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

instance instPixelRGB8 : Pixel PixelRGB8 where
  bytesPerPixel := bytesPerPixelRGB
  bytesPerPixel_pos := by decide
  read_write := by
    intro data base h px
    cases px with
    | mk r g b =>
        have h2 : base + 2 < data.size := by
          simpa [bytesPerPixelRGB] using h
        have h1 : base + 1 < data.size := by omega
        have h0 : base < data.size := by omega
        have size_set {bs : ByteArray} {i : Nat} (hi : i < bs.size) {v : UInt8} :
            (bs.set i v hi).size = bs.size := by
          cases bs with
          | mk arr =>
              simp [ByteArray.set, ByteArray.size, Array.size_set]
        let data1 := data.set base r h0
        have hsize1 : data1.size = data.size := by
          simp [data1, size_set]
        have h1d1 : base + 1 < data1.size := by
          simpa [hsize1] using h1
        let data2 := data1.set (base + 1) g h1d1
        have hsize2 : data2.size = data.size := by
          have hsize2' : data2.size = data1.size := by
            simp [data2, size_set]
          simpa [hsize1] using hsize2'
        have h2d2 : base + 2 < data2.size := by
          simpa [hsize2] using h2
        let data3 := data2.set (base + 2) b h2d2
        have hsize3 : data3.size = data.size := by
          have hsize3' : data3.size = data2.size := by
            simp [data3, size_set]
          simpa [hsize2] using hsize3'
        have h0d1 : base < data1.size := by
          simpa [hsize1] using h0
        have h0d2 : base < data2.size := by
          simpa [hsize2] using h0
        have h0d3 : base < data3.size := by
          simpa [hsize3] using h0
        have h1d2 : base + 1 < data2.size := by
          simpa [hsize2] using h1
        have h1d3 : base + 1 < data3.size := by
          simpa [hsize3] using h1
        have h2d3 : base + 2 < data3.size := by
          simpa [hsize3] using h2
        have get_set_ne :
            ∀ {bs : ByteArray} {i j : Nat} (hi : i < bs.size) (hj : j < bs.size)
              (hij : i ≠ j) {v : UInt8} {h' : j < (bs.set i v hi).size},
              (bs.set i v hi).get j h' = bs.get j hj := by
          intro bs i j hi hj hij v h'
          cases bs with
          | mk arr =>
              simpa [ByteArray.set, ByteArray.get] using
                (Array.getElem_set_ne (xs := arr) (i := i) (j := j) (h' := hi) (pj := hj)
                  (h := hij))
        have hr : data3.get base h0d3 = r := by
          have hr1 : data3.get base h0d3 = data2.get base h0d2 := by
            simpa [data3] using
              (get_set_ne (bs := data2) (i := base + 2) (j := base)
                (hi := h2d2) (hj := h0d2) (hij := by omega) (v := b) (h' := h0d3))
          have hr2 : data2.get base h0d2 = data1.get base h0d1 := by
            simpa [data2] using
              (get_set_ne (bs := data1) (i := base + 1) (j := base)
                (hi := h1d1) (hj := h0d1) (hij := by omega) (v := g) (h' := h0d2))
          have hr3 : data1.get base h0d1 = r := by
            simp [data1, ByteArray.set, ByteArray.get]
          simp [hr1, hr2, hr3]
        have hg : data3.get (base + 1) h1d3 = g := by
          have hg1 : data3.get (base + 1) h1d3 = data2.get (base + 1) h1d2 := by
            simpa [data3] using
              (get_set_ne (bs := data2) (i := base + 2) (j := base + 1)
                (hi := h2d2) (hj := h1d2) (hij := by omega) (v := b) (h' := h1d3))
          have hg2 : data2.get (base + 1) h1d2 = g := by
            simp [data2, ByteArray.set, ByteArray.get]
          simp [hg1, hg2]
        have hb : data3.get (base + 2) h2d3 = b := by
          simp [data3, ByteArray.set, ByteArray.get]
        simp [pixelReadRGB8, pixelWriteRGB8, data1, data2, data3, hr, hg, hb]
  read := fun data base h =>
    pixelReadRGB8 data base (by simpa [bytesPerPixelRGB] using h)
  write := fun data base h px =>
    pixelWriteRGB8 data base (by simpa [bytesPerPixelRGB] using h) px
  write_size := by
    intro data base h px
    cases data with
    | mk arr =>
        simp [pixelWriteRGB8, ByteArray.set, ByteArray.size, Array.size_set]

instance instPixelRGBA8 : Pixel PixelRGBA8 where
  bytesPerPixel := bytesPerPixelRGBA
  bytesPerPixel_pos := by decide
  read_write := by
    intro data base h px
    cases px with
    | mk r g b a =>
        have h3 : base + 3 < data.size := by
          simpa [bytesPerPixelRGBA] using h
        have h2 : base + 2 < data.size := by omega
        have h1 : base + 1 < data.size := by omega
        have h0 : base < data.size := by omega
        have size_set {bs : ByteArray} {i : Nat} (hi : i < bs.size) {v : UInt8} :
            (bs.set i v hi).size = bs.size := by
          cases bs with
          | mk arr =>
              simp [ByteArray.set, ByteArray.size, Array.size_set]
        let data1 := data.set base r h0
        have hsize1 : data1.size = data.size := by
          simp [data1, size_set]
        have h1d1 : base + 1 < data1.size := by
          simpa [hsize1] using h1
        let data2 := data1.set (base + 1) g h1d1
        have hsize2 : data2.size = data.size := by
          have hsize2' : data2.size = data1.size := by
            simp [data2, size_set]
          simpa [hsize1] using hsize2'
        have h2d2 : base + 2 < data2.size := by
          simpa [hsize2] using h2
        let data3 := data2.set (base + 2) b h2d2
        have hsize3 : data3.size = data.size := by
          have hsize3' : data3.size = data2.size := by
            simp [data3, size_set]
          simpa [hsize2] using hsize3'
        have h3d3 : base + 3 < data3.size := by
          simpa [hsize3] using h3
        let data4 := data3.set (base + 3) a h3d3
        have hsize4 : data4.size = data.size := by
          have hsize4' : data4.size = data3.size := by
            simp [data4, size_set]
          simpa [hsize3] using hsize4'
        have h0d1 : base < data1.size := by
          simpa [hsize1] using h0
        have h0d2 : base < data2.size := by
          simpa [hsize2] using h0
        have h0d3 : base < data3.size := by
          simpa [hsize3] using h0
        have h0d4 : base < data4.size := by
          simpa [hsize4] using h0
        have h1d2 : base + 1 < data2.size := by
          simpa [hsize2] using h1
        have h1d3 : base + 1 < data3.size := by
          simpa [hsize3] using h1
        have h1d4 : base + 1 < data4.size := by
          simpa [hsize4] using h1
        have h2d3 : base + 2 < data3.size := by
          simpa [hsize3] using h2
        have h2d4 : base + 2 < data4.size := by
          simpa [hsize4] using h2
        have h3d4 : base + 3 < data4.size := by
          simpa [hsize4] using h3
        have get_set_ne {bs : ByteArray} {i j : Nat}
            (hi : i < bs.size) (hj : j < bs.size) (hij : i ≠ j) {v : UInt8}
            (h' : j < (bs.set i v hi).size) :
            (bs.set i v hi).get j h' = bs.get j hj := by
          cases bs with
          | mk arr =>
              simpa [ByteArray.set, ByteArray.get] using
                (Array.getElem_set_ne (xs := arr) (i := i) (j := j) (h' := hi) (pj := hj)
                  (h := hij))
        have hr : data4.get base h0d4 = r := by
          have hr1 : data4.get base h0d4 = data3.get base h0d3 := by
            simpa [data4] using
              (get_set_ne (bs := data3) (i := base + 3) (j := base)
                (hi := h3d3) (hj := h0d3) (hij := by omega) (v := a) (h' := h0d4))
          have hr2 : data3.get base h0d3 = data2.get base h0d2 := by
            simpa [data3] using
              (get_set_ne (bs := data2) (i := base + 2) (j := base)
                (hi := h2d2) (hj := h0d2) (hij := by omega) (v := b) (h' := h0d3))
          have hr3 : data2.get base h0d2 = data1.get base h0d1 := by
            simpa [data2] using
              (get_set_ne (bs := data1) (i := base + 1) (j := base)
                (hi := h1d1) (hj := h0d1) (hij := by omega) (v := g) (h' := h0d2))
          have hr4 : data1.get base h0d1 = r := by
            simp [data1, ByteArray.set, ByteArray.get]
          simp [hr1, hr2, hr3, hr4]
        have hg : data4.get (base + 1) h1d4 = g := by
          have hg1 : data4.get (base + 1) h1d4 = data3.get (base + 1) h1d3 := by
            simpa [data4] using
              (get_set_ne (bs := data3) (i := base + 3) (j := base + 1)
                (hi := h3d3) (hj := h1d3) (hij := by omega) (v := a) (h' := h1d4))
          have hg2 : data3.get (base + 1) h1d3 = data2.get (base + 1) h1d2 := by
            simpa [data3] using
              (get_set_ne (bs := data2) (i := base + 2) (j := base + 1)
                (hi := h2d2) (hj := h1d2) (hij := by omega) (v := b) (h' := h1d3))
          have hg3 : data2.get (base + 1) h1d2 = g := by
            simp [data2, ByteArray.set, ByteArray.get]
          simp [hg1, hg2, hg3]
        have hb : data4.get (base + 2) h2d4 = b := by
          have hb1 : data4.get (base + 2) h2d4 = data3.get (base + 2) h2d3 := by
            simpa [data4] using
              (get_set_ne (bs := data3) (i := base + 3) (j := base + 2)
                (hi := h3d3) (hj := h2d3) (hij := by omega) (v := a) (h' := h2d4))
          have hb2 : data3.get (base + 2) h2d3 = b := by
            simp [data3, ByteArray.set, ByteArray.get]
          simp [hb1, hb2]
        have ha : data4.get (base + 3) h3d4 = a := by
          simp [data4, ByteArray.set, ByteArray.get]
        simp [pixelReadRGBA8, pixelWriteRGBA8, data1, data2, data3, data4, hr, hg, hb, ha]
  read := fun data base h =>
    pixelReadRGBA8 data base (by simpa [bytesPerPixelRGBA] using h)
  write := fun data base h px =>
    pixelWriteRGBA8 data base (by simpa [bytesPerPixelRGBA] using h) px
  write_size := by
    intro data base h px
    cases data with
    | mk arr =>
        simp [pixelWriteRGBA8, ByteArray.set, ByteArray.size, Array.size_set]

instance instPixelGray8 : Pixel PixelGray8 where
  bytesPerPixel := bytesPerPixelGray
  bytesPerPixel_pos := by decide
  read_write := by
    intro data base h px
    cases px with
    | mk v =>
        have h0 : base < data.size := by
          simpa [bytesPerPixelGray] using h
        simp [pixelReadGray8, pixelWriteGray8, ByteArray.set, ByteArray.get]
  read := fun data base h =>
    pixelReadGray8 data base (by simpa [bytesPerPixelGray] using h)
  write := fun data base h px =>
    pixelWriteGray8 data base (by simpa [bytesPerPixelGray] using h) px
  write_size := by
    intro data base h px
    cases data with
    | mk arr =>
        simp [pixelWriteGray8, ByteArray.set, ByteArray.size, Array.size_set]

-- Bytes per pixel for RGB8.
lemma bytesPerPixel_rgb : Pixel.bytesPerPixel (α := PixelRGB8) = bytesPerPixelRGB := by
  rfl

-- Bytes per pixel for RGBA8.
lemma bytesPerPixel_rgba : Pixel.bytesPerPixel (α := PixelRGBA8) = bytesPerPixelRGBA := by
  rfl

-- Bytes per pixel for Gray8.
lemma bytesPerPixel_gray : Pixel.bytesPerPixel (α := PixelGray8) = bytesPerPixelGray := by
  rfl

instance : PngPixel PixelRGB8 where
  encodeRaw := encodeRaw
  colorType := u8 2
  decodeRowsLoop := decodeRowsLoop

instance : PngPixel PixelRGBA8 where
  encodeRaw := encodeRaw
  colorType := u8 6
  decodeRowsLoop := decodeRowsLoopRGBA

instance : PngPixel PixelGray8 where
  encodeRaw := encodeRaw
  colorType := u8 0
  decodeRowsLoop := decodeRowsLoopGray

-- PNG color type for RGB8.
@[simp] lemma pngPixel_colorType_rgb : PngPixel.colorType (α := PixelRGB8) = u8 2 := by
  rfl

-- PNG color type for RGBA8.
@[simp] lemma pngPixel_colorType_rgba : PngPixel.colorType (α := PixelRGBA8) = u8 6 := by
  rfl

-- PNG color type for Gray8.
@[simp] lemma pngPixel_colorType_gray : PngPixel.colorType (α := PixelGray8) = u8 0 := by
  rfl

-- PNG raw encoding for RGB8.
@[simp] lemma pngPixel_encodeRaw_rgb : PngPixel.encodeRaw (α := PixelRGB8) = encodeRaw := by
  rfl

-- PNG raw encoding for RGBA8.
@[simp] lemma pngPixel_encodeRaw_rgba : PngPixel.encodeRaw (α := PixelRGBA8) = encodeRaw := by
  rfl

-- PNG raw encoding for Gray8.
@[simp] lemma pngPixel_encodeRaw_gray : PngPixel.encodeRaw (α := PixelGray8) = encodeRaw := by
  rfl

-- PNG row decoder for RGB8.
@[simp] lemma pngPixel_decodeRowsLoop_rgb :
    PngPixel.decodeRowsLoop (α := PixelRGB8) = decodeRowsLoop := by
  rfl

-- PNG row decoder for RGBA8.
@[simp] lemma pngPixel_decodeRowsLoop_rgba :
    PngPixel.decodeRowsLoop (α := PixelRGBA8) = decodeRowsLoopRGBA := by
  rfl

-- PNG row decoder for Gray8.
@[simp] lemma pngPixel_decodeRowsLoop_gray :
    PngPixel.decodeRowsLoop (α := PixelGray8) = decodeRowsLoopGray := by
  rfl

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

-- Reading a 16-bit value depends only on the extracted 2-byte slice.
lemma readU16LE_extract (bytes : ByteArray) (pos : Nat) (h : pos + 1 < bytes.size) :
    readU16LE bytes pos h =
      readU16LE (bytes.extract pos (pos + 2)) 0 (by
        have hle : pos + 2 ≤ bytes.size := Nat.succ_le_of_lt h
        simp [ByteArray.size_extract, Nat.min_eq_left hle, Nat.add_sub_cancel_left]) := by
  cases bytes with
  | mk data =>
      simp [readU16LE, ByteArray.extract, ByteArray.get]

-- `readU16LE` is proof-irrelevant in its bounds argument.
lemma readU16LE_proof_irrel {bytes : ByteArray} {pos : Nat}
    (h1 h2 : pos + 1 < bytes.size) :
    readU16LE bytes pos h1 = readU16LE bytes pos h2 := by
  rfl

-- Reading a 16-bit value from a slice that equals `u16le n` yields `n`.
lemma readU16LE_of_extract_eq (bytes : ByteArray) (pos n : Nat)
    (h : pos + 1 < bytes.size)
    (hextract : bytes.extract pos (pos + 2) = u16le n)
    (hn : n < 2 ^ 16) :
    readU16LE bytes pos h = n := by
  have h' := readU16LE_extract (bytes := bytes) (pos := pos) h
  have hcanon : readU16LE (u16le n) 0 (by simp [u16le_size]) = n :=
    readU16LE_u16le n hn
  have h'' :
      readU16LE (bytes.extract pos (pos + 2)) 0 (by
        have hle : pos + 2 ≤ bytes.size := Nat.succ_le_of_lt h
        simp [ByteArray.size_extract, Nat.min_eq_left hle]) = n := by
    simpa [hextract] using hcanon
  exact h'.trans h''

-- Proof-friendly spec: expose the stored-block inflater with remainder.
def inflateStoredSpec (data : ByteArray) : Option (ByteArray × ByteArray) :=
  if h : 0 < data.size then
    inflateStoredAux data h
  else
    none

-- The public inflater is the spec restricted to empty remainder.
lemma inflateStored_eq_spec (data : ByteArray) :
    inflateStored data =
      match inflateStoredSpec data with
      | some (payload, rest) => if rest.size == 0 then some payload else none
      | none => none := by
  by_cases h : 0 < data.size
  · cases haux : inflateStoredAux data h <;> simp [inflateStored, inflateStoredSpec, h, haux]
  · simp [inflateStored, inflateStoredSpec, h]

-- Transport `inflateStoredAux` across definitional equality of inputs.
lemma inflateStoredAux_congr {data1 data2 : ByteArray} (h : data1 = data2)
    (h1 : 0 < data1.size) :
    inflateStoredAux data1 h1 = inflateStoredAux data2 (by simpa [h] using h1) := by
  cases h
  rfl


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

@[simp] lemma emptyWithCapacity_eq_empty (c : Nat) :
    ByteArray.emptyWithCapacity c = ByteArray.empty := by
  rfl

attribute [simp] ByteArray.empty_append ByteArray.append_empty

lemma mkChunkBytes_def (typBytes data : ByteArray) :
    mkChunkBytes typBytes data =
      u32be data.size ++ typBytes ++ data ++ u32be (crc32Chunk typBytes data).toNat := by
  simp [mkChunkBytes, emptyWithCapacity_eq_empty, ByteArray.empty_append]

@[simp] lemma mkChunkBytes_ihdr (data : ByteArray) :
    mkChunkBytes ihdrTypeBytes data = mkChunk "IHDR" data := by
  rfl

@[simp] lemma mkChunkBytes_idat (data : ByteArray) :
    mkChunkBytes idatTypeBytes data = mkChunk "IDAT" data := by
  rfl

@[simp] lemma mkChunkBytes_iend (data : ByteArray) :
    mkChunkBytes iendTypeBytes data = mkChunk "IEND" data := by
  rfl

-- Chunk size = payload + type tag + length field + CRC field.
lemma mkChunk_size (typ : String) (data : ByteArray) :
    (mkChunk typ data).size = data.size + typ.utf8ByteSize + 8 := by
  calc
    (mkChunk typ data).size = data.size + typ.utf8ByteSize + 4 + 4 := by
      simp [mkChunk, mkChunkBytes_def, u32be_size, Nat.add_left_comm, Nat.add_comm]
    _ = data.size + typ.utf8ByteSize + (4 + 4) := by
      simp [Nat.add_assoc]
    _ = data.size + typ.utf8ByteSize + 8 := by
      simp

-- Size of a stored deflate block: header + LEN + NLEN + payload.
lemma storedBlock_size (payload : ByteArray) (final : Bool) :
    (storedBlock payload final).size = payload.size + 5 := by
  let header : ByteArray := ByteArray.mk #[if final then u8 0x01 else u8 0x00]
  have hheader : header.size = 1 := by rfl
  simp [storedBlock, header, ByteArray.size_append, u16le_size, hheader, Nat.add_comm]

-- Fast deflate-stored with an accumulator equals the specification.
lemma deflateStoredFastAux_correct (raw out : ByteArray) :
    deflateStoredFastAux raw out = out ++ deflateStored raw := by
  classical
  refine
    (Nat.strong_induction_on (n := raw.size)
      (p := fun n =>
        ∀ raw' out, raw'.size = n → deflateStoredFastAux raw' out = out ++ deflateStored raw')
      (fun n ih raw out hsize => by
        by_cases hzero : raw.size = 0
        · simp [deflateStoredFastAux, deflateStored, hzero]
        · have hpos_raw : 0 < raw.size := Nat.pos_of_ne_zero hzero
          let blockLen := if 65535 < raw.size then 65535 else raw.size
          let payload := raw.extract 0 blockLen
          let block := storedBlock payload (blockLen == raw.size)
          by_cases hfinal' : blockLen == raw.size
          ·
            have hblock : block = storedBlock (raw.extract 0 blockLen) true := by
              simp [block, payload, hfinal']
            have hfast :
                deflateStoredFastAux raw out =
                  out ++ storedBlock (raw.extract 0 blockLen) true := by
              rw [deflateStoredFastAux.eq_1]
              simp [hzero, blockLen, hfinal']
            have hslow :
                deflateStored raw = storedBlock (raw.extract 0 blockLen) true := by
              rw [deflateStored.eq_1]
              simp [hzero, blockLen, hfinal']
            have hfast' : deflateStoredFastAux raw out = out ++ block := by
              simpa [hblock] using hfast
            have hslow' : deflateStored raw = block := by
              simpa [hblock] using hslow
            simp [hfast', hslow']
          · have hle : blockLen ≤ raw.size := by
              by_cases hlarge : 65535 < raw.size
              · have : (65535 : Nat) ≤ raw.size := Nat.le_of_lt hlarge
                simpa [blockLen, hlarge] using this
              · simp [blockLen, hlarge]
            have hpos : 0 < blockLen := by
              by_cases hlarge : 65535 < raw.size
              · simp [blockLen, hlarge]
              · simp [blockLen, hlarge, hpos_raw]
            have hrest_size :
                (raw.extract blockLen raw.size).size < raw.size := by
              have hrest_size' :
                  (raw.extract blockLen raw.size).size = raw.size - blockLen := by
                simp [ByteArray.size_extract]
              have hsub : raw.size - blockLen < raw.size := Nat.sub_lt_self hpos hle
              simpa [hrest_size'] using hsub
            have hrest_size' : (raw.extract blockLen raw.size).size < n := by
              simpa [hsize] using hrest_size
            have hrec :=
              ih (raw.extract blockLen raw.size).size hrest_size'
                (raw.extract blockLen raw.size) (out ++ block) rfl
            have hfast :
                deflateStoredFastAux raw out =
                  deflateStoredFastAux (raw.extract blockLen raw.size)
                    (out ++ storedBlock (raw.extract 0 blockLen) false) := by
              rw [deflateStoredFastAux.eq_1]
              simp [hzero, blockLen, hfinal']
            have hslow :
                deflateStored raw =
                  storedBlock (raw.extract 0 blockLen) false ++
                    deflateStored (raw.extract blockLen raw.size) := by
              rw [deflateStored.eq_1]
              simp [hzero, blockLen, hfinal']
            have hblock : block = storedBlock (raw.extract 0 blockLen) false := by
              simp [block, payload, hfinal']
            have hfast' :
                deflateStoredFastAux raw out =
                  deflateStoredFastAux (raw.extract blockLen raw.size) (out ++ block) := by
              simpa [hblock] using hfast
            have hslow' :
                deflateStored raw =
                  block ++ deflateStored (raw.extract blockLen raw.size) := by
              simpa [hblock] using hslow
            calc
              deflateStoredFastAux raw out =
                  deflateStoredFastAux (raw.extract blockLen raw.size) (out ++ block) := hfast'
              _ = (out ++ block) ++ deflateStored (raw.extract blockLen raw.size) := hrec
              _ = out ++ (block ++ deflateStored (raw.extract blockLen raw.size)) := by
                  simp [ByteArray.append_assoc]
              _ = out ++ deflateStored raw := by
                  simp [hslow']
      )) raw out rfl

-- Fast deflate-stored equals the specification.
lemma deflateStoredFast_eq (raw : ByteArray) :
    deflateStoredFast raw = deflateStored raw := by
  unfold deflateStoredFast
  simpa using (deflateStoredFastAux_correct raw ByteArray.empty)

-- Deflate-stored output is always non-empty.
lemma deflateStored_pos (raw : ByteArray) : 0 < (deflateStored raw).size := by
  by_cases hzero : raw.size = 0
  · rw [deflateStored.eq_1]
    simp [hzero, storedBlock_size]
  · rw [deflateStored.eq_1]
    by_cases hfinal : ((if raw.size > 65535 then 65535 else raw.size) == raw.size) = true
    · simp [hzero, hfinal, storedBlock_size, -beq_iff_eq]
    · simp [hzero, hfinal, ByteArray.size_append, storedBlock_size, -beq_iff_eq]
      omega

-- The LEN field of a stored block encodes the payload size.
lemma storedBlock_extract_len (payload : ByteArray) (final : Bool) :
    (storedBlock payload final).extract 1 3 = u16le payload.size := by
  let len := payload.size
  let header : ByteArray := ByteArray.mk #[if final then u8 0x01 else u8 0x00]
  have hheader : header.size = 1 := by rfl
  have hshift :
      (storedBlock payload final).extract 1 3 =
        (u16le len ++ u16le (0xFFFF - len) ++ payload).extract 0 2 := by
    simpa [storedBlock, header, hheader, ByteArray.append_assoc] using
      (ByteArray.extract_append_size_add
        (a := header)
        (b := u16le len ++ u16le (0xFFFF - len) ++ payload)
        (i := 0) (j := 2))
  have hprefix :
      (u16le len ++ u16le (0xFFFF - len) ++ payload).extract 0 2 = u16le len := by
    have h :=
      (ByteArray.extract_append_eq_left
        (a := u16le len)
        (b := u16le (0xFFFF - len) ++ payload)
        (i := (u16le len).size) rfl)
    simpa [u16le_size] using h
  simp [hshift, hprefix, len]

-- The NLEN field of a stored block is the ones-complement of LEN.
lemma storedBlock_extract_nlen (payload : ByteArray) (final : Bool) :
    (storedBlock payload final).extract 3 5 = u16le (0xFFFF - payload.size) := by
  let len := payload.size
  let header : ByteArray := ByteArray.mk #[if final then u8 0x01 else u8 0x00]
  have hheader : header.size = 1 := by rfl
  have hshift :
      (storedBlock payload final).extract 3 5 =
        (u16le len ++ u16le (0xFFFF - len) ++ payload).extract 2 4 := by
    simpa [storedBlock, header, hheader, ByteArray.append_assoc] using
      (ByteArray.extract_append_size_add
        (a := header)
        (b := u16le len ++ u16le (0xFFFF - len) ++ payload)
        (i := 2) (j := 4))
  have hshift' :
      (u16le len ++ u16le (0xFFFF - len) ++ payload).extract 2 4 =
        (u16le (0xFFFF - len) ++ payload).extract 0 2 := by
    simpa [ByteArray.append_assoc] using
      (ByteArray.extract_append_size_add
        (a := u16le len)
        (b := u16le (0xFFFF - len) ++ payload)
        (i := 0) (j := 2))
  have hprefix :
      (u16le (0xFFFF - len) ++ payload).extract 0 2 = u16le (0xFFFF - len) := by
    have h :=
      (ByteArray.extract_append_eq_left
        (a := u16le (0xFFFF - len))
        (b := payload)
        (i := (u16le (0xFFFF - len)).size) rfl)
    simpa [u16le_size] using h
  simp [hshift, hshift', hprefix, len]

-- The payload slice of a stored block recovers the original payload.
lemma storedBlock_extract_payload (payload : ByteArray) (final : Bool) :
    (storedBlock payload final).extract 5 (5 + payload.size) = payload := by
  let len := payload.size
  let header : ByteArray := ByteArray.mk #[if final then u8 0x01 else u8 0x00]
  have hheader : header.size = 1 := by rfl
  let blockPrefix : ByteArray := header ++ u16le len ++ u16le (0xFFFF - len)
  have hprefix : blockPrefix.size = 5 := by
    simp [blockPrefix, ByteArray.size_append, u16le_size, hheader]
  have hprefix' : 5 = blockPrefix.size := hprefix.symm
  have hdef : storedBlock payload final = blockPrefix ++ payload := by
    simp [storedBlock, blockPrefix, len, header, ByteArray.append_assoc]
  have hbase :
      (blockPrefix ++ payload).extract blockPrefix.size (blockPrefix.size + payload.size) =
        payload.extract 0 payload.size :=
    (ByteArray.extract_append_size_add
      (a := blockPrefix)
      (b := payload)
      (i := 0) (j := payload.size))
  calc
    (storedBlock payload final).extract 5 (5 + payload.size) =
        (blockPrefix ++ payload).extract 5 (5 + payload.size) := by
          rw [hdef]
    _ = (blockPrefix ++ payload).extract blockPrefix.size (blockPrefix.size + payload.size) := by
          rw [hprefix']
    _ = payload.extract 0 payload.size := hbase
    _ = payload := by simp

-- The stored-block header has btype = 0.
lemma storedBlock_btype (final : Bool) :
    ((if final then (u8 0x01) else (u8 0x00)) >>> 1) &&& (0x03 : UInt8) = 0 := by
  cases final <;> decide

-- The stored-block header encodes the final bit in the low bit.
lemma storedBlock_bfinal (final : Bool) :
    (if final then (u8 0x01) else (u8 0x00)) &&& (0x01 : UInt8) =
      (if final then (1 : UInt8) else 0) := by
  cases final <;> decide

-- The stored-block final-bit test reduces to the boolean flag.
lemma storedBlock_bfinal_eq (final : Bool) :
    ((if final then (1 : UInt8) else 0) == (1 : UInt8)) = final := by
  cases final <;> decide

-- The first byte of a stored block (even with trailing bytes) encodes the final flag.
lemma storedBlock_get0_append (payload rest : ByteArray) (final : Bool)
    (h : 0 < (storedBlock payload final ++ rest).size) :
    (storedBlock payload final ++ rest).get 0 h = if final then u8 0x01 else u8 0x00 := by
  have h0 : 0 < (storedBlock payload final).size := by
    have : 0 < payload.size + 5 := by omega
    simp [storedBlock_size payload final, this]
  have hget0 :
      (storedBlock payload final ++ rest)[0]'h = (storedBlock payload final)[0]'h0 := by
    have hget := ByteArray.get_append_left (a := storedBlock payload final) (b := rest) (i := 0) h0
    simpa using hget
  have hheader0 :
      (storedBlock payload final)[0]'h0 = if final then u8 0x01 else u8 0x00 := by
    have hheaderPos : 0 < (ByteArray.mk #[if final then u8 0x01 else u8 0x00]).size := by
      simp [ByteArray.size]
    have hget :=
      ByteArray.get_append_left
        (a := ByteArray.mk #[if final then u8 0x01 else u8 0x00])
        (b := u16le payload.size ++ u16le (0xFFFF - payload.size) ++ payload)
        (i := 0) hheaderPos
    have hget' :
        (storedBlock payload final)[0]'h0 =
          (ByteArray.mk #[if final then u8 0x01 else u8 0x00])[0]'hheaderPos := by
      simpa [storedBlock, ByteArray.append_assoc] using hget
    have hhead : (ByteArray.mk #[if final then u8 0x01 else u8 0x00])[0]'hheaderPos =
        if final then u8 0x01 else u8 0x00 := by
      rfl
    simpa [hhead] using hget'
  have hget0' :
      (storedBlock payload final ++ rest)[0]'h = if final then u8 0x01 else u8 0x00 := by
    simpa [hheader0] using hget0
  simpa [byteArray_get_eq_getElem] using hget0'

-- Inflating a stored block recovers its payload and any remaining bytes.
set_option maxHeartbeats 5000000 in
lemma inflateStoredAux_storedBlock (payload rest : ByteArray) (final : Bool)
    (hlen : payload.size ≤ 0xFFFF)
    (hdataPos : 0 < (storedBlock payload final ++ rest).size) :
    inflateStoredAux (storedBlock payload final ++ rest) hdataPos =
      if final then some (payload, rest) else
        if hrest : 0 < rest.size then
          match inflateStoredAux rest hrest with
          | some (tail, rest') => some (payload ++ tail, rest')
          | none => none
        else
          none := by
  let data := storedBlock payload final ++ rest
  have hblockSize : (storedBlock payload final).size = payload.size + 5 :=
    storedBlock_size payload final
  have hdataPos' : 0 < data.size := by
    simpa [data] using hdataPos
  have hlenPos : 1 + 3 < data.size := by
    simp [data, ByteArray.size_append, hblockSize]
    omega
  have hsize1 : 1 ≤ (storedBlock payload final).size := by
    have : 1 ≤ payload.size + 5 := by omega
    simp [hblockSize, this]
  have hsize3 : 3 ≤ (storedBlock payload final).size := by
    have : 3 ≤ payload.size + 5 := by omega
    simp [hblockSize, this]
  have hsize5 : 5 ≤ (storedBlock payload final).size := by
    have : 5 ≤ payload.size + 5 := by omega
    simp [hblockSize, this]
  have hsize5len : 5 + payload.size ≤ (storedBlock payload final).size := by
    simp [hblockSize, Nat.add_comm]
  have hlen_extract :
      data.extract 1 3 = u16le payload.size := by
    have hleft :
        data.extract 1 3 = (storedBlock payload final).extract 1 3 := by
      apply byteArray_extract_append_left (a := storedBlock payload final) (b := rest) (i := 1) (j := 3)
      · exact hsize1
      · exact hsize3
    calc
      data.extract 1 3 = (storedBlock payload final).extract 1 3 := hleft
      _ = u16le payload.size := storedBlock_extract_len payload final
  have hnlen_extract :
      data.extract 3 5 = u16le (0xFFFF - payload.size) := by
    have hleft :
        data.extract 3 5 = (storedBlock payload final).extract 3 5 := by
      apply byteArray_extract_append_left (a := storedBlock payload final) (b := rest) (i := 3) (j := 5)
      · exact hsize3
      · exact hsize5
    calc
      data.extract 3 5 = (storedBlock payload final).extract 3 5 := hleft
      _ = u16le (0xFFFF - payload.size) := storedBlock_extract_nlen payload final
  have hpayload_extract :
      data.extract 5 (5 + payload.size) = payload := by
    have hleft :
        data.extract 5 (5 + payload.size) =
          (storedBlock payload final).extract 5 (5 + payload.size) := by
      apply byteArray_extract_append_left (a := storedBlock payload final) (b := rest)
        (i := 5) (j := 5 + payload.size)
      · exact hsize5
      · exact hsize5len
    calc
      data.extract 5 (5 + payload.size) =
          (storedBlock payload final).extract 5 (5 + payload.size) := hleft
      _ = payload := storedBlock_extract_payload payload final
  have hnext_extract :
      data.extract (5 + payload.size) data.size = rest := by
    have h :=
      (ByteArray.extract_append_size_add
        (a := storedBlock payload final)
        (b := rest)
        (i := 0) (j := rest.size))
    simpa [data, hblockSize, ByteArray.size_append, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  have hlen_read : readU16LE data 1 (by omega) = payload.size := by
    have hlt : payload.size < 2 ^ 16 := by
      have hlt' : (0xFFFF : Nat) < 2 ^ 16 := by decide
      exact lt_of_le_of_lt hlen hlt'
    exact readU16LE_of_extract_eq (bytes := data) (pos := 1) (n := payload.size)
      (h := by omega) hlen_extract hlt
  have hnlen_read : readU16LE data 3 (by omega) = 0xFFFF - payload.size := by
    have hlt : 0xFFFF - payload.size < 2 ^ 16 := by
      have hlt' : (0xFFFF : Nat) < 2 ^ 16 := by decide
      exact lt_of_le_of_lt (Nat.sub_le _ _) hlt'
    exact readU16LE_of_extract_eq (bytes := data) (pos := 3) (n := 0xFFFF - payload.size)
      (h := by omega) hnlen_extract hlt
  have hsum : payload.size + (0xFFFF - payload.size) = 0xFFFF := by
    exact Nat.add_sub_of_le hlen
  have hbad : ¬ 5 + payload.size > data.size := by
    have hle : 5 + payload.size ≤ data.size := by
      simp [data, ByteArray.size_append, hblockSize]
      omega
    exact not_lt_of_ge hle
  have hheader : data.get 0 hdataPos' = if final then u8 0x01 else u8 0x00 := by
    simpa [data] using
      (storedBlock_get0_append (payload := payload) (rest := rest) (final := final) hdataPos')
  have hbtype : (data.get 0 hdataPos' >>> 1 &&& (0x03 : UInt8)) = 0 := by
    simpa [hheader] using storedBlock_btype final
  have hbfinal : (data.get 0 hdataPos' &&& (0x01 : UInt8)) = if final then (1 : UInt8) else 0 := by
    simpa [hheader] using storedBlock_bfinal final
  have hbfinal_eq : (data.get 0 hdataPos' &&& (0x01 : UInt8) = (1 : UInt8)) = final := by
    cases final <;> simp [hbfinal]
  have hpos : 0 < (storedBlock payload final).size + rest.size := by
    simpa [data, ByteArray.size_append] using hdataPos'
  have hlenPos' : 4 < (storedBlock payload final).size + rest.size := by
    simp [hblockSize]
    omega
  have hlenPos1 : 1 + 1 < (storedBlock payload final ++ rest).size := by
    simp [ByteArray.size_append, hblockSize]
    omega
  have hlenPos3 : 3 + 1 < (storedBlock payload final ++ rest).size := by
    simp [ByteArray.size_append, hblockSize]
    omega
  have hlen_read' :
      readU16LE (storedBlock payload final ++ rest) 1 hlenPos1 = payload.size := by
    have hlen_read'' :
        readU16LE (storedBlock payload final ++ rest) 1 (by omega) = payload.size := by
      simpa [data] using hlen_read
    simpa [readU16LE_proof_irrel] using hlen_read''
  have hnlen_read' :
      readU16LE (storedBlock payload final ++ rest) 3 hlenPos3 = 0xFFFF - payload.size := by
    have hnlen_read'' :
        readU16LE (storedBlock payload final ++ rest) 3 (by omega) = 0xFFFF - payload.size := by
      simpa [data] using hnlen_read
    simpa [readU16LE_proof_irrel] using hnlen_read''
  have hsum' :
      readU16LE (storedBlock payload final ++ rest) 1 hlenPos1 +
        readU16LE (storedBlock payload final ++ rest) 3 hlenPos3 = 0xFFFF := by
    simpa [hlen_read', hnlen_read'] using hsum
  have hbad' :
      ¬ 5 + readU16LE (storedBlock payload final ++ rest) 1 hlenPos1 >
        (storedBlock payload final).size + rest.size := by
    simpa [data, ByteArray.size_append, hlen_read', readU16LE_proof_irrel] using hbad
  have hpayload_extract' :
      (storedBlock payload final ++ rest).extract 5
          (5 + readU16LE (storedBlock payload final ++ rest) 1 hlenPos1) = payload := by
    simpa [data, hlen_read', readU16LE_proof_irrel] using hpayload_extract
  have hnext_extract' :
      (storedBlock payload final ++ rest).extract
          (5 + readU16LE (storedBlock payload final ++ rest) 1 hlenPos1)
          ((storedBlock payload final).size + rest.size) = rest := by
    simpa [data, ByteArray.size_append, hlen_read', readU16LE_proof_irrel] using hnext_extract
  have hnot_lt : ¬ (storedBlock payload final).size + rest.size < 5 + payload.size := by
    simp [hblockSize]
    omega
  have hpayload_extract'' :
      (storedBlock payload final ++ rest).extract 5 (5 + payload.size) = payload := by
    simpa [data] using hpayload_extract
  have hnext_extract'' :
      (storedBlock payload final ++ rest).extract (5 + payload.size)
          ((storedBlock payload final).size + rest.size) = rest := by
    simpa [data, ByteArray.size_append] using hnext_extract
  rw [inflateStoredAux.eq_1]
  simp [hlenPos', hbtype, hbfinal_eq, hsum, hnot_lt, hpayload_extract'',
    hnext_extract'', hlen_read', hnlen_read', data]
  by_cases hfinal : final = true
  · simp [hfinal]
  · by_cases hrest : 0 < rest.size
    · have hblockSizeFalse : (storedBlock payload false).size = payload.size + 5 := by
        simpa using (storedBlock_size payload false)
      have hnext : 5 + payload.size < (storedBlock payload false).size + rest.size := by
        have hlt : 5 + payload.size < payload.size + 5 + rest.size := by
          omega
        simpa [hblockSizeFalse, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hlt
      cases h : inflateStoredAux rest hrest <;> simp [hfinal, hrest, hnext, Option.bind, h]
    · have hblockSizeFalse : (storedBlock payload false).size = payload.size + 5 := by
        simpa using (storedBlock_size payload false)
      have hrest0 : rest.size = 0 := Nat.eq_zero_of_not_pos hrest
      have hnext : ¬ 5 + payload.size < (storedBlock payload false).size + rest.size := by
        simp [hblockSizeFalse, hrest0, Nat.add_comm, Nat.add_left_comm]
      simp [hfinal, hrest, hnext]

-- Inflating the stored deflate stream yields the original bytes and no remainder.
lemma inflateStoredAux_deflateStored (raw : ByteArray) :
    inflateStoredAux (deflateStored raw) (deflateStored_pos raw) =
      some (raw, ByteArray.empty) := by
  classical
  refine Nat.strongRecOn (motive := fun n =>
    ∀ raw, raw.size = n →
      inflateStoredAux (deflateStored raw) (deflateStored_pos raw) =
        some (raw, ByteArray.empty))
    raw.size ?_ raw rfl
  intro n ih raw hsize
  subst hsize
  by_cases hzero : raw.size = 0
  · have hraw : raw = ByteArray.empty := (ByteArray.size_eq_zero_iff).1 hzero
    have hdef : deflateStored raw = storedBlock ByteArray.empty true := by
      rw [deflateStored.eq_1]
      simp [hraw]
    have haux :
        inflateStoredAux (storedBlock ByteArray.empty true)
            (by simpa [hdef] using deflateStored_pos raw) =
          some (ByteArray.empty, ByteArray.empty) := by
      simpa using
        (inflateStoredAux_storedBlock (payload := ByteArray.empty) (rest := ByteArray.empty)
          (final := true) (by decide) (hdataPos := by
            simpa [hdef] using deflateStored_pos raw))
    have hdone :
        inflateStoredAux (deflateStored raw) (deflateStored_pos raw) =
          some (ByteArray.empty, ByteArray.empty) := by
      calc
        inflateStoredAux (deflateStored raw) (deflateStored_pos raw) =
            inflateStoredAux (storedBlock ByteArray.empty true)
              (by simpa [hdef] using deflateStored_pos raw) := by
              exact
                (inflateStoredAux_congr (data1 := deflateStored raw)
                  (data2 := storedBlock ByteArray.empty true) hdef (deflateStored_pos raw))
        _ = some (ByteArray.empty, ByteArray.empty) := haux
    simpa [hraw] using hdone
  · let blockLen := if raw.size > 65535 then 65535 else raw.size
    let final := blockLen == raw.size
    let payload := raw.extract 0 blockLen
    let restRaw := raw.extract blockLen raw.size
    let block := storedBlock payload final
    have hblockLen_le : blockLen ≤ raw.size := by
      by_cases hlarge : raw.size > 65535
      · have : (65535 : Nat) ≤ raw.size := Nat.le_of_lt hlarge
        simpa [blockLen, hlarge] using this
      · simp [blockLen, hlarge]
    have hpayload_size : payload.size = blockLen := by
      simp [payload, ByteArray.size_extract, Nat.min_eq_left hblockLen_le]
    have hpayload_le : payload.size ≤ 65535 := by
      by_cases hlarge : raw.size > 65535
      · have hlen : blockLen = 65535 := by simp [blockLen, hlarge]
        simp [hpayload_size, hlen]
      · have hle : raw.size ≤ 65535 := Nat.le_of_not_lt hlarge
        have hlen : blockLen = raw.size := by simp [blockLen, hlarge]
        simpa [hpayload_size, hlen] using hle
    by_cases hlarge : raw.size > 65535
    · have hfinal : final = false := by
        have hlen : blockLen = 65535 := by simp [blockLen, hlarge]
        have hneq : (65535 : Nat) ≠ raw.size := by
          exact (ne_comm).mp (ne_of_gt hlarge)
        simp [final, hlen, hneq]
      have hneq : (65535 : Nat) ≠ raw.size := by
        exact (ne_comm).mp (ne_of_gt hlarge)
      have hbeq : (65535 == raw.size) = false := by
        exact beq_false_of_ne hneq
      have hdef :
          deflateStored raw = block ++ deflateStored restRaw := by
        rw [deflateStored.eq_1]
        simp [hzero, blockLen, hlarge, final, hfinal, block, payload, restRaw, hbeq]
      have hrest_size : restRaw.size = raw.size - blockLen := by
        simp [restRaw, ByteArray.size_extract]
      have hrest_lt : restRaw.size < raw.size := by
        have hpos : 0 < blockLen := by
          simp [blockLen, hlarge]
        have hlt : raw.size - blockLen < raw.size := Nat.sub_lt_self hpos hblockLen_le
        simpa [hrest_size] using hlt
      have ih' :
          inflateStoredAux (deflateStored restRaw) (deflateStored_pos restRaw) =
            some (restRaw, ByteArray.empty) :=
        ih restRaw.size hrest_lt restRaw rfl
      have haux :=
        inflateStoredAux_storedBlock (payload := payload) (rest := deflateStored restRaw)
          (final := false) hpayload_le (hdataPos := by
            simp [ByteArray.size_append, storedBlock_size]; omega)
      have hsplit : payload ++ restRaw = raw := by
        simp [payload, restRaw, byteArray_extract_split (a := raw) (n := blockLen) hblockLen_le]
      have hdef' : deflateStored raw = storedBlock payload false ++ deflateStored restRaw := by
        simpa [block, hfinal] using hdef
      calc
        inflateStoredAux (deflateStored raw) (deflateStored_pos raw)
            = inflateStoredAux (storedBlock payload false ++ deflateStored restRaw)
                (by simpa [hdef'] using deflateStored_pos raw) := by
                exact
                  (inflateStoredAux_congr (data1 := deflateStored raw)
                    (data2 := storedBlock payload false ++ deflateStored restRaw) hdef'
                    (deflateStored_pos raw))
        _ = some (payload ++ restRaw, ByteArray.empty) := by
              simp [haux, ih', deflateStored_pos restRaw]
        _ = some (raw, ByteArray.empty) := by
              simp [hsplit]
    · have hfinal : final = true := by
        have hlen : blockLen = raw.size := by simp [blockLen, hlarge]
        simp [final, hlen]
      have hdef : deflateStored raw = block := by
        rw [deflateStored.eq_1]
        simp [hzero, blockLen, hlarge, final, hfinal, block, payload]
      have hpayload_eq : payload = raw := by
        have hlen : blockLen = raw.size := by simp [blockLen, hlarge]
        simp [payload, hlen, ByteArray.extract_zero_size]
      have hdef' : deflateStored raw = storedBlock payload true := by
        simpa [block, hfinal] using hdef
      calc
        inflateStoredAux (deflateStored raw) (deflateStored_pos raw)
            = inflateStoredAux (storedBlock payload true)
                (by simpa [hdef'] using deflateStored_pos raw) := by
                exact
                  (inflateStoredAux_congr (data1 := deflateStored raw)
                    (data2 := storedBlock payload true) hdef' (deflateStored_pos raw))
        _ = some (payload, ByteArray.empty) := by
              simpa using (inflateStoredAux_storedBlock (payload := payload) (rest := ByteArray.empty)
                (final := true) hpayload_le (hdataPos := by
                  simpa [hdef] using deflateStored_pos raw))
        _ = some (raw, ByteArray.empty) := by
              simp [hpayload_eq]

-- Inflating a deflateStored stream yields the original bytes.
lemma inflateStored_deflateStored (raw : ByteArray) :
    inflateStored (deflateStored raw) = some raw := by
  have haux := inflateStoredAux_deflateStored raw
  simp [inflateStored, haux, deflateStored_pos raw]

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

-- Zlib stored-compression output has at least the 2-byte header and 4-byte Adler32.
lemma zlibCompressStored_size_ge (raw : ByteArray) :
    6 ≤ (zlibCompressStored raw).size := by
  have hsz : (zlibCompressStored raw).size = (deflateStored raw).size + 6 :=
    zlibCompressStored_size raw
  have h6 : 6 ≤ (deflateStored raw).size + 6 := Nat.le_add_left _ _
  rw [hsz]
  exact h6

set_option maxHeartbeats 5000000 in
-- The zlib fixed-compression header bytes are fixed.
lemma zlibCompressFixed_header (raw : ByteArray) :
    (zlibCompressFixed raw).extract 0 2 = ByteArray.mk #[u8 0x78, u8 0x01] := by
  let header : ByteArray := ByteArray.mk #[u8 0x78, u8 0x01]
  let deflated := deflateFixed raw
  let adler := u32be (adler32 raw).toNat
  have hsize : header.size = 2 := by decide
  have hprefix :
      (header ++ deflated ++ adler).extract 0 2 = header.extract 0 2 := by
    apply byteArray_extract_append_prefix (a := header) (b := deflated ++ adler) (n := 2)
    simp [hsize]
  have hheader : header.extract 0 2 = header := by
    rw [← hsize, ByteArray.extract_zero_size]
  simp [zlibCompressFixed, header, deflated, adler, hprefix, hheader]

set_option maxHeartbeats 5000000 in
-- Size of zlib fixed-compression output (header + deflate + adler32).
lemma zlibCompressFixed_size (raw : ByteArray) :
    (zlibCompressFixed raw).size = (deflateFixed raw).size + 6 := by
  unfold zlibCompressFixed
  have hheader : (ByteArray.mk #[u8 0x78, u8 0x01]).size = 2 := by decide
  simp [ByteArray.size_append, u32be_size, hheader]
  omega

set_option maxHeartbeats 5000000 in
-- Zlib fixed-compression output has at least the 2-byte header and 4-byte Adler32.
lemma zlibCompressFixed_size_ge (raw : ByteArray) :
    6 ≤ (zlibCompressFixed raw).size := by
  have hsz : (zlibCompressFixed raw).size = (deflateFixed raw).size + 6 :=
    zlibCompressFixed_size raw
  have h6 : 6 ≤ (deflateFixed raw).size + 6 := Nat.le_add_left _ _
  rw [hsz]
  exact h6

set_option maxHeartbeats 5000000 in
-- Zlib header bytes in fixed-compression output match the expected constants.
lemma zlibCompressFixed_cmf_flg (raw : ByteArray) :
    let bytes := zlibCompressFixed raw
    let h0 : 0 < bytes.size := by
      exact lt_of_lt_of_le (by decide : 0 < 6) (zlibCompressFixed_size_ge raw)
    let h1 : 1 < bytes.size := by
      exact lt_of_lt_of_le (by decide : 1 < 6) (zlibCompressFixed_size_ge raw)
    bytes[0]'h0 = u8 0x78 ∧ bytes[1]'h1 = u8 0x01 := by
  let bytes := zlibCompressFixed raw
  let header : ByteArray := ByteArray.mk #[u8 0x78, u8 0x01]
  let deflated := deflateFixed raw
  let adler := u32be (adler32 raw).toNat
  have h0h : 0 < header.size := by decide
  have h1h : 1 < header.size := by decide
  have h0 : 0 < bytes.size := by
    exact lt_of_lt_of_le (by decide : 0 < 6) (zlibCompressFixed_size_ge raw)
  have h1 : 1 < bytes.size := by
    exact lt_of_lt_of_le (by decide : 1 < 6) (zlibCompressFixed_size_ge raw)
  have hle : header.size ≤ (header ++ deflated ++ adler).size := by
    simp [ByteArray.size_append]
    omega
  have h0' : 0 < (header ++ deflated ++ adler).size := lt_of_lt_of_le h0h hle
  have h1' : 1 < (header ++ deflated ++ adler).size := lt_of_lt_of_le h1h hle
  have hget0 :
      (header ++ deflated ++ adler)[0]'h0' = header[0]'h0h := by
    have hget := ByteArray.get_append_left (a := header) (b := deflated ++ adler) (i := 0) h0h
    simpa [ByteArray.append_assoc] using hget
  have hget1 :
      (header ++ deflated ++ adler)[1]'h1' = header[1]'h1h := by
    have hget := ByteArray.get_append_left (a := header) (b := deflated ++ adler) (i := 1) h1h
    simpa [ByteArray.append_assoc] using hget
  have hheader0 : header[0]'h0h = u8 0x78 := by
    rfl
  have hheader1 : header[1]'h1h = u8 0x01 := by
    rfl
  have hget0' : bytes[0]'h0 = u8 0x78 := by
    simpa [bytes, zlibCompressFixed, hget0, hheader0]
  have hget1' : bytes[1]'h1 = u8 0x01 := by
    simpa [bytes, zlibCompressFixed, hget1, hheader1]
  exact ⟨hget0', hget1'⟩

-- Extracting the deflated payload from zlib fixed-compression output.
lemma zlibCompressFixed_extract_deflated (raw : ByteArray) :
    (zlibCompressFixed raw).extract 2 ((zlibCompressFixed raw).size - 4) = deflateFixed raw := by
  let header : ByteArray := ByteArray.mk #[u8 0x78, u8 0x01]
  let deflated := deflateFixed raw
  let adler := u32be (adler32 raw).toNat
  have hheader : header.size = 2 := by decide
  have hadler : adler.size = 4 := by
    simpa using (u32be_size (adler32 raw).toNat)
  have hsize'' : header.size + deflated.size + adler.size - 4 = deflated.size + 2 := by
    simp [hheader, hadler]
    omega
  calc
    (zlibCompressFixed raw).extract 2 ((zlibCompressFixed raw).size - 4)
        = (header ++ deflated ++ adler).extract 2 (header.size + deflated.size + adler.size - 4) := by
            simp [zlibCompressFixed, header, deflated, adler, ByteArray.size_append, hheader, hadler]
    _ = (header ++ deflated ++ adler).extract 2 (deflated.size + 2) := by
          simp [hsize'']
    _ = (deflated ++ adler).extract 0 deflated.size := by
          have h :=
            (ByteArray.extract_append_size_add
              (a := header) (b := deflated ++ adler) (i := 0) (j := deflated.size))
          simpa [hheader, ByteArray.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
    _ = deflated := by
          have hprefix :
              (deflated ++ adler).extract 0 deflated.size = deflated.extract 0 deflated.size := by
            exact byteArray_extract_append_prefix (a := deflated) (b := adler) (n := deflated.size) (by exact le_rfl)
          simp [hprefix, ByteArray.extract_zero_size]

-- Extracting the Adler32 trailer from zlib fixed-compression output.
lemma zlibCompressFixed_extract_adler (raw : ByteArray) :
    (zlibCompressFixed raw).extract ((zlibCompressFixed raw).size - 4)
        ((zlibCompressFixed raw).size - 4 + 4) = u32be (adler32 raw).toNat := by
  let header : ByteArray := ByteArray.mk #[u8 0x78, u8 0x01]
  let deflated := deflateFixed raw
  let adler := u32be (adler32 raw).toNat
  have hheader : header.size = 2 := by decide
  have hadler : adler.size = 4 := by
    simpa using (u32be_size (adler32 raw).toNat)
  have hsize'' : header.size + deflated.size + adler.size - 4 = deflated.size + 2 := by
    simp [hheader, hadler]
    omega
  have hprefix : (header ++ deflated).size = deflated.size + 2 := by
    simp [ByteArray.size_append, hheader, Nat.add_comm]
  calc
    (zlibCompressFixed raw).extract ((zlibCompressFixed raw).size - 4)
        ((zlibCompressFixed raw).size - 4 + 4)
        = (header ++ deflated ++ adler).extract (header.size + deflated.size + adler.size - 4)
            (header.size + deflated.size + adler.size - 4 + 4) := by
              simp [zlibCompressFixed, header, deflated, adler, ByteArray.size_append, hheader, hadler]
    _ = (header ++ deflated ++ adler).extract (deflated.size + 2) (deflated.size + 2 + 4) := by
          simp [hsize'']
    _ = adler.extract 0 adler.size := by
          have h :=
            (ByteArray.extract_append_size_add
              (a := header ++ deflated) (b := adler) (i := 0) (j := adler.size))
          simpa [hprefix, hadler, ByteArray.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
    _ = adler := by
          simp [ByteArray.extract_zero_size]

-- Stored-only zlib decompressor rejects fixed-Huffman streams.
lemma zlibDecompressStored_zlibCompressFixed_none (raw : ByteArray)
    (hsize : 2 ≤ (zlibCompressFixed raw).size) :
    zlibDecompressStored (zlibCompressFixed raw) hsize = none := by
  let bytes := zlibCompressFixed raw
  have hmin : 6 ≤ bytes.size := zlibCompressFixed_size_ge raw
  have h0 : 0 < bytes.size := lt_of_lt_of_le (by decide : 0 < 6) hmin
  have h1 : 1 < bytes.size := lt_of_lt_of_le (by decide : 1 < 6) hmin
  have h0' : 0 < bytes.size := lt_of_lt_of_le (by decide : 0 < 6) hmin
  have h1' : 1 < bytes.size := lt_of_lt_of_le (by decide : 1 < 6) hmin
  have hcmf' : bytes[0]'h0' = u8 0x78 := (zlibCompressFixed_cmf_flg raw).1
  have hflg' : bytes[1]'h1' = u8 0x01 := (zlibCompressFixed_cmf_flg raw).2
  have hcmf : bytes.get 0 h0 = u8 0x78 := by
    have htmp : bytes.get 0 h0' = u8 0x78 := by
      simpa [byteArray_get_eq_getElem] using hcmf'
    simpa using htmp
  have hflg : bytes.get 1 h1 = u8 0x01 := by
    have htmp : bytes.get 1 h1' = u8 0x01 := by
      simpa [byteArray_get_eq_getElem] using hflg'
    simpa using htmp
  have hdeflated : bytes.extract 2 (bytes.size - 4) = deflateFixed raw := by
    simpa [bytes] using zlibCompressFixed_extract_deflated raw
  have hinflate : inflateStored (bytes.extract 2 (bytes.size - 4)) = none := by
    simpa [hdeflated] using inflateStored_deflateFixed_none raw
  have hmod : ((u8 0x78).toNat <<< 8 + (u8 0x01).toNat) % 31 = 0 := by
    decide
  have hbtype : (u8 0x78 &&& (0x0F : UInt8)) = 8 := by
    decide
  have hflg0 : (u8 0x01 &&& (0x20 : UInt8)) = 0 := by
    decide
  unfold zlibDecompressStored
  simp [bytes, hcmf, hflg, hmin, hinflate, hmod, hbtype, hflg0]

-- Zlib header bytes in stored-compression output match the expected constants.
lemma zlibCompressStored_cmf_flg (raw : ByteArray) :
    let bytes := zlibCompressStored raw
    let h0 : 0 < bytes.size := by
      exact lt_of_lt_of_le (by decide : 0 < 6) (zlibCompressStored_size_ge raw)
    let h1 : 1 < bytes.size := by
      exact lt_of_lt_of_le (by decide : 1 < 6) (zlibCompressStored_size_ge raw)
    bytes[0]'h0 = u8 0x78 ∧ bytes[1]'h1 = u8 0x01 := by
  let bytes := zlibCompressStored raw
  let header : ByteArray := ByteArray.mk #[u8 0x78, u8 0x01]
  let deflated := deflateStored raw
  let adler := u32be (adler32 raw).toNat
  have h0h : 0 < header.size := by decide
  have h1h : 1 < header.size := by decide
  have h0 : 0 < bytes.size := by
    exact lt_of_lt_of_le (by decide : 0 < 6) (zlibCompressStored_size_ge raw)
  have h1 : 1 < bytes.size := by
    exact lt_of_lt_of_le (by decide : 1 < 6) (zlibCompressStored_size_ge raw)
  have hle : header.size ≤ (header ++ deflated ++ adler).size := by
    simp [ByteArray.size_append]
    omega
  have h0' : 0 < (header ++ deflated ++ adler).size := lt_of_lt_of_le h0h hle
  have h1' : 1 < (header ++ deflated ++ adler).size := lt_of_lt_of_le h1h hle
  have hget0 :
      (header ++ deflated ++ adler)[0]'h0' = header[0]'h0h := by
    have hget := ByteArray.get_append_left (a := header) (b := deflated ++ adler) (i := 0) h0h
    simpa [ByteArray.append_assoc] using hget
  have hget1 :
      (header ++ deflated ++ adler)[1]'h1' = header[1]'h1h := by
    have hget := ByteArray.get_append_left (a := header) (b := deflated ++ adler) (i := 1) h1h
    simpa [ByteArray.append_assoc] using hget
  have hheader0 : header[0]'h0h = u8 0x78 := by
    rfl
  have hheader1 : header[1]'h1h = u8 0x01 := by
    rfl
  have hget0' : bytes[0]'h0 = u8 0x78 := by
    simpa [bytes, zlibCompressStored, hget0, hheader0]
  have hget1' : bytes[1]'h1 = u8 0x01 := by
    simpa [bytes, zlibCompressStored, hget1, hheader1]
  exact ⟨hget0', hget1'⟩

-- Extracting the deflated payload from zlib stored-compression output.
lemma zlibCompressStored_extract_deflated (raw : ByteArray) :
    (zlibCompressStored raw).extract 2 ((zlibCompressStored raw).size - 4) = deflateStored raw := by
  let header : ByteArray := ByteArray.mk #[u8 0x78, u8 0x01]
  let deflated := deflateStored raw
  let adler := u32be (adler32 raw).toNat
  have hheader : header.size = 2 := by decide
  have hadler : adler.size = 4 := by
    simpa using (u32be_size (adler32 raw).toNat)
  have hsize'' : header.size + deflated.size + adler.size - 4 = deflated.size + 2 := by
    simp [hheader, hadler]
    omega
  calc
    (zlibCompressStored raw).extract 2 ((zlibCompressStored raw).size - 4)
        = (header ++ deflated ++ adler).extract 2 (header.size + deflated.size + adler.size - 4) := by
            simp [zlibCompressStored, header, deflated, adler, ByteArray.size_append, hheader, hadler]
    _ = (header ++ deflated ++ adler).extract 2 (deflated.size + 2) := by
          simp [hsize'']
    _ = (deflated ++ adler).extract 0 deflated.size := by
          have h :=
            (ByteArray.extract_append_size_add
              (a := header) (b := deflated ++ adler) (i := 0) (j := deflated.size))
          simpa [hheader, ByteArray.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
    _ = deflated := by
          have hprefix :
              (deflated ++ adler).extract 0 deflated.size = deflated.extract 0 deflated.size := by
            exact byteArray_extract_append_prefix (a := deflated) (b := adler) (n := deflated.size) (by exact le_rfl)
          simp [hprefix, ByteArray.extract_zero_size]

-- Extracting the Adler32 trailer from zlib stored-compression output.
lemma zlibCompressStored_extract_adler (raw : ByteArray) :
    (zlibCompressStored raw).extract ((zlibCompressStored raw).size - 4)
        ((zlibCompressStored raw).size - 4 + 4) = u32be (adler32 raw).toNat := by
  let header : ByteArray := ByteArray.mk #[u8 0x78, u8 0x01]
  let deflated := deflateStored raw
  let adler := u32be (adler32 raw).toNat
  have hheader : header.size = 2 := by decide
  have hadler : adler.size = 4 := by
    simpa using (u32be_size (adler32 raw).toNat)
  have hsize'' : header.size + deflated.size + adler.size - 4 = deflated.size + 2 := by
    simp [hheader, hadler]
    omega
  have hprefix : (header ++ deflated).size = deflated.size + 2 := by
    simp [ByteArray.size_append, hheader, Nat.add_comm]
  calc
    (zlibCompressStored raw).extract ((zlibCompressStored raw).size - 4)
        ((zlibCompressStored raw).size - 4 + 4)
        = (header ++ deflated ++ adler).extract (header.size + deflated.size + adler.size - 4)
            (header.size + deflated.size + adler.size - 4 + 4) := by
              simp [zlibCompressStored, header, deflated, adler, ByteArray.size_append, hheader, hadler]
    _ = (header ++ deflated ++ adler).extract (deflated.size + 2) (deflated.size + 2 + 4) := by
          simp [hsize'']
    _ = adler.extract 0 adler.size := by
          have h :=
            (ByteArray.extract_append_size_add
              (a := header ++ deflated) (b := adler) (i := 0) (j := adler.size))
          simpa [hprefix, hadler, ByteArray.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
    _ = adler := by
          simp [ByteArray.extract_zero_size]

-- Zlib decompression of stored-compression output yields the original bytes.
lemma zlibDecompressStored_zlibCompressStored (raw : ByteArray)
    (hsize : 2 ≤ (zlibCompressStored raw).size) :
    zlibDecompressStored (zlibCompressStored raw) hsize = some raw := by
  let bytes := zlibCompressStored raw
  have hmin : 6 ≤ bytes.size := zlibCompressStored_size_ge raw
  have h0 : 0 < bytes.size := lt_of_lt_of_le (by decide : 0 < 6) hmin
  have h1 : 1 < bytes.size := lt_of_lt_of_le (by decide : 1 < 6) hmin
  have h0' : 0 < bytes.size := lt_of_lt_of_le (by decide : 0 < 6) hmin
  have h1' : 1 < bytes.size := lt_of_lt_of_le (by decide : 1 < 6) hmin
  have hcmf' : bytes[0]'h0' = u8 0x78 := (zlibCompressStored_cmf_flg raw).1
  have hflg' : bytes[1]'h1' = u8 0x01 := (zlibCompressStored_cmf_flg raw).2
  have hcmf : bytes.get 0 h0 = u8 0x78 := by
    have htmp : bytes.get 0 h0' = u8 0x78 := by
      simpa [byteArray_get_eq_getElem] using hcmf'
    simpa using htmp
  have hflg : bytes.get 1 h1 = u8 0x01 := by
    have htmp : bytes.get 1 h1' = u8 0x01 := by
      simpa [byteArray_get_eq_getElem] using hflg'
    simpa using htmp
  have hdeflated : bytes.extract 2 (bytes.size - 4) = deflateStored raw := by
    simpa [bytes] using zlibCompressStored_extract_deflated raw
  have hAdlerPos : bytes.size - 4 + 3 < bytes.size := by
    omega
  have hadler : readU32BE bytes (bytes.size - 4) hAdlerPos = (adler32 raw).toNat := by
    have hextract :
        bytes.extract (bytes.size - 4) (bytes.size - 4 + 4) =
          u32be (adler32 raw).toNat := by
      simpa [bytes] using zlibCompressStored_extract_adler raw
    have hlt : (adler32 raw).toNat < 2 ^ 32 := by
      simpa using (UInt32.toNat_lt (adler32 raw))
    exact readU32BE_of_extract_eq (bytes := bytes) (pos := bytes.size - 4)
      (n := (adler32 raw).toNat) (h := hAdlerPos) hextract hlt
  have hinflate : inflateStored (bytes.extract 2 (bytes.size - 4)) = some raw := by
    simpa [hdeflated] using inflateStored_deflateStored raw
  have hmod : ((u8 0x78).toNat <<< 8 + (u8 0x01).toNat) % 31 = 0 := by
    decide
  have hbtype : (u8 0x78 &&& (0x0F : UInt8)) = 8 := by
    decide
  have hflg0 : (u8 0x01 &&& (0x20 : UInt8)) = 0 := by
    decide
  -- Evaluate the decompressor on the stored-compression stream.
  unfold zlibDecompressStored
  simp [bytes, hcmf, hflg, hmin, hinflate, hadler, hmod, hbtype, hflg0]

set_option maxHeartbeats 6000000 in
-- Zlib decompression of fixed-compression output yields the original bytes.
lemma zlibDecompress_zlibCompressFixed (raw : ByteArray)
    (hsize : 2 ≤ (zlibCompressFixed raw).size) :
    zlibDecompress (zlibCompressFixed raw) hsize = some raw := by
  classical
  let bytes := zlibCompressFixed raw
  have hmin : 6 ≤ bytes.size := zlibCompressFixed_size_ge raw
  have h0 : 0 < bytes.size := lt_of_lt_of_le (by decide : 0 < 6) hmin
  have h1 : 1 < bytes.size := lt_of_lt_of_le (by decide : 1 < 6) hmin
  have h0' : 0 < bytes.size := h0
  have h1' : 1 < bytes.size := h1
  have hcmf' : bytes[0]'h0' = u8 0x78 := (zlibCompressFixed_cmf_flg raw).1
  have hflg' : bytes[1]'h1' = u8 0x01 := (zlibCompressFixed_cmf_flg raw).2
  have hcmf : bytes.get 0 h0 = u8 0x78 := by
    have htmp : bytes.get 0 h0' = u8 0x78 := by
      simpa [byteArray_get_eq_getElem] using hcmf'
    simpa using htmp
  have hflg : bytes.get 1 h1 = u8 0x01 := by
    have htmp : bytes.get 1 h1' = u8 0x01 := by
      simpa [byteArray_get_eq_getElem] using hflg'
    simpa using htmp
  have hdeflated : bytes.extract 2 (bytes.size - 4) = deflateFixed raw := by
    simpa [bytes] using zlibCompressFixed_extract_deflated raw
  have hAdlerPos : bytes.size - 4 + 3 < bytes.size := by omega
  have hadler : readU32BE bytes (bytes.size - 4) hAdlerPos = (adler32 raw).toNat := by
    have hextract :
        bytes.extract (bytes.size - 4) (bytes.size - 4 + 4) =
          u32be (adler32 raw).toNat := by
      simpa [bytes] using zlibCompressFixed_extract_adler raw
    have hlt : (adler32 raw).toNat < 2 ^ 32 := by
      simpa using (UInt32.toNat_lt (adler32 raw))
    exact readU32BE_of_extract_eq (bytes := bytes) (pos := bytes.size - 4)
      (n := (adler32 raw).toNat) (h := hAdlerPos) hextract hlt
  have hmod : ((u8 0x78).toNat <<< 8 + (u8 0x01).toNat) % 31 = 0 := by
    decide
  have hbtype : (u8 0x78 &&& (0x0F : UInt8)) = 8 := by
    decide
  have hflg0 : (u8 0x01 &&& (0x20 : UInt8)) = 0 := by
    decide
  -- prepare the fixed literal bitstream decoder
  let hdr0 := BitWriter.empty
  let hdrBfinal := hdr0.writeBits 1 1
  let hdrHeader := hdrBfinal.writeBits 1 2
  let payloadBits := fixedLitBitsEob raw.data 0
  have hdeflateBits :
      deflateFixed raw = (BitWriter.writeBits hdrHeader payloadBits.1 payloadBits.2).flush := by
    simpa using deflateFixed_eq_writeBits raw
  have hdecode :
      decodeFixedLiteralBlock
          (BitWriter.readerAt hdrHeader (deflateFixed raw)
            (by
              -- `hdrHeader` is a prefix of the deflated stream
              simpa [hdeflateBits] using
                (flush_size_writeBits_le (bw := hdrHeader) (bits := payloadBits.1) (len := payloadBits.2)))
            (bitPos_lt_8_writeBits hdrBfinal 1 2 (bitPos_lt_8_writeBits hdr0 1 1 (by decide))))
          ByteArray.empty =
        some (BitWriter.readerAt (BitWriter.writeBits hdrHeader payloadBits.1 payloadBits.2) (deflateFixed raw)
          (by
            simp [hdeflateBits])
          (bitPos_lt_8_writeBits hdrHeader payloadBits.1 payloadBits.2
            (bitPos_lt_8_writeBits hdrBfinal 1 2 (bitPos_lt_8_writeBits hdr0 1 1 (by decide)))),
          raw) := by
    have hcur0 : hdr0.curClearAbove := curClearAbove_empty
    have hcur1 : hdrBfinal.curClearAbove := curClearAbove_writeBits hdr0 1 1 (by decide) hcur0
    have hcur2 : hdrHeader.curClearAbove := curClearAbove_writeBits hdrBfinal 1 2 (by decide) hcur1
    have hbits := decodeFixedLiteralBlock_fixedLitBitsEob (data := raw.data) (i := 0)
      (bw := hdrHeader) (out := ByteArray.empty)
      (hbit := bitPos_lt_8_writeBits hdrBfinal 1 2 (bitPos_lt_8_writeBits hdr0 1 1 (by decide)))
      (hcur := hcur2)
    -- rewrite the output ByteArray
    have hraw : byteArrayFromArray raw.data 0 ByteArray.empty = raw := by
      simpa using byteArrayFromArray_empty (data := raw.data)
    simpa [payloadBits, hdeflateBits, hraw] using hbits
  -- Collapse the header bits into one write.
  let streamBits := 3 ||| (payloadBits.1 <<< 3)
  let streamLen := 3 + payloadBits.2
  let streamWriter := BitWriter.writeBits hdr0 streamBits streamLen
  have hbw2 : hdrHeader = BitWriter.writeBits hdr0 3 3 := by
    have hbits : (1 : Nat) < 2 ^ 1 := by decide
    have hconcat := writeBits_concat hdr0 1 1 1 2 hbits
    have h' : BitWriter.writeBits hdr0 3 3 = hdrHeader := by
      simpa [hdrBfinal, hdrHeader] using hconcat
    simpa using h'.symm
  have hdeflateTotal : deflateFixed raw = streamWriter.flush := by
    have hbits : 3 < 2 ^ 3 := by decide
    have hconcat := writeBits_concat hdr0 3 payloadBits.1 3 payloadBits.2 hbits
    calc
      deflateFixed raw = (BitWriter.writeBits hdrHeader payloadBits.1 payloadBits.2).flush := hdeflateBits
      _ = (BitWriter.writeBits (BitWriter.writeBits hdr0 3 3) payloadBits.1 payloadBits.2).flush := by
            simp [hbw2]
      _ = streamWriter.flush := by
            simpa [streamWriter, streamBits, streamLen] using (congrArg BitWriter.flush hconcat).symm
  have hmod3 : streamBits % 2 ^ 3 = 3 := by
    have h := mod_two_pow_or_shift (a := 3) (b := payloadBits.1) (k := 3) (len := 3) (by decide)
    simpa [streamBits] using h
  have hprefix : BitWriter.writeBits hdr0 streamBits 3 = hdrHeader := by
    have hbw2' : BitWriter.writeBits hdr0 3 3 = hdrHeader := by
      simpa using hbw2.symm
    calc
      BitWriter.writeBits hdr0 streamBits 3 =
          BitWriter.writeBits hdr0 (streamBits % 2 ^ 3) 3 := by
            simpa using (writeBits_mod hdr0 streamBits 3)
      _ = BitWriter.writeBits hdr0 3 3 := by
            simp [hmod3]
      _ = hdrHeader := hbw2'
  -- Reader at the start of the deflated stream.
  let streamReader0 : BitReader := {
    data := streamWriter.flush
    bytePos := 0
    bitPos := 0
    hpos := by exact Nat.zero_le _
    hend := by intro _; rfl
    hbit := by decide
  }
  have hbw0 : hdr0.bitPos = 0 := rfl
  have hbw0out : hdr0.out.size = 0 := by
    simp [hdr0, BitWriter.empty]
  have hbr0 :
      streamReader0 = BitWriter.readerAt hdr0 streamWriter.flush
        (flush_size_writeBits_le hdr0 streamBits streamLen) (by decide) := by
    apply BitReader.ext <;> simp [streamReader0, BitWriter.readerAt, hdr0, hbw0, hbw0out]
  let streamReaderHeader := BitWriter.readerAt hdrHeader streamWriter.flush
      (by
        simpa [hprefix] using
          (flush_size_writeBits_prefix (bw := hdr0) (bits := streamBits) (k := 3)
            (len := streamLen) (hk := by omega)))
      (by
        simpa [hprefix] using
          (bitPos_lt_8_writeBits hdr0 streamBits 3 (by decide)))
  have hread0_at :
      (BitWriter.readerAt hdr0 streamWriter.flush
        (flush_size_writeBits_le hdr0 streamBits streamLen) (by decide)).bitIndex + 3 ≤
        (BitWriter.readerAt hdr0 streamWriter.flush
          (flush_size_writeBits_le hdr0 streamBits streamLen) (by decide)).data.size * 8 := by
    simpa using
      (readerAt_writeBits_bound (bw := hdr0) (bits := streamBits) (len := streamLen) (k := 3)
        (hk := by omega) (hbit := by decide))
  have hread0 : streamReader0.bitIndex + 3 ≤ streamReader0.data.size * 8 := by
    simpa [hbr0] using hread0_at
  have hread3 : streamReader0.readBits 3 hread0 = (3, streamReaderHeader) := by
    have h' :=
      (readBits_readerAt_writeBits_prefix (bw := hdr0) (bits := streamBits) (len := streamLen)
        (k := 3) (hk := by omega) (hbit := by decide) (hcur := curClearAbove_empty)
        (hread := hread0_at))
    dsimp at h'
    have h'br : streamReader0.readBits 3 hread0_at = (3, streamReaderHeader) := by
      -- rewrite with the collapsed header bits and prefix reader
      simpa [hbr0, hmod3, hprefix, streamReaderHeader, hdr0, hbw0] using h'
    have hirrel : streamReader0.readBits 3 hread0 = streamReader0.readBits 3 hread0_at :=
      readBits_proof_irrel (br := streamReader0) (n := 3) hread0 hread0_at
    exact hirrel.trans h'br
  -- Final reader after the fixed literal stream.
  have hflushFinal :
      (BitWriter.writeBits hdrHeader payloadBits.1 payloadBits.2).flush.size ≤ streamWriter.flush.size := by
    have hEq : streamWriter.flush = (BitWriter.writeBits hdrHeader payloadBits.1 payloadBits.2).flush := by
      exact hdeflateTotal.symm.trans hdeflateBits
    simp [hEq]
  let streamReaderFinal := BitWriter.readerAt (BitWriter.writeBits hdrHeader payloadBits.1 payloadBits.2) streamWriter.flush
    hflushFinal
    (bitPos_lt_8_writeBits hdrHeader payloadBits.1 payloadBits.2
      (bitPos_lt_8_writeBits hdrBfinal 1 2 (bitPos_lt_8_writeBits hdr0 1 1 (by decide))))
  -- Evaluate the block decoder once.
  have hloop :
      zlibDecompressLoop streamReader0 ByteArray.empty =
        some (streamReaderFinal, raw) := by
    -- unfold and simplify the fixed-block path
    have hdecode' : decodeFixedLiteralBlock streamReaderHeader ByteArray.empty =
        some (streamReaderFinal, raw) := by
      simpa [streamReaderFinal, hdeflateTotal, streamWriter] using hdecode
    -- Evaluate the loop body (bfinal = 1, btype = 1).
    have hbfinal : (3 % 2) = 1 := by decide
    have hbtype' : ((3 >>> 1) % 4) = 1 := by decide
    have hcond : streamReader0.bitIndex + 3 ≤ streamReader0.data.size * 8 := hread0
    have hread3' : streamReader0.readBits 3 hcond = (3, streamReaderHeader) := by
      simpa using hread3
    simp [zlibDecompressLoop, zlibDecompressLoopFuel, hcond, hread3', hdecode', hbfinal]
  -- Evaluate the decompressor on the fixed-compression stream.
  unfold zlibDecompress
  -- simplify header checks and the deflated slice
  simp [bytes, hcmf, hflg, hmod, hbtype, hflg0, hdeflated, hdeflateTotal, streamWriter]
  -- replace the loop with its computed result
  rw [hloop]
  -- compute the Adler position and value
  have hAlign : streamReaderFinal.alignByte.bytePos = streamWriter.flush.size := by
    -- `streamReaderFinal` reads from the flush itself
    simpa [streamReaderFinal] using
      (readerAt_alignByte_bytePos_eq_data
        (bw := BitWriter.writeBits hdrHeader payloadBits.1 payloadBits.2)
        (data := streamWriter.flush)
        (hflush := hflushFinal)
        (hbit := bitPos_lt_8_writeBits hdrHeader payloadBits.1 payloadBits.2
          (bitPos_lt_8_writeBits hdrBfinal 1 2 (bitPos_lt_8_writeBits hdr0 1 1 (by decide))))
        (hdata := hdeflateTotal.symm.trans hdeflateBits))
  have hsize : bytes.size = streamWriter.flush.size + 6 := by
    -- size = deflate + header + adler
    have hsz := zlibCompressFixed_size raw
    simpa [bytes, hdeflateTotal] using hsz
  have hposEq : streamReaderFinal.alignByte.bytePos + 2 = bytes.size - 4 := by
    -- bytes.size = streamWriter.flush.size + 6
    have : streamWriter.flush.size + 2 = (streamWriter.flush.size + 6) - 4 := by omega
    simpa [hAlign, hsize, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
  have hAdlerPos' : streamReaderFinal.alignByte.bytePos + 2 + 3 < bytes.size := by
    -- rewrite to the canonical Adler position
    simpa [hposEq, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hAdlerPos
  have hread : readU32BE bytes (streamReaderFinal.alignByte.bytePos + 2) hAdlerPos' = (adler32 raw).toNat := by
    simpa [hposEq, readU32BE_proof_irrel] using hadler
  -- close the final Adler check
  simp [hAdlerPos', hread, bytes]

-- Fixed tail bytes in the IHDR payload (bit depth, color type, and flags).
def ihdrTailColor (ct : UInt8) : ByteArray :=
  ByteArray.mk #[u8 8, ct, u8 0, u8 0, u8 0]

@[simp] lemma ihdrTailColor_size (ct : UInt8) : (ihdrTailColor ct).size = 5 := by
  simp [ihdrTailColor, ByteArray.size]

@[simp] lemma ihdrTailColor_get0 (ct : UInt8) : (ihdrTailColor ct).get! 0 = u8 8 := by
  rfl
@[simp] lemma ihdrTailColor_get1 (ct : UInt8) : (ihdrTailColor ct).get! 1 = ct := by
  rfl
@[simp] lemma ihdrTailColor_get2 (ct : UInt8) : (ihdrTailColor ct).get! 2 = u8 0 := by
  rfl
@[simp] lemma ihdrTailColor_get3 (ct : UInt8) : (ihdrTailColor ct).get! 3 = u8 0 := by
  rfl
@[simp] lemma ihdrTailColor_get4 (ct : UInt8) : (ihdrTailColor ct).get! 4 = u8 0 := by
  rfl


-- IHDR payload is always 13 bytes.
lemma ihdr_payload_size (w h : Nat) (ct : UInt8) :
    (u32be w ++ u32be h ++ ihdrTailColor ct).size = 13 := by
  simp [ByteArray.size_append, u32be_size, Nat.add_comm]

-- RGB-compatible IHDR tail (color type 2).
def ihdrTail : ByteArray :=
  ihdrTailColor (u8 2)

-- IHDR payload width slice is the encoded width.
lemma ihdr_payload_extract_width (w h : Nat) (ct : UInt8) :
    (u32be w ++ u32be h ++ ihdrTailColor ct).extract 0 4 =
      u32be w := by
  let tail := ihdrTailColor ct
  let ihdr := u32be w ++ u32be h ++ tail
  ext i hi
  · -- size goal
    have hle : 0 + 4 ≤ ihdr.size := by
      have : ihdr.size = 13 := by
        simpa [ihdr, tail] using ihdr_payload_size w h ct
      omega
    have hsize : (ihdr.extract 0 4).size = 4 := by
      simp [ByteArray.size_extract, Nat.min_eq_left hle]
    simp [ByteArray.size_data, u32be_size]
  · -- element goal
    have hle : 0 + 4 ≤ ihdr.size := by
      have : ihdr.size = 13 := by
        simpa [ihdr, tail] using ihdr_payload_size w h ct
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
lemma ihdr_payload_extract_height (w h : Nat) (ct : UInt8) :
    (u32be w ++ u32be h ++ ihdrTailColor ct).extract 4 8 =
      u32be h := by
  let tail := ihdrTailColor ct
  let ihdr := u32be w ++ u32be h ++ tail
  ext i hi
  · -- size goal
    have hle : 4 + 4 ≤ ihdr.size := by
      have : ihdr.size = 13 := by
        simpa [ihdr, tail] using ihdr_payload_size w h ct
      omega
    have hsize : (ihdr.extract 4 8).size = 4 := by
      simp [ByteArray.size_extract, Nat.min_eq_left hle]
    simp [ByteArray.size_data, u32be_size]
  · -- element goal
    have hle : 4 + 4 ≤ ihdr.size := by
      have : ihdr.size = 13 := by
        simpa [ihdr, tail] using ihdr_payload_size w h ct
      omega
    have hsize : (ihdr.extract 4 8).size = 4 := by
      simp [ByteArray.size_extract, Nat.min_eq_left hle]
    have hi4 : i < 4 := by
      simpa [hsize] using hi
    have hih : i < (u32be h).size := by
      simpa [u32be_size] using hi4
    have hright : ihdr[4 + i]'(by
      have : ihdr.size = 13 := by
        simpa [ihdr, tail] using ihdr_payload_size w h ct
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
          simpa [ihdr, tail] using ihdr_payload_size w h ct
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
          simpa [ihdr, tail] using ihdr_payload_size w h ct
        omega) := by
      simp
    calc
      (ihdr.extract 4 8)[i] = ihdr[4 + i]'(by
        have : ihdr.size = 13 := by
          simpa [ihdr, tail] using ihdr_payload_size w h ct
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
lemma readU32BE_ihdr_width (w h : Nat) (ct : UInt8) (hw : w < 2 ^ 32) :
    readU32BE (u32be w ++ u32be h ++ ihdrTailColor ct) 0 (by
      have : (u32be w ++ u32be h ++ ihdrTailColor ct).size = 13 := by
        simpa using ihdr_payload_size w h ct
      omega) = w := by
  have hpos : 0 + 3 < (u32be w ++ u32be h ++ ihdrTailColor ct).size := by
    have : (u32be w ++ u32be h ++ ihdrTailColor ct).size = 13 := by
      simpa using ihdr_payload_size w h ct
    omega
  have hread :=
    readU32BE_extract (bytes := u32be w ++ u32be h ++ ihdrTailColor ct) (pos := 0) hpos
  have hwidth : (u32be w ++ u32be h ++ ihdrTailColor ct).extract 0 4 = u32be w := by
    simpa using ihdr_payload_extract_width w h ct
  have htotal : (u32be w ++ u32be h ++ ihdrTailColor ct).size = 13 := by
    simpa using ihdr_payload_size w h ct
  have hsize : ((u32be w ++ u32be h ++ ihdrTailColor ct).extract 0 4).size = 4 := by
    simp [ByteArray.size_extract, htotal]
  have hpos' : 0 + 3 < ((u32be w ++ u32be h ++ ihdrTailColor ct).extract 0 4).size := by
    simp [hsize]
  have hread' :
      readU32BE ((u32be w ++ u32be h ++ ihdrTailColor ct).extract 0 4) 0 hpos' = w := by
    simpa [hwidth] using readU32BE_u32be w hw
  simp [hread'] at hread
  exact hread

-- Reading the height from an IHDR payload yields the original height.
lemma readU32BE_ihdr_height (w h : Nat) (ct : UInt8) (hh : h < 2 ^ 32) :
    readU32BE (u32be w ++ u32be h ++ ihdrTailColor ct) 4 (by
      have : (u32be w ++ u32be h ++ ihdrTailColor ct).size = 13 := by
        simpa using ihdr_payload_size w h ct
      omega) = h := by
  have hpos : 4 + 3 < (u32be w ++ u32be h ++ ihdrTailColor ct).size := by
    have : (u32be w ++ u32be h ++ ihdrTailColor ct).size = 13 := by
      simpa using ihdr_payload_size w h ct
    omega
  have hread :=
    readU32BE_extract (bytes := u32be w ++ u32be h ++ ihdrTailColor ct) (pos := 4) hpos
  have hheight : (u32be w ++ u32be h ++ ihdrTailColor ct).extract 4 8 = u32be h := by
    simpa using ihdr_payload_extract_height w h ct
  have htotal : (u32be w ++ u32be h ++ ihdrTailColor ct).size = 13 := by
    simpa using ihdr_payload_size w h ct
  have hsize : ((u32be w ++ u32be h ++ ihdrTailColor ct).extract 4 8).size = 4 := by
    simp [ByteArray.size_extract, htotal]
  have hpos' : 0 + 3 < ((u32be w ++ u32be h ++ ihdrTailColor ct).extract 4 8).size := by
    simp [hsize]
  have hread' :
      readU32BE ((u32be w ++ u32be h ++ ihdrTailColor ct).extract 4 8) 0 hpos' = h := by
    simpa [hheight] using readU32BE_u32be h hh
  simp [hread'] at hread
  exact hread

-- The fixed IHDR tail bytes are present.
lemma ihdr_payload_extract_tail (w h : Nat) (ct : UInt8) :
    (u32be w ++ u32be h ++ ihdrTailColor ct).extract 8 13 = ihdrTailColor ct := by
  have hsize : (u32be w ++ u32be h).size = 8 := by
    simp [ByteArray.size_append, u32be_size]
  have hshift :
      (u32be w ++ u32be h ++ ihdrTailColor ct).extract 8 13 =
        (ihdrTailColor ct).extract 0 5 := by
    simpa [ByteArray.append_assoc, hsize] using
      (ByteArray.extract_append_size_add
        (a := u32be w ++ u32be h)
        (b := ihdrTailColor ct)
        (i := 0) (j := 5))
  have htail : (ihdrTailColor ct).extract 0 5 = ihdrTailColor ct := by
    have hsize : (ihdrTailColor ct).size = 5 := by simp
    simpa [hsize] using (ByteArray.extract_zero_size (b := ihdrTailColor ct))
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
lemma encodeBitmap_signature {px : Type u} [Pixel px] [PngPixel px] (bmp : Bitmap px)
    (hw : bmp.size.width < 2 ^ 32) (hh : bmp.size.height < 2 ^ 32)
    (mode : PngEncodeMode := .stored) :
    (encodeBitmap bmp hw hh mode).extract 0 8 = pngSignature := by
  have hsig : pngSignature.size = 8 := pngSignature_size
  let idat := encodeBitmapIdat (bmp := bmp) (mode := mode)
  simpa [encodeBitmap, encodeBitmapUnchecked, hsig, ByteArray.append_assoc, idat, encodeBitmapIdat] using
    (ByteArray.extract_append_eq_left
      (a := pngSignature)
      (b := mkChunk "IHDR"
            (u32be bmp.size.width ++ u32be bmp.size.height ++
              ihdrTailColor (PngPixel.colorType (α := px))) ++
          mkChunk "IDAT" idat ++
          mkChunk "IEND" ByteArray.empty)
      (i := pngSignature.size) rfl)

-- The first 4 bytes of a chunk encode the payload length.
lemma mkChunk_extract_len (typ : String) (data : ByteArray) :
    (mkChunk typ data).extract 0 4 = u32be data.size := by
  have hlen : (u32be data.size).size = 4 := u32be_size _
  simpa [mkChunk, mkChunkBytes_def, hlen] using
    (ByteArray.extract_append_eq_left
      (a := u32be data.size)
      (b := typ.toUTF8 ++ data ++ u32be (crc32Chunk typ.toUTF8 data).toNat)
      (i := (u32be data.size).size) rfl)

-- The next 4 bytes of a chunk encode the type tag.
lemma mkChunk_extract_type (typ : String) (data : ByteArray) (htyp : typ.utf8ByteSize = 4) :
    (mkChunk typ data).extract 4 8 = typ.toUTF8 := by
  have hlen : (u32be data.size).size = 4 := u32be_size _
  have htyp' : typ.toUTF8.size = 4 := by
    simpa [String.toUTF8_eq_toByteArray, String.size_toByteArray] using htyp
  have h1 :
      (mkChunk typ data).extract 4 8 =
        (typ.toUTF8 ++ data ++ u32be (crc32Chunk typ.toUTF8 data).toNat).extract 0 4 := by
    simpa [mkChunk, mkChunkBytes_def, hlen, ByteArray.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (ByteArray.extract_append_size_add
        (a := u32be data.size)
        (b := typ.toUTF8 ++ data ++ u32be (crc32Chunk typ.toUTF8 data).toNat)
        (i := 0) (j := 4))
  have h2' :
      (typ.toUTF8 ++ data ++ u32be (crc32Chunk typ.toUTF8 data).toNat).extract 0
          typ.toUTF8.size = typ.toUTF8 := by
    simpa [ByteArray.append_assoc] using
      (ByteArray.extract_append_eq_left
        (a := typ.toUTF8)
        (b := data ++ u32be (crc32Chunk typ.toUTF8 data).toNat)
        (i := typ.toUTF8.size) rfl)
  have h2 :
      (typ.toUTF8 ++ data ++ u32be (crc32Chunk typ.toUTF8 data).toNat).extract 0 4 = typ.toUTF8 := by
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
        (data ++ u32be (crc32Chunk typ.toUTF8 data).toNat).extract 0 data.size := by
    simpa [mkChunk, mkChunkBytes_def, hprefix, ByteArray.append_assoc, String.toUTF8_eq_toByteArray,
      String.size_toByteArray, htyp, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (ByteArray.extract_append_size_add
        (a := u32be data.size ++ typ.toUTF8)
        (b := data ++ u32be (crc32Chunk typ.toUTF8 data).toNat)
        (i := 0) (j := data.size))
  have h2 :
      (data ++ u32be (crc32Chunk typ.toUTF8 data).toNat).extract 0 data.size = data := by
    simpa using
      (ByteArray.extract_append_eq_left
        (a := data)
        (b := u32be (crc32Chunk typ.toUTF8 data).toNat)
        (i := data.size) rfl)
  simpa [h1, h2]

-- The IHDR length field in the encoded PNG is 13.
lemma encodeBitmap_extract_ihdr_len {px : Type u} [Pixel px] [PngPixel px] (bmp : Bitmap px)
    (hw : bmp.size.width < 2 ^ 32) (hh : bmp.size.height < 2 ^ 32)
    (mode : PngEncodeMode := .stored) :
    (encodeBitmap bmp hw hh mode).extract 8 12 = u32be 13 := by
  let ihdr :=
    u32be bmp.size.width ++ u32be bmp.size.height ++
      ihdrTailColor (PngPixel.colorType (α := px))
  let idat := encodeBitmapIdat (bmp := bmp) (mode := mode)
  have hsig : pngSignature.size = 8 := pngSignature_size
  have hihdr : ihdr.size = 13 := by
    simpa [ihdr] using ihdr_payload_size bmp.size.width bmp.size.height (PngPixel.colorType (α := px))
  have hchunk_ge : 4 ≤ (mkChunk "IHDR" ihdr).size := by
    have hsize : (mkChunk "IHDR" ihdr).size = ihdr.size + "IHDR".utf8ByteSize + 8 :=
      mkChunk_size _ _
    calc
      4 ≤ ihdr.size + "IHDR".utf8ByteSize + 8 := by omega
      _ = (mkChunk "IHDR" ihdr).size := by
        simp [hsize]
  have hshift :
      (encodeBitmap bmp hw hh mode).extract 8 12 =
        (mkChunk "IHDR" ihdr ++ mkChunk "IDAT" idat ++ mkChunk "IEND" ByteArray.empty).extract 0 4 := by
    simpa [encodeBitmap, encodeBitmapUnchecked, hsig, idat, encodeBitmapIdat] using
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
lemma readU32BE_encodeBitmap_ihdr_len {px : Type u} [Pixel px] [PngPixel px]
    (bmp : Bitmap px) (hw : bmp.size.width < 2 ^ 32) (hh : bmp.size.height < 2 ^ 32)
    (mode : PngEncodeMode := .stored)
    (h : 8 + 3 < (encodeBitmap bmp hw hh mode).size) :
    readU32BE (encodeBitmap bmp hw hh mode) 8 h = 13 := by
  exact readU32BE_of_extract_eq (bytes := encodeBitmap bmp hw hh mode) (pos := 8) (n := 13) h
    (encodeBitmap_extract_ihdr_len bmp hw hh mode) (by decide)

-- The IHDR type field in the encoded PNG is "IHDR".
lemma encodeBitmap_extract_ihdr_type {px : Type u} [Pixel px] [PngPixel px] (bmp : Bitmap px)
    (hw : bmp.size.width < 2 ^ 32) (hh : bmp.size.height < 2 ^ 32)
    (mode : PngEncodeMode := .stored) :
    (encodeBitmap bmp hw hh mode).extract 12 16 = "IHDR".toUTF8 := by
  let ihdr :=
    u32be bmp.size.width ++ u32be bmp.size.height ++
      ihdrTailColor (PngPixel.colorType (α := px))
  let idat := encodeBitmapIdat (bmp := bmp) (mode := mode)
  have hsig : pngSignature.size = 8 := pngSignature_size
  have hchunk_ge : 8 ≤ (mkChunk "IHDR" ihdr).size := by
    have hsize : (mkChunk "IHDR" ihdr).size = ihdr.size + "IHDR".utf8ByteSize + 8 :=
      mkChunk_size _ _
    calc
      8 ≤ ihdr.size + "IHDR".utf8ByteSize + 8 := by omega
      _ = (mkChunk "IHDR" ihdr).size := by
        simp [hsize]
  have hshift :
      (encodeBitmap bmp hw hh mode).extract 12 16 =
        (mkChunk "IHDR" ihdr ++ mkChunk "IDAT" idat ++ mkChunk "IEND" ByteArray.empty).extract 4 8 := by
    simpa [encodeBitmap, encodeBitmapUnchecked, hsig, idat, encodeBitmapIdat] using
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
lemma encodeBitmap_extract_ihdr_data {px : Type u} [Pixel px] [PngPixel px] (bmp : Bitmap px)
    (hw : bmp.size.width < 2 ^ 32) (hh : bmp.size.height < 2 ^ 32)
    (mode : PngEncodeMode := .stored) :
    (encodeBitmap bmp hw hh mode).extract 16 29 =
      (u32be bmp.size.width ++ u32be bmp.size.height ++
        ihdrTailColor (PngPixel.colorType (α := px))) := by
  let ihdr :=
    u32be bmp.size.width ++ u32be bmp.size.height ++
      ihdrTailColor (PngPixel.colorType (α := px))
  let idat := encodeBitmapIdat (bmp := bmp) (mode := mode)
  have hsig : pngSignature.size = 8 := pngSignature_size
  have hihdr : ihdr.size = 13 := by
    simpa [ihdr] using ihdr_payload_size bmp.size.width bmp.size.height (PngPixel.colorType (α := px))
  have hchunk_ge : 21 ≤ (mkChunk "IHDR" ihdr).size := by
    have hsize : (mkChunk "IHDR" ihdr).size = ihdr.size + "IHDR".utf8ByteSize + 8 :=
      mkChunk_size _ _
    calc
      21 ≤ 13 + "IHDR".utf8ByteSize + 8 := by omega
      _ = (mkChunk "IHDR" ihdr).size := by
        simp [hsize, hihdr]
  have hshift :
      (encodeBitmap bmp hw hh mode).extract 16 29 =
        (mkChunk "IHDR" ihdr ++ mkChunk "IDAT" idat ++ mkChunk "IEND" ByteArray.empty).extract 8 21 := by
    simpa [encodeBitmap, encodeBitmapUnchecked, hsig, idat, encodeBitmapIdat] using
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
lemma encodeBitmap_sig_ihdr_size {px : Type u} [Pixel px] [PngPixel px] (bmp : Bitmap px) :
    (pngSignature ++
        mkChunk "IHDR"
          (u32be bmp.size.width ++ u32be bmp.size.height ++
            ihdrTailColor (PngPixel.colorType (α := px)))).size = 33 := by
  let ihdr :=
    u32be bmp.size.width ++ u32be bmp.size.height ++
      ihdrTailColor (PngPixel.colorType (α := px))
  have hihdr : ihdr.size = 13 := by
    simpa [ihdr] using ihdr_payload_size bmp.size.width bmp.size.height (PngPixel.colorType (α := px))
  calc
    (pngSignature ++ mkChunk "IHDR" ihdr).size
        = pngSignature.size + (mkChunk "IHDR" ihdr).size := by
            simp [ByteArray.size_append]
    _ = 8 + (ihdr.size + "IHDR".utf8ByteSize + 8) := by
            simp [pngSignature_size, mkChunk_size]
    _ = 33 := by
            simp [hihdr, ihdr_utf8ByteSize, Nat.add_comm]

-- The IDAT length field in the encoded PNG matches the compressed payload size.
lemma encodeBitmap_extract_idat_len {px : Type u} [Pixel px] [PngPixel px] (bmp : Bitmap px)
    (hw : bmp.size.width < 2 ^ 32) (hh : bmp.size.height < 2 ^ 32)
    (mode : PngEncodeMode := .stored) :
    (encodeBitmap bmp hw hh mode).extract 33 37 =
      u32be (encodeBitmapIdat (bmp := bmp) (mode := mode)).size := by
  let ihdr :=
    u32be bmp.size.width ++ u32be bmp.size.height ++
      ihdrTailColor (PngPixel.colorType (α := px))
  let idat := encodeBitmapIdat (bmp := bmp) (mode := mode)
  have hsig : (pngSignature ++ mkChunk "IHDR" ihdr).size = 33 := by
    simpa [ihdr] using encodeBitmap_sig_ihdr_size (bmp := bmp)
  have hshift :
      (encodeBitmap bmp hw hh mode).extract 33 37 =
        (mkChunk "IDAT" idat ++ mkChunk "IEND" ByteArray.empty).extract 0 4 := by
    simpa [encodeBitmap, encodeBitmapUnchecked, hsig, idat, encodeBitmapIdat, ByteArray.append_assoc] using
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
lemma readU32BE_encodeBitmap_idat_len {px : Type u} [Pixel px] [PngPixel px]
    (bmp : Bitmap px) (hw : bmp.size.width < 2 ^ 32) (hh : bmp.size.height < 2 ^ 32)
    (mode : PngEncodeMode := .stored)
    (h : 33 + 3 < (encodeBitmap bmp hw hh mode).size)
    (hidat : (encodeBitmapIdat (bmp := bmp) (mode := mode)).size < 2 ^ 32) :
    readU32BE (encodeBitmap bmp hw hh mode) 33 h =
      (encodeBitmapIdat (bmp := bmp) (mode := mode)).size := by
  let idat := encodeBitmapIdat (bmp := bmp) (mode := mode)
  have hextract : (encodeBitmap bmp hw hh mode).extract 33 37 = u32be idat.size := by
    simpa [idat] using encodeBitmap_extract_idat_len (bmp := bmp) (hw := hw) (hh := hh) (mode := mode)
  exact readU32BE_of_extract_eq (bytes := encodeBitmap bmp hw hh mode) (pos := 33) (n := idat.size) h
    hextract hidat

-- The IDAT type field in the encoded PNG is "IDAT".
lemma encodeBitmap_extract_idat_type {px : Type u} [Pixel px] [PngPixel px] (bmp : Bitmap px)
    (hw : bmp.size.width < 2 ^ 32) (hh : bmp.size.height < 2 ^ 32)
    (mode : PngEncodeMode := .stored) :
    (encodeBitmap bmp hw hh mode).extract 37 41 = "IDAT".toUTF8 := by
  let ihdr :=
    u32be bmp.size.width ++ u32be bmp.size.height ++
      ihdrTailColor (PngPixel.colorType (α := px))
  let idat := encodeBitmapIdat (bmp := bmp) (mode := mode)
  have hsig : (pngSignature ++ mkChunk "IHDR" ihdr).size = 33 := by
    simpa [ihdr] using encodeBitmap_sig_ihdr_size (bmp := bmp)
  have hshift :
      (encodeBitmap bmp hw hh mode).extract 37 41 =
        (mkChunk "IDAT" idat ++ mkChunk "IEND" ByteArray.empty).extract 4 8 := by
    simpa [encodeBitmap, encodeBitmapUnchecked, hsig, idat, encodeBitmapIdat, ByteArray.append_assoc] using
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
lemma encodeBitmap_extract_idat_data {px : Type u} [Pixel px] [PngPixel px] (bmp : Bitmap px)
    (hw : bmp.size.width < 2 ^ 32) (hh : bmp.size.height < 2 ^ 32)
    (mode : PngEncodeMode := .stored) :
    (encodeBitmap bmp hw hh mode).extract
        41 (41 + (encodeBitmapIdat (bmp := bmp) (mode := mode)).size) =
      encodeBitmapIdat (bmp := bmp) (mode := mode) := by
  let ihdr :=
    u32be bmp.size.width ++ u32be bmp.size.height ++
      ihdrTailColor (PngPixel.colorType (α := px))
  let idat := encodeBitmapIdat (bmp := bmp) (mode := mode)
  let sigIhdr := pngSignature ++ mkChunk "IHDR" ihdr
  let tail := mkChunk "IDAT" idat ++ mkChunk "IEND" ByteArray.empty
  have hsig : sigIhdr.size = 33 := by
    simpa [sigIhdr, ihdr] using encodeBitmap_sig_ihdr_size (bmp := bmp)
  have hdef : encodeBitmap bmp hw hh mode = sigIhdr ++ tail := by
    simp [encodeBitmap, encodeBitmapUnchecked, sigIhdr, tail, ihdr, idat, ihdrTailColor,
      encodeBitmapIdat, ByteArray.append_assoc, Id.run]
    rfl
  have hshift' :
      (encodeBitmap bmp hw hh mode).extract (sigIhdr.size + 8) (sigIhdr.size + (8 + idat.size)) =
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
      (encodeBitmap bmp hw hh mode).extract 41 (41 + idat.size) =
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
    (encodeBitmap bmp hw hh mode).extract 41 (41 + idat.size)
        = tail.extract 8 (8 + idat.size) := hshift
    _ = (mkChunk "IDAT" idat).extract 8 (8 + idat.size) := hleft
    _ = idat := hdata

-- The IEND length field in the encoded PNG is zero.
lemma encodeBitmap_extract_iend_len {px : Type u} [Pixel px] [PngPixel px] (bmp : Bitmap px)
    (hw : bmp.size.width < 2 ^ 32) (hh : bmp.size.height < 2 ^ 32)
    (mode : PngEncodeMode := .stored) :
    (encodeBitmap bmp hw hh mode).extract
        (45 + (encodeBitmapIdat (bmp := bmp) (mode := mode)).size)
        (49 + (encodeBitmapIdat (bmp := bmp) (mode := mode)).size) = u32be 0 := by
  let ihdr :=
    u32be bmp.size.width ++ u32be bmp.size.height ++
      ihdrTailColor (PngPixel.colorType (α := px))
  let idat := encodeBitmapIdat (bmp := bmp) (mode := mode)
  let sigIhdr := pngSignature ++ mkChunk "IHDR" ihdr
  let tail := mkChunk "IDAT" idat ++ mkChunk "IEND" ByteArray.empty
  have hsig : sigIhdr.size = 33 := by
    simpa [sigIhdr, ihdr] using encodeBitmap_sig_ihdr_size (bmp := bmp)
  have hidat : (mkChunk "IDAT" idat).size = idat.size + 12 := by
    have hsize : (mkChunk "IDAT" idat).size = idat.size + "IDAT".utf8ByteSize + 8 :=
      mkChunk_size _ _
    calc
      (mkChunk "IDAT" idat).size
          = idat.size + "IDAT".utf8ByteSize + 8 := hsize
      _ = idat.size + 12 := by
          simp [idat_utf8ByteSize]
  have hdef : encodeBitmap bmp hw hh mode = sigIhdr ++ tail := by
    simp [encodeBitmap, encodeBitmapUnchecked, sigIhdr, tail, ihdr, idat, ihdrTailColor,
      encodeBitmapIdat, ByteArray.append_assoc, Id.run]
    rfl
  have hshift' :
      (encodeBitmap bmp hw hh mode).extract
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
      (encodeBitmap bmp hw hh mode).extract (45 + idat.size) (49 + idat.size) =
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
    (encodeBitmap bmp hw hh mode).extract (45 + idat.size) (49 + idat.size)
        = tail.extract (mkChunk "IDAT" idat).size ((mkChunk "IDAT" idat).size + 4) := hshift
    _ = (mkChunk "IEND" ByteArray.empty).extract 0 4 := hleft
    _ = u32be 0 := hlen

-- Reading the IEND length from the encoded PNG yields zero.
set_option maxHeartbeats 5000000 in
lemma readU32BE_encodeBitmap_iend_len {px : Type u} [Pixel px] [PngPixel px]
    (bmp : Bitmap px) (hw : bmp.size.width < 2 ^ 32) (hh : bmp.size.height < 2 ^ 32)
    (mode : PngEncodeMode := .stored)
    (h : 45 + (encodeBitmapIdat (bmp := bmp) (mode := mode)).size + 3 <
      (encodeBitmap bmp hw hh mode).size) :
    readU32BE (encodeBitmap bmp hw hh mode)
      (45 + (encodeBitmapIdat (bmp := bmp) (mode := mode)).size) h = 0 := by
  let idat := encodeBitmapIdat (bmp := bmp) (mode := mode)
  have hpos : 45 + idat.size + 3 < (encodeBitmap bmp hw hh mode).size := by
    simpa [idat] using h
  have hextract :
      (encodeBitmap bmp hw hh mode).extract (45 + idat.size) (45 + idat.size + 4) = u32be 0 := by
    have hshift : 45 + idat.size + 4 = 49 + idat.size := by omega
    simpa [idat, hshift] using encodeBitmap_extract_iend_len (bmp := bmp) (hw := hw) (hh := hh)
      (mode := mode)
  exact readU32BE_of_extract_eq (bytes := encodeBitmap bmp hw hh mode) (pos := 45 + idat.size) (n := 0) hpos
    hextract (by decide)

-- The IEND type field in the encoded PNG is "IEND".
lemma encodeBitmap_extract_iend_type {px : Type u} [Pixel px] [PngPixel px] (bmp : Bitmap px)
    (hw : bmp.size.width < 2 ^ 32) (hh : bmp.size.height < 2 ^ 32)
    (mode : PngEncodeMode := .stored) :
    (encodeBitmap bmp hw hh mode).extract
        (49 + (encodeBitmapIdat (bmp := bmp) (mode := mode)).size)
        (53 + (encodeBitmapIdat (bmp := bmp) (mode := mode)).size) = "IEND".toUTF8 := by
  let ihdr :=
    u32be bmp.size.width ++ u32be bmp.size.height ++
      ihdrTailColor (PngPixel.colorType (α := px))
  let idat := encodeBitmapIdat (bmp := bmp) (mode := mode)
  let sigIhdr := pngSignature ++ mkChunk "IHDR" ihdr
  let tail := mkChunk "IDAT" idat ++ mkChunk "IEND" ByteArray.empty
  have hsig : sigIhdr.size = 33 := by
    simpa [sigIhdr, ihdr] using encodeBitmap_sig_ihdr_size (bmp := bmp)
  have hidat : (mkChunk "IDAT" idat).size = idat.size + 12 := by
    have hsize : (mkChunk "IDAT" idat).size = idat.size + "IDAT".utf8ByteSize + 8 :=
      mkChunk_size _ _
    calc
      (mkChunk "IDAT" idat).size
          = idat.size + "IDAT".utf8ByteSize + 8 := hsize
      _ = idat.size + 12 := by
          simp [idat_utf8ByteSize]
  have hdef : encodeBitmap bmp hw hh mode = sigIhdr ++ tail := by
    simp [encodeBitmap, encodeBitmapUnchecked, sigIhdr, tail, ihdr, idat, ihdrTailColor,
      encodeBitmapIdat, ByteArray.append_assoc, Id.run]
    rfl
  have hshift' :
      (encodeBitmap bmp hw hh mode).extract
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
      (encodeBitmap bmp hw hh mode).extract (49 + idat.size) (53 + idat.size) =
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
    (encodeBitmap bmp hw hh mode).extract (49 + idat.size) (53 + idat.size)
        = tail.extract ((mkChunk "IDAT" idat).size + 4) ((mkChunk "IDAT" idat).size + 8) := hshift
    _ = (mkChunk "IEND" ByteArray.empty).extract 4 8 := hleft
    _ = "IEND".toUTF8 := htyp

-- Closed-form size of PNG produced by encodeBitmap.
lemma encodeBitmap_size {px : Type u} [Pixel px] [PngPixel px] (bmp : Bitmap px)
    (hw : bmp.size.width < 2 ^ 32) (hh : bmp.size.height < 2 ^ 32)
    (mode : PngEncodeMode := .stored) :
    (encodeBitmap bmp hw hh mode).size =
      (encodeBitmapIdat (bmp := bmp) (mode := mode)).size + 57 := by
  cases mode with
  | stored =>
      unfold encodeBitmap encodeBitmapUnchecked encodeBitmapIdat
      have htail :
          (ByteArray.mk #[u8 8, PngPixel.colorType (α := px), u8 0, u8 0, u8 0]).size = 5 := by
        simp [ByteArray.size]
      simp [Id.run, ByteArray.size_append, mkChunk_size, pngSignature_size, htail,
        ihdr_utf8ByteSize, idat_utf8ByteSize, iend_utf8ByteSize, u32be_size,
        Nat.add_comm]
      omega
  | fixed =>
      unfold encodeBitmap encodeBitmapUnchecked encodeBitmapIdat
      have htail :
          (ByteArray.mk #[u8 8, PngPixel.colorType (α := px), u8 0, u8 0, u8 0]).size = 5 := by
        simp [ByteArray.size]
      simp [Id.run, ByteArray.size_append, mkChunk_size, pngSignature_size, htail,
        ihdr_utf8ByteSize, idat_utf8ByteSize, iend_utf8ByteSize, u32be_size,
        Nat.add_comm]
      omega

-- Reading the IHDR chunk from an encoded bitmap yields its header payload.
lemma readChunk_encodeBitmap_ihdr {px : Type u} [Pixel px] [PngPixel px]
    (bmp : Bitmap px) (hw : bmp.size.width < 2 ^ 32) (hh : bmp.size.height < 2 ^ 32)
    (mode : PngEncodeMode := .stored)
    (hLen : 8 + 3 < (encodeBitmap bmp hw hh mode).size) :
    readChunk (encodeBitmap bmp hw hh mode) 8 hLen =
      some ("IHDR".toUTF8,
        u32be bmp.size.width ++ u32be bmp.size.height ++
          ihdrTailColor (PngPixel.colorType (α := px)),
        33) := by
  let ihdr :=
    u32be bmp.size.width ++ u32be bmp.size.height ++
      ihdrTailColor (PngPixel.colorType (α := px))
  let idat := encodeBitmapIdat (bmp := bmp) (mode := mode)
  have hlenval : readU32BE (encodeBitmap bmp hw hh mode) 8 hLen = 13 := by
    exact readU32BE_encodeBitmap_ihdr_len (bmp := bmp) (hw := hw) (hh := hh) (h := hLen)
      (mode := mode)
  have hsize : (encodeBitmap bmp hw hh mode).size = idat.size + 57 := by
    simpa [idat] using encodeBitmap_size (bmp := bmp) (hw := hw) (hh := hh) (mode := mode)
  have hcrc : 33 ≤ (encodeBitmap bmp hw hh mode).size := by
    have hsz' : 33 ≤ idat.size + 57 := by omega
    simp [hsize, hsz']
  have hcrcEnd : 8 + 8 + 13 + 4 = 33 := by omega
  unfold readChunk
  simp [hlenval, hcrc, hcrcEnd,
    encodeBitmap_extract_ihdr_type (bmp := bmp) (hw := hw) (hh := hh) (mode := mode),
    encodeBitmap_extract_ihdr_data (bmp := bmp) (hw := hw) (hh := hh) (mode := mode)]

-- Reading the IDAT chunk from an encoded bitmap yields the compressed payload.
lemma readChunk_encodeBitmap_idat {px : Type u} [Pixel px] [PngPixel px]
    (bmp : Bitmap px) (hw : bmp.size.width < 2 ^ 32) (hh : bmp.size.height < 2 ^ 32)
    (mode : PngEncodeMode := .stored)
    (hidat : (encodeBitmapIdat (bmp := bmp) (mode := mode)).size < 2 ^ 32)
    (hLen : 33 + 3 < (encodeBitmap bmp hw hh mode).size) :
    readChunk (encodeBitmap bmp hw hh mode) 33 hLen =
      some ("IDAT".toUTF8, encodeBitmapIdat (bmp := bmp) (mode := mode),
        45 + (encodeBitmapIdat (bmp := bmp) (mode := mode)).size) := by
  let idat := encodeBitmapIdat (bmp := bmp) (mode := mode)
  have hlenval : readU32BE (encodeBitmap bmp hw hh mode) 33 hLen = idat.size := by
    simpa [idat] using
      (readU32BE_encodeBitmap_idat_len (bmp := bmp) (hw := hw) (hh := hh)
        (mode := mode) (h := hLen) (hidat := hidat))
  have hsize : (encodeBitmap bmp hw hh mode).size = idat.size + 57 := by
    simpa [idat] using encodeBitmap_size (bmp := bmp) (hw := hw) (hh := hh) (mode := mode)
  have hcrc : 45 + idat.size ≤ (encodeBitmap bmp hw hh mode).size := by
    have hsz' : 45 + idat.size ≤ idat.size + 57 := by omega
    simpa [hsize] using hsz'
  have hcrcEnd : 33 + 8 + idat.size + 4 = 45 + idat.size := by omega
  unfold readChunk
  simp [hlenval, hcrc, hcrcEnd,
    encodeBitmap_extract_idat_type (bmp := bmp) (hw := hw) (hh := hh) (mode := mode),
    encodeBitmap_extract_idat_data (bmp := bmp) (hw := hw) (hh := hh) (mode := mode),
    idat]

-- Reading the IEND chunk from an encoded bitmap yields an empty payload.
lemma readChunk_encodeBitmap_iend {px : Type u} [Pixel px] [PngPixel px]
    (bmp : Bitmap px) (hw : bmp.size.width < 2 ^ 32) (hh : bmp.size.height < 2 ^ 32)
    (mode : PngEncodeMode := .stored)
    (hLen :
      45 + (encodeBitmapIdat (bmp := bmp) (mode := mode)).size + 3 <
        (encodeBitmap bmp hw hh mode).size) :
    readChunk (encodeBitmap bmp hw hh mode)
        (45 + (encodeBitmapIdat (bmp := bmp) (mode := mode)).size) hLen =
      some ("IEND".toUTF8, ByteArray.empty,
        57 + (encodeBitmapIdat (bmp := bmp) (mode := mode)).size) := by
  let idat := encodeBitmapIdat (bmp := bmp) (mode := mode)
  have hlenval : readU32BE (encodeBitmap bmp hw hh mode) (45 + idat.size) hLen = 0 := by
    simpa [idat, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (readU32BE_encodeBitmap_iend_len (bmp := bmp) (hw := hw) (hh := hh)
        (mode := mode) (h := hLen))
  have hsize : (encodeBitmap bmp hw hh mode).size = idat.size + 57 := by
    simpa [idat] using encodeBitmap_size (bmp := bmp) (hw := hw) (hh := hh) (mode := mode)
  have hcrc : 57 + idat.size ≤ (encodeBitmap bmp hw hh mode).size := by
    have hsz' : 57 + idat.size ≤ idat.size + 57 := by omega
    simpa [hsize] using hsz'
  have htype : 45 + idat.size + 4 = 49 + idat.size := by omega
  have htypeEnd : 49 + idat.size + 4 = 53 + idat.size := by omega
  have hcrcEnd : 45 + idat.size + 8 + 4 = 57 + idat.size := by omega
  unfold readChunk
  simp [hlenval, hcrc, htype, htypeEnd, hcrcEnd,
    encodeBitmap_extract_iend_type (bmp := bmp) (hw := hw) (hh := hh) (mode := mode),
    idat]

-- Parsing an encoded bitmap with the simple PNG parser recovers the header and payload.
set_option maxHeartbeats 5000000 in
lemma parsePngSimple_encodeBitmap {px : Type u} [Pixel px] [PngPixel px] (bmp : Bitmap px)
    (hw : bmp.size.width < 2 ^ 32) (hh : bmp.size.height < 2 ^ 32)
    (mode : PngEncodeMode := .stored)
    (hidat : (encodeBitmapIdat (bmp := bmp) (mode := mode)).size < 2 ^ 32)
    (hsize : 8 <= (encodeBitmap bmp hw hh mode).size)
    (hct : (PngPixel.colorType (α := px)).toNat = 0 ∨
      (PngPixel.colorType (α := px)).toNat = 2 ∨
      (PngPixel.colorType (α := px)).toNat = 6) :
    parsePngSimple (encodeBitmap bmp hw hh mode) hsize =
      some ({ width := bmp.size.width, height := bmp.size.height
            , colorType := (PngPixel.colorType (α := px)).toNat, bitDepth := 8 },
            encodeBitmapIdat (bmp := bmp) (mode := mode)) := by
  let w := bmp.size.width
  let h := bmp.size.height
  let ct := PngPixel.colorType (α := px)
  let ihdr := u32be w ++ u32be h ++ ihdrTailColor ct
  let idat := encodeBitmapIdat (bmp := bmp) (mode := mode)
  have hlen' : ihdr.size = 13 := by
    simpa [ihdr] using ihdr_payload_size w h ct
  have hsigNe : (pngSignature != pngSignature) = false := by
    exact bne_self_eq_false' (a := pngSignature)
  have hihdrNe : ("IHDR".toUTF8 != "IHDR".toUTF8) = false := by
    exact bne_self_eq_false' (a := "IHDR".toUTF8)
  have hidatNe : ("IDAT".toUTF8 != "IDAT".toUTF8) = false := by
    exact bne_self_eq_false' (a := "IDAT".toUTF8)
  have hiendNe : ("IEND".toUTF8 != "IEND".toUTF8) = false := by
    exact bne_self_eq_false' (a := "IEND".toUTF8)
  have htailEq : ihdr.extract 8 13 = ihdrTailColor ct := by
    simpa [ihdr] using ihdr_payload_extract_tail w h ct
  have hbitDepth : ((ihdr.extract 8 13).get! 0).toNat = 8 := by
    simpa [htailEq] using (by decide : (u8 8).toNat = 8)
  have hctEq : ((ihdr.extract 8 13).get! 1).toNat = ct.toNat := by
    simp [htailEq]
  have hcomp : ((ihdr.extract 8 13).get! 2).toNat = 0 := by
    simpa [htailEq] using (by decide : (u8 0).toNat = 0)
  have hfilter : ((ihdr.extract 8 13).get! 3).toNat = 0 := by
    simpa [htailEq] using (by decide : (u8 0).toNat = 0)
  have hinterlace : ((ihdr.extract 8 13).get! 4).toNat = 0 := by
    simpa [htailEq] using (by decide : (u8 0).toNat = 0)
  have hcolorOk : (ct.toNat != 0 && ct.toNat != 2 && ct.toNat != 6) = false := by
    rcases hct with h0 | h2 | h6
    · rw [h0]; decide
    · rw [h2]; decide
    · rw [h6]; decide
  have hctProp : ¬ct.toNat = 0 → ¬ct.toNat = 2 → ct.toNat = 6 := by
    intro h0' h2'
    rcases hct with h0 | h2 | h6
    · exact (False.elim (h0' h0))
    · exact (False.elim (h2' h2))
    · exact h6
  have hpos0 : 0 + 3 < ihdr.size := by
    have : ihdr.size = 13 := hlen'
    omega
  have hpos4 : 4 + 3 < ihdr.size := by
    have : ihdr.size = 13 := hlen'
    omega
  have hwidth0 : readU32BE ihdr 0 hpos0 = w := by
    have hextract : ihdr.extract 0 4 = u32be w := by
      simpa [ihdr] using ihdr_payload_extract_width w h ct
    exact readU32BE_of_extract_eq ihdr 0 w hpos0 hextract hw
  have hheight0 : readU32BE ihdr 4 hpos4 = h := by
    have hextract : ihdr.extract 4 8 = u32be h := by
      simpa [ihdr] using ihdr_payload_extract_height w h ct
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
  have hheader :
      ∃ x : Nat,
        readU32BE ihdr 0 (by simp [hlen']) = w ∧
        readU32BE ihdr 4 (by simp [hlen']) = h ∧
        ((ihdr.extract 8 13).get! 1).toNat = ct.toNat ∧
        ((ihdr.extract 8 13).get! 0).toNat = 8 := by
    refine ⟨0, hwidth, hheight, hctEq, hbitDepth⟩
  have hbitDepth' :
      (((u32be w ++ u32be h ++ ihdrTailColor ct).extract 8 13).get! 0).toNat = 8 := by
    simpa [ihdr] using hbitDepth
  have hctEq' :
      (((u32be w ++ u32be h ++ ihdrTailColor ct).extract 8 13).get! 1).toNat = ct.toNat := by
    simpa [ihdr] using hctEq
  have hcomp' :
      (((u32be w ++ u32be h ++ ihdrTailColor ct).extract 8 13).get! 2).toNat = 0 := by
    simpa [ihdr] using hcomp
  have hfilter' :
      (((u32be w ++ u32be h ++ ihdrTailColor ct).extract 8 13).get! 3).toNat = 0 := by
    simpa [ihdr] using hfilter
  have hinterlace' :
      (((u32be w ++ u32be h ++ ihdrTailColor ct).extract 8 13).get! 4).toNat = 0 := by
    simpa [ihdr] using hinterlace
  have hctProp' :
      ¬(((u32be w ++ u32be h ++ ihdrTailColor ct).extract 8 13).get! 1).toNat = 0 →
      ¬(((u32be w ++ u32be h ++ ihdrTailColor ct).extract 8 13).get! 1).toNat = 2 →
      (((u32be w ++ u32be h ++ ihdrTailColor ct).extract 8 13).get! 1).toNat = 6 := by
    simpa [ihdr, hctEq] using hctProp
  have hpos0' : 0 + 3 < (u32be w ++ u32be h ++ ihdrTailColor ct).size := by
    have : (u32be w ++ u32be h ++ ihdrTailColor ct).size = 13 := by
      simpa [ihdr] using hlen'
    omega
  have hpos4' : 4 + 3 < (u32be w ++ u32be h ++ ihdrTailColor ct).size := by
    have : (u32be w ++ u32be h ++ ihdrTailColor ct).size = 13 := by
      simpa [ihdr] using hlen'
    omega
  have hwidth' :
      readU32BE (u32be w ++ u32be h ++ ihdrTailColor ct) 0 hpos0' = w := by
    have hproof :=
      readU32BE_proof_irrel
        (bytes := u32be w ++ u32be h ++ ihdrTailColor ct)
        (pos := 0)
        (h1 := hpos0') (h2 := by exact hpos0)
    have hwidth0' :
        readU32BE (u32be w ++ u32be h ++ ihdrTailColor ct) 0 (by exact hpos0) = w := by
      simpa [ihdr] using hwidth0
    exact hproof.trans hwidth0'
  have hheight' :
      readU32BE (u32be w ++ u32be h ++ ihdrTailColor ct) 4 hpos4' = h := by
    have hproof :=
      readU32BE_proof_irrel
        (bytes := u32be w ++ u32be h ++ ihdrTailColor ct)
        (pos := 4)
        (h1 := hpos4') (h2 := by exact hpos4)
    have hheight0' :
        readU32BE (u32be w ++ u32be h ++ ihdrTailColor ct) 4 (by exact hpos4) = h := by
      simpa [ihdr] using hheight0
    exact hproof.trans hheight0'
  have hsize8 : (u32be w).size + (u32be h).size = 8 := by
    simp [u32be_size]
  have hheader' :
      ∃ x : (u32be w).size + (u32be h).size = 8,
        readU32BE (u32be w ++ u32be h ++ ihdrTailColor ct) 0 hpos0' = w ∧
        readU32BE (u32be w ++ u32be h ++ ihdrTailColor ct) 4 hpos4' = h ∧
        (((u32be w ++ u32be h ++ ihdrTailColor ct).extract 8 13).get! 1).toNat = ct.toNat ∧
        (((u32be w ++ u32be h ++ ihdrTailColor ct).extract 8 13).get! 0).toNat = 8 := by
    exact ⟨hsize8, hwidth', hheight', hctEq', hbitDepth'⟩
  have hihdrNeBA : ("IHDR".toByteArray != "IHDR".toByteArray) = false := by
    exact bne_self_eq_false' (a := "IHDR".toByteArray)
  have hidatNeBA : ("IDAT".toByteArray != "IDAT".toByteArray) = false := by
    exact bne_self_eq_false' (a := "IDAT".toByteArray)
  have hiendNeBA : ("IEND".toByteArray != "IEND".toByteArray) = false := by
    exact bne_self_eq_false' (a := "IEND".toByteArray)
  have hsize : (encodeBitmap bmp hw hh mode).size = idat.size + 57 := by
    simpa [idat] using encodeBitmap_size (bmp := bmp) (hw := hw) (hh := hh) (mode := mode)
  have hlen1 : 8 + 3 < (encodeBitmap bmp hw hh mode).size := by
    simp [hsize]
  have hlen2 : 33 + 3 < (encodeBitmap bmp hw hh mode).size := by
    simp [hsize]
  have hlen3 :
      45 + idat.size + 3 < (encodeBitmap bmp hw hh mode).size := by
    simp [hsize]; omega
  -- Unfold and simplify the parser using the chunk-level lemmas.
  unfold parsePngSimple
  simp [encodeBitmap_signature (bmp := bmp) (hw := hw) (hh := hh) (mode := mode),
    hsigNe, hihdrNeBA, hidatNeBA, hiendNeBA,
    hlen1, hlen2,
    readChunk_encodeBitmap_ihdr (bmp := bmp) (hw := hw) (hh := hh) (mode := mode) (hLen := hlen1),
    readChunk_encodeBitmap_idat (bmp := bmp) (hw := hw) (hh := hh) (mode := mode)
      (hidat := hidat) (hLen := hlen2),
    readChunk_encodeBitmap_iend (bmp := bmp) (hw := hw) (hh := hh) (mode := mode) (hLen := hlen3)]
  refine And.intro hbitDepth' ?_
  refine And.intro hctProp' ?_
  refine And.intro ?_ ?_
  · exact And.intro (And.intro hcomp' hfilter') hinterlace'
  · refine And.intro ?_ ?_
    · exact hlen3
    · exact hheader'

-- Parsing an encoded bitmap with the full PNG parser yields the header and payload.
lemma parsePng_encodeBitmap {px : Type u} [Pixel px] [PngPixel px] (bmp : Bitmap px)
    (hw : bmp.size.width < 2 ^ 32) (hh : bmp.size.height < 2 ^ 32)
    (mode : PngEncodeMode := .stored)
    (hidat : (encodeBitmapIdat (bmp := bmp) (mode := mode)).size < 2 ^ 32)
    (hsize : 8 <= (encodeBitmap bmp hw hh mode).size)
    (hct : (PngPixel.colorType (α := px)).toNat = 0 ∨
      (PngPixel.colorType (α := px)).toNat = 2 ∨
      (PngPixel.colorType (α := px)).toNat = 6) :
    parsePng (encodeBitmap bmp hw hh mode) hsize =
      some ({ width := bmp.size.width, height := bmp.size.height
            , colorType := (PngPixel.colorType (α := px)).toNat, bitDepth := 8 },
            encodeBitmapIdat (bmp := bmp) (mode := mode)) := by
  have hsimple := parsePngSimple_encodeBitmap (bmp := bmp) hw hh (mode := mode) hidat hsize hct
  unfold parsePng
  simp [hsimple]

lemma bitIndex_readBit (br : BitReader) (h : br.bytePos < br.data.size) :
    (BitReader.readBit br).2.bitIndex = br.bitIndex + 1 :=
  Png.bitIndex_readBit br h

lemma readBit_data (br : BitReader) (h : br.bytePos < br.data.size) :
    (br.readBit).2.data = br.data :=
  Png.readBit_data br h

-- The raw-encoding loop preserves the buffer size.
lemma encodeRawLoop_size (data : ByteArray) (rowBytes h y : Nat) (raw : ByteArray)
    (hdata : data.size = h * rowBytes) (hraw : raw.size = h * (rowBytes + 1)) :
    (encodeRawLoop data rowBytes h y raw).size = raw.size := by
  have hk :
      ∀ k, ∀ y raw, h - y = k → raw.size = h * (rowBytes + 1) →
        (encodeRawLoop data rowBytes h y raw).size = raw.size := by
    intro k
    induction k with
    | zero =>
        intro y raw hk hraw
        have hy : h ≤ y := Nat.le_of_sub_eq_zero hk
        have hlt : ¬ y < h := not_lt_of_ge hy
        simp [encodeRawLoop, hlt, hraw]
    | succ k ih =>
        intro y raw hk hraw
        have hlt : y < h := Nat.lt_of_sub_eq_succ hk
        have hy : y + 1 ≤ h := Nat.succ_le_of_lt hlt
        have hsrc : y * rowBytes + rowBytes ≤ data.size := by
          have hmul : (y + 1) * rowBytes ≤ h * rowBytes :=
            Nat.mul_le_mul_right rowBytes hy
          have hmul' : (y + 1) * rowBytes ≤ data.size := by
            simpa [hdata] using hmul
          simpa [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm] using hmul'
        have hdest : y * (rowBytes + 1) + 1 + rowBytes ≤ raw.size := by
          have hmul : (y + 1) * (rowBytes + 1) ≤ h * (rowBytes + 1) :=
            Nat.mul_le_mul_right (rowBytes + 1) hy
          have hmul' : (y + 1) * (rowBytes + 1) ≤ raw.size := by
            simpa [hraw] using hmul
          have hcalc : y * (rowBytes + 1) + 1 + rowBytes = (y + 1) * (rowBytes + 1) := by
            calc
              y * (rowBytes + 1) + 1 + rowBytes =
                  y * (rowBytes + 1) + (rowBytes + 1) := by
                    omega
              _ = (y + 1) * (rowBytes + 1) := by
                    simp [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm]
          simpa [hcalc] using hmul'
        let raw' :=
          data.copySlice (y * rowBytes) raw (y * (rowBytes + 1) + 1) rowBytes
        have hcopy : raw'.size = raw.size := by
          exact
            byteArray_copySlice_size (src := data) (dest := raw)
              (srcOff := y * rowBytes) (destOff := y * (rowBytes + 1) + 1) (len := rowBytes) hsrc hdest
        have hk' : h - (y + 1) = k := by
          have hsum : h = Nat.succ k + y := Nat.eq_add_of_sub_eq (Nat.le_of_lt hlt) hk
          calc
            h - (y + 1) = (Nat.succ k + y) - (y + 1) := by simp [hsum]
            _ = k := by omega
        have hraw' : raw'.size = h * (rowBytes + 1) := by
          calc
            raw'.size = raw.size := hcopy
            _ = h * (rowBytes + 1) := hraw
        have ih' :=
          ih (y := y + 1) (raw := raw') hk' hraw'
        have hdef :
            (encodeRawLoop data rowBytes h y raw).size =
              (if y < h then encodeRawLoop data rowBytes h (y + 1) raw' else raw).size := by
          have hdef0 :=
            congrArg ByteArray.size
              (encodeRawLoop.eq_1 (data := data) (rowBytes := rowBytes) (h := h) (y := y) (raw := raw))
          simpa [raw'] using hdef0
        calc
          (encodeRawLoop data rowBytes h y raw).size =
              (if y < h then encodeRawLoop data rowBytes h (y + 1) raw' else raw).size := by
                rw [hdef]
          _ = (encodeRawLoop data rowBytes h (y + 1) raw').size := by
                simp [hlt]
          _ = raw'.size := ih'
          _ = raw.size := hcopy
  exact hk (h - y) y raw rfl hraw

-- Raw encoding size equals height times (row bytes + filter byte).
lemma encodeRaw_size {px : Type u} [Pixel px] (bmp : Bitmap px) :
    (encodeRaw bmp).size =
      bmp.size.height * (bmp.size.width * Pixel.bytesPerPixel (α := px) + 1) := by
  let w := bmp.size.width
  let h := bmp.size.height
  let rowBytes := w * Pixel.bytesPerPixel (α := px)
  let rawSize := h * (rowBytes + 1)
  have hdata : bmp.data.size = h * rowBytes := by
    calc
      bmp.data.size = w * h * Pixel.bytesPerPixel (α := px) := bmp.valid
      _ = h * (w * Pixel.bytesPerPixel (α := px)) := by
            simp [Nat.mul_left_comm, Nat.mul_assoc]
      _ = h * rowBytes := by simp [rowBytes]
  have hraw : (ByteArray.mk (Array.replicate rawSize 0)).size = h * (rowBytes + 1) := by
    simp [rawSize, ByteArray.size, Array.size_replicate]
  unfold encodeRaw
  have hsize :=
    encodeRawLoop_size (data := bmp.data) (rowBytes := rowBytes) (h := h) (y := 0)
      (raw := ByteArray.mk (Array.replicate rawSize 0)) hdata hraw
  calc
    (encodeRawLoop bmp.data rowBytes h 0
        (ByteArray.mk (Array.replicate rawSize 0))).size = (ByteArray.mk (Array.replicate rawSize 0)).size := hsize
    _ = h * (rowBytes + 1) := hraw

-- Starting at row `y`, the encoder leaves the prefix up to `y*(rowBytes+1)+1` untouched.
lemma encodeRawLoop_preserve_prefix (data : ByteArray) (rowBytes h y : Nat) (raw : ByteArray)
    (hdata : data.size = h * rowBytes) (hraw : raw.size = h * (rowBytes + 1))
    (n : Nat) (hn : n ≤ y * (rowBytes + 1) + 1) :
    (encodeRawLoop data rowBytes h y raw).extract 0 n = raw.extract 0 n := by
  have hk :
      ∀ k, ∀ y raw, h - y = k → raw.size = h * (rowBytes + 1) → n ≤ y * (rowBytes + 1) + 1 →
        (encodeRawLoop data rowBytes h y raw).extract 0 n = raw.extract 0 n := by
    intro k
    induction k with
    | zero =>
        intro y raw hk hraw hn
        have hy : h ≤ y := Nat.le_of_sub_eq_zero hk
        have hlt : ¬ y < h := not_lt_of_ge hy
        simp [encodeRawLoop, hlt]
    | succ k ih =>
        intro y raw hk hraw hn
        have hlt : y < h := Nat.lt_of_sub_eq_succ hk
        have hy : y + 1 ≤ h := Nat.succ_le_of_lt hlt
        have hsrc : y * rowBytes + rowBytes ≤ data.size := by
          have hmul : (y + 1) * rowBytes ≤ h * rowBytes :=
            Nat.mul_le_mul_right rowBytes hy
          have hmul' : (y + 1) * rowBytes ≤ data.size := by
            simpa [hdata] using hmul
          simpa [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm] using hmul'
        have hdest : y * (rowBytes + 1) + 1 + rowBytes ≤ raw.size := by
          have hmul : (y + 1) * (rowBytes + 1) ≤ h * (rowBytes + 1) :=
            Nat.mul_le_mul_right (rowBytes + 1) hy
          have hmul' : (y + 1) * (rowBytes + 1) ≤ raw.size := by
            simpa [hraw] using hmul
          have hcalc : y * (rowBytes + 1) + 1 + rowBytes = (y + 1) * (rowBytes + 1) := by
            calc
              y * (rowBytes + 1) + 1 + rowBytes =
                  y * (rowBytes + 1) + (rowBytes + 1) := by omega
              _ = (y + 1) * (rowBytes + 1) := by
                    simp [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm]
          simpa [hcalc] using hmul'
        let raw' :=
          data.copySlice (y * rowBytes) raw (y * (rowBytes + 1) + 1) rowBytes
        have hcopy : raw'.size = raw.size := by
          exact
            byteArray_copySlice_size (src := data) (dest := raw)
              (srcOff := y * rowBytes) (destOff := y * (rowBytes + 1) + 1) (len := rowBytes) hsrc hdest
        have hraw' : raw'.size = h * (rowBytes + 1) := by
          calc
            raw'.size = raw.size := hcopy
            _ = h * (rowBytes + 1) := hraw
        have ih' := ih (y := y + 1) (raw := raw') (by
          have hsum : h = Nat.succ k + y := Nat.eq_add_of_sub_eq (Nat.le_of_lt hlt) hk
          calc
            h - (y + 1) = (Nat.succ k + y) - (y + 1) := by simp [hsum]
            _ = k := by omega) hraw' (by
              have hle :
                  y * (rowBytes + 1) + 1 ≤ (y + 1) * (rowBytes + 1) + 1 := by
                    calc
                      y * (rowBytes + 1) + 1
                          ≤ y * (rowBytes + 1) + (rowBytes + 1) + 1 := by
                                omega
                      _ = (y + 1) * (rowBytes + 1) + 1 := by
                            simp [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm]
              exact Nat.le_trans hn hle)
        have hprefix :
            raw'.extract 0 n = raw.extract 0 n := by
          have hdestOff : n ≤ y * (rowBytes + 1) + 1 := by omega
          simpa [raw'] using
            byteArray_copySlice_extract_prefix_le
              (src := data) (dest := raw) (srcOff := y * rowBytes)
              (destOff := y * (rowBytes + 1) + 1) (len := rowBytes) (n := n) hdestOff hdest
        calc
          (encodeRawLoop data rowBytes h y raw).extract 0 n =
              (if y < h then encodeRawLoop data rowBytes h (y + 1) raw' else raw).extract 0 n := by
                have hdef :=
                  congrArg (fun b => b.extract 0 n)
                    (encodeRawLoop.eq_1 (data := data) (rowBytes := rowBytes) (h := h) (y := y) (raw := raw))
                simpa [raw'] using hdef
          _ = (encodeRawLoop data rowBytes h (y + 1) raw').extract 0 n := by
                simp [hlt]
          _ = raw'.extract 0 n := ih'
          _ = raw.extract 0 n := hprefix
  exact hk (h - y) y raw rfl hraw hn

-- Applying the prefix encoder preserves the buffer size.
lemma encodeRawPrefix_size (data : ByteArray) (rowBytes h y : Nat) (raw : ByteArray)
    (hdata : data.size = h * rowBytes) (hraw : raw.size = h * (rowBytes + 1))
    (hy : y ≤ h) :
    (encodeRawPrefix data rowBytes y raw).size = raw.size := by
  induction y with
  | zero =>
      simp [encodeRawPrefix]
  | succ y ih =>
      have hy' : y ≤ h := Nat.le_of_succ_le hy
      have hsrc : y * rowBytes + rowBytes ≤ data.size := by
        have hmul : (y + 1) * rowBytes ≤ h * rowBytes :=
          Nat.mul_le_mul_right rowBytes hy
        have hmul' : (y + 1) * rowBytes ≤ data.size := by
          simpa [hdata] using hmul
        simpa [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm] using hmul'
      have hdest : y * (rowBytes + 1) + 1 + rowBytes ≤ raw.size := by
        have hmul : (y + 1) * (rowBytes + 1) ≤ h * (rowBytes + 1) :=
          Nat.mul_le_mul_right (rowBytes + 1) hy
        have hmul' : (y + 1) * (rowBytes + 1) ≤ raw.size := by
          simpa [hraw] using hmul
        have hcalc : y * (rowBytes + 1) + 1 + rowBytes = (y + 1) * (rowBytes + 1) := by
          calc
            y * (rowBytes + 1) + 1 + rowBytes =
                y * (rowBytes + 1) + (rowBytes + 1) := by omega
            _ = (y + 1) * (rowBytes + 1) := by
                  simp [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm]
        simpa [hcalc] using hmul'
      have hraw' : (encodeRawPrefix data rowBytes y raw).size = raw.size := ih hy'
      have hdest' :
          y * (rowBytes + 1) + 1 + rowBytes ≤ (encodeRawPrefix data rowBytes y raw).size := by
        simpa [hraw'] using hdest
      have hsize :=
        byteArray_copySlice_size (src := data) (dest := encodeRawPrefix data rowBytes y raw)
          (srcOff := y * rowBytes) (destOff := y * (rowBytes + 1) + 1) (len := rowBytes)
          hsrc hdest'
      simpa [encodeRawPrefix, hraw'] using hsize

-- Running the encoder from row 0 is equivalent to resuming from row `y`.
lemma encodeRawLoop_eq_prefix (data : ByteArray) (rowBytes h y : Nat) (raw : ByteArray)
    (hy : y ≤ h) :
    encodeRawLoop data rowBytes h 0 raw =
      encodeRawLoop data rowBytes h y (encodeRawPrefix data rowBytes y raw) := by
  induction y with
  | zero =>
      simp [encodeRawPrefix]
  | succ y ih =>
      have hy' : y ≤ h := Nat.le_of_succ_le hy
      have hlt : y < h := Nat.lt_of_succ_le hy
      have hdef :=
        encodeRawLoop.eq_1 (data := data) (rowBytes := rowBytes) (h := h) (y := y)
          (raw := encodeRawPrefix data rowBytes y raw)
      calc
        encodeRawLoop data rowBytes h 0 raw =
            encodeRawLoop data rowBytes h y (encodeRawPrefix data rowBytes y raw) := ih hy'
        _ =
            (if y < h then
              encodeRawLoop data rowBytes h (y + 1)
                (data.copySlice (y * rowBytes) (encodeRawPrefix data rowBytes y raw)
                  (y * (rowBytes + 1) + 1) rowBytes)
            else encodeRawPrefix data rowBytes y raw) := by
              simpa using hdef
        _ = encodeRawLoop data rowBytes h (y + 1)
              (data.copySlice (y * rowBytes) (encodeRawPrefix data rowBytes y raw)
                (y * (rowBytes + 1) + 1) rowBytes) := by
              simp [hlt]
        _ = encodeRawLoop data rowBytes h (y + 1)
              (encodeRawPrefix data rowBytes (y + 1) raw) := by
              rfl

-- Running the encoder for all rows equals the prefix encoder at height `h`.
lemma encodeRawLoop_eq_prefix_full (data : ByteArray) (rowBytes h : Nat) (raw : ByteArray) :
    encodeRawLoop data rowBytes h 0 raw = encodeRawPrefix data rowBytes h raw := by
  have hprefix :=
    encodeRawLoop_eq_prefix (data := data) (rowBytes := rowBytes) (h := h) (y := h) (raw := raw) (hy := Nat.le_refl h)
  have hlt : ¬ h < h := Nat.lt_irrefl h
  have hstep :
      encodeRawLoop data rowBytes h h (encodeRawPrefix data rowBytes h raw) =
        encodeRawPrefix data rowBytes h raw := by
      rw [encodeRawLoop.eq_1]
      simp [hlt]
  exact hprefix.trans hstep

-- Fast raw encoding equals the specification.
lemma encodeRawFast_eq {px : Type u} [Pixel px] (bmp : Bitmap px) :
    encodeRawFast bmp = encodeRaw bmp := by
  unfold encodeRawFast encodeRaw
  dsimp
  exact (encodeRawLoop_eq_prefix_full (data := bmp.data)
    (rowBytes := bmp.size.width * Pixel.bytesPerPixel (α := px))
    (h := bmp.size.height)
    (raw := ByteArray.mk <| Array.replicate (bmp.size.height *
      (bmp.size.width * Pixel.bytesPerPixel (α := px) + 1)) 0)).symm

-- The raw encoding loop writes row `y` into its destination slice.
lemma encodeRawLoop_row_extract (data : ByteArray) (rowBytes h y : Nat) (raw : ByteArray)
    (hdata : data.size = h * rowBytes) (hraw : raw.size = h * (rowBytes + 1))
    (hy : y < h) :
    (encodeRawLoop data rowBytes h y raw).extract (y * (rowBytes + 1) + 1)
        (y * (rowBytes + 1) + 1 + rowBytes) =
      data.extract (y * rowBytes) (y * rowBytes + rowBytes) := by
  have hsrc : y * rowBytes + rowBytes ≤ data.size := by
    have hmul : (y + 1) * rowBytes ≤ h * rowBytes :=
      Nat.mul_le_mul_right rowBytes (Nat.succ_le_of_lt hy)
    have hmul' : (y + 1) * rowBytes ≤ data.size := by
      simpa [hdata] using hmul
    simpa [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm] using hmul'
  have hdest : y * (rowBytes + 1) + 1 + rowBytes ≤ raw.size := by
    have hmul : (y + 1) * (rowBytes + 1) ≤ h * (rowBytes + 1) :=
      Nat.mul_le_mul_right (rowBytes + 1) (Nat.succ_le_of_lt hy)
    have hmul' : (y + 1) * (rowBytes + 1) ≤ raw.size := by
      simpa [hraw] using hmul
    have hcalc : y * (rowBytes + 1) + 1 + rowBytes = (y + 1) * (rowBytes + 1) := by
      calc
        y * (rowBytes + 1) + 1 + rowBytes =
            y * (rowBytes + 1) + (rowBytes + 1) := by omega
        _ = (y + 1) * (rowBytes + 1) := by
              simp [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm]
    simpa [hcalc] using hmul'
  let raw' :=
    data.copySlice (y * rowBytes) raw (y * (rowBytes + 1) + 1) rowBytes
  have hcopy : raw'.size = raw.size := by
    exact
      byteArray_copySlice_size (src := data) (dest := raw)
        (srcOff := y * rowBytes) (destOff := y * (rowBytes + 1) + 1) (len := rowBytes) hsrc hdest
  have hraw' : raw'.size = h * (rowBytes + 1) := by
    simpa [hraw] using hcopy
  have hmid :
      raw'.extract (y * (rowBytes + 1) + 1) (y * (rowBytes + 1) + 1 + rowBytes) =
        data.extract (y * rowBytes) (y * rowBytes + rowBytes) := by
    simpa [raw'] using
      byteArray_copySlice_extract_mid (src := data) (dest := raw)
        (srcOff := y * rowBytes) (destOff := y * (rowBytes + 1) + 1) (len := rowBytes) hsrc hdest
  have hprefix :
      (encodeRawLoop data rowBytes h (y + 1) raw').extract 0 ((y + 1) * (rowBytes + 1)) =
        raw'.extract 0 ((y + 1) * (rowBytes + 1)) := by
    have hle : (y + 1) * (rowBytes + 1) ≤ (y + 1) * (rowBytes + 1) + 1 := by omega
    simpa using
      (encodeRawLoop_preserve_prefix (data := data) (rowBytes := rowBytes) (h := h) (y := y + 1)
        (raw := raw') hdata hraw' ((y + 1) * (rowBytes + 1)) hle)
  have hslice :
      (encodeRawLoop data rowBytes h (y + 1) raw').extract (y * (rowBytes + 1) + 1)
          (y * (rowBytes + 1) + 1 + rowBytes) =
        raw'.extract (y * (rowBytes + 1) + 1) (y * (rowBytes + 1) + 1 + rowBytes) := by
    have hj : y * (rowBytes + 1) + 1 + rowBytes = (y + 1) * (rowBytes + 1) := by
      calc
        y * (rowBytes + 1) + 1 + rowBytes =
            y * (rowBytes + 1) + (rowBytes + 1) := by omega
        _ = (y + 1) * (rowBytes + 1) := by
              simp [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm]
    have hslice' :=
      byteArray_extract_eq_of_prefix_eq
        (a := encodeRawLoop data rowBytes h (y + 1) raw')
        (b := raw') (n := (y + 1) * (rowBytes + 1))
        (i := y * (rowBytes + 1) + 1) (j := y * (rowBytes + 1) + 1 + rowBytes)
        hprefix (by omega)
    simpa [hj] using hslice'
  have hdef :
      encodeRawLoop data rowBytes h y raw =
        encodeRawLoop data rowBytes h (y + 1) raw' := by
    have hdef' :=
      encodeRawLoop.eq_1 (data := data) (rowBytes := rowBytes) (h := h) (y := y) (raw := raw)
    simpa [raw', hy] using hdef'
  calc
    (encodeRawLoop data rowBytes h y raw).extract (y * (rowBytes + 1) + 1)
        (y * (rowBytes + 1) + 1 + rowBytes) =
          (encodeRawLoop data rowBytes h (y + 1) raw').extract
            (y * (rowBytes + 1) + 1) (y * (rowBytes + 1) + 1 + rowBytes) := by
              simp [hdef]
    _ = raw'.extract (y * (rowBytes + 1) + 1) (y * (rowBytes + 1) + 1 + rowBytes) := hslice
    _ = data.extract (y * rowBytes) (y * rowBytes + rowBytes) := hmid

-- The `encodeRaw` output yields the original row slice.
lemma encodeRaw_row_extract {px : Type u} [Pixel px] (bmp : Bitmap px) (y : Nat) (hy : y < bmp.size.height) :
    let w := bmp.size.width
    let rowBytes := w * Pixel.bytesPerPixel (α := px)
    (encodeRaw bmp).extract (y * (rowBytes + 1) + 1) (y * (rowBytes + 1) + 1 + rowBytes) =
      bmp.data.extract (y * rowBytes) (y * rowBytes + rowBytes) := by
  let w := bmp.size.width
  let h := bmp.size.height
  let rowBytes := w * Pixel.bytesPerPixel (α := px)
  let rawSize := h * (rowBytes + 1)
  let raw0 := ByteArray.mk (Array.replicate rawSize 0)
  have hdata : bmp.data.size = h * rowBytes := by
    calc
      bmp.data.size = w * h * Pixel.bytesPerPixel (α := px) := bmp.valid
      _ = h * (w * Pixel.bytesPerPixel (α := px)) := by
            simp [Nat.mul_left_comm, Nat.mul_assoc]
      _ = h * rowBytes := by simp [rowBytes]
  have hraw0 : raw0.size = h * (rowBytes + 1) := by
    simp [raw0, rawSize, ByteArray.size, Array.size_replicate]
  have hy' : y ≤ h := Nat.le_of_lt hy
  have hprefix :
      encodeRawLoop bmp.data rowBytes h 0 raw0 =
        encodeRawLoop bmp.data rowBytes h y (encodeRawPrefix bmp.data rowBytes y raw0) := by
    exact encodeRawLoop_eq_prefix (data := bmp.data) (rowBytes := rowBytes) (h := h) (y := y)
      (raw := raw0) hy'
  have hraw' :
      (encodeRawPrefix bmp.data rowBytes y raw0).size = raw0.size := by
    exact encodeRawPrefix_size (data := bmp.data) (rowBytes := rowBytes) (h := h) (y := y)
      (raw := raw0) hdata hraw0 hy'
  have hrow :
      (encodeRawLoop bmp.data rowBytes h y (encodeRawPrefix bmp.data rowBytes y raw0)).extract
          (y * (rowBytes + 1) + 1) (y * (rowBytes + 1) + 1 + rowBytes) =
        bmp.data.extract (y * rowBytes) (y * rowBytes + rowBytes) := by
    have hraw'': (encodeRawPrefix bmp.data rowBytes y raw0).size = h * (rowBytes + 1) := by
      simpa [hraw0] using hraw'
    exact
      encodeRawLoop_row_extract (data := bmp.data) (rowBytes := rowBytes) (h := h) (y := y)
        (raw := encodeRawPrefix bmp.data rowBytes y raw0) hdata hraw'' hy
  unfold encodeRaw
  have hdef : encodeRawLoop bmp.data rowBytes h 0 raw0 =
      encodeRawLoop bmp.data rowBytes h y (encodeRawPrefix bmp.data rowBytes y raw0) := hprefix
  calc
    (encodeRawLoop bmp.data rowBytes h 0 raw0).extract (y * (rowBytes + 1) + 1)
        (y * (rowBytes + 1) + 1 + rowBytes) =
        (encodeRawLoop bmp.data rowBytes h y (encodeRawPrefix bmp.data rowBytes y raw0)).extract
          (y * (rowBytes + 1) + 1) (y * (rowBytes + 1) + 1 + rowBytes) := by
            simp [hdef]
    _ = bmp.data.extract (y * rowBytes) (y * rowBytes + rowBytes) := hrow

-- Prefix encoding does not touch indices at or beyond the next row boundary.
lemma encodeRawPrefix_get_of_ge (data : ByteArray) (rowBytes h y i : Nat) (raw : ByteArray)
    (hdata : data.size = h * rowBytes) (hraw : raw.size = h * (rowBytes + 1))
    (hy : y ≤ h) (hi : y * (rowBytes + 1) ≤ i) (hi' : i < raw.size) :
    (encodeRawPrefix data rowBytes y raw)[i]'(by
        have hsize :=
          encodeRawPrefix_size (data := data) (rowBytes := rowBytes) (h := h) (y := y)
            (raw := raw) hdata hraw hy
        simpa [hsize] using hi') = raw[i]'hi' := by
  induction y with
  | zero =>
      simp [encodeRawPrefix]
  | succ y ih =>
      have hy' : y ≤ h := Nat.le_of_succ_le hy
      have hsrc : y * rowBytes + rowBytes ≤ data.size := by
        have hmul : (y + 1) * rowBytes ≤ h * rowBytes :=
          Nat.mul_le_mul_right rowBytes hy
        have hmul' : (y + 1) * rowBytes ≤ data.size := by
          simpa [hdata] using hmul
        simpa [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm] using hmul'
      have hdest : y * (rowBytes + 1) + 1 + rowBytes ≤ raw.size := by
        have hmul : (y + 1) * (rowBytes + 1) ≤ h * (rowBytes + 1) :=
          Nat.mul_le_mul_right (rowBytes + 1) hy
        have hmul' : (y + 1) * (rowBytes + 1) ≤ raw.size := by
          simpa [hraw] using hmul
        have hcalc : y * (rowBytes + 1) + 1 + rowBytes = (y + 1) * (rowBytes + 1) := by
          calc
            y * (rowBytes + 1) + 1 + rowBytes =
                y * (rowBytes + 1) + (rowBytes + 1) := by omega
            _ = (y + 1) * (rowBytes + 1) := by
                  simp [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm]
        simpa [hcalc] using hmul'
      have hi'' : (y + 1) * (rowBytes + 1) ≤ i := by
        exact Nat.le_trans (by omega) hi
      have hraw' :
          (encodeRawPrefix data rowBytes y raw).size = raw.size :=
        encodeRawPrefix_size (data := data) (rowBytes := rowBytes) (h := h) (y := y)
          (raw := raw) hdata hraw hy'
      have hi_dest : i < (encodeRawPrefix data rowBytes y raw).size := by
        simpa [hraw'] using hi'
      have hcopy :
          (data.copySlice (y * rowBytes) (encodeRawPrefix data rowBytes y raw)
              (y * (rowBytes + 1) + 1) rowBytes)[i]'(by
                have hsize :=
                  byteArray_copySlice_size (src := data) (dest := encodeRawPrefix data rowBytes y raw)
                    (srcOff := y * rowBytes) (destOff := y * (rowBytes + 1) + 1) (len := rowBytes)
                    hsrc (by simpa [hraw'] using hdest)
                simpa [hsize] using hi_dest) =
            (encodeRawPrefix data rowBytes y raw)[i]'hi_dest := by
        have hge : y * (rowBytes + 1) + 1 + rowBytes ≤ i := by
          have hcalc : y * (rowBytes + 1) + 1 + rowBytes = (y + 1) * (rowBytes + 1) := by
            calc
              y * (rowBytes + 1) + 1 + rowBytes =
                  y * (rowBytes + 1) + (rowBytes + 1) := by omega
              _ = (y + 1) * (rowBytes + 1) := by
                    simp [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm]
          simpa [hcalc] using hi''
        exact
          byteArray_copySlice_get_of_ge (src := data) (dest := encodeRawPrefix data rowBytes y raw)
            (srcOff := y * rowBytes) (destOff := y * (rowBytes + 1) + 1) (len := rowBytes)
            (i := i) hsrc (by simpa [hraw'] using hdest) hge hi_dest
      have hle :
          y * (rowBytes + 1) ≤ (y + 1) * (rowBytes + 1) := by
        calc
          y * (rowBytes + 1) ≤ y * (rowBytes + 1) + (rowBytes + 1) := Nat.le_add_right _ _
          _ = (y + 1) * (rowBytes + 1) := by
                simp [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm]
      have hrec :=
        ih hy' (Nat.le_trans hle hi)
      have hrec' :
          (encodeRawPrefix data rowBytes y raw)[i]'hi_dest = raw[i]'hi' := by
        simpa [hraw'] using hrec
      simp [encodeRawPrefix, hcopy, hrec']

-- Filter bytes in the raw encoding are zero.
lemma encodeRaw_filter_zero {px : Type u} [Pixel px] (bmp : Bitmap px) (y : Nat) (hy : y < bmp.size.height) :
    let w := bmp.size.width
    let rowBytes := w * Pixel.bytesPerPixel (α := px)
    (encodeRaw bmp).get! (y * (rowBytes + 1)) = 0 := by
  let w := bmp.size.width
  let h := bmp.size.height
  let rowBytes := w * Pixel.bytesPerPixel (α := px)
  let rawSize := h * (rowBytes + 1)
  let raw0 := ByteArray.mk (Array.replicate rawSize 0)
  have hdata : bmp.data.size = h * rowBytes := by
    calc
      bmp.data.size = w * h * Pixel.bytesPerPixel (α := px) := bmp.valid
      _ = h * (w * Pixel.bytesPerPixel (α := px)) := by
            simp [Nat.mul_left_comm, Nat.mul_assoc]
      _ = h * rowBytes := by simp [rowBytes]
  have hraw0 : raw0.size = h * (rowBytes + 1) := by
    simp [raw0, rawSize, ByteArray.size, Array.size_replicate]
  have hy' : y ≤ h := Nat.le_of_lt hy
  let outOff := y * (rowBytes + 1)
  let rawPrefix := encodeRawPrefix bmp.data rowBytes y raw0
  have hrawPrefixSize : rawPrefix.size = h * (rowBytes + 1) := by
    have hsize :=
      encodeRawPrefix_size (data := bmp.data) (rowBytes := rowBytes) (h := h) (y := y)
        (raw := raw0) hdata hraw0 hy'
    simpa [hraw0] using hsize
  have hdef :
      encodeRawLoop bmp.data rowBytes h 0 raw0 =
        encodeRawLoop bmp.data rowBytes h y rawPrefix := by
    exact encodeRawLoop_eq_prefix (data := bmp.data) (rowBytes := rowBytes) (h := h) (y := y)
      (raw := raw0) hy'
  have hoff' : outOff < h * (rowBytes + 1) := by
    have hmul : y * (rowBytes + 1) < h * (rowBytes + 1) :=
      Nat.mul_lt_mul_of_pos_right hy (by omega)
    simpa [outOff] using hmul
  have hoff : outOff < rawPrefix.size := by
    simpa [hrawPrefixSize] using hoff'
  have hlen : outOff + 1 ≤ rawPrefix.size := Nat.succ_le_of_lt hoff
  have hsize_loop :
      (encodeRawLoop bmp.data rowBytes h y rawPrefix).size = rawPrefix.size := by
    exact
      encodeRawLoop_size (data := bmp.data) (rowBytes := rowBytes) (h := h) (y := y)
        (raw := rawPrefix) hdata hrawPrefixSize
  have hlen_loop : outOff + 1 ≤ (encodeRawLoop bmp.data rowBytes h y rawPrefix).size := by
    simpa [hsize_loop] using hlen
  have hprefix' :
      (encodeRawLoop bmp.data rowBytes h y rawPrefix).extract 0 (outOff + 1) =
        rawPrefix.extract 0 (outOff + 1) := by
    have hle : outOff + 1 ≤ outOff + 1 := by omega
    simpa [outOff] using
      (encodeRawLoop_preserve_prefix (data := bmp.data) (rowBytes := rowBytes) (h := h) (y := y)
        (raw := rawPrefix) hdata hrawPrefixSize (outOff + 1) hle)
  have hslice :
      (encodeRawLoop bmp.data rowBytes h y rawPrefix).extract outOff (outOff + 1) =
        rawPrefix.extract outOff (outOff + 1) := by
    exact
      byteArray_extract_eq_of_prefix_eq
        (a := encodeRawLoop bmp.data rowBytes h y rawPrefix) (b := rawPrefix)
        (n := outOff + 1) (i := outOff) (j := outOff + 1) hprefix' (by omega)
  have hget_left! :
      (encodeRawLoop bmp.data rowBytes h y rawPrefix).get! outOff = rawPrefix.get! outOff := by
    have hslice0 := congrArg (fun b => b.get! 0) hslice
    calc
      (encodeRawLoop bmp.data rowBytes h y rawPrefix).get! outOff =
          ((encodeRawLoop bmp.data rowBytes h y rawPrefix).extract outOff (outOff + 1)).get! 0 := by
            simpa using
              (byteArray_get!_extract0 (a := encodeRawLoop bmp.data rowBytes h y rawPrefix)
                (start := outOff) hlen_loop).symm
      _ = (rawPrefix.extract outOff (outOff + 1)).get! 0 := by
            simpa using hslice0
      _ = rawPrefix.get! outOff := by
            simpa using (byteArray_get!_extract0 (a := rawPrefix) (start := outOff) hlen)
  have hoff0 : outOff < raw0.size := by
    simpa [hraw0, outOff] using hoff'
  have hpre :
      rawPrefix.get! outOff = raw0.get! outOff := by
    have hpre' :=
      encodeRawPrefix_get_of_ge (data := bmp.data) (rowBytes := rowBytes) (h := h) (y := y)
        (i := outOff) (raw := raw0) hdata hraw0 hy' (by omega) hoff0
    calc
      rawPrefix.get! outOff = rawPrefix[outOff]'hoff := by
        simpa using (byteArray_get!_eq_get (a := rawPrefix) (i := outOff) hoff)
      _ = raw0[outOff]'hoff0 := by
        simpa [rawPrefix] using hpre'
      _ = raw0.get! outOff := by
        simpa using (byteArray_get!_eq_get (a := raw0) (i := outOff) hoff0).symm
  have hraw0get : raw0.get! outOff = 0 := by
    have hraw0get' : raw0[outOff]'hoff0 = 0 := by
      have hoff0' : outOff < (Array.replicate rawSize (0 : UInt8)).size := by
        simpa [raw0, ByteArray.size, Array.size_replicate] using hoff0
      simp [raw0, outOff, -Array.getElem_replicate]
      exact Array.getElem_replicate (n := rawSize) (v := (0 : UInt8)) (i := outOff) hoff0'
    calc
      raw0.get! outOff = raw0[outOff]'hoff0 := by
        simpa using (byteArray_get!_eq_get (a := raw0) (i := outOff) hoff0)
      _ = 0 := hraw0get'
  have hresult :
      (encodeRawLoop bmp.data rowBytes h y rawPrefix).get! outOff = 0 := by
    calc
      (encodeRawLoop bmp.data rowBytes h y rawPrefix).get! outOff = rawPrefix.get! outOff := hget_left!
      _ = raw0.get! outOff := hpre
      _ = 0 := hraw0get
  have hresult0 :
      (encodeRawLoop bmp.data rowBytes h 0 raw0).get! outOff = 0 := by
    simpa [hdef] using hresult
  simpa [encodeRaw, outOff, raw0, rawSize] using hresult0

-- Unfiltering a row preserves its length.
lemma unfilterRow_size (filter : UInt8) (row prev : ByteArray) (bpp : Nat)
    (hfilter : filter.toNat ≤ 4) :
    (unfilterRow filter row prev bpp hfilter).size = row.size := by
  -- Rewrite the loop to a fold over the range list.
  unfold unfilterRow
  simp [Std.Range.forIn_eq_forIn_range']
  -- Folding with `push` adds one element per iteration.
  have hfold :
      ∀ (xs : List Nat) (f : ByteArray → Nat → UInt8) (out : ByteArray),
        (List.foldl (fun out i => out.push (f out i)) out xs).size = out.size + xs.length := by
    intro xs f out
    induction xs generalizing out with
    | nil => simp
    | cons i xs ih =>
        have ih' := ih (out := out.push (f out i))
        simpa [ByteArray.size_push, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih'
  -- Apply the generic fold-size lemma and reduce the range length.
  simpa using hfold (List.range' 0 row.size 1) (fun out i =>
    let raw := row.get! i
    let a := if i >= bpp then out.get! (i - bpp) else (0 : UInt8)
    let b := if i < prev.size then prev.get! i else (0 : UInt8)
    let c := if i >= bpp && i < prev.size then prev.get! (i - bpp) else (0 : UInt8)
    let recon :=
      match filter.toNat with
      | 0 => raw
      | 1 => u8 (raw.toNat + a.toNat)
      | 2 => u8 (raw.toNat + b.toNat)
      | 3 => u8 (raw.toNat + ((a.toNat + b.toNat) / 2))
      | 4 => u8 (raw.toNat + paethPredictor a.toNat b.toNat c.toNat)
      | _ => raw
    recon) ByteArray.empty

-- Decoding helpers: raw offsets stay in bounds.
lemma decodeRowsLoop_offset_lt_raw
    (raw : ByteArray) (rowBytes h y : Nat)
    (hraw : raw.size = h * (rowBytes + 1)) (hy : y < h) :
    y * (rowBytes + 1) < raw.size := by
  have hmul : y * (rowBytes + 1) < h * (rowBytes + 1) :=
    Nat.mul_lt_mul_of_pos_right hy (by omega)
  simpa [hraw] using hmul

-- Decoding helpers: per-row slice fits in the raw buffer.
lemma decodeRowsLoop_rowData_bound
    (raw : ByteArray) (rowBytes h y : Nat)
    (hraw : raw.size = h * (rowBytes + 1)) (hy : y < h) :
    y * (rowBytes + 1) + 1 + rowBytes ≤ raw.size := by
  have hy' : y + 1 ≤ h := Nat.succ_le_of_lt hy
  have hmul : (y + 1) * (rowBytes + 1) ≤ h * (rowBytes + 1) :=
    Nat.mul_le_mul_right (rowBytes + 1) hy'
  have hmul' : (y + 1) * (rowBytes + 1) ≤ raw.size := by
    simpa [hraw] using hmul
  have hcalc : y * (rowBytes + 1) + 1 + rowBytes = (y + 1) * (rowBytes + 1) := by
    simp [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm]
  simpa [hcalc] using hmul'

-- Decoding helpers: the extracted row slice has the expected length.
lemma decodeRowsLoop_rowData_size
    (raw : ByteArray) (rowBytes h y : Nat)
    (hraw : raw.size = h * (rowBytes + 1)) (hy : y < h) :
    (raw.extract (y * (rowBytes + 1) + 1) (y * (rowBytes + 1) + 1 + rowBytes)).size = rowBytes := by
  have hdest :
      y * (rowBytes + 1) + 1 + rowBytes ≤ raw.size :=
    decodeRowsLoop_rowData_bound (raw := raw) (rowBytes := rowBytes) (h := h) (y := y) hraw hy
  simp [ByteArray.size_extract, Nat.min_eq_left hdest]

-- Decoding helpers: per-row destination offset fits in the pixel buffer.
lemma decodeRowsLoop_rowOffset_le_pixels
    (pixels : ByteArray) (rowBytes h y : Nat)
    (hpixels : pixels.size = h * rowBytes) (hy : y < h) :
    y * rowBytes + rowBytes ≤ pixels.size := by
  have hy' : y + 1 ≤ h := Nat.succ_le_of_lt hy
  have hmul : (y + 1) * rowBytes ≤ h * rowBytes :=
    Nat.mul_le_mul_right rowBytes hy'
  have hmul' : (y + 1) * rowBytes ≤ pixels.size := by
    simpa [hpixels] using hmul
  have hcalc : y * rowBytes + rowBytes = (y + 1) * rowBytes := by
    simp [Nat.add_mul, Nat.one_mul, Nat.add_comm]
  simpa [hcalc] using hmul'

-- Decoding helpers: per-row index is within bounds for RGB/RGBA rows.
lemma decodeRowsLoop_rowIndex_bound
    (w bpp x : Nat) (hx : x < w) (hbpp : bpp = 3 ∨ bpp = 4) :
    x * bpp + 2 < w * bpp := by
  cases hbpp with
  | inl hbpp =>
      subst hbpp
      omega
  | inr hbpp =>
      subst hbpp
      omega

-- Decoding helpers: pixel buffer index is within the RGB output size.
lemma decodeRowsLoop_pixBase_bound
    (pixels : ByteArray) (w h x y : Nat)
    (hx : x < w) (hy : y < h)
    (hpixels : pixels.size = w * h * bytesPerPixelRGB) :
    (y * w + x) * bytesPerPixelRGB + 2 < pixels.size := by
  have hPix0 :
      x + y * w < w * h :=
    arrayCoordSize_nat (i := x + y * w) (x := x) (y := y) (w := w) (h := h) hx hy rfl
  have hPix :
      y * w + x < w * h := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hPix0
  have hPix' :
      (y * w + x) * bytesPerPixelRGB + 2 < w * h * bytesPerPixelRGB := by
    simp [bytesPerPixelRGB] at hPix ⊢
    omega
  simpa [hpixels] using hPix'

-- Bounds used by `decodeRowsLoop` for byte accesses on a given row.
lemma decodeRowsLoop_bounds
    (raw pixels : ByteArray) (w h bpp rowBytes y offset : Nat)
    (hraw : raw.size = h * (rowBytes + 1))
    (hrowBytes : rowBytes = w * bpp)
    (hbpp : bpp = 3 ∨ bpp = 4)
    (hpixels : pixels.size = w * h * bytesPerPixelRGB)
    (hoff : offset = y * (rowBytes + 1))
    (hy : y < h) :
    offset < raw.size ∧
    offset + 1 + rowBytes ≤ raw.size ∧
    (raw.extract (offset + 1) (offset + 1 + rowBytes)).size = rowBytes ∧
    (∀ x < w, x * bpp + 2 < rowBytes) ∧
    (∀ x < w, (y * w + x) * bytesPerPixelRGB + 2 < pixels.size) ∧
    (bpp = 3 → y * rowBytes + rowBytes ≤ pixels.size) := by
  have hofflt : offset < raw.size := by
    have h := decodeRowsLoop_offset_lt_raw (raw := raw) (rowBytes := rowBytes) (h := h) (y := y) hraw hy
    simpa [hoff] using h
  have hrowBound : offset + 1 + rowBytes ≤ raw.size := by
    have h := decodeRowsLoop_rowData_bound (raw := raw) (rowBytes := rowBytes) (h := h) (y := y) hraw hy
    simpa [hoff] using h
  have hrowSize :
      (raw.extract (offset + 1) (offset + 1 + rowBytes)).size = rowBytes := by
    have h := decodeRowsLoop_rowData_size (raw := raw) (rowBytes := rowBytes) (h := h) (y := y) hraw hy
    simpa [hoff] using h
  have hrowIndex : ∀ x < w, x * bpp + 2 < rowBytes := by
    intro x hx
    have h := decodeRowsLoop_rowIndex_bound (w := w) (bpp := bpp) (x := x) hx hbpp
    simpa [hrowBytes] using h
  have hpixBase : ∀ x < w, (y * w + x) * bytesPerPixelRGB + 2 < pixels.size := by
    intro x hx
    exact decodeRowsLoop_pixBase_bound (pixels := pixels) (w := w) (h := h) (x := x) (y := y) hx hy hpixels
  have hrowOffset : bpp = 3 → y * rowBytes + rowBytes ≤ pixels.size := by
    intro hbpp3
    subst hbpp3
    have hrowBytes' : rowBytes = w * 3 := by
      simpa using hrowBytes
    have hpixels' : pixels.size = h * rowBytes := by
      calc
        pixels.size = w * h * bytesPerPixelRGB := hpixels
        _ = w * h * 3 := by simp [bytesPerPixelRGB]
        _ = h * (w * 3) := by
              simp [Nat.mul_left_comm, Nat.mul_assoc]
        _ = h * rowBytes := by simp [hrowBytes']
    exact decodeRowsLoop_rowOffset_le_pixels (pixels := pixels) (rowBytes := rowBytes) (h := h) (y := y) hpixels' hy
  exact ⟨hofflt, hrowBound, hrowSize, hrowIndex, hpixBase, hrowOffset⟩

-- The initial `decodeRowsLoop` call in `decodeBitmap` satisfies the bounds required for safe access.
lemma decodeBitmap_decodeRowsLoop_bounds
    (hdr : PngHeader) (raw : ByteArray)
    (hbpp : hdr.colorType = 2 ∨ hdr.colorType = 6)
    (hraw : raw.size = hdr.height * (hdr.width * (if hdr.colorType == 2 then 3 else 4) + 1)) :
    let bpp := if hdr.colorType == 2 then 3 else 4
    let rowBytes := hdr.width * bpp
    let pixels0 := ByteArray.mk <| Array.replicate (hdr.width * hdr.height * bytesPerPixelRGB) 0
    ∀ y < hdr.height,
      let offset := y * (rowBytes + 1)
      offset < raw.size ∧
      offset + 1 + rowBytes ≤ raw.size ∧
      (raw.extract (offset + 1) (offset + 1 + rowBytes)).size = rowBytes ∧
      (∀ x < hdr.width, x * bpp + 2 < rowBytes) ∧
      (∀ x < hdr.width, (y * hdr.width + x) * bytesPerPixelRGB + 2 < pixels0.size) ∧
      (bpp = 3 → y * rowBytes + rowBytes ≤ pixels0.size) := by
  intro bpp rowBytes pixels0 y hy offset
  have hbpp' : bpp = 3 ∨ bpp = 4 := by
    cases hbpp with
    | inl h2 => simp [bpp, h2]
    | inr h6 => simp [bpp, h6]
  have hrowBytes : rowBytes = hdr.width * bpp := by rfl
  have hpixels : pixels0.size = hdr.width * hdr.height * bytesPerPixelRGB := by
    simp [pixels0, ByteArray.size, Array.size_replicate]
  have hraw' : raw.size = hdr.height * (rowBytes + 1) := by
    simpa [rowBytes, bpp] using hraw
  have h :=
    decodeRowsLoop_bounds (raw := raw) (pixels := pixels0) (w := hdr.width) (h := hdr.height)
      (bpp := bpp) (rowBytes := rowBytes) (y := y) (offset := offset)
      hraw' hrowBytes hbpp' hpixels rfl hy
  simpa using h

-- No overflow: `decodeBitmap` passes bounds that keep `decodeRowsLoop` index-safe.
lemma decodeBitmap_no_overflow
    (hdr : PngHeader) (raw : ByteArray)
    (hbpp : hdr.colorType = 2 ∨ hdr.colorType = 6)
    (hraw : raw.size = hdr.height * (hdr.width * (if hdr.colorType == 2 then 3 else 4) + 1)) :
    let bpp := if hdr.colorType == 2 then 3 else 4
    let rowBytes := hdr.width * bpp
    let pixels0 := ByteArray.mk <| Array.replicate (hdr.width * hdr.height * bytesPerPixelRGB) 0
    ∀ y < hdr.height,
      let offset := y * (rowBytes + 1)
      offset < raw.size ∧
      offset + 1 + rowBytes ≤ raw.size ∧
      (raw.extract (offset + 1) (offset + 1 + rowBytes)).size = rowBytes ∧
      (∀ x < hdr.width, x * bpp + 2 < rowBytes) ∧
      (∀ x < hdr.width, (y * hdr.width + x) * bytesPerPixelRGB + 2 < pixels0.size) ∧
      (bpp = 3 → y * rowBytes + rowBytes ≤ pixels0.size) := by
  simpa using decodeBitmap_decodeRowsLoop_bounds (hdr := hdr) (raw := raw) hbpp hraw

-- Decoding the raw encoding reconstructs the original pixels.
lemma decodeRowsLoopCore_encodeRaw {px : Type u} [Pixel px]
    (bmp : Bitmap px) (convert : ByteArray -> Nat -> Nat -> Nat -> ByteArray -> ByteArray) :
    let w := bmp.size.width
    let h := bmp.size.height
    let bpp := Pixel.bytesPerPixel (α := px)
    let rowBytes := w * bpp
    let raw := encodeRaw bmp
    let pixels0 := ByteArray.mk <| Array.replicate (h * rowBytes) 0
    let loop := decodeRowsLoopCore raw w h bpp rowBytes bpp convert
    loop 0 0 ByteArray.empty pixels0 = some bmp.data := by
  let w := bmp.size.width
  let h := bmp.size.height
  let bpp := Pixel.bytesPerPixel (α := px)
  let rowBytes := w * bpp
  let raw := encodeRaw bmp
  let pixels0 := ByteArray.mk <| Array.replicate (h * rowBytes) 0
  let loop := decodeRowsLoopCore raw w h bpp rowBytes bpp convert
  have hdata : bmp.data.size = h * rowBytes := by
    calc
      bmp.data.size = w * h * Pixel.bytesPerPixel (α := px) := bmp.valid
      _ = h * (w * Pixel.bytesPerPixel (α := px)) := by
            simp [Nat.mul_left_comm, Nat.mul_assoc]
      _ = h * rowBytes := by simp [rowBytes, bpp]
  have hraw : raw.size = h * (rowBytes + 1) := by
    simpa [w, h, rowBytes] using encodeRaw_size bmp
  have hpixels0 : pixels0.size = h * rowBytes := by
    simp [pixels0, ByteArray.size, Array.size_replicate]
  have hk :
      ∀ k, ∀ y offset prevRow pixels,
        h - y = k →
        offset = y * (rowBytes + 1) →
        pixels.size = h * rowBytes →
        pixels.extract 0 (y * rowBytes) = bmp.data.extract 0 (y * rowBytes) →
        loop y offset prevRow pixels = some bmp.data := by
    intro k
    induction k with
    | zero =>
        intro y offset prevRow pixels hk hoff hpix hprefix
        have hy : h ≤ y := Nat.le_of_sub_eq_zero hk
        have hlt : ¬ y < h := not_lt_of_ge hy
        have hsize : pixels.size = bmp.data.size := by
          simpa [hdata] using hpix
        have hle : pixels.size ≤ y * rowBytes := by
          have hmul : h * rowBytes ≤ y * rowBytes :=
            Nat.mul_le_mul_right rowBytes hy
          simpa [hpix] using hmul
        have hprefix' :
            pixels.extract 0 pixels.size = bmp.data.extract 0 pixels.size := by
          have hpre :=
            byteArray_extract_eq_of_prefix_eq
              (a := pixels) (b := bmp.data) (n := y * rowBytes) (i := 0) (j := pixels.size)
              hprefix (by simpa [hsize] using hle)
          simpa using hpre
        have hpix_eq : pixels = bmp.data := by
          have hpix0 : pixels.extract 0 pixels.size = pixels := by
            simp [ByteArray.extract_zero_size]
          have hdata0 : bmp.data.extract 0 pixels.size = bmp.data := by
            have hdata0' : bmp.data.extract 0 bmp.data.size = bmp.data := by
              simp [ByteArray.extract_zero_size]
            simp [hsize, hdata0']
          simpa [hpix0, hdata0] using hprefix'
        simp [loop, decodeRowsLoopCore, hlt, hpix_eq]
    | succ k ih =>
        intro y offset prevRow pixels hk hoff hpix hprefix
        have hlt : y < h := Nat.lt_of_sub_eq_succ hk
        have hy : y + 1 ≤ h := Nat.succ_le_of_lt hlt
        have hofflt : offset < raw.size := by
          have hmul : y * (rowBytes + 1) < h * (rowBytes + 1) :=
            Nat.mul_lt_mul_of_pos_right hlt (by omega)
          simpa [hoff, hraw] using hmul
        have hfilter0 : raw.get! offset = 0 := by
          simpa [raw, w, h, rowBytes, hoff] using
            (encodeRaw_filter_zero (bmp := bmp) (y := y) hlt)
        have hfilter : (raw.get! offset).toNat ≤ 4 := by
          simp [hfilter0]
        have hrowData :
            raw.extract (offset + 1) (offset + 1 + rowBytes) =
              bmp.data.extract (y * rowBytes) (y * rowBytes + rowBytes) := by
          simpa [w, h, rowBytes, hoff] using
            (encodeRaw_row_extract (bmp := bmp) (y := y) hlt)
        let rowData := raw.extract (offset + 1) (offset + 1 + rowBytes)
        have hrowData' :
            rowData = bmp.data.extract (y * rowBytes) (y * rowBytes + rowBytes) := by
          simpa [rowData] using hrowData
        have hrowDataSize : rowData.size = rowBytes := by
          have hdest : offset + 1 + rowBytes ≤ raw.size := by
            have hmul : (y + 1) * (rowBytes + 1) ≤ h * (rowBytes + 1) :=
              Nat.mul_le_mul_right (rowBytes + 1) hy
            have hmul' : (y + 1) * (rowBytes + 1) ≤ raw.size := by
              simpa [hraw] using hmul
            have hcalc : offset + 1 + rowBytes = (y + 1) * (rowBytes + 1) := by
              calc
                offset + 1 + rowBytes = y * (rowBytes + 1) + (rowBytes + 1) := by
                  simp [hoff, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                _ = (y + 1) * (rowBytes + 1) := by
                  simp [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm]
            simpa [hcalc] using hmul'
          simp [rowData, ByteArray.size_extract, Nat.min_eq_left hdest]
        have hdestPix : y * rowBytes + rowBytes ≤ pixels.size := by
          have hmul : (y + 1) * rowBytes ≤ h * rowBytes :=
            Nat.mul_le_mul_right rowBytes hy
          have hmul' : (y + 1) * rowBytes ≤ pixels.size := by
            simpa [hpix] using hmul
          simpa [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm] using hmul'
        let rowOffset := y * rowBytes
        let pixels' := rowData.copySlice 0 pixels rowOffset rowBytes
        have hmid :
            pixels'.extract rowOffset (rowOffset + rowBytes) =
              bmp.data.extract (y * rowBytes) (y * rowBytes + rowBytes) := by
          have hsrc : 0 + rowBytes ≤ rowData.size := by
            simp [hrowDataSize]
          have hdest : rowOffset + rowBytes ≤ pixels.size := hdestPix
          have hrowData0 : rowData.extract 0 rowBytes = rowData := by
            have hsize : rowData.size = rowBytes := hrowDataSize
            have hzero :
                rowData.extract 0 rowData.size = rowData := by
              simp [ByteArray.extract_zero_size]
            simpa [hsize] using hzero
          calc
            pixels'.extract rowOffset (rowOffset + rowBytes) =
                rowData.extract 0 rowBytes := by
                  simpa [pixels', rowOffset] using
                    byteArray_copySlice_extract_mid (src := rowData) (dest := pixels)
                      (srcOff := 0) (destOff := rowOffset) (len := rowBytes) hsrc hdest
            _ = rowData := hrowData0
            _ = bmp.data.extract (y * rowBytes) (y * rowBytes + rowBytes) := hrowData'
        have hpre' :
            pixels'.extract 0 rowOffset = pixels.extract 0 rowOffset := by
          have hdest : rowOffset + rowBytes ≤ pixels.size := hdestPix
          simpa [pixels', rowOffset] using
            byteArray_copySlice_extract_prefix (src := rowData) (dest := pixels)
              (srcOff := 0) (destOff := rowOffset) (len := rowBytes) hdest
        have hprefix' :
            pixels'.extract 0 ((y + 1) * rowBytes) =
              bmp.data.extract 0 ((y + 1) * rowBytes) := by
          have hnm : rowOffset ≤ rowOffset + rowBytes := by omega
          have ha : rowOffset + rowBytes ≤ pixels'.size := by
            have hsize : pixels'.size = pixels.size := by
              have hsrc : 0 + rowBytes ≤ rowData.size := by
                simp [hrowDataSize]
              have hdest : rowOffset + rowBytes ≤ pixels.size := hdestPix
              simpa [pixels'] using
                byteArray_copySlice_size (src := rowData) (dest := pixels) (srcOff := 0)
                  (destOff := rowOffset) (len := rowBytes) hsrc hdest
            simpa [hsize] using hdestPix
          have hb : rowOffset + rowBytes ≤ bmp.data.size := by
            have hmul : (y + 1) * rowBytes ≤ h * rowBytes :=
              Nat.mul_le_mul_right rowBytes hy
            simpa [hdata, rowOffset, Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm] using hmul
          have hpref :
              pixels'.extract 0 rowOffset = bmp.data.extract 0 rowOffset := by
            simpa [rowOffset] using hpre'.trans hprefix
          have hprefix'' :
              pixels'.extract 0 (rowOffset + rowBytes) =
                bmp.data.extract 0 (rowOffset + rowBytes) := by
            exact
              byteArray_extract_prefix_extend (a := pixels') (b := bmp.data) (n := rowOffset)
                (m := rowOffset + rowBytes) hnm ha hb hpref hmid
          simpa [rowOffset, Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm] using hprefix''
        have hk' : h - (y + 1) = k := by
          have hsum : h = Nat.succ k + y := Nat.eq_add_of_sub_eq (Nat.le_of_lt hlt) hk
          calc
            h - (y + 1) = (Nat.succ k + y) - (y + 1) := by simp [hsum]
            _ = k := by omega
        have hoff' : offset + 1 + rowBytes = (y + 1) * (rowBytes + 1) := by
          calc
            offset + 1 + rowBytes = y * (rowBytes + 1) + (rowBytes + 1) := by
              simp [hoff, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            _ = (y + 1) * (rowBytes + 1) := by
              simp [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm]
        have hoff'' : offset + 1 + rowBytes = (y + 1) * (rowBytes + 1) := hoff'
        have hnext :
            loop (y + 1) (offset + 1 + rowBytes) rowData pixels' = some bmp.data := by
          have hsize' : pixels'.size = h * rowBytes := by
            have hsrc : 0 + rowBytes ≤ rowData.size := by
              simp [hrowDataSize]
            have hdest : rowOffset + rowBytes ≤ pixels.size := hdestPix
            have hsize'' : pixels'.size = pixels.size := by
              simpa [pixels'] using
                byteArray_copySlice_size (src := rowData) (dest := pixels)
                  (srcOff := 0) (destOff := rowOffset) (len := rowBytes) hsrc hdest
            simpa [hpix] using hsize''
          have hoffn : offset + 1 + rowBytes = (y + 1) * (rowBytes + 1) := hoff''
          exact ih (y := y + 1) (offset := offset + 1 + rowBytes) (prevRow := rowData)
            (pixels := pixels') hk' hoffn hsize' hprefix'
        have hgoal :
            loop y offset prevRow pixels =
              loop (y + 1) (offset + 1 + rowBytes) rowData pixels' := by
          dsimp [loop]
          rw [decodeRowsLoopCore.eq_1]
          simp [hlt, hfilter0, rowData, rowOffset, pixels']
        exact hgoal.trans hnext
  have hstart :=
    hk (h - 0) (y := 0) (offset := 0) (prevRow := ByteArray.empty) (pixels := pixels0)
      rfl (by simp) hpixels0 (by simp)
  simpa using hstart

-- Decoding the raw encoding reconstructs the original RGB pixels.
lemma decodeRowsLoop_encodeRaw (bmp : BitmapRGB8) :
    let w := bmp.size.width
    let h := bmp.size.height
    let rowBytes := w * bytesPerPixelRGB
    let raw := encodeRaw bmp
    let pixels0 := ByteArray.mk <| Array.replicate (h * rowBytes) 0
    decodeRowsLoop raw w h bytesPerPixelRGB rowBytes 0 0 ByteArray.empty pixels0 = some bmp.data := by
  simpa [decodeRowsLoop, bytesPerPixel_rgb, bytesPerPixelRGB] using
    (decodeRowsLoopCore_encodeRaw (bmp := bmp) (convert := decodeRowDropAlpha))

-- Decoding the raw encoding reconstructs the original RGBA pixels.
lemma decodeRowsLoopRGBA_encodeRaw (bmp : BitmapRGBA8) :
    let w := bmp.size.width
    let h := bmp.size.height
    let rowBytes := w * bytesPerPixelRGBA
    let raw := encodeRaw bmp
    let pixels0 := ByteArray.mk <| Array.replicate (h * rowBytes) 0
    decodeRowsLoopRGBA raw w h bytesPerPixelRGBA rowBytes 0 0 ByteArray.empty pixels0 = some bmp.data := by
  simpa [decodeRowsLoopRGBA, bytesPerPixel_rgba, bytesPerPixelRGBA] using
    (decodeRowsLoopCore_encodeRaw (bmp := bmp) (convert := decodeRowAddAlpha))

-- Decoding the raw encoding reconstructs the original grayscale pixels.
lemma decodeRowsLoopGray_encodeRaw (bmp : BitmapGray8) :
    let w := bmp.size.width
    let h := bmp.size.height
    let rowBytes := w * bytesPerPixelGray
    let raw := encodeRaw bmp
    let pixels0 := ByteArray.mk <| Array.replicate (h * rowBytes) 0
    decodeRowsLoopGray raw w h bytesPerPixelGray rowBytes 0 0 ByteArray.empty pixels0 = some bmp.data := by
  simpa [decodeRowsLoopGray, bytesPerPixel_gray, bytesPerPixelGray] using
    (decodeRowsLoopCore_encodeRaw (bmp := bmp) (convert := decodeRowGray))


end Lemmas
end Bitmaps
