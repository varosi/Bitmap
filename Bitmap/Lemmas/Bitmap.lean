import Bitmap.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Nat.Bitwise.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.ByteArray.Lemmas
import Init.Data.Range.Lemmas
import Init.Data.UInt.Lemmas
import Batteries.Data.ByteArray
import Bitmap.Lemmas.Png.EncodeDecode

universe u

namespace Bitmaps

namespace Lemmas

open Png

-- Setting a byte does not change the buffer size.
@[simp] lemma byteArray_size_set
    {bs : ByteArray} {i : Nat} (h : i < bs.size) {v : UInt8} :
    (bs.set i v h).size = bs.size := by
  cases bs with
  | mk arr =>
      simp [ByteArray.set, ByteArray.size, Array.size_set]

-- Getting the byte just set yields the new value.
@[simp] lemma byteArray_get_set_self
    {bs : ByteArray} {i : Nat} (h : i < bs.size) {v : UInt8} :
    (bs.set i v h).get i (by simpa [byteArray_size_set] using h) = v := by
  cases bs with
  | mk arr =>
      simp [ByteArray.set, ByteArray.get]

-- Getting the byte just set yields the new value (explicit bounds).
@[simp] lemma byteArray_get_set_self'
    {bs : ByteArray} {i : Nat} (h : i < bs.size) {v : UInt8}
    (h' : i < (bs.set i v h).size) :
    (bs.set i v h).get i h' = v := by
  cases bs with
  | mk arr =>
      simp [ByteArray.set, ByteArray.get]

-- Getting a different index after setting preserves the old value (explicit bounds).
lemma byteArray_get_set_ne'
    {bs : ByteArray} {i j : Nat} (hi : i < bs.size) (hj : j < bs.size)
    (hij : i ≠ j) {v : UInt8} (h' : j < (bs.set i v hi).size) :
    (bs.set i v hi).get j h' = bs.get j hj := by
  cases bs with
  | mk arr =>
      simpa [ByteArray.set, ByteArray.get] using
        (Array.getElem_set_ne (xs := arr) (i := i) (j := j) (h' := hi) (pj := hj) (h := hij))

-- Getting the byte just set yields the new value (alternate proof of bounds).
-- `getElem` is proof-irrelevant for ByteArrays.
@[simp] lemma byteArray_getElem_eq {bs : ByteArray} {i : Nat} (h1 h2 : i < bs.size) :
    bs[i]'h1 = bs[i]'h2 := by
  rfl


-- Writing an RGB8 pixel does not change the buffer size.
lemma pixelWriteRGB8_size
    (data : ByteArray) (base : Nat) (h : base + 2 < data.size) (px : PixelRGB8) :
    (pixelWriteRGB8 data base h px).size = data.size := by
  cases data with
  | mk arr =>
      simp [pixelWriteRGB8, ByteArray.set, ByteArray.size, Array.size_set]

-- Writing an RGBA8 pixel does not change the buffer size.
lemma pixelWriteRGBA8_size
    (data : ByteArray) (base : Nat) (h : base + 3 < data.size) (px : PixelRGBA8) :
    (pixelWriteRGBA8 data base h px).size = data.size := by
  cases data with
  | mk arr =>
      simp [pixelWriteRGBA8, ByteArray.set, ByteArray.size, Array.size_set]

-- Writing a grayscale pixel does not change the buffer size.
lemma pixelWriteGray8_size
    (data : ByteArray) (base : Nat) (h : base < data.size) (px : PixelGray8) :
    (pixelWriteGray8 data base h px).size = data.size := by
  cases data with
  | mk arr =>
      simp [pixelWriteGray8, ByteArray.set, ByteArray.size, Array.size_set]

-------------------------------------------------------------------------------
-- Verification. Converting tests into proofs.
-- https://lean-lang.org/theorem_proving_in_lean4/tactics.html

variable (aPixel : PixelRGB8)

example [Pixel PixelRGB8] :
    (mkBlankBitmap 1 1 aPixel).data.size =
      (mkBlankBitmap 1 1 aPixel).size.width *
        (mkBlankBitmap 1 1 aPixel).size.height *
        Pixel.bytesPerPixel (α := PixelRGB8) := by
  simpa using (mkBlankBitmap 1 1 aPixel).valid


-- Writing a pixel then reading it back yields the same pixel.
lemma getPixel_putPixel_eq
    {px : Type} [Pixel px]
    (img : Bitmap px) (x y : Nat) (pixel : px)
    (hx : x < img.size.width) (hy : y < img.size.height) :
    getPixel (putPixel img x y pixel hx hy) x y
      (by simpa using hx) (by simpa using hy) = pixel := by
  simp [getPixel, putPixel, Pixel.read_write]

-- Round-trip PNG encode/decode for bitmap payloads.
lemma decodeBitmap_encodeBitmap (bmp : BitmapRGB8)
    (hw : bmp.size.width < 2 ^ 32) (hh : bmp.size.height < 2 ^ 32)
    (mode : PngEncodeMode)
    (hidat : (encodeBitmapIdat (bmp := bmp) (mode := mode)).size < 2 ^ 32) :
    Png.decodeBitmap (Png.encodeBitmap bmp hw hh mode) = some bmp := by
  have hidat_min : 6 ≤ (encodeBitmapIdat (bmp := bmp) (mode := mode)).size := by
    cases mode <;> simp [encodeBitmapIdat, zlibCompressStored_size_ge, zlibCompressFixed_size_ge]
  have hsize : 8 ≤ (encodeBitmap bmp hw hh mode).size := by
    have hsize' :
        (encodeBitmap bmp hw hh mode).size =
          (encodeBitmapIdat (bmp := bmp) (mode := mode)).size + 57 := by
      simpa [encodeBitmapIdat] using encodeBitmap_size (bmp := bmp) (hw := hw) (hh := hh) (mode := mode)
    omega
  have hmin : 2 ≤ (encodeBitmapIdat (bmp := bmp) (mode := mode)).size := by
    omega
  have hct :
      (PngPixel.colorType (α := PixelRGB8)).toNat = 0 ∨
        (PngPixel.colorType (α := PixelRGB8)).toNat = 2 ∨
        (PngPixel.colorType (α := PixelRGB8)).toNat = 6 := by
    have : (u8 2).toNat = 0 ∨ (u8 2).toNat = 2 ∨ (u8 2).toNat = 6 := by decide
    simpa [pngPixel_colorType_rgb] using this
  have hctProp : ¬(u8 2).toNat = 0 → ¬(u8 2).toNat = 2 → (u8 2).toNat = 6 := by
    decide
  have hparse := parsePng_encodeBitmap (bmp := bmp) (hw := hw) (hh := hh)
    (mode := mode) hidat hsize hct
  have hraw : (encodeRaw bmp).size =
      bmp.size.height * (bmp.size.width * bytesPerPixelRGB + 1) := by
    simpa using encodeRaw_size bmp
  have hraw' : (encodeRaw bmp).size =
      bmp.size.height * (bmp.size.width * 3 + 1) := by
    simpa [bytesPerPixelRGB] using hraw
  have hrows := decodeRowsLoop_encodeRaw (bmp := bmp)
  have hvalid : bmp.data.size = bmp.size.width * bmp.size.height * bytesPerPixelRGB := by
    simpa [bytesPerPixel_rgb, Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc] using bmp.valid
  have hrows' :
      decodeRowsLoop (encodeRaw bmp) bmp.size.width bmp.size.height bytesPerPixelRGB
          (bmp.size.width * bytesPerPixelRGB) 0 0 ByteArray.empty
          (ByteArray.mk <| Array.replicate (bmp.size.height * (bmp.size.width * bytesPerPixelRGB)) 0) =
        some bmp.data := by
    simpa [bytesPerPixelRGB] using hrows
  have hrows'' :
      decodeRowsLoop (encodeRaw bmp) bmp.size.width bmp.size.height 3 (bmp.size.width * 3) 0 0
          ByteArray.empty { data := Array.replicate (bmp.size.height * (bmp.size.width * 3)) 0 } =
        some bmp.data := by
    dsimp [bytesPerPixelRGB]
    simpa using hrows'
  have hrows''' :
      decodeRowsLoop (encodeRaw bmp) bmp.size.width bmp.size.height 3 (bmp.size.width * 3) 0 0
          ByteArray.empty { data := Array.replicate (bmp.size.width * bmp.size.height * 3) 0 } =
        some bmp.data := by
    simpa [Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc] using hrows''
  have hvalid' : bmp.data.size = bmp.size.width * bmp.size.height * 3 := by
    simpa [bytesPerPixelRGB] using hvalid
  -- Raw size check and row decoding.
  have hbpp : (if (u8 2).toNat = 0 then 1 else if (u8 2).toNat = 2 then 3 else 4) = 3 := by
    decide
  have hrawEq :
      (encodeRaw bmp).size =
        bmp.size.height * ((bmp.size.width * if (u8 2).toNat = 0 then 1 else if (u8 2).toNat = 2 then 3 else 4) + 1) := by
    simpa [hbpp] using hraw'
  have hrowsEq :
      ((decodeRowsLoop (encodeRaw bmp) bmp.size.width bmp.size.height
              (if (u8 2).toNat = 0 then 1 else if (u8 2).toNat = 2 then 3 else 4)
              (bmp.size.width * if (u8 2).toNat = 0 then 1 else if (u8 2).toNat = 2 then 3 else 4) 0 0 ByteArray.empty
              { data := Array.replicate (bmp.size.width * bmp.size.height * 3) 0 }).bind
          fun pixels ↦
          if h : pixels.size = bmp.size.width * bmp.size.height * 3 then
            some { size := { width := bmp.size.width, height := bmp.size.height }, data := pixels, valid := h }
          else none) =
        some bmp := by
    simp [hbpp, hrows''', hvalid']
  unfold Png.decodeBitmap
  -- Parse and header checks.
  cases mode with
  | stored =>
      have hminStored : 2 ≤ (zlibCompressStored (encodeRaw bmp)).size := by
        simpa [encodeBitmapIdat] using hmin
      simpa [hsize, hparse, zlibDecompressStored_zlibCompressStored, encodeBitmapIdat] using
        (And.intro hctProp (And.intro hminStored (And.intro hrawEq hrowsEq)))
  | fixed =>
      have hminFixed : 2 ≤ (zlibCompressFixed (encodeRaw bmp)).size := by
        simpa [encodeBitmapIdat] using hmin
      simpa [hsize, hparse,
        zlibDecompressStored_zlibCompressFixed_none, zlibDecompress_zlibCompressFixed,
        encodeBitmapIdat] using
        (And.intro hctProp (And.intro hminFixed (And.intro hrawEq hrowsEq)))

-- Round-trip PNG encode/decode for RGBA bitmap payloads.
lemma decodeBitmap_encodeBitmap_rgba (bmp : BitmapRGBA8)
    (hw : bmp.size.width < 2 ^ 32) (hh : bmp.size.height < 2 ^ 32)
    (mode : PngEncodeMode)
    (hidat : (encodeBitmapIdat (bmp := bmp) (mode := mode)).size < 2 ^ 32) :
    Png.decodeBitmap (Png.encodeBitmap bmp hw hh mode) = some bmp := by
  have hidat' :
      (encodeBitmapIdat (bmp := bmp) (mode := mode)).size < 2 ^ 32 := by
    simpa using hidat
  have hidat_min : 6 ≤ (encodeBitmapIdat (bmp := bmp) (mode := mode)).size := by
    cases mode <;> simp [encodeBitmapIdat, zlibCompressStored_size_ge, zlibCompressFixed_size_ge]
  have hsize : 8 ≤ (encodeBitmap bmp hw hh mode).size := by
    have hsize' :
        (encodeBitmap bmp hw hh mode).size =
          (encodeBitmapIdat (bmp := bmp) (mode := mode)).size + 57 := by
      simpa [pngPixel_encodeRaw_rgba, encodeBitmapIdat] using
        encodeBitmap_size (bmp := bmp) (hw := hw) (hh := hh) (mode := mode)
    omega
  have hmin : 2 ≤ (encodeBitmapIdat (bmp := bmp) (mode := mode)).size := by
    omega
  have hct :
      (PngPixel.colorType (α := PixelRGBA8)).toNat = 0 ∨
        (PngPixel.colorType (α := PixelRGBA8)).toNat = 2 ∨
        (PngPixel.colorType (α := PixelRGBA8)).toNat = 6 := by
    have : (u8 6).toNat = 0 ∨ (u8 6).toNat = 2 ∨ (u8 6).toNat = 6 := by decide
    simpa [pngPixel_colorType_rgba] using this
  have hctProp : ¬(u8 6).toNat = 0 → ¬(u8 6).toNat = 2 → (u8 6).toNat = 6 := by
    decide
  have hparse := parsePng_encodeBitmap (bmp := bmp) (hw := hw) (hh := hh)
    (mode := mode) hidat' hsize hct
  have hraw : (encodeRaw bmp).size =
      bmp.size.height * (bmp.size.width * bytesPerPixelRGBA + 1) := by
    simpa [bytesPerPixel_rgba] using encodeRaw_size (bmp := bmp)
  have hraw' : (encodeRaw bmp).size =
      bmp.size.height * (bmp.size.width * 4 + 1) := by
    simpa [bytesPerPixelRGBA] using hraw
  have hrows := decodeRowsLoopRGBA_encodeRaw (bmp := bmp)
  have hvalid : bmp.data.size = bmp.size.width * bmp.size.height * bytesPerPixelRGBA := by
    simpa [bytesPerPixel_rgba, Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc] using bmp.valid
  have hrows' :
      decodeRowsLoopRGBA (encodeRaw bmp) bmp.size.width bmp.size.height bytesPerPixelRGBA
          (bmp.size.width * bytesPerPixelRGBA) 0 0 ByteArray.empty
          (ByteArray.mk <| Array.replicate (bmp.size.height * (bmp.size.width * bytesPerPixelRGBA)) 0) =
        some bmp.data := by
    simpa [bytesPerPixelRGBA] using hrows
  have hrows'' :
      decodeRowsLoopRGBA (encodeRaw bmp) bmp.size.width bmp.size.height 4 (bmp.size.width * 4) 0 0
          ByteArray.empty { data := Array.replicate (bmp.size.height * (bmp.size.width * 4)) 0 } =
        some bmp.data := by
    dsimp [bytesPerPixelRGBA]
    simpa using hrows'
  have hrows''' :
      decodeRowsLoopRGBA (encodeRaw bmp) bmp.size.width bmp.size.height 4 (bmp.size.width * 4) 0 0
          ByteArray.empty { data := Array.replicate (bmp.size.width * bmp.size.height * 4) 0 } =
        some bmp.data := by
    simpa [Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc] using hrows''
  have hvalid' : bmp.data.size = bmp.size.width * bmp.size.height * 4 := by
    simpa [bytesPerPixelRGBA] using hvalid
  -- Raw size check and row decoding.
  have hbpp : (if (u8 6).toNat = 0 then 1 else if (u8 6).toNat = 2 then 3 else 4) = 4 := by
    decide
  have hrawEq :
      (encodeRaw bmp).size =
        bmp.size.height * ((bmp.size.width * if (u8 6).toNat = 0 then 1 else if (u8 6).toNat = 2 then 3 else 4) + 1) := by
    simpa [hbpp] using hraw'
  have hrowsEq :
      ((decodeRowsLoopRGBA (encodeRaw bmp) bmp.size.width bmp.size.height
              (if (u8 6).toNat = 0 then 1 else if (u8 6).toNat = 2 then 3 else 4)
              (bmp.size.width * if (u8 6).toNat = 0 then 1 else if (u8 6).toNat = 2 then 3 else 4) 0 0 ByteArray.empty
              { data := Array.replicate (bmp.size.width * bmp.size.height * 4) 0 }).bind
          fun pixels ↦
          if h : pixels.size = bmp.size.width * bmp.size.height * 4 then
            some { size := { width := bmp.size.width, height := bmp.size.height }, data := pixels, valid := h }
          else none) =
        some bmp := by
    simp [hbpp, hrows''', hvalid']
  unfold Png.decodeBitmap
  -- Parse and header checks.
  cases mode with
  | stored =>
      have hminStored : 2 ≤ (zlibCompressStored (encodeRaw bmp)).size := by
        simpa [encodeBitmapIdat] using hmin
      simpa [hsize, hparse, zlibDecompressStored_zlibCompressStored, encodeBitmapIdat] using
        (And.intro hctProp (And.intro hminStored (And.intro hrawEq hrowsEq)))
  | fixed =>
      have hminFixed : 2 ≤ (zlibCompressFixed (encodeRaw bmp)).size := by
        simpa [encodeBitmapIdat] using hmin
      simpa [hsize, hparse,
        zlibDecompressStored_zlibCompressFixed_none, zlibDecompress_zlibCompressFixed,
        encodeBitmapIdat] using
        (And.intro hctProp (And.intro hminFixed (And.intro hrawEq hrowsEq)))

-- Round-trip PNG encode/decode for grayscale bitmap payloads.
lemma decodeBitmap_encodeBitmap_gray (bmp : BitmapGray8)
    (hw : bmp.size.width < 2 ^ 32) (hh : bmp.size.height < 2 ^ 32)
    (mode : PngEncodeMode)
    (hidat : (encodeBitmapIdat (bmp := bmp) (mode := mode)).size < 2 ^ 32) :
    Png.decodeBitmap (Png.encodeBitmap bmp hw hh mode) = some bmp := by
  have hidat' :
      (encodeBitmapIdat (bmp := bmp) (mode := mode)).size < 2 ^ 32 := by
    simpa using hidat
  have hidat_min : 6 ≤ (encodeBitmapIdat (bmp := bmp) (mode := mode)).size := by
    cases mode <;> simp [encodeBitmapIdat, zlibCompressStored_size_ge, zlibCompressFixed_size_ge]
  have hsize : 8 ≤ (encodeBitmap bmp hw hh mode).size := by
    have hsize' :
        (encodeBitmap bmp hw hh mode).size =
          (encodeBitmapIdat (bmp := bmp) (mode := mode)).size + 57 := by
      simpa [pngPixel_encodeRaw_gray, encodeBitmapIdat] using
        encodeBitmap_size (bmp := bmp) (hw := hw) (hh := hh) (mode := mode)
    omega
  have hmin : 2 ≤ (encodeBitmapIdat (bmp := bmp) (mode := mode)).size := by
    omega
  have hct :
      (PngPixel.colorType (α := PixelGray8)).toNat = 0 ∨
        (PngPixel.colorType (α := PixelGray8)).toNat = 2 ∨
        (PngPixel.colorType (α := PixelGray8)).toNat = 6 := by
    have : (u8 0).toNat = 0 ∨ (u8 0).toNat = 2 ∨ (u8 0).toNat = 6 := by decide
    simpa [pngPixel_colorType_gray] using this
  have hctProp : ¬(u8 0).toNat = 0 → ¬(u8 0).toNat = 2 → (u8 0).toNat = 6 := by
    decide
  have hparse := parsePng_encodeBitmap (bmp := bmp) (hw := hw) (hh := hh)
    (mode := mode) hidat' hsize hct
  have hraw : (encodeRaw bmp).size =
      bmp.size.height * (bmp.size.width * bytesPerPixelGray + 1) := by
    simpa [bytesPerPixel_gray] using encodeRaw_size (bmp := bmp)
  have hraw' : (encodeRaw bmp).size =
      bmp.size.height * (bmp.size.width * 1 + 1) := by
    simpa [bytesPerPixelGray] using hraw
  have hrows := decodeRowsLoopGray_encodeRaw (bmp := bmp)
  have hvalid : bmp.data.size = bmp.size.width * bmp.size.height * bytesPerPixelGray := by
    simpa [bytesPerPixel_gray, Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc] using bmp.valid
  have hrows' :
      decodeRowsLoopGray (encodeRaw bmp) bmp.size.width bmp.size.height bytesPerPixelGray
          (bmp.size.width * bytesPerPixelGray) 0 0 ByteArray.empty
          (ByteArray.mk <| Array.replicate (bmp.size.height * (bmp.size.width * bytesPerPixelGray)) 0) =
        some bmp.data := by
    simpa [bytesPerPixelGray] using hrows
  have hrows'' :
      decodeRowsLoopGray (encodeRaw bmp) bmp.size.width bmp.size.height 1 bmp.size.width 0 0 ByteArray.empty
          { data := Array.replicate (bmp.size.width * bmp.size.height) 0 } =
        some bmp.data := by
    simpa [bytesPerPixelGray, Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc] using hrows'
  have hvalid' : bmp.data.size = bmp.size.width * bmp.size.height * 1 := by
    simpa [bytesPerPixelGray] using hvalid
  have hvalid'' : bmp.data.size = bmp.size.width * bmp.size.height := by
    simpa using hvalid'
  -- Raw size check and row decoding.
  have hbpp : (if (u8 0).toNat = 0 then 1 else if (u8 0).toNat = 2 then 3 else 4) = 1 := by
    decide
  have hrawEq :
      (encodeRaw bmp).size =
        bmp.size.height * ((bmp.size.width * if (u8 0).toNat = 0 then 1 else if (u8 0).toNat = 2 then 3 else 4) + 1) := by
    simpa [hbpp] using hraw'
  have hrowsEq' :
      ((decodeRowsLoopGray (encodeRaw bmp) bmp.size.width bmp.size.height
              (if (u8 0).toNat = 0 then 1 else if (u8 0).toNat = 2 then 3 else 4)
              (bmp.size.width * if (u8 0).toNat = 0 then 1 else if (u8 0).toNat = 2 then 3 else 4) 0 0 ByteArray.empty
              { data := Array.replicate (bmp.size.width * bmp.size.height) 0 }).bind
          fun pixels ↦
          if h : pixels.size = bmp.size.width * bmp.size.height then
            some
              { size := { width := bmp.size.width, height := bmp.size.height }
              , data := pixels
              , valid := by simpa [bytesPerPixel_gray, bytesPerPixelGray] using h }
          else none) =
        some bmp := by
    simp [hbpp, hrows'', hvalid'']
  have hrowsEq :
      ((decodeRowsLoopGray (encodeRaw bmp) bmp.size.width bmp.size.height
              (if (u8 0).toNat = 0 then 1 else if (u8 0).toNat = 2 then 3 else 4)
              (bmp.size.width * if (u8 0).toNat = 0 then 1 else if (u8 0).toNat = 2 then 3 else 4) 0 0 ByteArray.empty
              { data := Array.replicate (bmp.size.width * bmp.size.height * Pixel.bytesPerPixel (α := PixelGray8)) 0 }).bind
          fun pixels ↦
          if h : pixels.size = bmp.size.width * bmp.size.height * Pixel.bytesPerPixel (α := PixelGray8) then
            some { size := { width := bmp.size.width, height := bmp.size.height }, data := pixels, valid := h }
          else none) =
        some bmp := by
    simpa [bytesPerPixel_gray, bytesPerPixelGray] using hrowsEq'
  unfold Png.decodeBitmap
  -- Parse and header checks.
  cases mode with
  | stored =>
      have hminStored : 2 ≤ (zlibCompressStored (encodeRaw bmp)).size := by
        simpa [encodeBitmapIdat] using hmin
      simp [hsize, hparse, zlibDecompressStored_zlibCompressStored,
        encodeBitmapIdat, hrawEq, hrowsEq]
      exact And.intro hctProp hminStored
  | fixed =>
      have hminFixed : 2 ≤ (zlibCompressFixed (encodeRaw bmp)).size := by
        simpa [encodeBitmapIdat] using hmin
      simp [hsize, hparse, hminFixed,
        zlibDecompressStored_zlibCompressFixed_none, zlibDecompress_zlibCompressFixed,
        encodeBitmapIdat, hrawEq, hrowsEq]
      exact hctProp

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
