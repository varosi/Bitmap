import Bitmap.Png
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

-- Shared proof skeleton for PNG round-trip correctness.
lemma decodeBitmap_encodeBitmap_common {px : Type u} [Pixel px] [PngPixel px]
    (bmp : Bitmap px)
    (hw : bmp.size.width < 2 ^ 32) (hh : bmp.size.height < 2 ^ 32)
    (mode : PngEncodeMode)
    (hidat : (encodeBitmapIdat (bmp := bmp) (mode := mode)).size < 2 ^ 32)
    (hct :
      (PngPixel.colorType (α := px)).toNat = 0 ∨
        (PngPixel.colorType (α := px)).toNat = 2 ∨
        (PngPixel.colorType (α := px)).toNat = 6)
    (hrawEq :
      (PngPixel.encodeRaw (α := px) bmp).size =
        bmp.size.height *
          ((bmp.size.width *
            (if (PngPixel.colorType (α := px)).toNat = 0 then 1 else
              if (PngPixel.colorType (α := px)).toNat = 2 then 3 else 4)) + 1))
    (hrows :
      PngPixel.decodeRowsLoop (α := px)
        (PngPixel.encodeRaw (α := px) bmp) bmp.size.width bmp.size.height
        (if (PngPixel.colorType (α := px)).toNat = 0 then 1 else
          if (PngPixel.colorType (α := px)).toNat = 2 then 3 else 4)
        (bmp.size.width *
          (if (PngPixel.colorType (α := px)).toNat = 0 then 1 else
            if (PngPixel.colorType (α := px)).toNat = 2 then 3 else 4))
        0 0 ByteArray.empty
        { data := Array.replicate
            (bmp.size.width * bmp.size.height * Pixel.bytesPerPixel (α := px)) 0 } =
        some bmp.data) :
    Png.decodeBitmap (Png.encodeBitmap bmp hw hh mode) = some bmp := by
  -- Basic size bounds.
  have hidat_min : 6 ≤ (encodeBitmapIdat (bmp := bmp) (mode := mode)).size := by
    cases mode <;> simp [encodeBitmapIdat, zlibCompressStored_size_ge,
      zlibCompressFixed_size_ge, zlibCompressDynamic_size_ge]
  have hsize : 8 ≤ (encodeBitmap bmp hw hh mode).size := by
    have hsize' :
        (encodeBitmap bmp hw hh mode).size =
          (encodeBitmapIdat (bmp := bmp) (mode := mode)).size + 57 := by
      simpa [encodeBitmapIdat] using encodeBitmap_size (bmp := bmp) (hw := hw) (hh := hh) (mode := mode)
    omega
  have hmin : 2 ≤ (encodeBitmapIdat (bmp := bmp) (mode := mode)).size := by
    omega
  -- Color type constraints.
  let ct := (PngPixel.colorType (α := px)).toNat
  have hct' : ct = 0 ∨ ct = 2 ∨ ct = 6 := by
    simpa [ct] using hct
  have hctProp : ¬ ct = 0 → ¬ ct = 2 → ct = 6 := by
    intro h0 h2
    cases hct' with
    | inl h0' => exact (False.elim (h0 h0'))
    | inr hrest =>
        cases hrest with
        | inl h2' => exact (False.elim (h2 h2'))
        | inr h6 => exact h6
  -- Parsed PNG header.
  have hparse := parsePng_encodeBitmap (bmp := bmp) (hw := hw) (hh := hh)
    (mode := mode) hidat hsize hct
  -- Raw size and row decoding results.
  let bpp := if ct = 0 then 1 else if ct = 2 then 3 else 4
  have hrawEq' :
      (PngPixel.encodeRaw (α := px) bmp).size =
        bmp.size.height * ((bmp.size.width * bpp) + 1) := by
    simpa [ct, bpp] using hrawEq
  have hrows' :
      PngPixel.decodeRowsLoop (α := px)
        (PngPixel.encodeRaw (α := px) bmp) bmp.size.width bmp.size.height bpp
        (bmp.size.width * bpp) 0 0 ByteArray.empty
        { data := Array.replicate
            (bmp.size.width * bmp.size.height * Pixel.bytesPerPixel (α := px)) 0 } =
        some bmp.data := by
    simpa [ct, bpp] using hrows
  have hvalid : bmp.data.size = bmp.size.width * bmp.size.height * Pixel.bytesPerPixel (α := px) := by
    simpa [Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc] using bmp.valid
  have hrowsEq :
      ((PngPixel.decodeRowsLoop (α := px)
          (PngPixel.encodeRaw (α := px) bmp) bmp.size.width bmp.size.height bpp
          (bmp.size.width * bpp) 0 0 ByteArray.empty
          { data := Array.replicate
              (bmp.size.width * bmp.size.height * Pixel.bytesPerPixel (α := px)) 0 }).bind
        fun pixels ↦
          if h : pixels.size = bmp.size.width * bmp.size.height * Pixel.bytesPerPixel (α := px) then
            some { size := { width := bmp.size.width, height := bmp.size.height }, data := pixels, valid := h }
          else none) =
        some bmp := by
    simp [hrows', hvalid]
  -- Finish by unfolding the decoder.
  unfold Png.decodeBitmap
  cases mode with
  | stored =>
      have hminStored : 2 ≤ (zlibCompressStored (PngPixel.encodeRaw (α := px) bmp)).size := by
        simpa [encodeBitmapIdat] using hmin
      simpa [hsize, hparse, zlibDecompressStored_zlibCompressStored, encodeBitmapIdat] using
        (And.intro hctProp (And.intro hminStored (And.intro hrawEq' hrowsEq)))
  | fixed =>
      have hminFixed : 2 ≤ (zlibCompressFixed (PngPixel.encodeRaw (α := px) bmp)).size := by
        simpa [encodeBitmapIdat] using hmin
      simpa [hsize, hparse,
        zlibDecompressStored_zlibCompressFixed_none, zlibDecompress_zlibCompressFixed,
        encodeBitmapIdat] using
        (And.intro hctProp (And.intro hminFixed (And.intro hrawEq' hrowsEq)))
  | dynamic =>
      have hminDyn : 2 ≤ (zlibCompressDynamic (PngPixel.encodeRaw (α := px) bmp)).size := by
        simpa [encodeBitmapIdat] using hmin
      simpa [hsize, hparse,
        zlibDecompressStored_zlibCompressDynamic_none, zlibDecompress_zlibCompressDynamic,
        encodeBitmapIdat] using
        (And.intro hctProp (And.intro hminDyn (And.intro hrawEq' hrowsEq)))

-- Package the pixel-specific facts needed for PNG round-trips.
class PngRoundTrip (px : Type u) [Pixel px] [PngPixel px] : Prop where
  colorType_ok :
    (PngPixel.colorType (α := px)).toNat = 0 ∨
      (PngPixel.colorType (α := px)).toNat = 2 ∨
      (PngPixel.colorType (α := px)).toNat = 6
  encodeRaw_size :
    ∀ bmp : Bitmap px,
      (PngPixel.encodeRaw (α := px) bmp).size =
        bmp.size.height *
          ((bmp.size.width *
            (if (PngPixel.colorType (α := px)).toNat = 0 then 1 else
              if (PngPixel.colorType (α := px)).toNat = 2 then 3 else 4)) + 1)
  decodeRowsLoop_encodeRaw :
    ∀ bmp : Bitmap px,
      PngPixel.decodeRowsLoop (α := px)
        (PngPixel.encodeRaw (α := px) bmp) bmp.size.width bmp.size.height
        (if (PngPixel.colorType (α := px)).toNat = 0 then 1 else
          if (PngPixel.colorType (α := px)).toNat = 2 then 3 else 4)
        (bmp.size.width *
          (if (PngPixel.colorType (α := px)).toNat = 0 then 1 else
            if (PngPixel.colorType (α := px)).toNat = 2 then 3 else 4))
        0 0 ByteArray.empty
        { data := Array.replicate
            (bmp.size.width * bmp.size.height * Pixel.bytesPerPixel (α := px)) 0 } =
        some bmp.data

instance : PngRoundTrip PixelRGB8 where
  colorType_ok := by
    have : (u8 2).toNat = 0 ∨ (u8 2).toNat = 2 ∨ (u8 2).toNat = 6 := by decide
    simpa [pngPixel_colorType_rgb] using this
  encodeRaw_size := by
    intro bmp
    have hraw : (encodeRaw bmp).size =
        bmp.size.height * (bmp.size.width * bytesPerPixelRGB + 1) := by
      simpa using encodeRaw_size (bmp := bmp)
    have hbpp :
        (if (u8 2).toNat = 0 then 1 else if (u8 2).toNat = 2 then 3 else 4) = 3 := by
      decide
    simpa [pngPixel_encodeRaw_rgb, pngPixel_colorType_rgb, hbpp, bytesPerPixelRGB] using hraw
  decodeRowsLoop_encodeRaw := by
    intro bmp
    have hrows :
        decodeRowsLoop (encodeRaw bmp) bmp.size.width bmp.size.height bytesPerPixelRGB
            (bmp.size.width * bytesPerPixelRGB) 0 0 ByteArray.empty
            (ByteArray.mk <| Array.replicate
              (bmp.size.height * (bmp.size.width * bytesPerPixelRGB)) 0) =
          some bmp.data := by
      simpa using (decodeRowsLoop_encodeRaw (bmp := bmp))
    have hbpp :
        (if (u8 2).toNat = 0 then 1 else if (u8 2).toNat = 2 then 3 else 4) = 3 := by
      decide
    simpa [pngPixel_decodeRowsLoop_rgb, pngPixel_encodeRaw_rgb, pngPixel_colorType_rgb, hbpp,
      bytesPerPixel_rgb, bytesPerPixelRGB, Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc] using hrows

instance : PngRoundTrip PixelRGBA8 where
  colorType_ok := by
    have : (u8 6).toNat = 0 ∨ (u8 6).toNat = 2 ∨ (u8 6).toNat = 6 := by decide
    simpa [pngPixel_colorType_rgba] using this
  encodeRaw_size := by
    intro bmp
    have hraw : (encodeRaw bmp).size =
        bmp.size.height * (bmp.size.width * bytesPerPixelRGBA + 1) := by
      simpa [bytesPerPixel_rgba] using encodeRaw_size (bmp := bmp)
    have hbpp :
        (if (u8 6).toNat = 0 then 1 else if (u8 6).toNat = 2 then 3 else 4) = 4 := by
      decide
    simpa [pngPixel_encodeRaw_rgba, pngPixel_colorType_rgba, hbpp, bytesPerPixelRGBA] using hraw
  decodeRowsLoop_encodeRaw := by
    intro bmp
    have hrows :
        decodeRowsLoopRGBA (encodeRaw bmp) bmp.size.width bmp.size.height bytesPerPixelRGBA
            (bmp.size.width * bytesPerPixelRGBA) 0 0 ByteArray.empty
            (ByteArray.mk <| Array.replicate
              (bmp.size.height * (bmp.size.width * bytesPerPixelRGBA)) 0) =
          some bmp.data := by
      simpa using (decodeRowsLoopRGBA_encodeRaw (bmp := bmp))
    have hbpp :
        (if (u8 6).toNat = 0 then 1 else if (u8 6).toNat = 2 then 3 else 4) = 4 := by
      decide
    simpa [pngPixel_decodeRowsLoop_rgba, pngPixel_encodeRaw_rgba, pngPixel_colorType_rgba, hbpp,
      bytesPerPixel_rgba, bytesPerPixelRGBA, Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc] using hrows

instance : PngRoundTrip PixelGray8 where
  colorType_ok := by
    have : (u8 0).toNat = 0 ∨ (u8 0).toNat = 2 ∨ (u8 0).toNat = 6 := by decide
    simpa [pngPixel_colorType_gray] using this
  encodeRaw_size := by
    intro bmp
    have hraw : (encodeRaw bmp).size =
        bmp.size.height * (bmp.size.width * bytesPerPixelGray + 1) := by
      simpa [bytesPerPixel_gray] using encodeRaw_size (bmp := bmp)
    have hbpp :
        (if (u8 0).toNat = 0 then 1 else if (u8 0).toNat = 2 then 3 else 4) = 1 := by
      decide
    simpa [pngPixel_encodeRaw_gray, pngPixel_colorType_gray, hbpp, bytesPerPixelGray] using hraw
  decodeRowsLoop_encodeRaw := by
    intro bmp
    have hrows :
        decodeRowsLoopGray (encodeRaw bmp) bmp.size.width bmp.size.height bytesPerPixelGray
            (bmp.size.width * bytesPerPixelGray) 0 0 ByteArray.empty
            (ByteArray.mk <| Array.replicate
              (bmp.size.height * (bmp.size.width * bytesPerPixelGray)) 0) =
          some bmp.data := by
      simpa using (decodeRowsLoopGray_encodeRaw (bmp := bmp))
    have hbpp :
        (if (u8 0).toNat = 0 then 1 else if (u8 0).toNat = 2 then 3 else 4) = 1 := by
      decide
    simpa [pngPixel_decodeRowsLoop_gray, pngPixel_encodeRaw_gray, pngPixel_colorType_gray, hbpp,
      bytesPerPixel_gray, bytesPerPixelGray, Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc] using hrows

-- Round-trip PNG encode/decode for bitmap payloads.
lemma decodeBitmap_encodeBitmap {px : Type u} [Pixel px] [PngPixel px] [PngRoundTrip px]
    (bmp : Bitmap px)
    (hw : bmp.size.width < 2 ^ 32) (hh : bmp.size.height < 2 ^ 32)
    (mode : PngEncodeMode)
    (hidat : (encodeBitmapIdat (bmp := bmp) (mode := mode)).size < 2 ^ 32) :
    Png.decodeBitmap (Png.encodeBitmap bmp hw hh mode) = some bmp := by
  have hct := PngRoundTrip.colorType_ok (px := px)
  have hrawEq := PngRoundTrip.encodeRaw_size (px := px) bmp
  have hrows := PngRoundTrip.decodeRowsLoop_encodeRaw (px := px) bmp
  exact
    decodeBitmap_encodeBitmap_common (bmp := bmp) (hw := hw) (hh := hh)
      (mode := mode) hidat hct hrawEq hrows

-- RGB-specialized wrapper for symmetry.
lemma decodeBitmap_encodeBitmap_rgb (bmp : BitmapRGB8)
    (hw : bmp.size.width < 2 ^ 32) (hh : bmp.size.height < 2 ^ 32)
    (mode : PngEncodeMode)
    (hidat : (encodeBitmapIdat (bmp := bmp) (mode := mode)).size < 2 ^ 32) :
    Png.decodeBitmap (Png.encodeBitmap bmp hw hh mode) = some bmp := by
  simpa using
    (decodeBitmap_encodeBitmap (px := PixelRGB8) (bmp := bmp)
      (hw := hw) (hh := hh) (mode := mode) hidat)


-- Re-export: static Huffman length base table size.
lemma lengthBases_size : lengthBases.size = 29 := by decide
-- Re-export: static Huffman length extra table size.
lemma lengthExtra_size : lengthExtra.size = 29 := by decide
-- Re-export: static Huffman distance base table size.
lemma distBases_size : distBases.size = 30 := by decide
-- Re-export: static Huffman distance extra table size.
lemma distExtra_size : distExtra.size = 30 := by decide

end Lemmas
end Bitmaps
