import Bitmap.Png
import Bitmap.Lemmas.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Nat.Bitwise.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.ByteArray.Lemmas
import Init.Data.Range.Lemmas
import Init.Data.UInt.Lemmas
import Batteries.Data.UInt
import Batteries.Data.ByteArray
import Bitmap.Lemmas.Png.EncodeDecodeBase
import Bitmap.Lemmas.Png.EncodeDecode

universe u

namespace Bitmaps

namespace Lemmas

open Png

-------------------------------------------------------------------------------
-- Verification. Converting tests into proofs.
-- https://lean-lang.org/theorem_proving_in_lean4/tactics.html

variable (aPixel : RGB8)

example [PixelFormat RGB8] :
    (Bitmap.fill 1 1 aPixel).data.size =
      (Bitmap.fill 1 1 aPixel).size.width *
        (Bitmap.fill 1 1 aPixel).size.height *
        PixelFormat.bytesPerPixel (α := RGB8) := by
  simpa using (Bitmap.fill 1 1 aPixel).valid


-- Writing a pixel then reading it back yields the same pixel.
lemma getPixel_setPixel_eq
    {px : Type} [PixelFormat px] [LawfulPixelFormat px]
    (img : Bitmap px) (x y : Nat) (pixel : px)
    (hx : x < img.size.width) (hy : y < img.size.height) :
    Bitmap.getPixel (Bitmap.setPixel img x y pixel hx hy) x y
      (by simpa [Bitmap.setPixel] using hx) (by simpa [Bitmap.setPixel] using hy) = pixel := by
  simp [Bitmap.getPixel, Bitmap.setPixel, LawfulPixelFormat.read_write]

-- Shared proof skeleton for PNG round-trip correctness.
lemma decodeBitmap_encodeBitmap_common {px : Type u} [PixelFormat px] [Png.PixelFormat px]
    (bmp : Bitmap px)
    (hw : bmp.size.width < 2 ^ 32) (hh : bmp.size.height < 2 ^ 32)
    (mode : PngEncodeMode)
    (hidat : (encodeBitmapIdat (bmp := bmp) (mode := mode)).size < 2 ^ 32)
    (hct :
      (Png.PixelFormat.colorType (α := px)).toNat = 0 ∨
        (Png.PixelFormat.colorType (α := px)).toNat = 2 ∨
        (Png.PixelFormat.colorType (α := px)).toNat = 4 ∨
        (Png.PixelFormat.colorType (α := px)).toNat = 6)
    (hbd : pngBitDepthSupported (Png.PixelFormat.bitDepth (α := px)).toNat = true)
    (hctbd :
      pngColorTypeBitDepthSupported
        (Png.PixelFormat.colorType (α := px)).toNat
        (Png.PixelFormat.bitDepth (α := px)).toNat = true)
    (hbdNot1 : ¬ (Png.PixelFormat.bitDepth (α := px)).toNat = 1)
    (hpngBpp :
      pngBytesPerPixelForColorTypeAndBitDepth?
        (Png.PixelFormat.colorType (α := px)).toNat
        (Png.PixelFormat.bitDepth (α := px)).toNat =
          some (PixelFormat.bytesPerPixel (α := px)))
    (hrawEq :
      (Png.PixelFormat.encodeRaw (α := px) bmp).size =
        bmp.size.height * (bmp.size.width * PixelFormat.bytesPerPixel (α := px) + 1))
    (hrows :
      Png.PixelFormat.decodeRowsLoop (α := px)
        (Png.PixelFormat.encodeRaw (α := px) bmp) bmp.size.width bmp.size.height
        (PixelFormat.bytesPerPixel (α := px))
        (bmp.size.width * PixelFormat.bytesPerPixel (α := px))
        0 0 ByteArray.empty
        { data := Array.replicate
            (bmp.size.width * bmp.size.height * PixelFormat.bytesPerPixel (α := px)) 0 } =
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
  let ct := (Png.PixelFormat.colorType (α := px)).toNat
  have hct' : ct = 0 ∨ ct = 2 ∨ ct = 4 ∨ ct = 6 := by
    simpa [ct] using hct
  have hctProp : ¬ ct = 0 → ¬ ct = 2 → ¬ ct = 4 → ct = 6 := by
    intro h0 h2 h4
    cases hct' with
    | inl h0' => exact (False.elim (h0 h0'))
    | inr hrest =>
        cases hrest with
        | inl h2' => exact (False.elim (h2 h2'))
        | inr hrest' =>
            cases hrest' with
            | inl h4' => exact (False.elim (h4 h4'))
            | inr h6 => exact h6
  have hctNot3 : ¬ ct = 3 := by
    intro h3
    rcases hct' with h0 | hrest
    · omega
    rcases hrest with h2 | hrest
    · omega
    rcases hrest with h4 | h6 <;> omega
  -- Parsed PNG header.
  have hparseSimple := parsePngSimple_encodeBitmap (bmp := bmp) (hw := hw) (hh := hh)
    (mode := mode) hidat hsize hct hbd hctbd
  have hparseForDecode :
      parsePngForDecode (encodeBitmap bmp hw hh mode) hsize =
        some
          { header :=
              { width := bmp.size.width
                height := bmp.size.height
                colorType := (Png.PixelFormat.colorType (α := px)).toNat
                bitDepth := (Png.PixelFormat.bitDepth (α := px)).toNat
                interlace := 0 }
            idat := encodeBitmapIdat (bmp := bmp) (mode := mode)
            metadata := PngMetadata.empty } := by
    unfold parsePngForDecode parsePngSimpleWithMetadata
    simp [hparseSimple]
  -- Raw size and row decoding results.
  let bd := (Png.PixelFormat.bitDepth (α := px)).toNat
  let bpp := PixelFormat.bytesPerPixel (α := px)
  have hrawEq' :
      (Png.PixelFormat.encodeRaw (α := px) bmp).size =
        bmp.size.height * ((bmp.size.width * bpp) + 1) := by
    simpa [bpp, Nat.add_assoc] using hrawEq
  have hrows' :
      Png.PixelFormat.decodeRowsLoop (α := px)
        (Png.PixelFormat.encodeRaw (α := px) bmp) bmp.size.width bmp.size.height bpp
        (bmp.size.width * bpp) 0 0 ByteArray.empty
        { data := Array.replicate
            (bmp.size.width * bmp.size.height * PixelFormat.bytesPerPixel (α := px)) 0 } =
        some bmp.data := by
    simpa [bpp] using hrows
  have hvalid : bmp.data.size = bmp.size.width * bmp.size.height * PixelFormat.bytesPerPixel (α := px) := by
    simpa [Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc] using bmp.valid
  have hpngBpp' : pngBytesPerPixelForColorTypeAndBitDepth? ct bd = some bpp := by
    simpa [ct, bd, bpp] using hpngBpp
  have hctbd' : pngColorTypeBitDepthSupported ct bd = true := by
    simpa [ct, bd] using hctbd
  have hbdNot1' : ¬ bd = 1 := by
    simpa [bd] using hbdNot1
  have hbdNoReject : (pngBitDepthSupported bd) = true := by
    simpa [bd] using hbd
  have hbitDepthEq :
      ((Png.PixelFormat.bitDepth (α := px)).toNat != bd) = false := by
    simp [bd]
  have hbitDepthEqHeader :
      (bd != (Png.PixelFormat.bitDepth (α := px)).toNat) = false := by
    simp [bd]
  have hnoDownsample :
      ¬((Png.PixelFormat.bitDepth (α := px)).toNat = 16 ∧ Png.PixelFormat.bitDepth (α := px) = u8 8) := by
    rintro ⟨h16, h8⟩
    have h8nat' :
        (Png.PixelFormat.bitDepth (α := px)).toNat = (u8 8).toNat :=
      congrArg UInt8.toNat h8
    have h8nat : (Png.PixelFormat.bitDepth (α := px)).toNat = 8 := by
      have hu8 : (u8 8).toNat = 8 := by decide
      exact h8nat'.trans hu8
    omega
  have hctNoReject :
      ct = 4 → ¬Png.PixelFormat.colorType (α := px) = u8 4 →
        Png.PixelFormat.colorType (α := px) = u8 6 := by
    intro h4 hne
    have heq4 : Png.PixelFormat.colorType (α := px) = u8 4 := by
      have hnat : (Png.PixelFormat.colorType (α := px)).toNat = 4 := by
        simpa [ct] using h4
      apply UInt8.ext
      rw [hnat]
      decide
    exact False.elim (hne heq4)
  have hmetadataNoTransparency : PngMetadata.empty.transparency = none := by
    rfl
  have hrowsEq :
      ((Png.PixelFormat.decodeRowsLoop (α := px)
          (Png.PixelFormat.encodeRaw (α := px) bmp) bmp.size.width bmp.size.height bpp
          (bmp.size.width * bpp) 0 0 ByteArray.empty
          { data := Array.replicate
              (bmp.size.width * bmp.size.height * PixelFormat.bytesPerPixel (α := px)) 0 }).bind
        fun decodedPixels ↦
          (applyPngColorSpaceTransform PngMetadata.empty
            (Png.PixelFormat.colorType (α := px)).toNat
            (Png.PixelFormat.colorType (α := px)) (Png.PixelFormat.bitDepth (α := px)) decodedPixels).bind
            fun pixels ↦
              if h : pixels.size = bmp.size.width * bmp.size.height * PixelFormat.bytesPerPixel (α := px) then
                some { size := { width := bmp.size.width, height := bmp.size.height }, data := pixels, valid := h }
              else none) =
      some bmp := by
    simp [hrows', hvalid, applyPngColorSpaceTransform, PngMetadata.empty]
  -- Finish by unfolding the decoder.
  unfold Png.decodeBitmap
  cases mode with
  | stored =>
      have hminStored : 2 ≤ (zlibCompressStored (Png.PixelFormat.encodeRaw (α := px) bmp)).size := by
        simpa [encodeBitmapIdat] using hmin
      simpa [hsize, hparseForDecode, zlibDecompressStored_zlibCompressStored, encodeBitmapIdat,
        ct, bd, hbdNoReject, hbitDepthEq, hbitDepthEqHeader, hnoDownsample, hpngBpp',
        hctNot3, hctbd', hbdNot1', normalizeRawByInterlace?, PngMetadata.pixelOnlyColorSpace,
        PngMetadata.empty, applyPngColorSpaceTransform] using
        (And.intro hmetadataNoTransparency
          (And.intro hctProp
            (And.intro hctNoReject (And.intro hminStored (And.intro hrawEq' hrowsEq)))))
  | fixed =>
      have hminFixed : 2 ≤ (zlibCompressFixed (Png.PixelFormat.encodeRaw (α := px) bmp)).size := by
        simpa [encodeBitmapIdat] using hmin
      simpa [hsize, hparseForDecode,
        zlibDecompressStored_zlibCompressFixed_none, zlibDecompress_zlibCompressFixed,
        encodeBitmapIdat, ct, bd, hbdNoReject, hbitDepthEq, hbitDepthEqHeader,
        hnoDownsample, hpngBpp', hctNot3, hctbd', hbdNot1', normalizeRawByInterlace?,
        PngMetadata.pixelOnlyColorSpace, PngMetadata.empty, applyPngColorSpaceTransform] using
        (And.intro hmetadataNoTransparency
          (And.intro hctProp
            (And.intro hctNoReject (And.intro hminFixed (And.intro hrawEq' hrowsEq)))))
  | dynamic =>
      have hminDyn : 2 ≤ (zlibCompressDynamic (Png.PixelFormat.encodeRaw (α := px) bmp)).size := by
        simpa [encodeBitmapIdat] using hmin
      simpa [hsize, hparseForDecode,
        zlibDecompressStored_zlibCompressDynamic_none, zlibDecompress_zlibCompressDynamic,
        encodeBitmapIdat, ct, bd, hbdNoReject, hbitDepthEq, hbitDepthEqHeader,
        hnoDownsample, hpngBpp', hctNot3, hctbd', hbdNot1', normalizeRawByInterlace?,
        PngMetadata.pixelOnlyColorSpace, PngMetadata.empty, applyPngColorSpaceTransform] using
        (And.intro hmetadataNoTransparency
          (And.intro hctProp
            (And.intro hctNoReject (And.intro hminDyn (And.intro hrawEq' hrowsEq)))))

-- Package the pixel-specific facts needed for PNG round-trips.
class PngRoundTrip (px : Type u) [PixelFormat px] [Png.PixelFormat px] : Prop where
  colorType_ok :
    (Png.PixelFormat.colorType (α := px)).toNat = 0 ∨
      (Png.PixelFormat.colorType (α := px)).toNat = 2 ∨
      (Png.PixelFormat.colorType (α := px)).toNat = 4 ∨
      (Png.PixelFormat.colorType (α := px)).toNat = 6
  bitDepth_ok :
    pngBitDepthSupported (Png.PixelFormat.bitDepth (α := px)).toNat = true
  colorTypeBitDepth_ok :
    pngColorTypeBitDepthSupported
      (Png.PixelFormat.colorType (α := px)).toNat
      (Png.PixelFormat.bitDepth (α := px)).toNat = true
  bitDepth_ne_one :
    ¬ (Png.PixelFormat.bitDepth (α := px)).toNat = 1
  pngBytesPerPixel_ok :
    pngBytesPerPixelForColorTypeAndBitDepth?
      (Png.PixelFormat.colorType (α := px)).toNat
      (Png.PixelFormat.bitDepth (α := px)).toNat =
        some (PixelFormat.bytesPerPixel (α := px))
  encodeRaw_size :
    ∀ bmp : Bitmap px,
      (Png.PixelFormat.encodeRaw (α := px) bmp).size =
        bmp.size.height * (bmp.size.width * PixelFormat.bytesPerPixel (α := px) + 1)
  decodeRowsLoop_encodeRaw :
    ∀ bmp : Bitmap px,
      Png.PixelFormat.decodeRowsLoop (α := px)
        (Png.PixelFormat.encodeRaw (α := px) bmp) bmp.size.width bmp.size.height
        (PixelFormat.bytesPerPixel (α := px))
        (bmp.size.width * PixelFormat.bytesPerPixel (α := px))
        0 0 ByteArray.empty
        { data := Array.replicate
            (bmp.size.width * bmp.size.height * PixelFormat.bytesPerPixel (α := px)) 0 } =
        some bmp.data

instance : PngRoundTrip RGB8 where
  colorType_ok := by
    have : (u8 2).toNat = 0 ∨ (u8 2).toNat = 2 ∨
        (u8 2).toNat = 4 ∨ (u8 2).toNat = 6 := by decide
    simpa [pngPixel_colorType_rgb] using this
  bitDepth_ok := by
    decide
  colorTypeBitDepth_ok := by
    decide
  bitDepth_ne_one := by
    decide
  pngBytesPerPixel_ok := by
    decide
  encodeRaw_size := by
    intro bmp
    have hraw : (encodeRawFast bmp).size =
        bmp.size.height * (bmp.size.width * RGB8.bytesPerPixel + 1) := by
      rw [encodeRawFast_eq]
      simpa [bytesPerPixel_rgb, RGB8.bytesPerPixel] using encodeRaw_size (bmp := bmp)
    have hbpp :
        (if (u8 2).toNat = 0 then 1 else if (u8 2).toNat = 2 then 3 else
          if (u8 2).toNat = 4 then 2 else 4) = 3 := by
      decide
    simpa [pngPixel_encodeRaw_rgb, pngPixel_colorType_rgb, hbpp, bytesPerPixel_rgb,
      RGB8.bytesPerPixel] using hraw
  decodeRowsLoop_encodeRaw := by
    intro bmp
    have hrows :
        decodeRowsLoop (encodeRawFast bmp) bmp.size.width bmp.size.height RGB8.bytesPerPixel
            (bmp.size.width * RGB8.bytesPerPixel) 0 0 ByteArray.empty
            (ByteArray.mk <| Array.replicate
              (bmp.size.height * (bmp.size.width * RGB8.bytesPerPixel)) 0) =
          some bmp.data := by
      rw [encodeRawFast_eq]
      simpa using (decodeRowsLoop_encodeRaw (bmp := bmp))
    have hbpp :
        (if (u8 2).toNat = 0 then 1 else if (u8 2).toNat = 2 then 3 else
          if (u8 2).toNat = 4 then 2 else 4) = 3 := by
      decide
    simpa [pngPixel_decodeRowsLoop_rgb, pngPixel_encodeRaw_rgb, pngPixel_colorType_rgb, hbpp,
      bytesPerPixel_rgb, RGB8.bytesPerPixel, Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc] using hrows

instance : PngRoundTrip RGBA8 where
  colorType_ok := by
    have : (u8 6).toNat = 0 ∨ (u8 6).toNat = 2 ∨
        (u8 6).toNat = 4 ∨ (u8 6).toNat = 6 := by decide
    simpa [pngPixel_colorType_rgba] using this
  bitDepth_ok := by
    decide
  colorTypeBitDepth_ok := by
    decide
  bitDepth_ne_one := by
    decide
  pngBytesPerPixel_ok := by
    decide
  encodeRaw_size := by
    intro bmp
    have hraw : (encodeRawFast bmp).size =
        bmp.size.height * (bmp.size.width * RGBA8.bytesPerPixel + 1) := by
      rw [encodeRawFast_eq]
      simpa [bytesPerPixel_rgba] using encodeRaw_size (bmp := bmp)
    have hbpp :
        (if (u8 6).toNat = 0 then 1 else if (u8 6).toNat = 2 then 3 else
          if (u8 6).toNat = 4 then 2 else 4) = 4 := by
      decide
    simpa [pngPixel_encodeRaw_rgba, pngPixel_colorType_rgba, hbpp, bytesPerPixel_rgba,
      RGBA8.bytesPerPixel] using hraw
  decodeRowsLoop_encodeRaw := by
    intro bmp
    have hrows :
        decodeRowsLoopRGBA (encodeRawFast bmp) bmp.size.width bmp.size.height RGBA8.bytesPerPixel
            (bmp.size.width * RGBA8.bytesPerPixel) 0 0 ByteArray.empty
            (ByteArray.mk <| Array.replicate
              (bmp.size.height * (bmp.size.width * RGBA8.bytesPerPixel)) 0) =
          some bmp.data := by
      rw [encodeRawFast_eq]
      simpa using (decodeRowsLoopRGBA_encodeRaw (bmp := bmp))
    have hbpp :
        (if (u8 6).toNat = 0 then 1 else if (u8 6).toNat = 2 then 3 else
          if (u8 6).toNat = 4 then 2 else 4) = 4 := by
      decide
    simpa [pngPixel_decodeRowsLoop_rgba, pngPixel_encodeRaw_rgba, pngPixel_colorType_rgba, hbpp,
      bytesPerPixel_rgba, RGBA8.bytesPerPixel, Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc] using hrows

instance : PngRoundTrip Gray8 where
  colorType_ok := by
    have : (u8 0).toNat = 0 ∨ (u8 0).toNat = 2 ∨
        (u8 0).toNat = 4 ∨ (u8 0).toNat = 6 := by decide
    simpa [pngPixel_colorType_gray] using this
  bitDepth_ok := by
    decide
  colorTypeBitDepth_ok := by
    decide
  bitDepth_ne_one := by
    decide
  pngBytesPerPixel_ok := by
    decide
  encodeRaw_size := by
    intro bmp
    have hraw : (encodeRawFast bmp).size =
        bmp.size.height * (bmp.size.width * Gray8.bytesPerPixel + 1) := by
      rw [encodeRawFast_eq]
      simpa [bytesPerPixel_gray] using encodeRaw_size (bmp := bmp)
    have hbpp :
        (if (u8 0).toNat = 0 then 1 else if (u8 0).toNat = 2 then 3 else
          if (u8 0).toNat = 4 then 2 else 4) = 1 := by
      decide
    simpa [pngPixel_encodeRaw_gray, pngPixel_colorType_gray, hbpp, bytesPerPixel_gray,
      Gray8.bytesPerPixel] using hraw
  decodeRowsLoop_encodeRaw := by
    intro bmp
    have hrows :
        decodeRowsLoopGray (encodeRawFast bmp) bmp.size.width bmp.size.height Gray8.bytesPerPixel
            (bmp.size.width * Gray8.bytesPerPixel) 0 0 ByteArray.empty
            (ByteArray.mk <| Array.replicate
              (bmp.size.height * (bmp.size.width * Gray8.bytesPerPixel)) 0) =
          some bmp.data := by
      rw [encodeRawFast_eq]
      simpa using (decodeRowsLoopGray_encodeRaw (bmp := bmp))
    have hbpp :
        (if (u8 0).toNat = 0 then 1 else if (u8 0).toNat = 2 then 3 else
          if (u8 0).toNat = 4 then 2 else 4) = 1 := by
      decide
    simpa [pngPixel_decodeRowsLoop_gray, pngPixel_encodeRaw_gray, pngPixel_colorType_gray, hbpp,
      bytesPerPixel_gray, Gray8.bytesPerPixel, Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc] using hrows

/-- `GrayAlpha8` satisfies the generic PNG round-trip contract.
It provides the color type 4 facts consumed by `decodeBitmap_encodeBitmap`. -/
instance : PngRoundTrip GrayAlpha8 where
  colorType_ok := by
    have : (u8 4).toNat = 0 ∨ (u8 4).toNat = 2 ∨
        (u8 4).toNat = 4 ∨ (u8 4).toNat = 6 := by decide
    simpa [pngPixel_colorType_grayAlpha] using this
  bitDepth_ok := by
    decide
  colorTypeBitDepth_ok := by
    decide
  bitDepth_ne_one := by
    decide
  pngBytesPerPixel_ok := by
    decide
  encodeRaw_size := by
    intro bmp
    have hraw : (encodeRawFast bmp).size =
        bmp.size.height * (bmp.size.width * GrayAlpha8.bytesPerPixel + 1) := by
      rw [encodeRawFast_eq]
      simpa [bytesPerPixel_grayAlpha] using encodeRaw_size (bmp := bmp)
    have hbpp :
        (if (u8 4).toNat = 0 then 1 else if (u8 4).toNat = 2 then 3 else
          if (u8 4).toNat = 4 then 2 else 4) = 2 := by
      decide
    simpa [pngPixel_encodeRaw_grayAlpha, pngPixel_colorType_grayAlpha, hbpp,
      bytesPerPixel_grayAlpha, GrayAlpha8.bytesPerPixel] using hraw
  decodeRowsLoop_encodeRaw := by
    intro bmp
    have hrows :
        decodeRowsLoopGrayAlpha (encodeRawFast bmp) bmp.size.width bmp.size.height
            GrayAlpha8.bytesPerPixel (bmp.size.width * GrayAlpha8.bytesPerPixel) 0 0
            ByteArray.empty
            (ByteArray.mk <| Array.replicate
              (bmp.size.height * (bmp.size.width * GrayAlpha8.bytesPerPixel)) 0) =
          some bmp.data := by
      rw [encodeRawFast_eq]
      simpa using (decodeRowsLoopGrayAlpha_encodeRaw (bmp := bmp))
    have hbpp :
        (if (u8 4).toNat = 0 then 1 else if (u8 4).toNat = 2 then 3 else
          if (u8 4).toNat = 4 then 2 else 4) = 2 := by
      decide
    simpa [pngPixel_decodeRowsLoop_grayAlpha, pngPixel_encodeRaw_grayAlpha,
      pngPixel_colorType_grayAlpha, hbpp, bytesPerPixel_grayAlpha, GrayAlpha8.bytesPerPixel,
      Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc] using hrows

/-- `RGB16` satisfies the generic PNG round-trip contract.
It proves exact 16-bit RGB encode/decode without sample downconversion. -/
instance : PngRoundTrip RGB16 where
  colorType_ok := by
    have : (u8 2).toNat = 0 ∨ (u8 2).toNat = 2 ∨
        (u8 2).toNat = 4 ∨ (u8 2).toNat = 6 := by decide
    simpa [pngPixel_colorType_rgb16] using this
  bitDepth_ok := by
    decide
  colorTypeBitDepth_ok := by
    decide
  bitDepth_ne_one := by
    decide
  pngBytesPerPixel_ok := by
    decide
  encodeRaw_size := by
    intro bmp
    have hraw : (encodeRawFast bmp).size =
        bmp.size.height * (bmp.size.width * RGB16.bytesPerPixel + 1) := by
      rw [encodeRawFast_eq]
      simpa [bytesPerPixel_rgb16] using encodeRaw_size (bmp := bmp)
    simpa [pngPixel_encodeRaw_rgb16, bytesPerPixel_rgb16, RGB16.bytesPerPixel] using hraw
  decodeRowsLoop_encodeRaw := by
    intro bmp
    have hrows :
        decodeRowsLoopRGB16 (encodeRawFast bmp) bmp.size.width bmp.size.height
            RGB16.bytesPerPixel (bmp.size.width * RGB16.bytesPerPixel) 0 0 ByteArray.empty
            (ByteArray.mk <| Array.replicate
              (bmp.size.height * (bmp.size.width * RGB16.bytesPerPixel)) 0) =
          some bmp.data := by
      rw [encodeRawFast_eq]
      simpa using (decodeRowsLoopRGB16_encodeRaw (bmp := bmp))
    simpa [pngPixel_decodeRowsLoop_rgb16, pngPixel_encodeRaw_rgb16,
      bytesPerPixel_rgb16, RGB16.bytesPerPixel, Nat.mul_left_comm, Nat.mul_comm,
      Nat.mul_assoc] using hrows

/-- `RGBA16` satisfies the generic PNG round-trip contract.
It proves exact 16-bit RGBA encode/decode without sample downconversion. -/
instance : PngRoundTrip RGBA16 where
  colorType_ok := by
    have : (u8 6).toNat = 0 ∨ (u8 6).toNat = 2 ∨
        (u8 6).toNat = 4 ∨ (u8 6).toNat = 6 := by decide
    simpa [pngPixel_colorType_rgba16] using this
  bitDepth_ok := by
    decide
  colorTypeBitDepth_ok := by
    decide
  bitDepth_ne_one := by
    decide
  pngBytesPerPixel_ok := by
    decide
  encodeRaw_size := by
    intro bmp
    have hraw : (encodeRawFast bmp).size =
        bmp.size.height * (bmp.size.width * RGBA16.bytesPerPixel + 1) := by
      rw [encodeRawFast_eq]
      simpa [bytesPerPixel_rgba16] using encodeRaw_size (bmp := bmp)
    simpa [pngPixel_encodeRaw_rgba16, bytesPerPixel_rgba16, RGBA16.bytesPerPixel] using hraw
  decodeRowsLoop_encodeRaw := by
    intro bmp
    have hrows :
        decodeRowsLoopRGBA16 (encodeRawFast bmp) bmp.size.width bmp.size.height
            RGBA16.bytesPerPixel (bmp.size.width * RGBA16.bytesPerPixel) 0 0 ByteArray.empty
            (ByteArray.mk <| Array.replicate
              (bmp.size.height * (bmp.size.width * RGBA16.bytesPerPixel)) 0) =
          some bmp.data := by
      rw [encodeRawFast_eq]
      simpa using (decodeRowsLoopRGBA16_encodeRaw (bmp := bmp))
    simpa [pngPixel_decodeRowsLoop_rgba16, pngPixel_encodeRaw_rgba16,
      bytesPerPixel_rgba16, RGBA16.bytesPerPixel, Nat.mul_left_comm, Nat.mul_comm,
      Nat.mul_assoc] using hrows

/-- `Gray16` satisfies the generic PNG round-trip contract.
It proves exact 16-bit grayscale encode/decode without sample downconversion. -/
instance : PngRoundTrip Gray16 where
  colorType_ok := by
    have : (u8 0).toNat = 0 ∨ (u8 0).toNat = 2 ∨
        (u8 0).toNat = 4 ∨ (u8 0).toNat = 6 := by decide
    simpa [pngPixel_colorType_gray16] using this
  bitDepth_ok := by
    decide
  colorTypeBitDepth_ok := by
    decide
  bitDepth_ne_one := by
    decide
  pngBytesPerPixel_ok := by
    decide
  encodeRaw_size := by
    intro bmp
    have hraw : (encodeRawFast bmp).size =
        bmp.size.height * (bmp.size.width * Gray16.bytesPerPixel + 1) := by
      rw [encodeRawFast_eq]
      simpa [bytesPerPixel_gray16] using encodeRaw_size (bmp := bmp)
    simpa [pngPixel_encodeRaw_gray16, bytesPerPixel_gray16, Gray16.bytesPerPixel] using hraw
  decodeRowsLoop_encodeRaw := by
    intro bmp
    have hrows :
        decodeRowsLoopGray16 (encodeRawFast bmp) bmp.size.width bmp.size.height
            Gray16.bytesPerPixel (bmp.size.width * Gray16.bytesPerPixel) 0 0 ByteArray.empty
            (ByteArray.mk <| Array.replicate
              (bmp.size.height * (bmp.size.width * Gray16.bytesPerPixel)) 0) =
          some bmp.data := by
      rw [encodeRawFast_eq]
      simpa using (decodeRowsLoopGray16_encodeRaw (bmp := bmp))
    simpa [pngPixel_decodeRowsLoop_gray16, pngPixel_encodeRaw_gray16,
      bytesPerPixel_gray16, Gray16.bytesPerPixel, Nat.mul_left_comm, Nat.mul_comm,
      Nat.mul_assoc] using hrows

/-- `GrayAlpha16` satisfies the generic PNG round-trip contract.
It proves exact 16-bit grayscale+alpha encode/decode for color type 4. -/
instance : PngRoundTrip GrayAlpha16 where
  colorType_ok := by
    have : (u8 4).toNat = 0 ∨ (u8 4).toNat = 2 ∨
        (u8 4).toNat = 4 ∨ (u8 4).toNat = 6 := by decide
    simpa [pngPixel_colorType_grayAlpha16] using this
  bitDepth_ok := by
    decide
  colorTypeBitDepth_ok := by
    decide
  bitDepth_ne_one := by
    decide
  pngBytesPerPixel_ok := by
    decide
  encodeRaw_size := by
    intro bmp
    have hraw : (encodeRawFast bmp).size =
        bmp.size.height * (bmp.size.width * GrayAlpha16.bytesPerPixel + 1) := by
      rw [encodeRawFast_eq]
      simpa [bytesPerPixel_grayAlpha16] using encodeRaw_size (bmp := bmp)
    simpa [pngPixel_encodeRaw_grayAlpha16, bytesPerPixel_grayAlpha16,
      GrayAlpha16.bytesPerPixel] using hraw
  decodeRowsLoop_encodeRaw := by
    intro bmp
    have hrows :
        decodeRowsLoopGrayAlpha16 (encodeRawFast bmp) bmp.size.width bmp.size.height
            GrayAlpha16.bytesPerPixel (bmp.size.width * GrayAlpha16.bytesPerPixel) 0 0
            ByteArray.empty
            (ByteArray.mk <| Array.replicate
              (bmp.size.height * (bmp.size.width * GrayAlpha16.bytesPerPixel)) 0) =
          some bmp.data := by
      rw [encodeRawFast_eq]
      simpa using (decodeRowsLoopGrayAlpha16_encodeRaw (bmp := bmp))
    simpa [pngPixel_decodeRowsLoop_grayAlpha16, pngPixel_encodeRaw_grayAlpha16,
      bytesPerPixel_grayAlpha16, GrayAlpha16.bytesPerPixel, Nat.mul_left_comm,
      Nat.mul_comm, Nat.mul_assoc] using hrows

-- Round-trip PNG encode/decode for bitmap payloads.
lemma decodeBitmap_encodeBitmap {px : Type u} [PixelFormat px] [Png.PixelFormat px] [PngRoundTrip px]
    (bmp : Bitmap px)
    (hw : bmp.size.width < 2 ^ 32) (hh : bmp.size.height < 2 ^ 32)
    (mode : PngEncodeMode)
    (hidat : (encodeBitmapIdat (bmp := bmp) (mode := mode)).size < 2 ^ 32) :
    Png.decodeBitmap (Png.encodeBitmap bmp hw hh mode) = some bmp := by
  have hct := PngRoundTrip.colorType_ok (px := px)
  have hbd := PngRoundTrip.bitDepth_ok (px := px)
  have hctbd := PngRoundTrip.colorTypeBitDepth_ok (px := px)
  have hbdNot1 := PngRoundTrip.bitDepth_ne_one (px := px)
  have hbpp := PngRoundTrip.pngBytesPerPixel_ok (px := px)
  have hrawEq := PngRoundTrip.encodeRaw_size (px := px) bmp
  have hrows := PngRoundTrip.decodeRowsLoop_encodeRaw (px := px) bmp
  exact
    decodeBitmap_encodeBitmap_common (bmp := bmp) (hw := hw) (hh := hh)
      (mode := mode) hidat hct hbd hctbd hbdNot1 hbpp hrawEq hrows

-- RGB-specialized wrapper for symmetry.
lemma decodeBitmap_encodeBitmap_rgb (bmp : Bitmap.RGB8)
    (hw : bmp.size.width < 2 ^ 32) (hh : bmp.size.height < 2 ^ 32)
    (mode : PngEncodeMode)
    (hidat : (encodeBitmapIdat (bmp := bmp) (mode := mode)).size < 2 ^ 32) :
    Png.decodeBitmap (Png.encodeBitmap bmp hw hh mode) = some bmp := by
  simpa using
    (decodeBitmap_encodeBitmap (px := RGB8) (bmp := bmp)
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
