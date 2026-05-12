import Bitmap.Png
import Bitmap.Lemmas.Png.Adam7
import Bitmap.Lemmas.Png.EncodeDecodeBase

namespace Bitmaps

namespace Lemmas

open Png

/-! ## 1-bit grayscale helper facts

These lemmas document the packed row geometry used by PNG color type 0 at bit
depth 1. They are focused helper coverage rather than a full container theorem. -/

/-- A packed Gray1 row uses the PNG/RFC byte count formula.
This pins the row-size helper used by encoder, decoder, and Adam7 scatter. -/
@[simp] lemma gray1RowBytes_eq (w : Nat) :
    gray1RowBytes w = (w + 7) / 8 := by
  rfl

/-- Packed Gray1 image data is height times packed row bytes.
This is the storage invariant carried by `BitmapGray1`. -/
@[simp] lemma gray1DataSize_eq (w h : Nat) :
    gray1DataSize w h = h * gray1RowBytes w := by
  rfl

/-- PNG allows grayscale bit depth 1.
This is the positive validation fact for native `BitmapGray1` files. -/
@[simp] lemma pngColorTypeBitDepthSupported_gray1 :
    pngColorTypeBitDepthSupported 0 1 = true := by
  rfl

/-- PNG rejects truecolor RGB at bit depth 1.
This records the spec boundary that keeps `PixelRGB1` out of scope. -/
@[simp] lemma pngColorTypeBitDepthSupported_rgb1_false :
    pngColorTypeBitDepthSupported 2 1 = false := by
  rfl

/-- PNG row-byte calculation for Gray1 matches packed bitmap row storage.
This keeps parser-side row sizing aligned with `BitmapGray1`. -/
lemma pngRowBytes_gray1 (w : Nat) :
    pngRowBytesForColorTypeAndBitDepth? w 0 1 = some (gray1RowBytes w) := by
  simp [pngRowBytesForColorTypeAndBitDepth?, pngBitsPerPixelForColorTypeAndBitDepth?,
    pngChannelCountForColorType?, gray1RowBytes]

/-- Non-interlaced Gray1 images bypass Adam7 normalization unchanged.
This is the bit-packed analogue of the byte-oriented normalization lemma. -/
@[simp] lemma normalizeGray1RawByInterlace_zero (raw : ByteArray) (hdr : PngHeader)
    (hinterlace : hdr.interlace = 0) :
    normalizeGray1RawByInterlace? raw hdr = some raw := by
  simp [normalizeGray1RawByInterlace?, hinterlace]

/-- Converting packed Gray1 flat rows to filter-0 raw rows has the expected size.
This validates the normalized row envelope consumed by the exact Gray1 decoder. -/
lemma gray1FlatToFilterZeroRaw_size (flat : ByteArray) (w h : Nat)
    (hflat : flat.size = gray1DataSize w h) :
    (gray1FlatToFilterZeroRaw flat w h).size = h * (gray1RowBytes w + 1) := by
  let rowBytes := gray1RowBytes w
  let rawSize := h * (rowBytes + 1)
  have hraw : (ByteArray.mk (Array.replicate rawSize 0)).size = h * (rowBytes + 1) := by
    simp [rawSize, ByteArray.size, Array.size_replicate]
  unfold gray1FlatToFilterZeroRaw
  have hsize :=
    adam7FlatToRawLoop_size (flat := flat) (rowBytes := rowBytes) (h := h) (y := 0)
      (raw := ByteArray.mk (Array.replicate rawSize 0)) (by simpa [gray1DataSize, rowBytes] using hflat) hraw
  calc
    (adam7FlatToRawLoop flat rowBytes h 0
        (ByteArray.mk (Array.replicate rawSize 0))).size =
        (ByteArray.mk (Array.replicate rawSize 0)).size := hsize
    _ = h * (gray1RowBytes w + 1) := by
          simp [rawSize, rowBytes, ByteArray.size, Array.size_replicate]

/-- The Gray1 encoder emits one filter byte plus one packed row per image row.
This is the size fact needed before proving full Gray1 container round-trips. -/
lemma encodeRawGray1_size (bmp : BitmapGray1) :
    (encodeRawGray1 bmp).size =
      bmp.size.height * (gray1RowBytes bmp.size.width + 1) := by
  let rowBytes := gray1RowBytes bmp.size.width
  let rawSize := bmp.size.height * (rowBytes + 1)
  have hraw : (ByteArray.mk (Array.replicate rawSize 0)).size =
      bmp.size.height * (rowBytes + 1) := by
    simp [rawSize, ByteArray.size, Array.size_replicate]
  have hdata : bmp.data.size = bmp.size.height * rowBytes := by
    simpa [gray1DataSize, rowBytes] using bmp.valid
  unfold encodeRawGray1
  have hsize :=
    encodeRawPrefix_size (data := bmp.data) (rowBytes := rowBytes)
      (h := bmp.size.height) (y := bmp.size.height)
      (raw := ByteArray.mk (Array.replicate rawSize 0)) hdata hraw (Nat.le_refl _)
  calc
    (encodeRawPrefix bmp.data rowBytes bmp.size.height
        (ByteArray.mk (Array.replicate rawSize 0))).size =
        (ByteArray.mk (Array.replicate rawSize 0)).size := hsize
    _ = bmp.size.height * (gray1RowBytes bmp.size.width + 1) := by
          simpa [rowBytes] using hraw

end Lemmas

end Bitmaps
