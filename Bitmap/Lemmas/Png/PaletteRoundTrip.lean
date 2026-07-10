import Bitmap.Lemmas.Png.Palette
import Bitmap.Lemmas.Png.EncodeDecodeFixed
import Bitmap.Lemmas.Png.EncodeDecodeDynamic

namespace Bitmaps

namespace Lemmas

open Png

/-! ## Indexed-palette parsed decode round-trip layers

These theorems sit above the raw palette payload facts and below full PNG chunk
container parsing. They compose indexed raw decoding with zlib envelope proofs. -/

/-- Projection used by exact indexed bitmap shape theorems.
It avoids comparing proof fields while still recording all runtime fields. -/
def indexedBitmapShape (bitmap : PngIndexedBitmap) :
    Size × Nat × PngPalette × ByteArray × Option ByteArray × Option UInt8 :=
  (bitmap.size, bitmap.bitDepth, bitmap.palette, bitmap.data,
    bitmap.transparency, bitmap.background)

/-- Projection used by exact indexed decode result shape theorems.
It records bitmap runtime fields together with preserved PNG metadata. -/
def indexedDecodeResultShape (result : PngIndexedDecodeResult) :
    (Size × Nat × PngPalette × ByteArray × Option ByteArray × Option UInt8) ×
      PngMetadata :=
  (indexedBitmapShape result.bitmap, result.metadata)

/-- A parsed non-interlaced 1/2/4-bit indexed PNG with stored zlib IDAT
decodes back to the bitmap's index bytes when the palette is exactly the
bit-depth-addressable size and all source indices fit that bit depth. -/
lemma decodeParsedIndexedBitmapWithMetadata_stored_encodeRawIndexed_none_non8_data
    (bmp : PngIndexedBitmap)
    (hbd : bmp.bitDepth = 1 ∨ bmp.bitDepth = 2 ∨ bmp.bitDepth = 4)
    (hpal : bmp.palette.entryCount = paletteIndexLimit bmp.bitDepth)
    (hrange :
      ∀ y, y < bmp.size.height → ∀ x, x < bmp.size.width →
        (bmp.data.get! (y * bmp.size.width + x)).toNat <
          paletteIndexLimit bmp.bitDepth) :
    let metadata : PngMetadata := { PngMetadata.empty with palette := some bmp.palette }
    let parsed : PngParsed :=
      { header :=
          { width := bmp.size.width, height := bmp.size.height, colorType := 3,
            bitDepth := bmp.bitDepth, interlace := 0 }
        idat := zlibCompressStored (encodeRawIndexedWithFilter bmp .none)
        metadata := metadata }
    (decodeParsedIndexedBitmapWithMetadata parsed).map (fun result => result.bitmap.data) =
      some bmp.data := by
  intro metadata parsed
  have hraw :=
    decodePaletteIndicesByInterlace_encodeRawIndexedWithFilter_none_non8
      bmp hbd bmp.palette.entryCount (by simp [hpal]) hrange
  have hrawPal :
      decodePaletteIndicesByInterlace? (encodeRawIndexedWithFilter bmp .none)
        { width := bmp.size.width, height := bmp.size.height, colorType := 3,
          bitDepth := bmp.bitDepth, interlace := 0 }
        bmp.palette.entryCount = some bmp.data := by
    simpa using hraw
  have hsize6 := zlibCompressStored_size_ge (encodeRawIndexedWithFilter bmp .none)
  have hsize2 : 2 ≤ (zlibCompressStored (encodeRawIndexedWithFilter bmp .none)).size := by
    omega
  have hvalid : bmp.data.size = bmp.size.width * bmp.size.height := bmp.valid
  unfold decodeParsedIndexedBitmapWithMetadata
  rcases hbd with hbd | hbd | hbd
  all_goals
    have hrawPalBd := by simpa [hbd] using hrawPal
    simp [parsed, metadata, PngMetadata.empty, hbd, hsize2, hvalid, hrawPalBd,
      zlibDecompressStored_zlibCompressStored, pngColorTypeBitDepthSupported]

/-- A parsed non-interlaced 8-bit indexed PNG with fixed-Huffman zlib IDAT and
a full palette decodes back to the bitmap's index bytes. This covers the
default indexed encoder compression mode below chunk parsing. -/
lemma decodeParsedIndexedBitmapWithMetadata_fixed_encodeRawIndexed_none_8_256_data
    (bmp : PngIndexedBitmap) (hbd : bmp.bitDepth = 8)
    (hpal : bmp.palette.entryCount = 256) :
    let metadata : PngMetadata := { PngMetadata.empty with palette := some bmp.palette }
    let parsed : PngParsed :=
      { header :=
          { width := bmp.size.width, height := bmp.size.height, colorType := 3,
            bitDepth := 8, interlace := 0 }
        idat := zlibCompressFixed (encodeRawIndexedWithFilter bmp .none)
        metadata := metadata }
    (decodeParsedIndexedBitmapWithMetadata parsed).map (fun result => result.bitmap.data) =
      some bmp.data := by
  intro metadata parsed
  have hraw :=
    decodePaletteIndicesByInterlace_encodeRawIndexedWithFilter_none_8_256 bmp hbd
  have hrawPal :
      decodePaletteIndicesByInterlace? (encodeRawIndexedWithFilter bmp .none)
        { width := bmp.size.width, height := bmp.size.height, colorType := 3,
          bitDepth := 8, interlace := 0 }
        bmp.palette.entryCount = some bmp.data := by
    simpa [hpal] using hraw
  have hsize6 := zlibCompressFixed_size_ge (encodeRawIndexedWithFilter bmp .none)
  have hsize2 : 2 ≤ (zlibCompressFixed (encodeRawIndexedWithFilter bmp .none)).size := by
    omega
  have hvalid : bmp.data.size = bmp.size.width * bmp.size.height := bmp.valid
  unfold decodeParsedIndexedBitmapWithMetadata
  simp [parsed, metadata, PngMetadata.empty, hsize2, hvalid, hrawPal,
    zlibDecompressStored_zlibCompressFixed_none, zlibDecompress_zlibCompressFixed,
    pngColorTypeBitDepthSupported]

/-- A parsed non-interlaced 1/2/4-bit indexed PNG with fixed-Huffman zlib IDAT
decodes back to the bitmap's index bytes under the same explicit packed-index
range assumptions as the raw theorem. -/
lemma decodeParsedIndexedBitmapWithMetadata_fixed_encodeRawIndexed_none_non8_data
    (bmp : PngIndexedBitmap)
    (hbd : bmp.bitDepth = 1 ∨ bmp.bitDepth = 2 ∨ bmp.bitDepth = 4)
    (hpal : bmp.palette.entryCount = paletteIndexLimit bmp.bitDepth)
    (hrange :
      ∀ y, y < bmp.size.height → ∀ x, x < bmp.size.width →
        (bmp.data.get! (y * bmp.size.width + x)).toNat <
          paletteIndexLimit bmp.bitDepth) :
    let metadata : PngMetadata := { PngMetadata.empty with palette := some bmp.palette }
    let parsed : PngParsed :=
      { header :=
          { width := bmp.size.width, height := bmp.size.height, colorType := 3,
            bitDepth := bmp.bitDepth, interlace := 0 }
        idat := zlibCompressFixed (encodeRawIndexedWithFilter bmp .none)
        metadata := metadata }
    (decodeParsedIndexedBitmapWithMetadata parsed).map (fun result => result.bitmap.data) =
      some bmp.data := by
  intro metadata parsed
  have hraw :=
    decodePaletteIndicesByInterlace_encodeRawIndexedWithFilter_none_non8
      bmp hbd bmp.palette.entryCount (by simp [hpal]) hrange
  have hrawPal :
      decodePaletteIndicesByInterlace? (encodeRawIndexedWithFilter bmp .none)
        { width := bmp.size.width, height := bmp.size.height, colorType := 3,
          bitDepth := bmp.bitDepth, interlace := 0 }
        bmp.palette.entryCount = some bmp.data := by
    simpa using hraw
  have hsize6 := zlibCompressFixed_size_ge (encodeRawIndexedWithFilter bmp .none)
  have hsize2 : 2 ≤ (zlibCompressFixed (encodeRawIndexedWithFilter bmp .none)).size := by
    omega
  have hvalid : bmp.data.size = bmp.size.width * bmp.size.height := bmp.valid
  unfold decodeParsedIndexedBitmapWithMetadata
  rcases hbd with hbd | hbd | hbd
  all_goals
    have hrawPalBd := by simpa [hbd] using hrawPal
    simp [parsed, metadata, PngMetadata.empty, hbd, hsize2, hvalid, hrawPalBd,
      zlibDecompressStored_zlibCompressFixed_none, zlibDecompress_zlibCompressFixed,
      pngColorTypeBitDepthSupported]

/-- A parsed non-interlaced 8-bit indexed PNG with dynamic-Huffman zlib IDAT
and a full palette decodes back to the bitmap's index bytes. This covers the
generated dynamic indexed encoder mode below chunk parsing. -/
lemma decodeParsedIndexedBitmapWithMetadata_dynamic_encodeRawIndexed_none_8_256_data
    (bmp : PngIndexedBitmap) (hbd : bmp.bitDepth = 8)
    (hpal : bmp.palette.entryCount = 256) :
    let metadata : PngMetadata := { PngMetadata.empty with palette := some bmp.palette }
    let parsed : PngParsed :=
      { header :=
          { width := bmp.size.width, height := bmp.size.height, colorType := 3,
            bitDepth := 8, interlace := 0 }
        idat := zlibCompressDynamic (encodeRawIndexedWithFilter bmp .none)
        metadata := metadata }
    (decodeParsedIndexedBitmapWithMetadata parsed).map (fun result => result.bitmap.data) =
      some bmp.data := by
  intro metadata parsed
  have hraw :=
    decodePaletteIndicesByInterlace_encodeRawIndexedWithFilter_none_8_256 bmp hbd
  have hrawPal :
      decodePaletteIndicesByInterlace? (encodeRawIndexedWithFilter bmp .none)
        { width := bmp.size.width, height := bmp.size.height, colorType := 3,
          bitDepth := 8, interlace := 0 }
        bmp.palette.entryCount = some bmp.data := by
    simpa [hpal] using hraw
  have hsize6 := zlibCompressDynamic_size_ge (encodeRawIndexedWithFilter bmp .none)
  have hsize2 : 2 ≤ (zlibCompressDynamic (encodeRawIndexedWithFilter bmp .none)).size := by
    omega
  have hvalid : bmp.data.size = bmp.size.width * bmp.size.height := bmp.valid
  unfold decodeParsedIndexedBitmapWithMetadata
  simp [parsed, metadata, PngMetadata.empty, hsize2, hvalid, hrawPal,
    zlibDecompressStored_zlibCompressDynamic_none, zlibDecompress_zlibCompressDynamic,
    pngColorTypeBitDepthSupported]

/-- A parsed non-interlaced 1/2/4-bit indexed PNG with dynamic-Huffman zlib IDAT
decodes back to the bitmap's index bytes under the same explicit packed-index
range assumptions as the raw theorem. -/
lemma decodeParsedIndexedBitmapWithMetadata_dynamic_encodeRawIndexed_none_non8_data
    (bmp : PngIndexedBitmap)
    (hbd : bmp.bitDepth = 1 ∨ bmp.bitDepth = 2 ∨ bmp.bitDepth = 4)
    (hpal : bmp.palette.entryCount = paletteIndexLimit bmp.bitDepth)
    (hrange :
      ∀ y, y < bmp.size.height → ∀ x, x < bmp.size.width →
        (bmp.data.get! (y * bmp.size.width + x)).toNat <
          paletteIndexLimit bmp.bitDepth) :
    let metadata : PngMetadata := { PngMetadata.empty with palette := some bmp.palette }
    let parsed : PngParsed :=
      { header :=
          { width := bmp.size.width, height := bmp.size.height, colorType := 3,
            bitDepth := bmp.bitDepth, interlace := 0 }
        idat := zlibCompressDynamic (encodeRawIndexedWithFilter bmp .none)
        metadata := metadata }
    (decodeParsedIndexedBitmapWithMetadata parsed).map (fun result => result.bitmap.data) =
      some bmp.data := by
  intro metadata parsed
  have hraw :=
    decodePaletteIndicesByInterlace_encodeRawIndexedWithFilter_none_non8
      bmp hbd bmp.palette.entryCount (by simp [hpal]) hrange
  have hrawPal :
      decodePaletteIndicesByInterlace? (encodeRawIndexedWithFilter bmp .none)
        { width := bmp.size.width, height := bmp.size.height, colorType := 3,
          bitDepth := bmp.bitDepth, interlace := 0 }
        bmp.palette.entryCount = some bmp.data := by
    simpa using hraw
  have hsize6 := zlibCompressDynamic_size_ge (encodeRawIndexedWithFilter bmp .none)
  have hsize2 : 2 ≤ (zlibCompressDynamic (encodeRawIndexedWithFilter bmp .none)).size := by
    omega
  have hvalid : bmp.data.size = bmp.size.width * bmp.size.height := bmp.valid
  unfold decodeParsedIndexedBitmapWithMetadata
  rcases hbd with hbd | hbd | hbd
  all_goals
    have hrawPalBd := by simpa [hbd] using hrawPal
    simp [parsed, metadata, PngMetadata.empty, hbd, hsize2, hvalid, hrawPalBd,
      zlibDecompressStored_zlibCompressDynamic_none, zlibDecompress_zlibCompressDynamic,
      pngColorTypeBitDepthSupported]

/-- A parsed non-interlaced 8-bit indexed PNG with stored zlib IDAT decodes
back to the bitmap's index bytes for any palette containing every source
index. This generalizes the full-256 stored wrapper. -/
lemma decodeParsedIndexedBitmapWithMetadata_stored_encodeRawIndexed_none_8_paletteRange_data
    (bmp : PngIndexedBitmap) (hbd : bmp.bitDepth = 8)
    (hpalFits : bmp.palette.entryCount ≤ paletteIndexLimit bmp.bitDepth)
    (hrange :
      ∀ y, y < bmp.size.height → ∀ x, x < bmp.size.width →
        (bmp.data.get! (y * bmp.size.width + x)).toNat < bmp.palette.entryCount) :
    let metadata : PngMetadata := { PngMetadata.empty with palette := some bmp.palette }
    let parsed : PngParsed :=
      { header :=
          { width := bmp.size.width, height := bmp.size.height, colorType := 3,
            bitDepth := 8, interlace := 0 }
        idat := zlibCompressStored (encodeRawIndexedWithFilter bmp .none)
        metadata := metadata }
    (decodeParsedIndexedBitmapWithMetadata parsed).map (fun result => result.bitmap.data) =
      some bmp.data := by
  intro metadata parsed
  have hraw :=
    decodePaletteIndicesByInterlace_encodeRawIndexedWithFilter_none_8_paletteRange
      bmp hbd bmp.palette.entryCount hpalFits hrange
  have hrawPal :
      decodePaletteIndicesByInterlace? (encodeRawIndexedWithFilter bmp .none)
        { width := bmp.size.width, height := bmp.size.height, colorType := 3,
          bitDepth := 8, interlace := 0 }
        bmp.palette.entryCount = some bmp.data := by
    simpa using hraw
  have hsize6 := zlibCompressStored_size_ge (encodeRawIndexedWithFilter bmp .none)
  have hsize2 : 2 ≤ (zlibCompressStored (encodeRawIndexedWithFilter bmp .none)).size := by
    omega
  have hvalid : bmp.data.size = bmp.size.width * bmp.size.height := bmp.valid
  unfold decodeParsedIndexedBitmapWithMetadata
  simp [parsed, metadata, PngMetadata.empty, hsize2, hvalid, hrawPal,
    zlibDecompressStored_zlibCompressStored, pngColorTypeBitDepthSupported]

/-- A parsed non-interlaced 1/2/4-bit indexed PNG with stored zlib IDAT decodes
back to the bitmap's index bytes for any palette containing every source index
and fitting the selected bit depth. -/
lemma decodeParsedIndexedBitmapWithMetadata_stored_encodeRawIndexed_none_non8_paletteRange_data
    (bmp : PngIndexedBitmap)
    (hbd : bmp.bitDepth = 1 ∨ bmp.bitDepth = 2 ∨ bmp.bitDepth = 4)
    (hpalFits : bmp.palette.entryCount ≤ paletteIndexLimit bmp.bitDepth)
    (hrange :
      ∀ y, y < bmp.size.height → ∀ x, x < bmp.size.width →
        (bmp.data.get! (y * bmp.size.width + x)).toNat < bmp.palette.entryCount) :
    let metadata : PngMetadata := { PngMetadata.empty with palette := some bmp.palette }
    let parsed : PngParsed :=
      { header :=
          { width := bmp.size.width, height := bmp.size.height, colorType := 3,
            bitDepth := bmp.bitDepth, interlace := 0 }
        idat := zlibCompressStored (encodeRawIndexedWithFilter bmp .none)
        metadata := metadata }
    (decodeParsedIndexedBitmapWithMetadata parsed).map (fun result => result.bitmap.data) =
      some bmp.data := by
  intro metadata parsed
  have hraw :=
    decodePaletteIndicesByInterlace_encodeRawIndexedWithFilter_none_non8_paletteRange
      bmp hbd bmp.palette.entryCount hpalFits hrange
  have hrawPal :
      decodePaletteIndicesByInterlace? (encodeRawIndexedWithFilter bmp .none)
        { width := bmp.size.width, height := bmp.size.height, colorType := 3,
          bitDepth := bmp.bitDepth, interlace := 0 }
        bmp.palette.entryCount = some bmp.data := by
    simpa using hraw
  have hsize6 := zlibCompressStored_size_ge (encodeRawIndexedWithFilter bmp .none)
  have hsize2 : 2 ≤ (zlibCompressStored (encodeRawIndexedWithFilter bmp .none)).size := by
    omega
  have hvalid : bmp.data.size = bmp.size.width * bmp.size.height := bmp.valid
  unfold decodeParsedIndexedBitmapWithMetadata
  rcases hbd with hbd | hbd | hbd
  all_goals
    have hrawPalBd := by simpa [hbd] using hrawPal
    simp [parsed, metadata, PngMetadata.empty, hbd, hsize2, hvalid, hrawPalBd,
      zlibDecompressStored_zlibCompressStored, pngColorTypeBitDepthSupported]

/-- Fixed-Huffman parsed 8-bit indexed decode round-trips any source-index-safe
palette, not only a full 256-entry palette. -/
lemma decodeParsedIndexedBitmapWithMetadata_fixed_encodeRawIndexed_none_8_paletteRange_data
    (bmp : PngIndexedBitmap) (hbd : bmp.bitDepth = 8)
    (hpalFits : bmp.palette.entryCount ≤ paletteIndexLimit bmp.bitDepth)
    (hrange :
      ∀ y, y < bmp.size.height → ∀ x, x < bmp.size.width →
        (bmp.data.get! (y * bmp.size.width + x)).toNat < bmp.palette.entryCount) :
    let metadata : PngMetadata := { PngMetadata.empty with palette := some bmp.palette }
    let parsed : PngParsed :=
      { header :=
          { width := bmp.size.width, height := bmp.size.height, colorType := 3,
            bitDepth := 8, interlace := 0 }
        idat := zlibCompressFixed (encodeRawIndexedWithFilter bmp .none)
        metadata := metadata }
    (decodeParsedIndexedBitmapWithMetadata parsed).map (fun result => result.bitmap.data) =
      some bmp.data := by
  intro metadata parsed
  have hraw :=
    decodePaletteIndicesByInterlace_encodeRawIndexedWithFilter_none_8_paletteRange
      bmp hbd bmp.palette.entryCount hpalFits hrange
  have hrawPal :
      decodePaletteIndicesByInterlace? (encodeRawIndexedWithFilter bmp .none)
        { width := bmp.size.width, height := bmp.size.height, colorType := 3,
          bitDepth := 8, interlace := 0 }
        bmp.palette.entryCount = some bmp.data := by
    simpa using hraw
  have hsize6 := zlibCompressFixed_size_ge (encodeRawIndexedWithFilter bmp .none)
  have hsize2 : 2 ≤ (zlibCompressFixed (encodeRawIndexedWithFilter bmp .none)).size := by
    omega
  have hvalid : bmp.data.size = bmp.size.width * bmp.size.height := bmp.valid
  unfold decodeParsedIndexedBitmapWithMetadata
  simp [parsed, metadata, PngMetadata.empty, hsize2, hvalid, hrawPal,
    zlibDecompressStored_zlibCompressFixed_none, zlibDecompress_zlibCompressFixed,
    pngColorTypeBitDepthSupported]

/-- Fixed-Huffman parsed 1/2/4-bit indexed decode round-trips any
source-index-safe palette that fits the selected bit depth. -/
lemma decodeParsedIndexedBitmapWithMetadata_fixed_encodeRawIndexed_none_non8_paletteRange_data
    (bmp : PngIndexedBitmap)
    (hbd : bmp.bitDepth = 1 ∨ bmp.bitDepth = 2 ∨ bmp.bitDepth = 4)
    (hpalFits : bmp.palette.entryCount ≤ paletteIndexLimit bmp.bitDepth)
    (hrange :
      ∀ y, y < bmp.size.height → ∀ x, x < bmp.size.width →
        (bmp.data.get! (y * bmp.size.width + x)).toNat < bmp.palette.entryCount) :
    let metadata : PngMetadata := { PngMetadata.empty with palette := some bmp.palette }
    let parsed : PngParsed :=
      { header :=
          { width := bmp.size.width, height := bmp.size.height, colorType := 3,
            bitDepth := bmp.bitDepth, interlace := 0 }
        idat := zlibCompressFixed (encodeRawIndexedWithFilter bmp .none)
        metadata := metadata }
    (decodeParsedIndexedBitmapWithMetadata parsed).map (fun result => result.bitmap.data) =
      some bmp.data := by
  intro metadata parsed
  have hraw :=
    decodePaletteIndicesByInterlace_encodeRawIndexedWithFilter_none_non8_paletteRange
      bmp hbd bmp.palette.entryCount hpalFits hrange
  have hrawPal :
      decodePaletteIndicesByInterlace? (encodeRawIndexedWithFilter bmp .none)
        { width := bmp.size.width, height := bmp.size.height, colorType := 3,
          bitDepth := bmp.bitDepth, interlace := 0 }
        bmp.palette.entryCount = some bmp.data := by
    simpa using hraw
  have hsize6 := zlibCompressFixed_size_ge (encodeRawIndexedWithFilter bmp .none)
  have hsize2 : 2 ≤ (zlibCompressFixed (encodeRawIndexedWithFilter bmp .none)).size := by
    omega
  have hvalid : bmp.data.size = bmp.size.width * bmp.size.height := bmp.valid
  unfold decodeParsedIndexedBitmapWithMetadata
  rcases hbd with hbd | hbd | hbd
  all_goals
    have hrawPalBd := by simpa [hbd] using hrawPal
    simp [parsed, metadata, PngMetadata.empty, hbd, hsize2, hvalid, hrawPalBd,
      zlibDecompressStored_zlibCompressFixed_none, zlibDecompress_zlibCompressFixed,
      pngColorTypeBitDepthSupported]

/-- Dynamic-Huffman parsed 8-bit indexed decode round-trips any
source-index-safe palette, not only a full 256-entry palette. -/
lemma decodeParsedIndexedBitmapWithMetadata_dynamic_encodeRawIndexed_none_8_paletteRange_data
    (bmp : PngIndexedBitmap) (hbd : bmp.bitDepth = 8)
    (hpalFits : bmp.palette.entryCount ≤ paletteIndexLimit bmp.bitDepth)
    (hrange :
      ∀ y, y < bmp.size.height → ∀ x, x < bmp.size.width →
        (bmp.data.get! (y * bmp.size.width + x)).toNat < bmp.palette.entryCount) :
    let metadata : PngMetadata := { PngMetadata.empty with palette := some bmp.palette }
    let parsed : PngParsed :=
      { header :=
          { width := bmp.size.width, height := bmp.size.height, colorType := 3,
            bitDepth := 8, interlace := 0 }
        idat := zlibCompressDynamic (encodeRawIndexedWithFilter bmp .none)
        metadata := metadata }
    (decodeParsedIndexedBitmapWithMetadata parsed).map (fun result => result.bitmap.data) =
      some bmp.data := by
  intro metadata parsed
  have hraw :=
    decodePaletteIndicesByInterlace_encodeRawIndexedWithFilter_none_8_paletteRange
      bmp hbd bmp.palette.entryCount hpalFits hrange
  have hrawPal :
      decodePaletteIndicesByInterlace? (encodeRawIndexedWithFilter bmp .none)
        { width := bmp.size.width, height := bmp.size.height, colorType := 3,
          bitDepth := 8, interlace := 0 }
        bmp.palette.entryCount = some bmp.data := by
    simpa using hraw
  have hsize6 := zlibCompressDynamic_size_ge (encodeRawIndexedWithFilter bmp .none)
  have hsize2 : 2 ≤ (zlibCompressDynamic (encodeRawIndexedWithFilter bmp .none)).size := by
    omega
  have hvalid : bmp.data.size = bmp.size.width * bmp.size.height := bmp.valid
  unfold decodeParsedIndexedBitmapWithMetadata
  simp [parsed, metadata, PngMetadata.empty, hsize2, hvalid, hrawPal,
    zlibDecompressStored_zlibCompressDynamic_none, zlibDecompress_zlibCompressDynamic,
    pngColorTypeBitDepthSupported]

/-- Dynamic-Huffman parsed 1/2/4-bit indexed decode round-trips any
source-index-safe palette that fits the selected bit depth. -/
lemma decodeParsedIndexedBitmapWithMetadata_dynamic_encodeRawIndexed_none_non8_paletteRange_data
    (bmp : PngIndexedBitmap)
    (hbd : bmp.bitDepth = 1 ∨ bmp.bitDepth = 2 ∨ bmp.bitDepth = 4)
    (hpalFits : bmp.palette.entryCount ≤ paletteIndexLimit bmp.bitDepth)
    (hrange :
      ∀ y, y < bmp.size.height → ∀ x, x < bmp.size.width →
        (bmp.data.get! (y * bmp.size.width + x)).toNat < bmp.palette.entryCount) :
    let metadata : PngMetadata := { PngMetadata.empty with palette := some bmp.palette }
    let parsed : PngParsed :=
      { header :=
          { width := bmp.size.width, height := bmp.size.height, colorType := 3,
            bitDepth := bmp.bitDepth, interlace := 0 }
        idat := zlibCompressDynamic (encodeRawIndexedWithFilter bmp .none)
        metadata := metadata }
    (decodeParsedIndexedBitmapWithMetadata parsed).map (fun result => result.bitmap.data) =
      some bmp.data := by
  intro metadata parsed
  have hraw :=
    decodePaletteIndicesByInterlace_encodeRawIndexedWithFilter_none_non8_paletteRange
      bmp hbd bmp.palette.entryCount hpalFits hrange
  have hrawPal :
      decodePaletteIndicesByInterlace? (encodeRawIndexedWithFilter bmp .none)
        { width := bmp.size.width, height := bmp.size.height, colorType := 3,
          bitDepth := bmp.bitDepth, interlace := 0 }
        bmp.palette.entryCount = some bmp.data := by
    simpa using hraw
  have hsize6 := zlibCompressDynamic_size_ge (encodeRawIndexedWithFilter bmp .none)
  have hsize2 : 2 ≤ (zlibCompressDynamic (encodeRawIndexedWithFilter bmp .none)).size := by
    omega
  have hvalid : bmp.data.size = bmp.size.width * bmp.size.height := bmp.valid
  unfold decodeParsedIndexedBitmapWithMetadata
  rcases hbd with hbd | hbd | hbd
  all_goals
    have hrawPalBd := by simpa [hbd] using hrawPal
    simp [parsed, metadata, PngMetadata.empty, hbd, hsize2, hvalid, hrawPalBd,
      zlibDecompressStored_zlibCompressDynamic_none, zlibDecompress_zlibCompressDynamic,
      pngColorTypeBitDepthSupported]

/-- Parsed indexed decode reconstructs the complete runtime shape for any
supported bit depth, source-index-safe palette, filter-0 rows, and supported
zlib mode. This strengthens the data-only parsed round-trip facts. -/
lemma decodeParsedIndexedBitmapWithMetadata_encodeRawIndexed_none_paletteRange_shape
    (mode : PngEncodeMode) (bmp : PngIndexedBitmap)
    (hbd : bmp.bitDepth = 1 ∨ bmp.bitDepth = 2 ∨ bmp.bitDepth = 4 ∨ bmp.bitDepth = 8)
    (hpalFits : bmp.palette.entryCount ≤ paletteIndexLimit bmp.bitDepth)
    (hrange :
      ∀ y, y < bmp.size.height → ∀ x, x < bmp.size.width →
        (bmp.data.get! (y * bmp.size.width + x)).toNat < bmp.palette.entryCount) :
    let metadata : PngMetadata := { PngMetadata.empty with palette := some bmp.palette }
    let parsed : PngParsed :=
      { header :=
          { width := bmp.size.width, height := bmp.size.height, colorType := 3,
            bitDepth := bmp.bitDepth, interlace := 0 }
        idat :=
          match mode with
          | .stored => zlibCompressStored (encodeRawIndexedWithFilter bmp .none)
          | .fixed => zlibCompressFixed (encodeRawIndexedWithFilter bmp .none)
          | .dynamic => zlibCompressDynamic (encodeRawIndexedWithFilter bmp .none)
        metadata := metadata }
    (decodeParsedIndexedBitmapWithMetadata parsed).map indexedDecodeResultShape =
      some
        (indexedBitmapShape
          { size := bmp.size
            bitDepth := bmp.bitDepth
            palette := bmp.palette
            data := bmp.data
            transparency := none
            background := none
            valid := bmp.valid },
          metadata) := by
  intro metadata parsed
  have hrawPal :
      decodePaletteIndicesByInterlace? (encodeRawIndexedWithFilter bmp .none)
        { width := bmp.size.width, height := bmp.size.height, colorType := 3,
          bitDepth := bmp.bitDepth, interlace := 0 }
        bmp.palette.entryCount = some bmp.data := by
    rcases hbd with hbd | hbd | hbd | hbd
    · have hraw :=
        decodePaletteIndicesByInterlace_encodeRawIndexedWithFilter_none_non8_paletteRange
          bmp (Or.inl hbd) bmp.palette.entryCount hpalFits hrange
      simpa using hraw
    · have hraw :=
        decodePaletteIndicesByInterlace_encodeRawIndexedWithFilter_none_non8_paletteRange
          bmp (Or.inr (Or.inl hbd)) bmp.palette.entryCount hpalFits hrange
      simpa using hraw
    · have hraw :=
        decodePaletteIndicesByInterlace_encodeRawIndexedWithFilter_none_non8_paletteRange
          bmp (Or.inr (Or.inr hbd)) bmp.palette.entryCount hpalFits hrange
      simpa using hraw
    · have hraw :=
        decodePaletteIndicesByInterlace_encodeRawIndexedWithFilter_none_8_paletteRange
          bmp hbd bmp.palette.entryCount hpalFits hrange
      simpa [hbd] using hraw
  have hvalid : bmp.data.size = bmp.size.width * bmp.size.height := bmp.valid
  unfold decodeParsedIndexedBitmapWithMetadata
  cases mode
  · have hsize6 := zlibCompressStored_size_ge (encodeRawIndexedWithFilter bmp .none)
    have hsize2 :
        2 ≤ (zlibCompressStored (encodeRawIndexedWithFilter bmp .none)).size := by
      omega
    rcases hbd with hbd | hbd | hbd | hbd
    all_goals
      have hrawPalBd := by simpa [hbd] using hrawPal
      simp [parsed, metadata, indexedDecodeResultShape, indexedBitmapShape,
        PngMetadata.empty, hbd, hsize2, hvalid, hrawPalBd,
        zlibDecompressStored_zlibCompressStored, pngColorTypeBitDepthSupported]
  · have hsize6 := zlibCompressFixed_size_ge (encodeRawIndexedWithFilter bmp .none)
    have hsize2 :
        2 ≤ (zlibCompressFixed (encodeRawIndexedWithFilter bmp .none)).size := by
      omega
    rcases hbd with hbd | hbd | hbd | hbd
    all_goals
      have hrawPalBd := by simpa [hbd] using hrawPal
      simp [parsed, metadata, indexedDecodeResultShape, indexedBitmapShape,
        PngMetadata.empty, hbd, hsize2, hvalid, hrawPalBd,
        zlibDecompressStored_zlibCompressFixed_none, zlibDecompress_zlibCompressFixed,
        pngColorTypeBitDepthSupported]
  · have hsize6 := zlibCompressDynamic_size_ge (encodeRawIndexedWithFilter bmp .none)
    have hsize2 :
        2 ≤ (zlibCompressDynamic (encodeRawIndexedWithFilter bmp .none)).size := by
      omega
    rcases hbd with hbd | hbd | hbd | hbd
    all_goals
      have hrawPalBd := by simpa [hbd] using hrawPal
      simp [parsed, metadata, indexedDecodeResultShape, indexedBitmapShape,
        PngMetadata.empty, hbd, hsize2, hvalid, hrawPalBd,
        zlibDecompressStored_zlibCompressDynamic_none, zlibDecompress_zlibCompressDynamic,
        pngColorTypeBitDepthSupported]

end Lemmas

end Bitmaps
