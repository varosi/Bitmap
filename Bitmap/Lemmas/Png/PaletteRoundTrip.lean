import Bitmap.Lemmas.Png.Palette
import Bitmap.Lemmas.Png.EncodeDecodeFixed

namespace Bitmaps

namespace Lemmas

open Png

/-! ## Indexed-palette parsed decode round-trip layers

These theorems sit above the raw palette payload facts and below full PNG chunk
container parsing. They compose indexed raw decoding with zlib envelope proofs. -/

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

end Lemmas

end Bitmaps
