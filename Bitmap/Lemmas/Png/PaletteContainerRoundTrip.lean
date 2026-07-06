import Bitmap.Lemmas.Png.PaletteContainerSpec
import Bitmap.Lemmas.Png.PaletteRoundTrip

namespace Bitmaps

namespace Lemmas

open Png

/-! ## Indexed-palette container decode round-trip layers

These theorems compose the palette container parser scaffold with the parsed
indexed decode round-trip facts.  They cover explicit 8-bit indexed inputs with
a full 256-entry palette and filter-0 rows, across stored, fixed, and dynamic
zlib payloads. -/

namespace PaletteContainerSpec

/-- Metadata-aware decode over a stored-zlib palette container returns the
original index bytes for 8-bit full-palette filter-0 inputs. -/
theorem decodeIndexedBitmapWithMetadata_stored_encodeRawIndexed_none_8_256_data
    (s : PaletteContainerSpec) (bmp : PngIndexedBitmap)
    (hHeader :
      s.header =
        { width := bmp.size.width, height := bmp.size.height, colorType := 3,
          bitDepth := 8, interlace := 0 })
    (hPalette : s.palette = bmp.palette)
    (hIdat : s.idatData = zlibCompressStored (encodeRawIndexedWithFilter bmp .none))
    (hIdatSize : s.idatData.size < 2 ^ 32)
    (hbd : bmp.bitDepth = 8)
    (hpal : bmp.palette.entryCount = 256) :
    (decodeIndexedBitmapWithMetadata s.bytes).map (fun result => result.bitmap.data) =
      some bmp.data := by
  unfold decodeIndexedBitmapWithMetadata
  have hParse (h : 8 ≤ s.bytes.size) :
      parsePngWithMetadata s.bytes h = some (parsed s) := by
    simpa using parsePngWithMetadata_accepts s hIdatSize
  simp [s.bytes_size_ge_8, hParse]
  have hParsed :=
    decodeParsedIndexedBitmapWithMetadata_stored_encodeRawIndexed_none_8_256_data
      bmp hbd hpal
  simpa [parsed, metadata, hHeader, hPalette, hIdat] using hParsed

/-- Metadata-aware decode over a fixed-Huffman palette container returns the
original index bytes for 8-bit full-palette filter-0 inputs. -/
theorem decodeIndexedBitmapWithMetadata_fixed_encodeRawIndexed_none_8_256_data
    (s : PaletteContainerSpec) (bmp : PngIndexedBitmap)
    (hHeader :
      s.header =
        { width := bmp.size.width, height := bmp.size.height, colorType := 3,
          bitDepth := 8, interlace := 0 })
    (hPalette : s.palette = bmp.palette)
    (hIdat : s.idatData = zlibCompressFixed (encodeRawIndexedWithFilter bmp .none))
    (hIdatSize : s.idatData.size < 2 ^ 32)
    (hbd : bmp.bitDepth = 8)
    (hpal : bmp.palette.entryCount = 256) :
    (decodeIndexedBitmapWithMetadata s.bytes).map (fun result => result.bitmap.data) =
      some bmp.data := by
  unfold decodeIndexedBitmapWithMetadata
  have hParse (h : 8 ≤ s.bytes.size) :
      parsePngWithMetadata s.bytes h = some (parsed s) := by
    simpa using parsePngWithMetadata_accepts s hIdatSize
  simp [s.bytes_size_ge_8, hParse]
  have hParsed :=
    decodeParsedIndexedBitmapWithMetadata_fixed_encodeRawIndexed_none_8_256_data
      bmp hbd hpal
  simpa [parsed, metadata, hHeader, hPalette, hIdat] using hParsed

/-- Metadata-aware decode over a dynamic-Huffman palette container returns the
original index bytes for 8-bit full-palette filter-0 inputs. -/
theorem decodeIndexedBitmapWithMetadata_dynamic_encodeRawIndexed_none_8_256_data
    (s : PaletteContainerSpec) (bmp : PngIndexedBitmap)
    (hHeader :
      s.header =
        { width := bmp.size.width, height := bmp.size.height, colorType := 3,
          bitDepth := 8, interlace := 0 })
    (hPalette : s.palette = bmp.palette)
    (hIdat : s.idatData = zlibCompressDynamic (encodeRawIndexedWithFilter bmp .none))
    (hIdatSize : s.idatData.size < 2 ^ 32)
    (hbd : bmp.bitDepth = 8)
    (hpal : bmp.palette.entryCount = 256) :
    (decodeIndexedBitmapWithMetadata s.bytes).map (fun result => result.bitmap.data) =
      some bmp.data := by
  unfold decodeIndexedBitmapWithMetadata
  have hParse (h : 8 ≤ s.bytes.size) :
      parsePngWithMetadata s.bytes h = some (parsed s) := by
    simpa using parsePngWithMetadata_accepts s hIdatSize
  simp [s.bytes_size_ge_8, hParse]
  have hParsed :=
    decodeParsedIndexedBitmapWithMetadata_dynamic_encodeRawIndexed_none_8_256_data
      bmp hbd hpal
  simpa [parsed, metadata, hHeader, hPalette, hIdat] using hParsed

end PaletteContainerSpec

end Lemmas

end Bitmaps
