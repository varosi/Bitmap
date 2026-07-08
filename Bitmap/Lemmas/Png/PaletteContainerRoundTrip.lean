import Bitmap.Lemmas.Png.PaletteContainerSpec
import Bitmap.Lemmas.Png.PaletteRoundTrip

namespace Bitmaps

namespace Lemmas

open Png

/-! ## Indexed-palette container decode round-trip layers

These theorems compose the palette container parser scaffold with the parsed
indexed decode round-trip facts.  They cover filter-0 indexed inputs across
stored, fixed, and dynamic zlib payloads, including smaller palettes when every
source index is below the actual palette entry count. -/

namespace PaletteContainerSpec

/-- Pixel-only indexed decode calls the metadata-aware decoder after keeping
only palette color-space metadata. This bridge normalizes that parsed record
for Lean 4.30 and 4.31. -/
private lemma decodeParsedIndexedBitmapWithMetadata_bind_pixelOnly
    (parsed : PngParsed) (decoded : PngIndexedDecodeResult)
    (hdecoded :
      decodeParsedIndexedBitmapWithMetadata
        { parsed with metadata := PngMetadata.pixelOnlyColorSpace parsed.metadata } =
          some decoded) :
    ((decodeParsedIndexedBitmapWithMetadata
        { header := parsed.header, idat := parsed.idat,
          metadata :=
            { PngMetadata.empty with
              palette := parsed.metadata.palette
              gamma := parsed.metadata.gamma
              chromaticities := parsed.metadata.chromaticities
              srgb := parsed.metadata.srgb } }).bind
      fun decoded => some decoded.bitmap) = some decoded.bitmap := by
  have hparsedEq :
      { header := parsed.header, idat := parsed.idat,
        metadata :=
          { PngMetadata.empty with
            palette := parsed.metadata.palette
            gamma := parsed.metadata.gamma
            chromaticities := parsed.metadata.chromaticities
            srgb := parsed.metadata.srgb } } =
        { parsed with metadata := PngMetadata.pixelOnlyColorSpace parsed.metadata } := by
    rcases parsed with ⟨header, idat, md⟩
    cases md
    simp [PngMetadata.pixelOnlyColorSpace, PngMetadata.empty]
  rw [hparsedEq, hdecoded]
  rfl

/-- IDAT payload shape shared by the generalized palette container round-trip
proofs. Keeping this as a named term avoids proof-dependent `match` artifacts
when rewriting scaffold fields. -/
private def paletteRangeIdat (mode : PngEncodeMode) (bmp : PngIndexedBitmap) :
    ByteArray :=
  match mode with
  | .stored => zlibCompressStored (encodeRawIndexedWithFilter bmp .none)
  | .fixed => zlibCompressFixed (encodeRawIndexedWithFilter bmp .none)
  | .dynamic => zlibCompressDynamic (encodeRawIndexedWithFilter bmp .none)

/-- Rewrites the palette container's parsed scaffold to the explicit parsed PNG
record used by parsed indexed round-trip theorems. This keeps later transports
stable across Lean 4.30 and 4.31. -/
private lemma parsed_eq_paletteRange
    (s : PaletteContainerSpec) (bmp : PngIndexedBitmap) (mode : PngEncodeMode)
    (hHeader :
      s.header =
        { width := bmp.size.width, height := bmp.size.height, colorType := 3,
          bitDepth := bmp.bitDepth, interlace := 0 })
    (hPalette : s.palette = bmp.palette)
    (hIdat : s.idatData = paletteRangeIdat mode bmp) :
    parsed s =
      { header :=
          { width := bmp.size.width, height := bmp.size.height, colorType := 3,
            bitDepth := bmp.bitDepth, interlace := 0 }
        idat := paletteRangeIdat mode bmp
        metadata := { PngMetadata.empty with palette := some bmp.palette } } := by
  cases s
  simp [parsed, metadata] at hHeader hPalette hIdat ⊢
  cases hHeader
  cases hPalette
  cases hIdat
  simp

/-- Metadata-aware decode over a stored-zlib palette container returns the
original index bytes for 1/2/4-bit full-addressable-palette filter-0 inputs. -/
theorem decodeIndexedBitmapWithMetadata_stored_encodeRawIndexed_none_non8_data
    (s : PaletteContainerSpec) (bmp : PngIndexedBitmap)
    (hHeader :
      s.header =
        { width := bmp.size.width, height := bmp.size.height, colorType := 3,
          bitDepth := bmp.bitDepth, interlace := 0 })
    (hPalette : s.palette = bmp.palette)
    (hIdat : s.idatData = zlibCompressStored (encodeRawIndexedWithFilter bmp .none))
    (hIdatSize : s.idatData.size < 2 ^ 32)
    (hbd : bmp.bitDepth = 1 ∨ bmp.bitDepth = 2 ∨ bmp.bitDepth = 4)
    (hpal : bmp.palette.entryCount = paletteIndexLimit bmp.bitDepth)
    (hrange :
      ∀ y, y < bmp.size.height → ∀ x, x < bmp.size.width →
        (bmp.data.get! (y * bmp.size.width + x)).toNat <
          paletteIndexLimit bmp.bitDepth) :
    (decodeIndexedBitmapWithMetadata s.bytes).map (fun result => result.bitmap.data) =
      some bmp.data := by
  unfold decodeIndexedBitmapWithMetadata
  have hParse (h : 8 ≤ s.bytes.size) :
      parsePngWithMetadata s.bytes h = some (parsed s) := by
    simpa using parsePngWithMetadata_accepts s hIdatSize
  simp [s.bytes_size_ge_8, hParse]
  have hParsed :=
    decodeParsedIndexedBitmapWithMetadata_stored_encodeRawIndexed_none_non8_data
      bmp hbd hpal hrange
  simpa [parsed, metadata, hHeader, hPalette, hIdat] using hParsed

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
original index bytes for 1/2/4-bit full-addressable-palette filter-0 inputs. -/
theorem decodeIndexedBitmapWithMetadata_fixed_encodeRawIndexed_none_non8_data
    (s : PaletteContainerSpec) (bmp : PngIndexedBitmap)
    (hHeader :
      s.header =
        { width := bmp.size.width, height := bmp.size.height, colorType := 3,
          bitDepth := bmp.bitDepth, interlace := 0 })
    (hPalette : s.palette = bmp.palette)
    (hIdat : s.idatData = zlibCompressFixed (encodeRawIndexedWithFilter bmp .none))
    (hIdatSize : s.idatData.size < 2 ^ 32)
    (hbd : bmp.bitDepth = 1 ∨ bmp.bitDepth = 2 ∨ bmp.bitDepth = 4)
    (hpal : bmp.palette.entryCount = paletteIndexLimit bmp.bitDepth)
    (hrange :
      ∀ y, y < bmp.size.height → ∀ x, x < bmp.size.width →
        (bmp.data.get! (y * bmp.size.width + x)).toNat <
          paletteIndexLimit bmp.bitDepth) :
    (decodeIndexedBitmapWithMetadata s.bytes).map (fun result => result.bitmap.data) =
      some bmp.data := by
  unfold decodeIndexedBitmapWithMetadata
  have hParse (h : 8 ≤ s.bytes.size) :
      parsePngWithMetadata s.bytes h = some (parsed s) := by
    simpa using parsePngWithMetadata_accepts s hIdatSize
  simp [s.bytes_size_ge_8, hParse]
  have hParsed :=
    decodeParsedIndexedBitmapWithMetadata_fixed_encodeRawIndexed_none_non8_data
      bmp hbd hpal hrange
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
original index bytes for 1/2/4-bit full-addressable-palette filter-0 inputs. -/
theorem decodeIndexedBitmapWithMetadata_dynamic_encodeRawIndexed_none_non8_data
    (s : PaletteContainerSpec) (bmp : PngIndexedBitmap)
    (hHeader :
      s.header =
        { width := bmp.size.width, height := bmp.size.height, colorType := 3,
          bitDepth := bmp.bitDepth, interlace := 0 })
    (hPalette : s.palette = bmp.palette)
    (hIdat : s.idatData = zlibCompressDynamic (encodeRawIndexedWithFilter bmp .none))
    (hIdatSize : s.idatData.size < 2 ^ 32)
    (hbd : bmp.bitDepth = 1 ∨ bmp.bitDepth = 2 ∨ bmp.bitDepth = 4)
    (hpal : bmp.palette.entryCount = paletteIndexLimit bmp.bitDepth)
    (hrange :
      ∀ y, y < bmp.size.height → ∀ x, x < bmp.size.width →
        (bmp.data.get! (y * bmp.size.width + x)).toNat <
          paletteIndexLimit bmp.bitDepth) :
    (decodeIndexedBitmapWithMetadata s.bytes).map (fun result => result.bitmap.data) =
      some bmp.data := by
  unfold decodeIndexedBitmapWithMetadata
  have hParse (h : 8 ≤ s.bytes.size) :
      parsePngWithMetadata s.bytes h = some (parsed s) := by
    simpa using parsePngWithMetadata_accepts s hIdatSize
  simp [s.bytes_size_ge_8, hParse]
  have hParsed :=
    decodeParsedIndexedBitmapWithMetadata_dynamic_encodeRawIndexed_none_non8_data
      bmp hbd hpal hrange
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

/-- Pixel-only indexed decode over a stored-zlib palette container returns the
original index bytes for 1/2/4-bit full-addressable-palette filter-0 inputs. -/
theorem decodeIndexedBitmap_stored_encodeRawIndexed_none_non8_data
    (s : PaletteContainerSpec) (bmp : PngIndexedBitmap)
    (hHeader :
      s.header =
        { width := bmp.size.width, height := bmp.size.height, colorType := 3,
          bitDepth := bmp.bitDepth, interlace := 0 })
    (hPalette : s.palette = bmp.palette)
    (hIdat : s.idatData = zlibCompressStored (encodeRawIndexedWithFilter bmp .none))
    (hIdatSize : s.idatData.size < 2 ^ 32)
    (hbd : bmp.bitDepth = 1 ∨ bmp.bitDepth = 2 ∨ bmp.bitDepth = 4)
    (hpal : bmp.palette.entryCount = paletteIndexLimit bmp.bitDepth)
    (hrange :
      ∀ y, y < bmp.size.height → ∀ x, x < bmp.size.width →
        (bmp.data.get! (y * bmp.size.width + x)).toNat <
          paletteIndexLimit bmp.bitDepth) :
    (decodeIndexedBitmap s.bytes).map (fun bitmap => bitmap.data) = some bmp.data := by
  unfold decodeIndexedBitmap
  have hParse (h : 8 ≤ s.bytes.size) :
      parsePngForDecode s.bytes h = some (parsed s) := by
    simpa using parsePngForDecode_accepts s hIdatSize
  simp [s.bytes_size_ge_8, hParse, PngMetadata.pixelOnlyColorSpace]
  have hParsed :
      (decodeParsedIndexedBitmapWithMetadata
        { parsed s with metadata := PngMetadata.pixelOnlyColorSpace (parsed s).metadata }).map
          (fun result => result.bitmap.data) = some bmp.data := by
    have hp :=
      decodeParsedIndexedBitmapWithMetadata_stored_encodeRawIndexed_none_non8_data
        bmp hbd hpal hrange
    simpa [parsed, metadata, PngMetadata.pixelOnlyColorSpace, hHeader, hPalette, hIdat] using hp
  simp at hParsed
  rcases hParsed with ⟨decoded, hdecoded, hdata⟩
  exact
    ⟨decoded.bitmap,
      ⟨by rfl, by
        simpa [PngMetadata.pixelOnlyColorSpace] using
          decodeParsedIndexedBitmapWithMetadata_bind_pixelOnly (parsed s) decoded hdecoded⟩,
      hdata⟩

/-- Pixel-only indexed decode over a stored-zlib palette container returns the
original index bytes for 8-bit full-palette filter-0 inputs. -/
theorem decodeIndexedBitmap_stored_encodeRawIndexed_none_8_256_data
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
    (decodeIndexedBitmap s.bytes).map (fun bitmap => bitmap.data) = some bmp.data := by
  unfold decodeIndexedBitmap
  have hParse (h : 8 ≤ s.bytes.size) :
      parsePngForDecode s.bytes h = some (parsed s) := by
    simpa using parsePngForDecode_accepts s hIdatSize
  simp [s.bytes_size_ge_8, hParse, PngMetadata.pixelOnlyColorSpace]
  have hParsed :
      (decodeParsedIndexedBitmapWithMetadata
        { parsed s with metadata := PngMetadata.pixelOnlyColorSpace (parsed s).metadata }).map
          (fun result => result.bitmap.data) = some bmp.data := by
    have hp :=
      decodeParsedIndexedBitmapWithMetadata_stored_encodeRawIndexed_none_8_256_data
        bmp hbd hpal
    simpa [parsed, metadata, PngMetadata.pixelOnlyColorSpace, hHeader, hPalette, hIdat] using hp
  simp at hParsed
  rcases hParsed with ⟨decoded, hdecoded, hdata⟩
  exact
    ⟨decoded.bitmap,
      ⟨by rfl, by
        simpa [PngMetadata.pixelOnlyColorSpace] using
          decodeParsedIndexedBitmapWithMetadata_bind_pixelOnly (parsed s) decoded hdecoded⟩,
      hdata⟩

/-- Pixel-only indexed decode over a fixed-Huffman palette container returns the
original index bytes for 1/2/4-bit full-addressable-palette filter-0 inputs. -/
theorem decodeIndexedBitmap_fixed_encodeRawIndexed_none_non8_data
    (s : PaletteContainerSpec) (bmp : PngIndexedBitmap)
    (hHeader :
      s.header =
        { width := bmp.size.width, height := bmp.size.height, colorType := 3,
          bitDepth := bmp.bitDepth, interlace := 0 })
    (hPalette : s.palette = bmp.palette)
    (hIdat : s.idatData = zlibCompressFixed (encodeRawIndexedWithFilter bmp .none))
    (hIdatSize : s.idatData.size < 2 ^ 32)
    (hbd : bmp.bitDepth = 1 ∨ bmp.bitDepth = 2 ∨ bmp.bitDepth = 4)
    (hpal : bmp.palette.entryCount = paletteIndexLimit bmp.bitDepth)
    (hrange :
      ∀ y, y < bmp.size.height → ∀ x, x < bmp.size.width →
        (bmp.data.get! (y * bmp.size.width + x)).toNat <
          paletteIndexLimit bmp.bitDepth) :
    (decodeIndexedBitmap s.bytes).map (fun bitmap => bitmap.data) = some bmp.data := by
  unfold decodeIndexedBitmap
  have hParse (h : 8 ≤ s.bytes.size) :
      parsePngForDecode s.bytes h = some (parsed s) := by
    simpa using parsePngForDecode_accepts s hIdatSize
  simp [s.bytes_size_ge_8, hParse, PngMetadata.pixelOnlyColorSpace]
  have hParsed :
      (decodeParsedIndexedBitmapWithMetadata
        { parsed s with metadata := PngMetadata.pixelOnlyColorSpace (parsed s).metadata }).map
          (fun result => result.bitmap.data) = some bmp.data := by
    have hp :=
      decodeParsedIndexedBitmapWithMetadata_fixed_encodeRawIndexed_none_non8_data
        bmp hbd hpal hrange
    simpa [parsed, metadata, PngMetadata.pixelOnlyColorSpace, hHeader, hPalette, hIdat] using hp
  simp at hParsed
  rcases hParsed with ⟨decoded, hdecoded, hdata⟩
  exact
    ⟨decoded.bitmap,
      ⟨by rfl, by
        simpa [PngMetadata.pixelOnlyColorSpace] using
          decodeParsedIndexedBitmapWithMetadata_bind_pixelOnly (parsed s) decoded hdecoded⟩,
      hdata⟩

/-- Pixel-only indexed decode over a fixed-Huffman palette container returns the
original index bytes for 8-bit full-palette filter-0 inputs. -/
theorem decodeIndexedBitmap_fixed_encodeRawIndexed_none_8_256_data
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
    (decodeIndexedBitmap s.bytes).map (fun bitmap => bitmap.data) = some bmp.data := by
  unfold decodeIndexedBitmap
  have hParse (h : 8 ≤ s.bytes.size) :
      parsePngForDecode s.bytes h = some (parsed s) := by
    simpa using parsePngForDecode_accepts s hIdatSize
  simp [s.bytes_size_ge_8, hParse, PngMetadata.pixelOnlyColorSpace]
  have hParsed :
      (decodeParsedIndexedBitmapWithMetadata
        { parsed s with metadata := PngMetadata.pixelOnlyColorSpace (parsed s).metadata }).map
          (fun result => result.bitmap.data) = some bmp.data := by
    have hp :=
      decodeParsedIndexedBitmapWithMetadata_fixed_encodeRawIndexed_none_8_256_data
        bmp hbd hpal
    simpa [parsed, metadata, PngMetadata.pixelOnlyColorSpace, hHeader, hPalette, hIdat] using hp
  simp at hParsed
  rcases hParsed with ⟨decoded, hdecoded, hdata⟩
  exact
    ⟨decoded.bitmap,
      ⟨by rfl, by
        simpa [PngMetadata.pixelOnlyColorSpace] using
          decodeParsedIndexedBitmapWithMetadata_bind_pixelOnly (parsed s) decoded hdecoded⟩,
      hdata⟩

/-- Pixel-only indexed decode over a dynamic-Huffman palette container returns
the original index bytes for 1/2/4-bit full-addressable-palette filter-0 inputs. -/
theorem decodeIndexedBitmap_dynamic_encodeRawIndexed_none_non8_data
    (s : PaletteContainerSpec) (bmp : PngIndexedBitmap)
    (hHeader :
      s.header =
        { width := bmp.size.width, height := bmp.size.height, colorType := 3,
          bitDepth := bmp.bitDepth, interlace := 0 })
    (hPalette : s.palette = bmp.palette)
    (hIdat : s.idatData = zlibCompressDynamic (encodeRawIndexedWithFilter bmp .none))
    (hIdatSize : s.idatData.size < 2 ^ 32)
    (hbd : bmp.bitDepth = 1 ∨ bmp.bitDepth = 2 ∨ bmp.bitDepth = 4)
    (hpal : bmp.palette.entryCount = paletteIndexLimit bmp.bitDepth)
    (hrange :
      ∀ y, y < bmp.size.height → ∀ x, x < bmp.size.width →
        (bmp.data.get! (y * bmp.size.width + x)).toNat <
          paletteIndexLimit bmp.bitDepth) :
    (decodeIndexedBitmap s.bytes).map (fun bitmap => bitmap.data) = some bmp.data := by
  unfold decodeIndexedBitmap
  have hParse (h : 8 ≤ s.bytes.size) :
      parsePngForDecode s.bytes h = some (parsed s) := by
    simpa using parsePngForDecode_accepts s hIdatSize
  simp [s.bytes_size_ge_8, hParse, PngMetadata.pixelOnlyColorSpace]
  have hParsed :
      (decodeParsedIndexedBitmapWithMetadata
        { parsed s with metadata := PngMetadata.pixelOnlyColorSpace (parsed s).metadata }).map
          (fun result => result.bitmap.data) = some bmp.data := by
    have hp :=
      decodeParsedIndexedBitmapWithMetadata_dynamic_encodeRawIndexed_none_non8_data
        bmp hbd hpal hrange
    simpa [parsed, metadata, PngMetadata.pixelOnlyColorSpace, hHeader, hPalette, hIdat] using hp
  simp at hParsed
  rcases hParsed with ⟨decoded, hdecoded, hdata⟩
  exact
    ⟨decoded.bitmap,
      ⟨by rfl, by
        simpa [PngMetadata.pixelOnlyColorSpace] using
          decodeParsedIndexedBitmapWithMetadata_bind_pixelOnly (parsed s) decoded hdecoded⟩,
      hdata⟩

/-- Pixel-only indexed decode over a dynamic-Huffman palette container returns
the original index bytes for 8-bit full-palette filter-0 inputs. -/
theorem decodeIndexedBitmap_dynamic_encodeRawIndexed_none_8_256_data
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
    (decodeIndexedBitmap s.bytes).map (fun bitmap => bitmap.data) = some bmp.data := by
  unfold decodeIndexedBitmap
  have hParse (h : 8 ≤ s.bytes.size) :
      parsePngForDecode s.bytes h = some (parsed s) := by
    simpa using parsePngForDecode_accepts s hIdatSize
  simp [s.bytes_size_ge_8, hParse, PngMetadata.pixelOnlyColorSpace]
  have hParsed :
      (decodeParsedIndexedBitmapWithMetadata
        { parsed s with metadata := PngMetadata.pixelOnlyColorSpace (parsed s).metadata }).map
          (fun result => result.bitmap.data) = some bmp.data := by
    have hp :=
      decodeParsedIndexedBitmapWithMetadata_dynamic_encodeRawIndexed_none_8_256_data
        bmp hbd hpal
    simpa [parsed, metadata, PngMetadata.pixelOnlyColorSpace, hHeader, hPalette, hIdat] using hp
  simp at hParsed
  rcases hParsed with ⟨decoded, hdecoded, hdata⟩
  exact
    ⟨decoded.bitmap,
      ⟨by rfl, by
        simpa [PngMetadata.pixelOnlyColorSpace] using
          decodeParsedIndexedBitmapWithMetadata_bind_pixelOnly (parsed s) decoded hdecoded⟩,
      hdata⟩

/-- Metadata-aware decode over a palette container returns the original index
bytes for any supported bit depth when the explicit palette contains every
source index and fits that bit depth. This is the smaller-palette container
counterpart to the full-addressable-palette wrappers. -/
theorem decodeIndexedBitmapWithMetadata_encodeRawIndexed_none_paletteRange_data
    (s : PaletteContainerSpec) (bmp : PngIndexedBitmap) (mode : PngEncodeMode)
    (hHeader :
      s.header =
        { width := bmp.size.width, height := bmp.size.height, colorType := 3,
          bitDepth := bmp.bitDepth, interlace := 0 })
    (hPalette : s.palette = bmp.palette)
    (hIdat :
      s.idatData =
        match mode with
        | .stored => zlibCompressStored (encodeRawIndexedWithFilter bmp .none)
        | .fixed => zlibCompressFixed (encodeRawIndexedWithFilter bmp .none)
        | .dynamic => zlibCompressDynamic (encodeRawIndexedWithFilter bmp .none))
    (hIdatSize : s.idatData.size < 2 ^ 32)
    (hbd : bmp.bitDepth = 1 ∨ bmp.bitDepth = 2 ∨ bmp.bitDepth = 4 ∨ bmp.bitDepth = 8)
    (hpalFits : bmp.palette.entryCount ≤ paletteIndexLimit bmp.bitDepth)
    (hrange :
      ∀ y, y < bmp.size.height → ∀ x, x < bmp.size.width →
        (bmp.data.get! (y * bmp.size.width + x)).toNat < bmp.palette.entryCount) :
    (decodeIndexedBitmapWithMetadata s.bytes).map (fun result => result.bitmap.data) =
      some bmp.data := by
  unfold decodeIndexedBitmapWithMetadata
  have hParse (h : 8 ≤ s.bytes.size) :
      parsePngWithMetadata s.bytes h = some (parsed s) := by
    simpa using parsePngWithMetadata_accepts s hIdatSize
  have hParsed :
      (decodeParsedIndexedBitmapWithMetadata (parsed s)).map
          (fun result => result.bitmap.data) = some bmp.data := by
    cases mode
    · rcases hbd with hbd | hbd | hbd | hbd
      · have hp :=
          decodeParsedIndexedBitmapWithMetadata_stored_encodeRawIndexed_none_non8_paletteRange_data
            bmp (Or.inl hbd) hpalFits hrange
        simpa [parsed, metadata, hHeader, hPalette, hIdat, hbd] using hp
      · have hp :=
          decodeParsedIndexedBitmapWithMetadata_stored_encodeRawIndexed_none_non8_paletteRange_data
            bmp (Or.inr (Or.inl hbd)) hpalFits hrange
        simpa [parsed, metadata, hHeader, hPalette, hIdat, hbd] using hp
      · have hp :=
          decodeParsedIndexedBitmapWithMetadata_stored_encodeRawIndexed_none_non8_paletteRange_data
            bmp (Or.inr (Or.inr hbd)) hpalFits hrange
        simpa [parsed, metadata, hHeader, hPalette, hIdat, hbd] using hp
      · have hp :=
          decodeParsedIndexedBitmapWithMetadata_stored_encodeRawIndexed_none_8_paletteRange_data
            bmp hbd hpalFits hrange
        simpa [parsed, metadata, hHeader, hPalette, hIdat, hbd] using hp
    · rcases hbd with hbd | hbd | hbd | hbd
      · have hp :=
          decodeParsedIndexedBitmapWithMetadata_fixed_encodeRawIndexed_none_non8_paletteRange_data
            bmp (Or.inl hbd) hpalFits hrange
        simpa [parsed, metadata, hHeader, hPalette, hIdat, hbd] using hp
      · have hp :=
          decodeParsedIndexedBitmapWithMetadata_fixed_encodeRawIndexed_none_non8_paletteRange_data
            bmp (Or.inr (Or.inl hbd)) hpalFits hrange
        simpa [parsed, metadata, hHeader, hPalette, hIdat, hbd] using hp
      · have hp :=
          decodeParsedIndexedBitmapWithMetadata_fixed_encodeRawIndexed_none_non8_paletteRange_data
            bmp (Or.inr (Or.inr hbd)) hpalFits hrange
        simpa [parsed, metadata, hHeader, hPalette, hIdat, hbd] using hp
      · have hp :=
          decodeParsedIndexedBitmapWithMetadata_fixed_encodeRawIndexed_none_8_paletteRange_data
            bmp hbd hpalFits hrange
        simpa [parsed, metadata, hHeader, hPalette, hIdat, hbd] using hp
    · rcases hbd with hbd | hbd | hbd | hbd
      · have hp :=
          decodeParsedIndexedBitmapWithMetadata_dynamic_encodeRawIndexed_none_non8_paletteRange_data
            bmp (Or.inl hbd) hpalFits hrange
        simpa [parsed, metadata, hHeader, hPalette, hIdat, hbd] using hp
      · have hp :=
          decodeParsedIndexedBitmapWithMetadata_dynamic_encodeRawIndexed_none_non8_paletteRange_data
            bmp (Or.inr (Or.inl hbd)) hpalFits hrange
        simpa [parsed, metadata, hHeader, hPalette, hIdat, hbd] using hp
      · have hp :=
          decodeParsedIndexedBitmapWithMetadata_dynamic_encodeRawIndexed_none_non8_paletteRange_data
            bmp (Or.inr (Or.inr hbd)) hpalFits hrange
        simpa [parsed, metadata, hHeader, hPalette, hIdat, hbd] using hp
      · have hp :=
          decodeParsedIndexedBitmapWithMetadata_dynamic_encodeRawIndexed_none_8_paletteRange_data
            bmp hbd hpalFits hrange
        simpa [parsed, metadata, hHeader, hPalette, hIdat, hbd] using hp
  simpa [s.bytes_size_ge_8, hParse] using hParsed

/-- Pixel-only indexed decode over a palette container returns the original
index bytes under the same smaller-palette assumptions as the metadata-aware
container theorem. -/
theorem decodeIndexedBitmap_encodeRawIndexed_none_paletteRange_data
    (s : PaletteContainerSpec) (bmp : PngIndexedBitmap) (mode : PngEncodeMode)
    (hHeader :
      s.header =
        { width := bmp.size.width, height := bmp.size.height, colorType := 3,
          bitDepth := bmp.bitDepth, interlace := 0 })
    (hPalette : s.palette = bmp.palette)
    (hIdat :
      s.idatData =
        match mode with
        | .stored => zlibCompressStored (encodeRawIndexedWithFilter bmp .none)
        | .fixed => zlibCompressFixed (encodeRawIndexedWithFilter bmp .none)
        | .dynamic => zlibCompressDynamic (encodeRawIndexedWithFilter bmp .none))
    (hIdatSize : s.idatData.size < 2 ^ 32)
    (hbd : bmp.bitDepth = 1 ∨ bmp.bitDepth = 2 ∨ bmp.bitDepth = 4 ∨ bmp.bitDepth = 8)
    (hpalFits : bmp.palette.entryCount ≤ paletteIndexLimit bmp.bitDepth)
    (hrange :
      ∀ y, y < bmp.size.height → ∀ x, x < bmp.size.width →
        (bmp.data.get! (y * bmp.size.width + x)).toNat < bmp.palette.entryCount) :
    (decodeIndexedBitmap s.bytes).map (fun bitmap => bitmap.data) = some bmp.data := by
  unfold decodeIndexedBitmap
  have hParse (h : 8 ≤ s.bytes.size) :
      parsePngForDecode s.bytes h = some (parsed s) := by
    simpa using parsePngForDecode_accepts s hIdatSize
  simp [s.bytes_size_ge_8, hParse, PngMetadata.pixelOnlyColorSpace]
  have hParsed :
      (decodeParsedIndexedBitmapWithMetadata
        { parsed s with metadata := PngMetadata.pixelOnlyColorSpace (parsed s).metadata }).map
          (fun result => result.bitmap.data) = some bmp.data := by
    cases mode
    · rcases hbd with hbd | hbd | hbd | hbd
      · have hp :=
          decodeParsedIndexedBitmapWithMetadata_stored_encodeRawIndexed_none_non8_paletteRange_data
            bmp (Or.inl hbd) hpalFits hrange
        simpa [parsed, metadata, PngMetadata.pixelOnlyColorSpace, hHeader, hPalette, hIdat, hbd] using hp
      · have hp :=
          decodeParsedIndexedBitmapWithMetadata_stored_encodeRawIndexed_none_non8_paletteRange_data
            bmp (Or.inr (Or.inl hbd)) hpalFits hrange
        simpa [parsed, metadata, PngMetadata.pixelOnlyColorSpace, hHeader, hPalette, hIdat, hbd] using hp
      · have hp :=
          decodeParsedIndexedBitmapWithMetadata_stored_encodeRawIndexed_none_non8_paletteRange_data
            bmp (Or.inr (Or.inr hbd)) hpalFits hrange
        simpa [parsed, metadata, PngMetadata.pixelOnlyColorSpace, hHeader, hPalette, hIdat, hbd] using hp
      · have hp :=
          decodeParsedIndexedBitmapWithMetadata_stored_encodeRawIndexed_none_8_paletteRange_data
            bmp hbd hpalFits hrange
        simpa [parsed, metadata, PngMetadata.pixelOnlyColorSpace, hHeader, hPalette, hIdat, hbd] using hp
    · rcases hbd with hbd | hbd | hbd | hbd
      · have hp :=
          decodeParsedIndexedBitmapWithMetadata_fixed_encodeRawIndexed_none_non8_paletteRange_data
            bmp (Or.inl hbd) hpalFits hrange
        simpa [parsed, metadata, PngMetadata.pixelOnlyColorSpace, hHeader, hPalette, hIdat, hbd] using hp
      · have hp :=
          decodeParsedIndexedBitmapWithMetadata_fixed_encodeRawIndexed_none_non8_paletteRange_data
            bmp (Or.inr (Or.inl hbd)) hpalFits hrange
        simpa [parsed, metadata, PngMetadata.pixelOnlyColorSpace, hHeader, hPalette, hIdat, hbd] using hp
      · have hp :=
          decodeParsedIndexedBitmapWithMetadata_fixed_encodeRawIndexed_none_non8_paletteRange_data
            bmp (Or.inr (Or.inr hbd)) hpalFits hrange
        simpa [parsed, metadata, PngMetadata.pixelOnlyColorSpace, hHeader, hPalette, hIdat, hbd] using hp
      · have hp :=
          decodeParsedIndexedBitmapWithMetadata_fixed_encodeRawIndexed_none_8_paletteRange_data
            bmp hbd hpalFits hrange
        simpa [parsed, metadata, PngMetadata.pixelOnlyColorSpace, hHeader, hPalette, hIdat, hbd] using hp
    · rcases hbd with hbd | hbd | hbd | hbd
      · have hp :=
          decodeParsedIndexedBitmapWithMetadata_dynamic_encodeRawIndexed_none_non8_paletteRange_data
            bmp (Or.inl hbd) hpalFits hrange
        simpa [parsed, metadata, PngMetadata.pixelOnlyColorSpace, hHeader, hPalette, hIdat, hbd] using hp
      · have hp :=
          decodeParsedIndexedBitmapWithMetadata_dynamic_encodeRawIndexed_none_non8_paletteRange_data
            bmp (Or.inr (Or.inl hbd)) hpalFits hrange
        simpa [parsed, metadata, PngMetadata.pixelOnlyColorSpace, hHeader, hPalette, hIdat, hbd] using hp
      · have hp :=
          decodeParsedIndexedBitmapWithMetadata_dynamic_encodeRawIndexed_none_non8_paletteRange_data
            bmp (Or.inr (Or.inr hbd)) hpalFits hrange
        simpa [parsed, metadata, PngMetadata.pixelOnlyColorSpace, hHeader, hPalette, hIdat, hbd] using hp
      · have hp :=
          decodeParsedIndexedBitmapWithMetadata_dynamic_encodeRawIndexed_none_8_paletteRange_data
            bmp hbd hpalFits hrange
        simpa [parsed, metadata, PngMetadata.pixelOnlyColorSpace, hHeader, hPalette, hIdat, hbd] using hp
  simp at hParsed
  rcases hParsed with ⟨decoded, hdecoded, hdata⟩
  exact
    ⟨decoded.bitmap,
      ⟨by rfl, by
        simpa [PngMetadata.pixelOnlyColorSpace] using
          decodeParsedIndexedBitmapWithMetadata_bind_pixelOnly (parsed s) decoded hdecoded⟩,
      hdata⟩

/-- Metadata-aware indexed decode over a palette container reconstructs the
complete runtime decode shape under the source-index-safe smaller-palette
assumptions. -/
theorem decodeIndexedBitmapWithMetadata_encodeRawIndexed_none_paletteRange_shape
    (s : PaletteContainerSpec) (bmp : PngIndexedBitmap) (mode : PngEncodeMode)
    (hHeader :
      s.header =
        { width := bmp.size.width, height := bmp.size.height, colorType := 3,
          bitDepth := bmp.bitDepth, interlace := 0 })
    (hPalette : s.palette = bmp.palette)
    (hIdat :
      s.idatData =
        match mode with
        | .stored => zlibCompressStored (encodeRawIndexedWithFilter bmp .none)
        | .fixed => zlibCompressFixed (encodeRawIndexedWithFilter bmp .none)
        | .dynamic => zlibCompressDynamic (encodeRawIndexedWithFilter bmp .none))
    (hIdatSize : s.idatData.size < 2 ^ 32)
    (hbd : bmp.bitDepth = 1 ∨ bmp.bitDepth = 2 ∨ bmp.bitDepth = 4 ∨ bmp.bitDepth = 8)
    (hpalFits : bmp.palette.entryCount ≤ paletteIndexLimit bmp.bitDepth)
    (hrange :
      ∀ y, y < bmp.size.height → ∀ x, x < bmp.size.width →
        (bmp.data.get! (y * bmp.size.width + x)).toNat < bmp.palette.entryCount) :
    (decodeIndexedBitmapWithMetadata s.bytes).map indexedDecodeResultShape =
      some
        (indexedBitmapShape
          { size := bmp.size
            bitDepth := bmp.bitDepth
            palette := bmp.palette
            data := bmp.data
            transparency := none
            background := none
            valid := bmp.valid },
          { PngMetadata.empty with palette := some bmp.palette }) := by
  unfold decodeIndexedBitmapWithMetadata
  have hParse (h : 8 ≤ s.bytes.size) :
      parsePngWithMetadata s.bytes h = some (parsed s) := by
    simpa using parsePngWithMetadata_accepts s hIdatSize
  have hIdatDef : s.idatData = paletteRangeIdat mode bmp := by
    simpa [paletteRangeIdat] using hIdat
  have hParsedEq := parsed_eq_paletteRange s bmp mode hHeader hPalette hIdatDef
  have hParsed :=
    decodeParsedIndexedBitmapWithMetadata_encodeRawIndexed_none_paletteRange_shape
      mode bmp hbd hpalFits hrange
  rw [dif_pos s.bytes_size_ge_8]
  simp only [hParse s.bytes_size_ge_8]
  change (decodeParsedIndexedBitmapWithMetadata (parsed s)).map indexedDecodeResultShape =
    some
      (indexedBitmapShape
        { size := bmp.size
          bitDepth := bmp.bitDepth
          palette := bmp.palette
          data := bmp.data
          transparency := none
          background := none
          valid := bmp.valid },
        { PngMetadata.empty with palette := some bmp.palette })
  rw [hParsedEq]
  rcases Option.map_eq_some_iff.mp hParsed with ⟨decoded, hdecoded, hshape⟩
  exact Option.map_eq_some_iff.mpr
    ⟨decoded,
      by
        cases mode <;> exact hdecoded,
      hshape⟩

/-- Pixel-only indexed decode over a palette container reconstructs the
complete indexed bitmap runtime shape under the source-index-safe
smaller-palette assumptions. -/
theorem decodeIndexedBitmap_encodeRawIndexed_none_paletteRange_shape
    (s : PaletteContainerSpec) (bmp : PngIndexedBitmap) (mode : PngEncodeMode)
    (hHeader :
      s.header =
        { width := bmp.size.width, height := bmp.size.height, colorType := 3,
          bitDepth := bmp.bitDepth, interlace := 0 })
    (hPalette : s.palette = bmp.palette)
    (hIdat :
      s.idatData =
        match mode with
        | .stored => zlibCompressStored (encodeRawIndexedWithFilter bmp .none)
        | .fixed => zlibCompressFixed (encodeRawIndexedWithFilter bmp .none)
        | .dynamic => zlibCompressDynamic (encodeRawIndexedWithFilter bmp .none))
    (hIdatSize : s.idatData.size < 2 ^ 32)
    (hbd : bmp.bitDepth = 1 ∨ bmp.bitDepth = 2 ∨ bmp.bitDepth = 4 ∨ bmp.bitDepth = 8)
    (hpalFits : bmp.palette.entryCount ≤ paletteIndexLimit bmp.bitDepth)
    (hrange :
      ∀ y, y < bmp.size.height → ∀ x, x < bmp.size.width →
        (bmp.data.get! (y * bmp.size.width + x)).toNat < bmp.palette.entryCount) :
    (decodeIndexedBitmap s.bytes).map indexedBitmapShape =
      some
        (indexedBitmapShape
          { size := bmp.size
            bitDepth := bmp.bitDepth
            palette := bmp.palette
            data := bmp.data
            transparency := none
            background := none
            valid := bmp.valid }) := by
  unfold decodeIndexedBitmap
  have hParse (h : 8 ≤ s.bytes.size) :
      parsePngForDecode s.bytes h = some (parsed s) := by
    simpa using parsePngForDecode_accepts s hIdatSize
  simp [s.bytes_size_ge_8, hParse, PngMetadata.pixelOnlyColorSpace]
  have hParsed :
      (decodeParsedIndexedBitmapWithMetadata
        { parsed s with metadata := PngMetadata.pixelOnlyColorSpace (parsed s).metadata }).map
          indexedDecodeResultShape =
        some
          (indexedBitmapShape
            { size := bmp.size
              bitDepth := bmp.bitDepth
              palette := bmp.palette
              data := bmp.data
              transparency := none
              background := none
              valid := bmp.valid },
            { PngMetadata.empty with palette := some bmp.palette }) := by
    have hIdatDef : s.idatData = paletteRangeIdat mode bmp := by
      simpa [paletteRangeIdat] using hIdat
    have hBaseParsedEq := parsed_eq_paletteRange s bmp mode hHeader hPalette hIdatDef
    have hParsedEq :
        { parsed s with metadata := PngMetadata.pixelOnlyColorSpace (parsed s).metadata } =
          { header :=
              { width := bmp.size.width, height := bmp.size.height, colorType := 3,
                bitDepth := bmp.bitDepth, interlace := 0 }
            idat := paletteRangeIdat mode bmp
            metadata := { PngMetadata.empty with palette := some bmp.palette } } := by
      rw [hBaseParsedEq]
      simp [PngMetadata.pixelOnlyColorSpace, PngMetadata.empty]
    have hp :=
      decodeParsedIndexedBitmapWithMetadata_encodeRawIndexed_none_paletteRange_shape
        mode bmp hbd hpalFits hrange
    rw [hParsedEq]
    rcases Option.map_eq_some_iff.mp hp with ⟨decoded, hdecoded, hshape⟩
    exact Option.map_eq_some_iff.mpr
      ⟨decoded,
        by
          cases mode <;> exact hdecoded,
        hshape⟩
  simp [indexedDecodeResultShape] at hParsed
  rcases hParsed with ⟨decoded, hdecoded, hshape⟩
  rcases hshape with ⟨hbitmapShape, _hmetadata⟩
  exact
    ⟨decoded.bitmap,
      ⟨by rfl, by
        simpa [PngMetadata.pixelOnlyColorSpace] using
          decodeParsedIndexedBitmapWithMetadata_bind_pixelOnly (parsed s) decoded hdecoded⟩,
      by
        simpa using hbitmapShape⟩

end PaletteContainerSpec

end Lemmas

end Bitmaps
