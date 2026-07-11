import Bitmap.Lemmas.Png.PaletteContainerSpec

namespace Bitmaps

namespace Lemmas

open Png

/-! ## External indexed-palette PNG spec

`ExternalIndexedPalettePngSpec` describes palette PNG byte streams by their
container, zlib, and indexed-row decoding witnesses. Unlike the encoder
round-trip theorems, this spec is independent of this library's encoder: any
byte stream matching the witnesses is accepted by the exact indexed decoders. -/

/-- A decoder-side specification for exact indexed palette PNGs.

The container layer is the palette-specific PNG scaffold. The zlib witness
supplies the inflated row stream, and `hIndices` captures the indexed row
decoder result for either non-interlaced or Adam7 palette data. -/
structure ExternalIndexedPalettePngSpec where
  /-- The exact indexed bitmap expected from the decoder. -/
  bitmap : PngIndexedBitmap
  /-- PNG container with `IHDR`, required `PLTE`, one `IDAT`, and `IEND`. -/
  container : PaletteContainerSpec
  /-- Container width matches the indexed bitmap. -/
  hWidth : container.header.width = bitmap.size.width
  /-- Container height matches the indexed bitmap. -/
  hHeight : container.header.height = bitmap.size.height
  /-- Container indexed bit depth matches the bitmap bit depth. -/
  hBitDepth : container.header.bitDepth = bitmap.bitDepth
  /-- Container palette matches the bitmap palette. -/
  hPalette : container.palette = bitmap.palette
  /-- The minimal palette scaffold carries no palette alpha metadata. -/
  hTransparency : bitmap.transparency = none
  /-- The minimal palette scaffold carries no palette background metadata. -/
  hBackground : bitmap.background = none
  /-- The IDAT data size fits in the PNG u32 length field. -/
  hIdatSize : container.idatData.size < 2 ^ 32
  /-- The IDAT data has the zlib CMF + FLG header bytes. -/
  hIdatMin : 2 ≤ container.idatData.size
  /-- The inflated palette row stream. -/
  inflatedRaw : ByteArray
  /-- The container's IDAT bytes decompress to `inflatedRaw`. -/
  hInflated :
    zlibDecompressStored container.idatData hIdatMin = some inflatedRaw ∨
    (zlibDecompressStored container.idatData hIdatMin = none ∧
     zlibDecompress container.idatData hIdatMin = some inflatedRaw)
  /-- The indexed row decoder reconstructs the expected one-byte-per-pixel
  palette index buffer. -/
  hIndices :
    decodePaletteIndicesByInterlace? inflatedRaw container.header
      container.palette.entryCount = some bitmap.data

namespace ExternalIndexedPalettePngSpec

/-- Parser routing for external indexed-palette PNGs.
This is the palette-container layer used by both exact indexed decode APIs. -/
theorem parsePngWithMetadata_external (s : ExternalIndexedPalettePngSpec) :
    parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
      some (PaletteContainerSpec.parsed s.container) :=
  s.container.parsePngWithMetadata_accepts s.hIdatSize

/-- Parser routing through the pixel-only indexed decode front door.
The parser still records the required `PLTE` metadata for exact indexed decode. -/
theorem parsePngForDecode_external (s : ExternalIndexedPalettePngSpec) :
    parsePngForDecode s.container.bytes s.container.bytes_size_ge_8 =
      some (PaletteContainerSpec.parsed s.container) :=
  s.container.parsePngForDecode_accepts s.hIdatSize

/-- The zlib inflate branch used by indexed palette decode reduces to the
spec's inflated row stream. -/
theorem zlibInflate_external {α : Type} (s : ExternalIndexedPalettePngSpec)
    (f : ByteArray → Option α) :
    (do
      let inflated ←
        match zlibDecompressStored s.container.idatData s.hIdatMin with
        | some raw => some raw
        | none => zlibDecompress s.container.idatData s.hIdatMin
      f inflated) = f s.inflatedRaw := by
  rcases s.hInflated with hStored | ⟨hStoredNone, hZlib⟩
  · simp [hStored]
  · simp [hStoredNone, hZlib]

private lemma data_size_header (s : ExternalIndexedPalettePngSpec) :
    s.bitmap.data.size = s.container.header.width * s.container.header.height := by
  calc
    s.bitmap.data.size = s.bitmap.size.width * s.bitmap.size.height := s.bitmap.valid
    _ = s.container.header.width * s.container.header.height := by
      rw [s.hWidth, s.hHeight]

/-- Metadata-aware exact indexed decode accepts any external indexed-palette
PNG matching the spec and reconstructs the expected indexed bitmap fields. -/
theorem decodeIndexedBitmapWithMetadata_external_correct
    (s : ExternalIndexedPalettePngSpec) :
    (decodeIndexedBitmapWithMetadata s.container.bytes).map
        (fun result =>
          (result.bitmap.size, result.bitmap.bitDepth, result.bitmap.palette,
            result.bitmap.data, result.bitmap.transparency, result.bitmap.background,
            result.metadata.palette)) =
      some
        (s.bitmap.size, s.bitmap.bitDepth, s.bitmap.palette, s.bitmap.data,
          none, none, some s.bitmap.palette) := by
  unfold decodeIndexedBitmapWithMetadata
  have hParse (h : 8 ≤ s.container.bytes.size) :
      parsePngWithMetadata s.container.bytes h =
        some (PaletteContainerSpec.parsed s.container) := by
    simpa using s.parsePngWithMetadata_external
  simp [s.container.bytes_size_ge_8, hParse]
  unfold decodeParsedIndexedBitmapWithMetadata
  have hsize : s.bitmap.data.size = s.container.header.width * s.container.header.height :=
    s.data_size_header
  have hsizeBitmap : s.bitmap.data.size = s.bitmap.size.width * s.bitmap.size.height :=
    s.bitmap.valid
  have hSupported :
      pngColorTypeBitDepthSupported 3 s.bitmap.bitDepth = true := by
    simpa [s.container.hColorType, s.hBitDepth] using s.container.hCtBdSupported
  have hIndices' :
      decodePaletteIndicesByInterlace? s.inflatedRaw s.container.header
        s.bitmap.palette.entryCount = some s.bitmap.data := by
    simpa [s.hPalette] using s.hIndices
  rcases s.hInflated with hStored | ⟨hStoredNone, hZlib⟩
  · simp [PaletteContainerSpec.parsed, PaletteContainerSpec.metadata,
      PngMetadata.empty, s.container.hColorType, s.hIdatMin, hStored,
      hSupported, hIndices', hsize, s.hWidth, s.hHeight, s.hBitDepth,
      s.hPalette]
  · simp [PaletteContainerSpec.parsed, PaletteContainerSpec.metadata,
      PngMetadata.empty, s.container.hColorType, s.hIdatMin, hStoredNone,
      hZlib, hSupported, hIndices', hsize, s.hWidth, s.hHeight,
      s.hBitDepth, s.hPalette]

/-- pixel-only exact indexed decode accepts any external indexed-palette PNG
matching the spec when the minimal scaffold carries no transparency metadata. -/
theorem decodeIndexedBitmap_external_correct
    (s : ExternalIndexedPalettePngSpec) :
    (decodeIndexedBitmap s.container.bytes).map
        (fun bitmap =>
          (bitmap.size, bitmap.bitDepth, bitmap.palette, bitmap.data,
            bitmap.transparency, bitmap.background)) =
      some
        (s.bitmap.size, s.bitmap.bitDepth, s.bitmap.palette, s.bitmap.data,
          none, none) := by
  unfold decodeIndexedBitmap
  have hParse (h : 8 ≤ s.container.bytes.size) :
      parsePngForDecode s.container.bytes h =
        some (PaletteContainerSpec.parsed s.container) := by
    simpa using s.parsePngForDecode_external
  simp [s.container.bytes_size_ge_8, hParse, PaletteContainerSpec.parsed,
    PaletteContainerSpec.metadata, PngMetadata.pixelOnlyColorSpace]
  unfold decodeParsedIndexedBitmapWithMetadata
  have hsize : s.bitmap.data.size = s.container.header.width * s.container.header.height :=
    s.data_size_header
  have hsizeBitmap : s.bitmap.data.size = s.bitmap.size.width * s.bitmap.size.height :=
    s.bitmap.valid
  have hSupported :
      pngColorTypeBitDepthSupported 3 s.bitmap.bitDepth = true := by
    simpa [s.container.hColorType, s.hBitDepth] using s.container.hCtBdSupported
  have hIndices' :
      decodePaletteIndicesByInterlace? s.inflatedRaw s.container.header
        s.bitmap.palette.entryCount = some s.bitmap.data := by
    simpa [s.hPalette] using s.hIndices
  rcases s.hInflated with hStored | ⟨hStoredNone, hZlib⟩
  · simp [PngMetadata.empty, s.container.hColorType, s.hIdatMin, hStored,
      hSupported, hIndices', hsize, s.hWidth, s.hHeight, s.hBitDepth,
      s.hPalette]
  · simp [PngMetadata.empty, s.container.hColorType, s.hIdatMin,
      hStoredNone, hZlib, hSupported, hIndices', hsize, s.hWidth,
      s.hHeight, s.hBitDepth, s.hPalette]

end ExternalIndexedPalettePngSpec

end Lemmas

end Bitmaps
