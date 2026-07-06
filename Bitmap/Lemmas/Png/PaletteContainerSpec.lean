import Bitmap.Lemmas.Png.ContainerSpec

namespace Bitmaps

namespace Lemmas

open Png

/-! ## Indexed-palette PNG container scaffold

This module captures the minimal container shape for an indexed-palette PNG:
signature, IHDR, required PLTE, one IDAT, and IEND.  The first facts prove the
wire-size arithmetic and the PLTE payload acceptance needed by later parser
forward-correctness proofs. -/

/-- The indexed-palette container shape: PNG signature, IHDR, required PLTE,
one IDAT, and IEND.  It carries the validation facts needed by the runtime
parser before proving the full parser loop over this byte stream. -/
structure PaletteContainerSpec where
  header : PngHeader
  palette : PngPalette
  idatData : ByteArray
  /-- PNG indexed bit depth is one of the supported packed depths. -/
  hBitDepth :
    header.bitDepth = 1 ∨ header.bitDepth = 2 ∨
      header.bitDepth = 4 ∨ header.bitDepth = 8
  /-- This scaffold is specifically for indexed-color PNGs. -/
  hColorType : header.colorType = 3
  /-- The runtime accepts this color type and bit-depth pair. -/
  hCtBdSupported :
    pngColorTypeBitDepthSupported header.colorType header.bitDepth = true
  /-- Interlace method is valid for the parser. -/
  hInterlace : header.interlace = 0 ∨ header.interlace = 1
  hWidth : header.width < 2 ^ 32
  hHeight : header.height < 2 ^ 32
  /-- PLTE must contain at least one RGB triplet. -/
  hPaletteNonempty : palette.entries.size ≠ 0
  /-- PLTE bytes are RGB triplets. -/
  hPaletteTriplets : palette.entries.size % 3 = 0
  /-- PNG palettes have at most 256 entries. -/
  hPaletteMax : palette.entries.size ≤ 256 * 3
  /-- The PLTE entry count fits the selected bit depth. -/
  hPaletteFits :
    palette.entryCount ≤ paletteMaxEntriesForBitDepth header.bitDepth

/-- On-the-wire bytes for the indexed palette scaffold. -/
def PaletteContainerSpec.bytes (s : PaletteContainerSpec) : ByteArray :=
  pngSignature
    ++ mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header)
    ++ mkChunkBytes plteTypeBytes s.palette.entries
    ++ mkChunkBytes idatTypeBytes s.idatData
    ++ mkChunkBytes iendTypeBytes ByteArray.empty

/-- Palette container bytes always carry at least the PNG signature.
This discharges the outer parser size precondition for later proofs. -/
lemma PaletteContainerSpec.bytes_size_ge_8 (s : PaletteContainerSpec) :
    8 ≤ s.bytes.size := by
  unfold PaletteContainerSpec.bytes
  simp [pngSignature_size, ByteArray.size_append]
  omega

/-- Exact byte size of the indexed-palette scaffold.
This pins down the chunk overhead before parser-position proofs. -/
lemma PaletteContainerSpec.bytes_size (s : PaletteContainerSpec) :
    s.bytes.size = s.idatData.size + s.palette.entries.size + 69 := by
  have hIhdrSize :
      (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header)).size = 25 := by
    have ht : ihdrTypeBytes.size = 4 := by rfl
    have hs := mkChunkBytes_size ihdrTypeBytes (encodeIHDRData s.header) ht
    simpa [encodeIHDRData_size] using hs
  have hPlteSize :
      (mkChunkBytes plteTypeBytes s.palette.entries).size =
        s.palette.entries.size + 12 := by
    have ht : plteTypeBytes.size = 4 := by rfl
    simpa using mkChunkBytes_size plteTypeBytes s.palette.entries ht
  have hIdatSize :
      (mkChunkBytes idatTypeBytes s.idatData).size =
        s.idatData.size + 12 := by
    have ht : idatTypeBytes.size = 4 := by rfl
    simpa using mkChunkBytes_size idatTypeBytes s.idatData ht
  have hIendSize : (mkChunkBytes iendTypeBytes ByteArray.empty).size = 12 := by
    have ht : iendTypeBytes.size = 4 := by rfl
    have hs := mkChunkBytes_size iendTypeBytes ByteArray.empty ht
    simpa using hs
  unfold PaletteContainerSpec.bytes
  simp only [ByteArray.size_append, pngSignature_size, hIhdrSize, hPlteSize,
    hIdatSize, hIendSize]
  omega

/-- The scaffold PLTE payload is accepted by `parsePlteData`.
This bridges the container-level palette invariant to chunk validation. -/
lemma PaletteContainerSpec.parsePlteData (s : PaletteContainerSpec) :
    parsePlteData s.header s.palette.entries = some s.palette := by
  have hfits :
      s.header.colorType = 3 →
        s.palette.entries.size / 3 ≤
          paletteMaxEntriesForBitDepth s.header.bitDepth := by
    intro _
    simpa [PngPalette.entryCount] using s.hPaletteFits
  have hparse :=
    parsePlteData_accepts_valid s.header s.palette.entries
      s.hPaletteNonempty s.hPaletteTriplets s.hPaletteMax hfits
  have hpal : ({ entries := s.palette.entries } : PngPalette) = s.palette := by
    cases s.palette
    rfl
  simpa [hpal] using hparse

end Lemmas

end Bitmaps
