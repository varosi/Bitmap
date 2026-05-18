import Bitmap.Lemmas.ExternalPngSpec
import Bitmap.Lemmas.ExternalPngCore

universe u

namespace Bitmaps

namespace Lemmas

open Png

/-! ## End-to-end external-PNG spec — 16→8 downsampling path

`ExternalPngSpecDown16To8 px` describes a byte stream whose container
declares `bitDepth = 16` while the target pixel type is 8-bit (e.g. a
16-bit grayscale PNG decoded into `PixelGray8`). The runtime takes the
`decodeRowsLoopDown16To8` branch; the spec mirrors `ExternalPngSpec`
but threads the source 16-bit bpp through `hBppLookup`, `hRawSize`,
and `hPixels`.

The closure theorem `decodeBitmap_external_down16to8_correct` is a
direct corollary of `decodeBitmap_correct_of_witnesses_down16to8`. -/

structure ExternalPngSpecDown16To8 (px : Type u) [Pixel px] [PngPixel px] where
  /-- The bitmap the byte stream should decode to. -/
  bitmap : Bitmap px
  /-- The container layer (signature + IHDR + IDAT + IEND chunks).
  Reuses `SimpleContainerSpec`; the disjunction `hBitDepth ∈ {8, 16}`
  on the container is narrowed to 16 via `hSourceBitDepth`. -/
  container : SimpleContainerSpec
  /-- Container declares 16-bit source samples. -/
  hSourceBitDepth : container.header.bitDepth = 16
  /-- Target pixel type uses 8-bit depth. -/
  hTargetBitDepth : PngPixel.bitDepth (α := px) = u8 8
  hWidth : container.header.width = bitmap.size.width
  hHeight : container.header.height = bitmap.size.height
  hInterlace : container.header.interlace = 0
  hPxColorType : PngPixel.colorType (α := px) = u8 container.header.colorType
  /-- The source 16-bit bytes-per-pixel (2 for gray, 6 for RGB, etc.).
  Equals twice the target's `Pixel.bytesPerPixel` since each channel is
  2 bytes at 16-bit vs. 1 byte at 8-bit. -/
  sourceBpp : Nat
  hBppLookup :
    pngBytesPerPixelForColorTypeAndBitDepth?
      container.header.colorType 16 = some sourceBpp
  hIdatSize : container.idatData.size < 2 ^ 32
  hIdatMin : 2 ≤ container.idatData.size
  inflatedRaw : ByteArray
  hInflated :
    zlibDecompressStored container.idatData hIdatMin = some inflatedRaw ∨
    (zlibDecompressStored container.idatData hIdatMin = none ∧
     zlibDecompress container.idatData hIdatMin = some inflatedRaw)
  /-- `inflatedRaw` is the expected size for a filter-byte + row-payload
  stream of `height` rows of source-bpp bytes. -/
  hRawSize :
    inflatedRaw.size =
      bitmap.size.height * (bitmap.size.width * sourceBpp + 1)
  /-- The downsampling decode loop on `inflatedRaw` produces the
  bitmap's pixel data. -/
  hPixels :
    decodeRowsLoopDown16To8 (PngPixel.colorType (α := px))
        container.header.colorType inflatedRaw bitmap.size.width
        bitmap.size.height sourceBpp (bitmap.size.width * sourceBpp)
        0 0 ByteArray.empty
        { data := Array.replicate
            (bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px)) 0 } =
      some bitmap.data

namespace ExternalPngSpecDown16To8

variable {px : Type u} [Pixel px] [PngPixel px]

/-- Phase 3 routing: `parsePngForDecode` accepts `s.container.bytes`
and produces the parsed header + IDAT data + empty metadata. Mirrors
`ExternalPngSpec.parsePngForDecode_external`. -/
theorem parsePngForDecode_external_down16to8
    (s : ExternalPngSpecDown16To8 px) :
    parsePngForDecode s.container.bytes s.container.bytes_size_ge_8 =
      some
        { header := s.container.header
          idat := s.container.idatData
          metadata := PngMetadata.empty } := by
  have hSimple :
      parsePngSimple s.container.bytes s.container.bytes_size_ge_8 =
        some (s.container.header, s.container.idatData) :=
    parsePngSimple_simpleContainerSpec_correct s.container s.hIdatSize
  unfold parsePngForDecode parsePngSimpleWithMetadata
  simp [hSimple]

/-- End-to-end closure: any `ExternalPngSpecDown16To8` is accepted by
`decodeBitmap` and decodes to the spec's bitmap. -/
theorem decodeBitmap_external_down16to8_correct
    (s : ExternalPngSpecDown16To8 px) :
    Png.decodeBitmap s.container.bytes = some s.bitmap := by
  have hChrmGrayInactive :
      ¬ (((PngMetadata.empty.pixelOnlyColorSpace.srgb = none ∧
            PngMetadata.empty.pixelOnlyColorSpace.chromaticities.isSome = true) ∧
          (s.container.header.colorType = 2 ∨ s.container.header.colorType = 6)) ∧
        (PngPixel.colorType (α := px) = u8 0 ∨ PngPixel.colorType (α := px) = u8 4)) := by
    intro ⟨⟨⟨_, h⟩, _⟩, _⟩; exact absurd h (by decide)
  have hTransform :
      applyPngColorSpaceTransform
        (PngMetadata.pixelOnlyColorSpace PngMetadata.empty)
        s.container.header.colorType (PngPixel.colorType (α := px))
        (PngPixel.bitDepth (α := px)) s.bitmap.data = some s.bitmap.data := by
    unfold applyPngColorSpaceTransform PngMetadata.pixelOnlyColorSpace
    rfl
  exact decodeBitmap_correct_of_witnesses_down16to8
    s.container.bytes_size_ge_8 s.hSourceBitDepth s.hTargetBitDepth
    s.container.hColorType s.hWidth s.hHeight s.hInterlace s.hPxColorType
    s.hBppLookup
    (show (PngMetadata.empty : PngMetadata).transparency = none from rfl)
    hChrmGrayInactive
    s.parsePngForDecode_external_down16to8
    s.hIdatMin s.hInflated s.hRawSize s.hPixels hTransform

end ExternalPngSpecDown16To8

end Lemmas

end Bitmaps
