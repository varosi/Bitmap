import Bitmap.Lemmas.ExternalPngSpec
import Bitmap.Lemmas.ExternalPngCore

universe u

namespace Bitmaps

namespace Lemmas

open Png

/-! ## End-to-end external-PNG specs — 1-bit grayscale upsampling

`ExternalPngSpecGray1To8` and `ExternalPngSpecGray1To16` describe byte
streams whose container declares 1-bit grayscale (`bitDepth = 1`,
`colorType = 0`) and whose target pixel type is 8-bit or 16-bit gray.
The runtime unpacks packed bits into a sample raw of the target bit
depth, then runs the standard per-pixel decode loop.

Both spec types share a common container layer and zlib witnesses;
they differ only in the target bit depth and the parameters threaded
into the gray1 core. The closure theorems are one-line corollaries of
`decodeBitmap_correct_of_witnesses_gray1_to{8,16}`. -/

/-- Common witness bundle shared by `ExternalPngSpecGray1To{8,16}`.
Captures the container layer, zlib inflate, and the intermediate
`flat` byte array produced by `decodeRowsLoopGray1Packed`. -/
structure ExternalPngSpecGray1Common (px : Type u) [Pixel px] [PngPixel px] where
  bitmap : Bitmap px
  container : SimpleContainerSpec
  hSourceBitDepth : container.header.bitDepth = 1
  hColorType0 : container.header.colorType = 0
  hWidth : container.header.width = bitmap.size.width
  hHeight : container.header.height = bitmap.size.height
  hInterlace : container.header.interlace = 0
  hPxColorType : PngPixel.colorType (α := px) = u8 0
  hIdatSize : container.idatData.size < 2 ^ 32
  hIdatMin : 2 ≤ container.idatData.size
  inflatedRaw : ByteArray
  hInflated :
    zlibDecompressStored container.idatData hIdatMin = some inflatedRaw ∨
    (zlibDecompressStored container.idatData hIdatMin = none ∧
     zlibDecompress container.idatData hIdatMin = some inflatedRaw)
  /-- The packed inflated raw has the expected (filter-byte + packed-row)
  size for a 1-bit grayscale image. -/
  hPackedSize :
    inflatedRaw.size = bitmap.size.height * (gray1RowBytes bitmap.size.width + 1)
  /-- The packed-gray1 decoder produces the flat-bits byte array. -/
  flat : ByteArray
  hFlat :
    decodeRowsLoopGray1Packed inflatedRaw bitmap.size.width
      bitmap.size.height = some flat

namespace ExternalPngSpecGray1Common

variable {px : Type u} [Pixel px] [PngPixel px]

/-- Phase 3 routing: `parsePngForDecode` accepts the container bytes
and produces the parsed header + IDAT data + empty metadata. -/
theorem parsePngForDecode_gray1_external (s : ExternalPngSpecGray1Common px) :
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

end ExternalPngSpecGray1Common

/-- 1-bit grayscale → 8-bit target. Mirrors the
`decodeBitmap_correct_of_witnesses_gray1_to8` witness chain. -/
structure ExternalPngSpecGray1To8 (px : Type u) [Pixel px] [PngPixel px]
    extends ExternalPngSpecGray1Common px where
  hTargetBitDepth : PngPixel.bitDepth (α := px) = u8 8
  /-- The pixel-extraction loop on the 8-bit-expanded raw. -/
  hPixels :
    PngPixel.decodeRowsLoop (α := px)
        (gray1FlatToSampleRaw toExternalPngSpecGray1Common.flat
          bitmap.size.width bitmap.size.height 8)
        bitmap.size.width bitmap.size.height 1 bitmap.size.width
        0 0 ByteArray.empty
        { data := Array.replicate
            (bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px)) 0 } =
      some bitmap.data

namespace ExternalPngSpecGray1To8

variable {px : Type u} [Pixel px] [PngPixel px]

/-- End-to-end closure: any `ExternalPngSpecGray1To8` is accepted by
`decodeBitmap` and decodes to the spec's bitmap. -/
theorem decodeBitmap_external_gray1_to8_correct
    (s : ExternalPngSpecGray1To8 px) :
    Png.decodeBitmap s.container.bytes = some s.bitmap := by
  have hTransform :
      applyPngColorSpaceTransform
        (PngMetadata.pixelOnlyColorSpace PngMetadata.empty)
        s.container.header.colorType (PngPixel.colorType (α := px))
        (PngPixel.bitDepth (α := px)) s.bitmap.data = some s.bitmap.data := by
    unfold applyPngColorSpaceTransform PngMetadata.pixelOnlyColorSpace
    rfl
  exact decodeBitmap_correct_of_witnesses_gray1_to8
    s.container.bytes_size_ge_8 s.hSourceBitDepth s.hTargetBitDepth
    s.hColorType0 s.hWidth s.hHeight s.hInterlace s.hPxColorType
    (show (PngMetadata.empty : PngMetadata).transparency = none from rfl)
    s.toExternalPngSpecGray1Common.parsePngForDecode_gray1_external
    s.hIdatMin s.hInflated s.hPackedSize s.hFlat s.hPixels hTransform

end ExternalPngSpecGray1To8

/-- 1-bit grayscale → 16-bit target. -/
structure ExternalPngSpecGray1To16 (px : Type u) [Pixel px] [PngPixel px]
    extends ExternalPngSpecGray1Common px where
  hTargetBitDepth : PngPixel.bitDepth (α := px) = u8 16
  /-- The pixel-extraction loop on the 16-bit-expanded raw. -/
  hPixels :
    PngPixel.decodeRowsLoop (α := px)
        (gray1FlatToSampleRaw toExternalPngSpecGray1Common.flat
          bitmap.size.width bitmap.size.height 16)
        bitmap.size.width bitmap.size.height 2 (bitmap.size.width * 2)
        0 0 ByteArray.empty
        { data := Array.replicate
            (bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px)) 0 } =
      some bitmap.data

namespace ExternalPngSpecGray1To16

variable {px : Type u} [Pixel px] [PngPixel px]

theorem decodeBitmap_external_gray1_to16_correct
    (s : ExternalPngSpecGray1To16 px) :
    Png.decodeBitmap s.container.bytes = some s.bitmap := by
  have hTransform :
      applyPngColorSpaceTransform
        (PngMetadata.pixelOnlyColorSpace PngMetadata.empty)
        s.container.header.colorType (PngPixel.colorType (α := px))
        (PngPixel.bitDepth (α := px)) s.bitmap.data = some s.bitmap.data := by
    unfold applyPngColorSpaceTransform PngMetadata.pixelOnlyColorSpace
    rfl
  exact decodeBitmap_correct_of_witnesses_gray1_to16
    s.container.bytes_size_ge_8 s.hSourceBitDepth s.hTargetBitDepth
    s.hColorType0 s.hWidth s.hHeight s.hInterlace s.hPxColorType
    (show (PngMetadata.empty : PngMetadata).transparency = none from rfl)
    s.toExternalPngSpecGray1Common.parsePngForDecode_gray1_external
    s.hIdatMin s.hInflated s.hPackedSize s.hFlat s.hPixels hTransform

end ExternalPngSpecGray1To16

end Lemmas

end Bitmaps
