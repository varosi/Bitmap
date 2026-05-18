import Bitmap.Lemmas.ExternalPngSpec
import Bitmap.Lemmas.ExternalPngCore

universe u

namespace Bitmaps

namespace Lemmas

open Png

/-! ## End-to-end external-PNG spec — Adam7 interlaced (match-depth path)

`ExternalPngSpecAdam7 px` describes a byte stream with the Adam7
interlaced layout (`header.interlace = 1`) where the source bit
depth matches the target pixel type (8 or 16).

The container layer reuses `SimpleContainerSpec` (now generalised to
allow `interlace ∈ {0, 1}`). The runtime calls `decodeAdam7ToFlatRaw?`
to deinterlace the raw bytes; the spec carries both the inflated
interlaced bytes and the deinterlaced flat raw, linked via `hAdam7`.

The closure theorem `decodeBitmap_external_adam7_correct` is a direct
corollary of `decodeBitmap_correct_of_witnesses_adam7`. -/

structure ExternalPngSpecAdam7 (px : Type u) [Pixel px] [PngPixel px] where
  bitmap : Bitmap px
  container : SimpleContainerSpec
  hWidth : container.header.width = bitmap.size.width
  hHeight : container.header.height = bitmap.size.height
  hColorType :
    container.header.colorType = (PngPixel.colorType (α := px)).toNat
  /-- The Adam7 spec narrows the `{0, 1}` interlace disjunction on the
  container to `= 1`. -/
  hInterlace1 : container.header.interlace = 1
  hPxColorType : PngPixel.colorType (α := px) = u8 container.header.colorType
  hTargetBitDepth :
    PngPixel.bitDepth (α := px) = u8 8 ∨ PngPixel.bitDepth (α := px) = u8 16
  hBitDepthMatch :
    container.header.bitDepth = (PngPixel.bitDepth (α := px)).toNat
  hBppLookup :
    pngBytesPerPixelForColorTypeAndBitDepth?
      container.header.colorType container.header.bitDepth =
        some (Pixel.bytesPerPixel (α := px))
  hIdatSize : container.idatData.size < 2 ^ 32
  hIdatMin : 2 ≤ container.idatData.size
  inflatedRaw : ByteArray
  hInflated :
    zlibDecompressStored container.idatData hIdatMin = some inflatedRaw ∨
    (zlibDecompressStored container.idatData hIdatMin = none ∧
     zlibDecompress container.idatData hIdatMin = some inflatedRaw)
  /-- The deinterlaced flat raw, produced by `decodeAdam7ToFlatRaw?`. -/
  flatRaw : ByteArray
  hAdam7 :
    decodeAdam7ToFlatRaw? inflatedRaw bitmap.size.width bitmap.size.height
      (Pixel.bytesPerPixel (α := px)) = some flatRaw
  hRawSize :
    flatRaw.size =
      bitmap.size.height *
        (bitmap.size.width * Pixel.bytesPerPixel (α := px) + 1)
  hPixels :
    PngPixel.decodeRowsLoop (α := px) flatRaw bitmap.size.width
        bitmap.size.height (Pixel.bytesPerPixel (α := px))
        (bitmap.size.width * Pixel.bytesPerPixel (α := px))
        0 0 ByteArray.empty
        { data := Array.replicate
            (bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px)) 0 } =
      some bitmap.data

namespace ExternalPngSpecAdam7

variable {px : Type u} [Pixel px] [PngPixel px]

theorem parsePngForDecode_external_adam7 (s : ExternalPngSpecAdam7 px) :
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

theorem decodeBitmap_external_adam7_correct (s : ExternalPngSpecAdam7 px) :
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
  exact decodeBitmap_correct_of_witnesses_adam7
    s.container.bytes_size_ge_8 s.hBitDepthMatch s.hTargetBitDepth
    s.container.hColorType s.hWidth s.hHeight s.hInterlace1 s.hPxColorType
    s.hBppLookup
    (show (PngMetadata.empty : PngMetadata).transparency = none from rfl)
    hChrmGrayInactive
    s.parsePngForDecode_external_adam7
    s.hIdatMin s.hInflated s.hAdam7 s.hRawSize s.hPixels hTransform

end ExternalPngSpecAdam7

/-! ## Adam7 inhabitability sanity check

The Adam7 spec is inhabitable: a `PngHeader` with `interlace = 1`
satisfies `SimpleContainerSpec.hInterlace = Or.inr rfl`. -/

example : ∃ h : PngHeader, h.interlace = 1 ∧
    (h.interlace = 0 ∨ h.interlace = 1) :=
  ⟨{ width := 1, height := 1, colorType := 0, bitDepth := 8, interlace := 1 },
   rfl, Or.inr rfl⟩

end Lemmas

end Bitmaps
