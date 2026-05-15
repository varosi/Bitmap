import Bitmap.Lemmas.MultiIdatExternalPngSpec
import Bitmap.Lemmas.ExternalPngCore
import Bitmap.Lemmas.Png.MultiIdatBkgdContainerSpec

universe u

namespace Bitmaps

namespace Lemmas

open Png

/-! ## End-to-end multi-IDAT + bKGD spec (Step 2d bKGD end-to-end)

bKGD metadata is preserved by the parser but stripped away by
`pixelOnlyColorSpace` before `applyPngColorSpaceTransform` runs.
Combined with transparency=none and srgb/chrm/gamma=none, the
color-space transform reduces to identity. -/

structure ExternalPngMultiIdatBkgdSpec (px : Type u) [Pixel px] [PngPixel px] where
  bitmap : Bitmap px
  container : MultiIdatBkgdContainerSpec
  hWidth : container.header.width = bitmap.size.width
  hHeight : container.header.height = bitmap.size.height
  hColorType :
    container.header.colorType = (PngPixel.colorType (α := px)).toNat
  hInterlace : container.header.interlace = 0
  hPxColorType : PngPixel.colorType (α := px) = u8 container.header.colorType
  hTargetBitDepth : PngPixel.bitDepth (α := px) = u8 8
  hBppLookup :
    pngBytesPerPixelForColorTypeAndBitDepth?
      container.header.colorType container.header.bitDepth =
        some (Pixel.bytesPerPixel (α := px))
  hIdatMin : 2 ≤ container.idatData.size
  inflatedRaw : ByteArray
  hInflated :
    zlibDecompressStored container.idatData hIdatMin = some inflatedRaw ∨
    (zlibDecompressStored container.idatData hIdatMin = none ∧
     zlibDecompress container.idatData hIdatMin = some inflatedRaw)
  hRawSize :
    inflatedRaw.size =
      bitmap.size.height *
        (bitmap.size.width * Pixel.bytesPerPixel (α := px) + 1)
  hPixels :
    PngPixel.decodeRowsLoop (α := px) inflatedRaw bitmap.size.width
        bitmap.size.height (Pixel.bytesPerPixel (α := px))
        (bitmap.size.width * Pixel.bytesPerPixel (α := px))
        0 0 ByteArray.empty
        { data := Array.replicate
            (bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px)) 0 } =
      some bitmap.data

namespace ExternalPngMultiIdatBkgdSpec

variable {px : Type u} [Pixel px] [PngPixel px]

lemma expectedMetadata_transparency_none (s : ExternalPngMultiIdatBkgdSpec px) :
    s.container.expectedMetadata.transparency = none := by
  unfold MultiIdatBkgdContainerSpec.expectedMetadata
    MultiIdatGenericPreChunkContainerSpec.expectedMetadata
    MultiIdatBkgdContainerSpec.toGeneric
  rcases s.container.bKGD with _ | _ <;> simp [BkgdChunkWitness.toPreIdat, PngMetadata.empty]

lemma expectedMetadata_srgb_none (s : ExternalPngMultiIdatBkgdSpec px) :
    s.container.expectedMetadata.srgb = none := by
  unfold MultiIdatBkgdContainerSpec.expectedMetadata
    MultiIdatGenericPreChunkContainerSpec.expectedMetadata
    MultiIdatBkgdContainerSpec.toGeneric
  rcases s.container.bKGD with _ | _ <;> simp [BkgdChunkWitness.toPreIdat, PngMetadata.empty]

lemma expectedMetadata_chromaticities_none (s : ExternalPngMultiIdatBkgdSpec px) :
    s.container.expectedMetadata.chromaticities = none := by
  unfold MultiIdatBkgdContainerSpec.expectedMetadata
    MultiIdatGenericPreChunkContainerSpec.expectedMetadata
    MultiIdatBkgdContainerSpec.toGeneric
  rcases s.container.bKGD with _ | _ <;> simp [BkgdChunkWitness.toPreIdat, PngMetadata.empty]

lemma expectedMetadata_gamma_none (s : ExternalPngMultiIdatBkgdSpec px) :
    s.container.expectedMetadata.gamma = none := by
  unfold MultiIdatBkgdContainerSpec.expectedMetadata
    MultiIdatGenericPreChunkContainerSpec.expectedMetadata
    MultiIdatBkgdContainerSpec.toGeneric
  rcases s.container.bKGD with _ | _ <;> simp [BkgdChunkWitness.toPreIdat, PngMetadata.empty]

theorem parsePngForDecode_multiIdatBkgd_external (s : ExternalPngMultiIdatBkgdSpec px) :
    parsePngForDecode s.container.bytes s.container.bytes_size_ge_8 =
      some
        { header := s.container.header
          idat := s.container.idatData
          metadata := s.container.expectedMetadata } :=
  s.container.parsePngForDecode_multiIdatBkgdContainerSpec_correct

theorem decodeBitmap_external_multiIdatBkgd_correct (s : ExternalPngMultiIdatBkgdSpec px) :
    Png.decodeBitmap s.container.bytes = some s.bitmap := by
  have hMetaSrgb : s.container.expectedMetadata.srgb = none :=
    s.expectedMetadata_srgb_none
  have hMetaChrm : s.container.expectedMetadata.chromaticities = none :=
    s.expectedMetadata_chromaticities_none
  have hMetaGamma : s.container.expectedMetadata.gamma = none :=
    s.expectedMetadata_gamma_none
  have hPixelOnlySrgb :
      (PngMetadata.pixelOnlyColorSpace s.container.expectedMetadata).srgb = none := by
    unfold PngMetadata.pixelOnlyColorSpace; exact hMetaSrgb
  have hPixelOnlyChrm :
      (PngMetadata.pixelOnlyColorSpace s.container.expectedMetadata).chromaticities = none := by
    unfold PngMetadata.pixelOnlyColorSpace; exact hMetaChrm
  have hPixelOnlyGamma :
      (PngMetadata.pixelOnlyColorSpace s.container.expectedMetadata).gamma = none := by
    unfold PngMetadata.pixelOnlyColorSpace; exact hMetaGamma
  have hChrmGrayInactive :
      ¬ (((s.container.expectedMetadata.pixelOnlyColorSpace.srgb = none ∧
            s.container.expectedMetadata.pixelOnlyColorSpace.chromaticities.isSome = true) ∧
          (s.container.header.colorType = 2 ∨ s.container.header.colorType = 6)) ∧
        (PngPixel.colorType (α := px) = u8 0 ∨ PngPixel.colorType (α := px) = u8 4)) := by
    intro ⟨⟨⟨_, h⟩, _⟩, _⟩
    rw [hPixelOnlyChrm] at h; exact absurd h (by decide)
  have hTransform :
      applyPngColorSpaceTransform
        (PngMetadata.pixelOnlyColorSpace s.container.expectedMetadata)
        s.container.header.colorType (PngPixel.colorType (α := px))
        (u8 8) s.bitmap.data = some s.bitmap.data := by
    unfold applyPngColorSpaceTransform
    rw [hPixelOnlySrgb, hPixelOnlyChrm, hPixelOnlyGamma]
  exact decodeBitmap_correct_of_witnesses s.container.bytes_size_ge_8
    s.container.hBitDepth s.container.hColorType
    s.hWidth s.hHeight s.hInterlace s.hPxColorType s.hTargetBitDepth s.hBppLookup
    s.expectedMetadata_transparency_none
    hChrmGrayInactive
    s.parsePngForDecode_multiIdatBkgd_external
    s.hIdatMin s.hInflated s.hRawSize s.hPixels hTransform

end ExternalPngMultiIdatBkgdSpec

end Lemmas

end Bitmaps
