import Bitmap.Lemmas.MultiIdatExternalPngSpec
import Bitmap.Lemmas.ExternalPngCore
import Bitmap.Lemmas.Png.MultiIdatGammaContainerSpec

universe u

namespace Bitmaps

namespace Lemmas

open Png

/-! ## End-to-end multi-IDAT + gAMA spec (Step 2c gAMA end-to-end)

Unlike tIME/pHYs/sRGB, the gamma metadata genuinely transforms the
pixel data via `applyGamma8ToPixels`. So the spec carries an explicit
pre-transform pixel array (`preTransformPixels`) plus a witness that
applying the color-space transform yields `bitmap.data`. -/

structure ExternalPngMultiIdatGammaSpec (px : Type u) [Pixel px] [PngPixel px] where
  bitmap : Bitmap px
  container : MultiIdatGammaContainerSpec
  hWidth : container.header.width = bitmap.size.width
  hHeight : container.header.height = bitmap.size.height
  hColorType :
    container.header.colorType = (PngPixel.colorType (α := px)).toNat
  hInterlace : container.header.interlace = 0
  hPxColorType : PngPixel.colorType (α := px) = u8 container.header.colorType
  hTargetBitDepth :
    PngPixel.bitDepth (α := px) = u8 8 ∨ PngPixel.bitDepth (α := px) = u8 16
  hBitDepthMatch :
    container.header.bitDepth = (PngPixel.bitDepth (α := px)).toNat
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
  /-- The intermediate pixel array after row-filter reconstruction
      but BEFORE the gamma color-space transform. -/
  preTransformPixels : ByteArray
  hPixels :
    PngPixel.decodeRowsLoop (α := px) inflatedRaw bitmap.size.width
        bitmap.size.height (Pixel.bytesPerPixel (α := px))
        (bitmap.size.width * Pixel.bytesPerPixel (α := px))
        0 0 ByteArray.empty
        { data := Array.replicate
            (bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px)) 0 } =
      some preTransformPixels
  /-- Applying the gamma transform to `preTransformPixels` produces
      `bitmap.data`. For gAMA-none, this reduces to identity. -/
  hTransform :
    applyPngColorSpaceTransform
      (PngMetadata.pixelOnlyColorSpace container.expectedMetadata)
      container.header.colorType (PngPixel.colorType (α := px))
      (PngPixel.bitDepth (α := px)) preTransformPixels = some bitmap.data

namespace ExternalPngMultiIdatGammaSpec

variable {px : Type u} [Pixel px] [PngPixel px]

lemma expectedMetadata_chromaticities_none (s : ExternalPngMultiIdatGammaSpec px) :
    s.container.expectedMetadata.chromaticities = none := by
  unfold MultiIdatGammaContainerSpec.expectedMetadata
    MultiIdatGenericPreChunkContainerSpec.expectedMetadata
    MultiIdatGammaContainerSpec.toGeneric
  rcases s.container.gAMA with _ | _ <;> simp [GammaChunkWitness.toPreIdat, PngMetadata.empty]

lemma expectedMetadata_srgb_none (s : ExternalPngMultiIdatGammaSpec px) :
    s.container.expectedMetadata.srgb = none := by
  unfold MultiIdatGammaContainerSpec.expectedMetadata
    MultiIdatGenericPreChunkContainerSpec.expectedMetadata
    MultiIdatGammaContainerSpec.toGeneric
  rcases s.container.gAMA with _ | _ <;> simp [GammaChunkWitness.toPreIdat, PngMetadata.empty]

lemma expectedMetadata_transparency_none (s : ExternalPngMultiIdatGammaSpec px) :
    s.container.expectedMetadata.transparency = none := by
  unfold MultiIdatGammaContainerSpec.expectedMetadata
    MultiIdatGenericPreChunkContainerSpec.expectedMetadata
    MultiIdatGammaContainerSpec.toGeneric
  rcases s.container.gAMA with _ | _ <;> simp [GammaChunkWitness.toPreIdat, PngMetadata.empty]

lemma expectedMetadata_chromaticities_isSome (s : ExternalPngMultiIdatGammaSpec px) :
    (s.container.expectedMetadata.chromaticities.isSome : Bool) = false := by
  rw [s.expectedMetadata_chromaticities_none]; rfl

theorem parsePngForDecode_multiIdatGamma_external (s : ExternalPngMultiIdatGammaSpec px) :
    parsePngForDecode s.container.bytes s.container.bytes_size_ge_8 =
      some
        { header := s.container.header
          idat := s.container.idatData
          metadata := s.container.expectedMetadata } :=
  s.container.parsePngForDecode_multiIdatGammaContainerSpec_correct

theorem zlibInflate_multiIdatGamma_external {α : Type} (s : ExternalPngMultiIdatGammaSpec px)
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

theorem decodeBitmap_external_multiIdatGamma_correct (s : ExternalPngMultiIdatGammaSpec px) :
    Png.decodeBitmap s.container.bytes = some s.bitmap := by
  have hChrmGrayInactive :
      ¬ (((s.container.expectedMetadata.pixelOnlyColorSpace.srgb = none ∧
            s.container.expectedMetadata.pixelOnlyColorSpace.chromaticities.isSome = true) ∧
          (s.container.header.colorType = 2 ∨ s.container.header.colorType = 6)) ∧
        (PngPixel.colorType (α := px) = u8 0 ∨ PngPixel.colorType (α := px) = u8 4)) := by
    intro ⟨⟨⟨_, h⟩, _⟩, _⟩
    have : s.container.expectedMetadata.pixelOnlyColorSpace.chromaticities.isSome = false := by
      unfold PngMetadata.pixelOnlyColorSpace
      show s.container.expectedMetadata.chromaticities.isSome = false
      exact s.expectedMetadata_chromaticities_isSome
    rw [this] at h; exact absurd h (by decide)
  exact decodeBitmap_correct_of_witnesses s.container.bytes_size_ge_8
    s.hBitDepthMatch s.hTargetBitDepth s.container.hColorType
    s.hWidth s.hHeight s.hInterlace s.hPxColorType s.hBppLookup
    s.expectedMetadata_transparency_none
    hChrmGrayInactive
    s.parsePngForDecode_multiIdatGamma_external
    s.hIdatMin s.hInflated s.hRawSize s.hPixels s.hTransform

end ExternalPngMultiIdatGammaSpec

end Lemmas

end Bitmaps
