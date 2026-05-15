import Bitmap.Lemmas.MultiIdatExternalPngSpec
import Bitmap.Lemmas.ExternalPngCore
import Bitmap.Lemmas.Png.MultiIdatChrmContainerSpec

universe u

namespace Bitmaps

namespace Lemmas

open Png

/-! ## End-to-end multi-IDAT + cHRM spec (Step 2c cHRM end-to-end)

Unlike tIME/pHYs/sRGB, the gamma metadata genuinely transforms the
pixel data via `applyGamma8ToPixels`. So the spec carries an explicit
pre-transform pixel array (`preTransformPixels`) plus a witness that
applying the color-space transform yields `bitmap.data`. -/

structure ExternalPngMultiIdatChrmSpec (px : Type u) [Pixel px] [PngPixel px] where
  bitmap : Bitmap px
  container : MultiIdatChrmContainerSpec
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
      `bitmap.data`. For cHRM-none, this reduces to identity. -/
  hTransform :
    applyPngColorSpaceTransform
      (PngMetadata.pixelOnlyColorSpace container.expectedMetadata)
      container.header.colorType (PngPixel.colorType (α := px))
      (u8 8) preTransformPixels = some bitmap.data

namespace ExternalPngMultiIdatChrmSpec

variable {px : Type u} [Pixel px] [PngPixel px]

lemma expectedMetadata_srgb_none (s : ExternalPngMultiIdatChrmSpec px) :
    s.container.expectedMetadata.srgb = none := by
  unfold MultiIdatChrmContainerSpec.expectedMetadata
    MultiIdatGenericPreChunkContainerSpec.expectedMetadata
    MultiIdatChrmContainerSpec.toGeneric
  rcases s.container.cHRM with _ | _ <;> simp [ChrmChunkWitness.toPreIdat, PngMetadata.empty]

lemma expectedMetadata_transparency_none (s : ExternalPngMultiIdatChrmSpec px) :
    s.container.expectedMetadata.transparency = none := by
  unfold MultiIdatChrmContainerSpec.expectedMetadata
    MultiIdatGenericPreChunkContainerSpec.expectedMetadata
    MultiIdatChrmContainerSpec.toGeneric
  rcases s.container.cHRM with _ | _ <;> simp [ChrmChunkWitness.toPreIdat, PngMetadata.empty]

theorem parsePngForDecode_multiIdatChrm_external (s : ExternalPngMultiIdatChrmSpec px) :
    parsePngForDecode s.container.bytes s.container.bytes_size_ge_8 =
      some
        { header := s.container.header
          idat := s.container.idatData
          metadata := s.container.expectedMetadata } :=
  s.container.parsePngForDecode_multiIdatChrmContainerSpec_correct

theorem zlibInflate_multiIdatChrm_external {α : Type} (s : ExternalPngMultiIdatChrmSpec px)
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

lemma pngColorTypeBitDepthSupported_multiIdatChrm_external
    (s : ExternalPngMultiIdatChrmSpec px) :
    pngColorTypeBitDepthSupported s.container.header.colorType 8 = true := by
  rcases s.container.hColorType with h | h | h | h <;> rw [h] <;> decide

lemma colorTypeCases_multiIdatChrm_external (s : ExternalPngMultiIdatChrmSpec px) :
    ¬ s.container.header.colorType = 0 →
    ¬ s.container.header.colorType = 2 →
    ¬ s.container.header.colorType = 4 →
    s.container.header.colorType = 6 := by
  intro h0 h2 h4
  rcases s.container.hColorType with hc | hc | hc | hc
  · exact absurd hc h0
  · exact absurd hc h2
  · exact absurd hc h4
  · exact hc

lemma ct4_noReject_multiIdatChrm_external (s : ExternalPngMultiIdatChrmSpec px) :
    s.container.header.colorType = 4 →
    ¬ PngPixel.colorType (α := px) = u8 4 →
    PngPixel.colorType (α := px) = u8 6 := by
  intro h4 hne
  have : PngPixel.colorType (α := px) = u8 4 := by rw [s.hPxColorType, h4]
  exact absurd this hne

theorem decodeBitmap_external_multiIdatChrm_correct (s : ExternalPngMultiIdatChrmSpec px) :
    Png.decodeBitmap s.container.bytes = some s.bitmap := by
  -- For cHRM spec, target colorType = source colorType (via hColorType +
  -- hPxColorType). If source ∈ {2,6}, target ∉ {u8 0, u8 4}; if source ∈
  -- {0,4}, source ∉ {2,6}. Either way, chrmGrayActive is false.
  have hChrmGrayInactive :
      ¬ (((s.container.expectedMetadata.pixelOnlyColorSpace.srgb = none ∧
            s.container.expectedMetadata.pixelOnlyColorSpace.chromaticities.isSome = true) ∧
          (s.container.header.colorType = 2 ∨ s.container.header.colorType = 6)) ∧
        (PngPixel.colorType (α := px) = u8 0 ∨ PngPixel.colorType (α := px) = u8 4)) := by
    intro ⟨⟨_, hSrc⟩, hTgt⟩
    -- target = u8 source, so target ∈ {u8 2, u8 6}, not {u8 0, u8 4}.
    rcases hSrc with h2 | h6
    · have hPxIs : PngPixel.colorType (α := px) = u8 2 := by
        rw [s.hPxColorType, h2]
      rcases hTgt with h | h
      · rw [hPxIs] at h; exact absurd h (by decide)
      · rw [hPxIs] at h; exact absurd h (by decide)
    · have hPxIs : PngPixel.colorType (α := px) = u8 6 := by
        rw [s.hPxColorType, h6]
      rcases hTgt with h | h
      · rw [hPxIs] at h; exact absurd h (by decide)
      · rw [hPxIs] at h; exact absurd h (by decide)
  have hBitDepthMatch :
      s.container.header.bitDepth = (PngPixel.bitDepth (α := px)).toNat := by
    rw [s.container.hBitDepth, s.hTargetBitDepth]; decide
  have hTransform_bd :
      applyPngColorSpaceTransform
        (PngMetadata.pixelOnlyColorSpace s.container.expectedMetadata)
        s.container.header.colorType (PngPixel.colorType (α := px))
        (PngPixel.bitDepth (α := px)) s.preTransformPixels = some s.bitmap.data := by
    rw [s.hTargetBitDepth]; exact s.hTransform
  exact decodeBitmap_correct_of_witnesses s.container.bytes_size_ge_8
    hBitDepthMatch (Or.inl s.hTargetBitDepth) s.container.hColorType
    s.hWidth s.hHeight s.hInterlace s.hPxColorType s.hBppLookup
    s.expectedMetadata_transparency_none
    hChrmGrayInactive
    s.parsePngForDecode_multiIdatChrm_external
    s.hIdatMin s.hInflated s.hRawSize s.hPixels hTransform_bd

end ExternalPngMultiIdatChrmSpec

end Lemmas

end Bitmaps
