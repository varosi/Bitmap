import Bitmap.Lemmas.MultiIdatExternalPngSpec
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
      `bitmap.data`. For gAMA-none, this reduces to identity. -/
  hTransform :
    applyPngColorSpaceTransform
      (PngMetadata.pixelOnlyColorSpace container.expectedMetadata)
      container.header.colorType (PngPixel.colorType (α := px))
      (u8 8) preTransformPixels = some bitmap.data

namespace ExternalPngMultiIdatGammaSpec

variable {px : Type u} [Pixel px] [PngPixel px]

lemma expectedMetadata_chromaticities_none (s : ExternalPngMultiIdatGammaSpec px) :
    s.container.expectedMetadata.chromaticities = none := by
  unfold MultiIdatGammaContainerSpec.expectedMetadata
  rcases s.container.gAMA with _ | _ <;> simp [PngMetadata.empty]

lemma expectedMetadata_srgb_none (s : ExternalPngMultiIdatGammaSpec px) :
    s.container.expectedMetadata.srgb = none := by
  unfold MultiIdatGammaContainerSpec.expectedMetadata
  rcases s.container.gAMA with _ | _ <;> simp [PngMetadata.empty]

lemma expectedMetadata_transparency_none (s : ExternalPngMultiIdatGammaSpec px) :
    s.container.expectedMetadata.transparency = none := by
  unfold MultiIdatGammaContainerSpec.expectedMetadata
  rcases s.container.gAMA with _ | _ <;> simp [PngMetadata.empty]

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

lemma pngColorTypeBitDepthSupported_multiIdatGamma_external
    (s : ExternalPngMultiIdatGammaSpec px) :
    pngColorTypeBitDepthSupported s.container.header.colorType 8 = true := by
  rcases s.container.hColorType with h | h | h | h <;> rw [h] <;> decide

lemma colorTypeCases_multiIdatGamma_external (s : ExternalPngMultiIdatGammaSpec px) :
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

lemma ct4_noReject_multiIdatGamma_external (s : ExternalPngMultiIdatGammaSpec px) :
    s.container.header.colorType = 4 →
    ¬ PngPixel.colorType (α := px) = u8 4 →
    PngPixel.colorType (α := px) = u8 6 := by
  intro h4 hne
  have : PngPixel.colorType (α := px) = u8 4 := by rw [s.hPxColorType, h4]
  exact absurd this hne

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 4096 in
theorem decodeBitmap_external_multiIdatGamma_correct (s : ExternalPngMultiIdatGammaSpec px) :
    Png.decodeBitmap s.container.bytes = some s.bitmap := by
  have hParseForDecode := s.parsePngForDecode_multiIdatGamma_external
  let ct := (PngPixel.colorType (α := px)).toNat
  let bd := (PngPixel.bitDepth (α := px)).toNat
  let bpp := Pixel.bytesPerPixel (α := px)
  have hBitDepth : s.container.header.bitDepth = 8 := s.container.hBitDepth
  have hCtSet : s.container.header.colorType = 0 ∨ s.container.header.colorType = 2 ∨
      s.container.header.colorType = 4 ∨ s.container.header.colorType = 6 :=
    s.container.hColorType
  have hbd_8 : bd = 8 := by
    show (PngPixel.bitDepth (α := px)).toNat = 8
    rw [s.hTargetBitDepth]; decide
  have hBdNot1' : ¬ bd = 1 := by rw [hbd_8]; decide
  have hbdNoReject : pngBitDepthSupported bd = true := by rw [hbd_8]; decide
  have hbitDepthEq :
      ((PngPixel.bitDepth (α := px)).toNat != bd) = false := by simp [bd]
  have hbitDepthEqHeader :
      (bd != (PngPixel.bitDepth (α := px)).toNat) = false := by simp [bd]
  have hnoDownsample :
      ¬((PngPixel.bitDepth (α := px)).toNat = 16 ∧ PngPixel.bitDepth (α := px) = u8 8) := by
    rintro ⟨h16, _⟩
    rw [s.hTargetBitDepth] at h16
    revert h16; decide
  have hct'eq : ct = s.container.header.colorType := by simp [ct, s.hColorType]
  have hct' : ct = 0 ∨ ct = 2 ∨ ct = 4 ∨ ct = 6 := by rw [hct'eq]; exact hCtSet
  have hctNoReject :
      ct = 4 → ¬ PngPixel.colorType (α := px) = u8 4 →
        PngPixel.colorType (α := px) = u8 6 := by
    intro h4 hne
    have hCtH : s.container.header.colorType = 4 := by rw [← hct'eq]; exact h4
    have : PngPixel.colorType (α := px) = u8 4 := by rw [s.hPxColorType, hCtH]
    exact absurd this hne
  have hctbd' : pngColorTypeBitDepthSupported ct bd = true := by
    rw [hct'eq, hbd_8]
    rcases hCtSet with h | h | h | h <;> rw [h] <;> decide
  have hpngBpp' : pngBytesPerPixelForColorTypeAndBitDepth? ct bd = some bpp := by
    rw [hct'eq, hbd_8, ← hBitDepth]; exact s.hBppLookup
  have hmetadataNoTransparency :
      s.container.expectedMetadata.transparency = none :=
    s.expectedMetadata_transparency_none
  have hrawEq' :
      s.inflatedRaw.size = s.bitmap.size.height * (s.bitmap.size.width * bpp + 1) := by
    simpa [bpp] using s.hRawSize
  -- Compose decode + transform.
  have hrowsEq :
      ((PngPixel.decodeRowsLoop (α := px) s.inflatedRaw s.bitmap.size.width
            s.bitmap.size.height bpp (s.bitmap.size.width * bpp) 0 0 ByteArray.empty
            { data := Array.replicate
                (s.bitmap.size.width * s.bitmap.size.height * Pixel.bytesPerPixel (α := px))
                0 }).bind
        fun decodedPixels ↦
          (applyPngColorSpaceTransform
              (PngMetadata.pixelOnlyColorSpace s.container.expectedMetadata)
              s.container.header.colorType
              (PngPixel.colorType (α := px)) (u8 8) decodedPixels).bind
            fun pixels ↦
              if h : pixels.size = s.bitmap.size.width * s.bitmap.size.height *
                  Pixel.bytesPerPixel (α := px) then
                some { size := { width := s.bitmap.size.width,
                                 height := s.bitmap.size.height },
                       data := pixels, valid := h }
              else none) =
      some s.bitmap := by
    rw [s.hPixels, Option.bind_some]
    rw [s.hTransform, Option.bind_some]
    have hvalid :
        s.bitmap.data.size = s.bitmap.size.width * s.bitmap.size.height * bpp := by
      simpa [bpp] using s.bitmap.valid
    simp [hvalid, bpp]
  have hctbdHdr8 :
      pngColorTypeBitDepthSupported s.container.header.colorType 8 = true :=
    s.pngColorTypeBitDepthSupported_multiIdatGamma_external
  have h8eq : (8 : Nat) = (u8 8).toNat := by decide
  have hBppChain :
      ((pngBytesPerPixelForColorTypeAndBitDepth? s.container.header.colorType 8).bind
        fun bpp ↦
          if s.inflatedRaw.size = s.bitmap.size.height * (s.bitmap.size.width * bpp + 1) then
            (PngPixel.decodeRowsLoop (α := px) s.inflatedRaw s.bitmap.size.width
                  s.bitmap.size.height bpp (s.bitmap.size.width * bpp) 0 0 ByteArray.empty
                  { data := Array.replicate
                      (s.bitmap.size.width * s.bitmap.size.height *
                        Pixel.bytesPerPixel (α := px)) 0 }).bind
              fun y ↦
                (applyPngColorSpaceTransform
                    (PngMetadata.pixelOnlyColorSpace s.container.expectedMetadata)
                    s.container.header.colorType (PngPixel.colorType (α := px))
                    (u8 8) y).bind
                  fun pixels ↦
                    if h : pixels.size = s.bitmap.size.width * s.bitmap.size.height *
                        Pixel.bytesPerPixel (α := px) then
                      some { size := { width := s.bitmap.size.width,
                                       height := s.bitmap.size.height },
                             data := pixels, valid := h }
                    else none
          else none) = some s.bitmap := by
    have hBpp8 : pngBytesPerPixelForColorTypeAndBitDepth?
        s.container.header.colorType 8 =
          some (Pixel.bytesPerPixel (α := px)) := by
      rw [← hBitDepth]; exact s.hBppLookup
    rw [hBpp8]
    simp only [Option.bind_some]
    rw [if_pos s.hRawSize]
    exact hrowsEq
  have hCtCases := s.colorTypeCases_multiIdatGamma_external
  have hCt4Reject := s.ct4_noReject_multiIdatGamma_external
  have hChrmIsSome : (s.container.expectedMetadata.chromaticities.isSome : Bool) = false :=
    s.expectedMetadata_chromaticities_isSome
  have hPixelOnlyChrmIsSome :
      (s.container.expectedMetadata.pixelOnlyColorSpace.chromaticities.isSome : Bool) = false := by
    unfold PngMetadata.pixelOnlyColorSpace
    show (s.container.expectedMetadata.chromaticities.isSome : Bool) = false
    exact hChrmIsSome
  unfold Png.decodeBitmap
  rcases s.hInflated with hStored | ⟨hStoredNone, hZlib⟩
  · simpa [s.container.bytes_size_ge_8, hParseForDecode, hStored,
      ct, bd, hbdNoReject, hbitDepthEq, hbitDepthEqHeader, hnoDownsample, hpngBpp',
      hctbd', hBdNot1', normalizeRawByInterlace?,
      s.hIdatMin, s.hInterlace, s.hWidth, s.hHeight, hBitDepth,
      s.hTargetBitDepth, hChrmIsSome, hPixelOnlyChrmIsSome] using
      (And.intro hmetadataNoTransparency
        (And.intro hctbdHdr8
          (And.intro hCtCases
            (And.intro h8eq
              (And.intro hCt4Reject hBppChain)))))
  · simpa [s.container.bytes_size_ge_8, hParseForDecode, hStoredNone, hZlib,
      ct, bd, hbdNoReject, hbitDepthEq, hbitDepthEqHeader, hnoDownsample, hpngBpp',
      hctbd', hBdNot1', normalizeRawByInterlace?,
      s.hIdatMin, s.hInterlace, s.hWidth, s.hHeight, hBitDepth,
      s.hTargetBitDepth, hChrmIsSome, hPixelOnlyChrmIsSome] using
      (And.intro hmetadataNoTransparency
        (And.intro hctbdHdr8
          (And.intro hCtCases
            (And.intro h8eq
              (And.intro hCt4Reject hBppChain)))))

end ExternalPngMultiIdatGammaSpec

end Lemmas

end Bitmaps
