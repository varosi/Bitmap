import Bitmap.Lemmas.MultiIdatExternalPngSpec
import Bitmap.Lemmas.Png.MultiIdatSrgbContainerSpec

universe u

namespace Bitmaps

namespace Lemmas

open Png

/-! ## End-to-end multi-IDAT + sRGB spec (Step 2c (sRGB) end-to-end)

`ExternalPngMultiIdatSrgbSpec` is the natural generalisation of
`ExternalPngMultiIdatSpec` to byte streams that include an optional
`sRGB` chunk. Because the recorded modification timestamp does not
flow through `applyPngColorSpaceTransform` (which inspects only
`srgb`/`chromaticities`/`gamma`), the end-to-end proof is essentially
the multi-IDAT one with the empty-metadata discharge swapped for the
`expectedMetadata`-with-`srgb` form. -/

/-- A description of an external PNG byte stream with multiple IDAT
chunks plus an optional `sRGB` chunk between IHDR and the first IDAT. -/
structure ExternalPngMultiIdatSrgbSpec (px : Type u) [Pixel px] [PngPixel px] where
  bitmap : Bitmap px
  container : MultiIdatSrgbContainerSpec
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

namespace ExternalPngMultiIdatSrgbSpec

variable {px : Type u} [Pixel px] [PngPixel px]

/-- The sRGB-only metadata has `chromaticities = none` (no cHRM chunk). -/
lemma expectedMetadata_chromaticities_none (s : ExternalPngMultiIdatSrgbSpec px) :
    s.container.expectedMetadata.chromaticities = none := by
  unfold MultiIdatSrgbContainerSpec.expectedMetadata
  rcases s.container.sRGB with _ | _ <;> simp [PngMetadata.empty]

/-- The sRGB-only metadata has `gamma = none` (no gAMA chunk). -/
lemma expectedMetadata_gamma_none (s : ExternalPngMultiIdatSrgbSpec px) :
    s.container.expectedMetadata.gamma = none := by
  unfold MultiIdatSrgbContainerSpec.expectedMetadata
  rcases s.container.sRGB with _ | _ <;> simp [PngMetadata.empty]

/-- The sRGB-only metadata has `transparency = none` (no tRNS chunk). -/
lemma expectedMetadata_transparency_none (s : ExternalPngMultiIdatSrgbSpec px) :
    s.container.expectedMetadata.transparency = none := by
  unfold MultiIdatSrgbContainerSpec.expectedMetadata
  rcases s.container.sRGB with _ | _ <;> simp [PngMetadata.empty]

lemma expectedMetadata_chromaticities_isSome (s : ExternalPngMultiIdatSrgbSpec px) :
    (s.container.expectedMetadata.chromaticities.isSome : Bool) = false := by
  rw [s.expectedMetadata_chromaticities_none]; rfl

/-! ### Container layer -/

theorem parsePngForDecode_multiIdatSrgb_external (s : ExternalPngMultiIdatSrgbSpec px) :
    parsePngForDecode s.container.bytes s.container.bytes_size_ge_8 =
      some
        { header := s.container.header
          idat := s.container.idatData
          metadata := s.container.expectedMetadata } :=
  s.container.parsePngForDecode_multiIdatSrgbContainerSpec_correct

/-! ### Zlib layer -/

theorem zlibInflate_multiIdatSrgb_external {α : Type} (s : ExternalPngMultiIdatSrgbSpec px)
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

/-! ### Discharging lemmas -/

lemma pngColorTypeBitDepthSupported_multiIdatSrgb_external
    (s : ExternalPngMultiIdatSrgbSpec px) :
    pngColorTypeBitDepthSupported s.container.header.colorType 8 = true := by
  rcases s.container.hColorType with h | h | h | h <;> rw [h] <;> decide

lemma colorTypeCases_multiIdatSrgb_external (s : ExternalPngMultiIdatSrgbSpec px) :
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

lemma ct4_noReject_multiIdatSrgb_external (s : ExternalPngMultiIdatSrgbSpec px) :
    s.container.header.colorType = 4 →
    ¬ PngPixel.colorType (α := px) = u8 4 →
    PngPixel.colorType (α := px) = u8 6 := by
  intro h4 hne
  have : PngPixel.colorType (α := px) = u8 4 := by rw [s.hPxColorType, h4]
  exact absurd this hne

/-! ### End-to-end forward correctness -/

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 4096 in
/-- The metadata's `srgb` doesn't perturb the decoder
color flow (`applyPngColorSpaceTransform` inspects only
srgb/chromaticities/gamma), so the proof mirrors
`decodeBitmap_external_multiIdat_correct`. -/
theorem decodeBitmap_external_multiIdatSrgb_correct (s : ExternalPngMultiIdatSrgbSpec px) :
    Png.decodeBitmap s.container.bytes = some s.bitmap := by
  have hParseForDecode := s.parsePngForDecode_multiIdatSrgb_external
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
  have hvalid :
      s.bitmap.data.size = s.bitmap.size.width * s.bitmap.size.height * bpp := by
    simpa [bpp] using s.bitmap.valid
  have hMetaChrm : s.container.expectedMetadata.chromaticities = none :=
    s.expectedMetadata_chromaticities_none
  have hMetaGamma : s.container.expectedMetadata.gamma = none :=
    s.expectedMetadata_gamma_none
  -- Key observation: for our spec, srgb may be `some _` or `none`; in
  -- both cases the color-space transform is identity (srgb=some
  -- short-circuits; srgb=none falls through with chrm/gamma both none).
  have hPixelOnlyChrm :
      (PngMetadata.pixelOnlyColorSpace s.container.expectedMetadata).chromaticities = none := by
    unfold PngMetadata.pixelOnlyColorSpace; exact hMetaChrm
  have hPixelOnlyGamma :
      (PngMetadata.pixelOnlyColorSpace s.container.expectedMetadata).gamma = none := by
    unfold PngMetadata.pixelOnlyColorSpace; exact hMetaGamma
  have hApplyId :
      ∀ (sct : Nat) (tct : UInt8) (tbd : UInt8) (pixels : ByteArray),
        applyPngColorSpaceTransform
          (PngMetadata.pixelOnlyColorSpace s.container.expectedMetadata)
          sct tct tbd pixels = some pixels := by
    intro sct tct tbd pixels
    unfold applyPngColorSpaceTransform
    rcases h : (PngMetadata.pixelOnlyColorSpace s.container.expectedMetadata).srgb with _ | _
    · rw [hPixelOnlyChrm, hPixelOnlyGamma]
    · rfl
  have hrowsEq :
      ((PngPixel.decodeRowsLoop (α := px) s.inflatedRaw s.bitmap.size.width
            s.bitmap.size.height bpp (s.bitmap.size.width * bpp) 0 0 ByteArray.empty
            { data := Array.replicate
                (s.bitmap.size.width * s.bitmap.size.height * Pixel.bytesPerPixel (α := px))
                0 }).bind
        fun decodedPixels ↦
          (applyPngColorSpaceTransform
              (PngMetadata.pixelOnlyColorSpace s.container.expectedMetadata)
            (PngPixel.colorType (α := px)).toNat
            (PngPixel.colorType (α := px)) (PngPixel.bitDepth (α := px)) decodedPixels).bind
            fun pixels ↦
              if h : pixels.size = s.bitmap.size.width * s.bitmap.size.height *
                  Pixel.bytesPerPixel (α := px) then
                some { size := { width := s.bitmap.size.width,
                                 height := s.bitmap.size.height },
                       data := pixels, valid := h }
              else none) =
      some s.bitmap := by
    simp [s.hPixels, hApplyId, hvalid, bpp]
  have hctbdHdr8 :
      pngColorTypeBitDepthSupported s.container.header.colorType 8 = true :=
    s.pngColorTypeBitDepthSupported_multiIdatSrgb_external
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
    have hsize : s.inflatedRaw.size =
        s.bitmap.size.height * (s.bitmap.size.width * Pixel.bytesPerPixel (α := px) + 1) :=
      s.hRawSize
    simp [hsize, s.hPixels, hApplyId, s.bitmap.valid]
  have hCtCases := s.colorTypeCases_multiIdatSrgb_external
  have hCt4Reject := s.ct4_noReject_multiIdatSrgb_external
  have hChrmIsSome : (s.container.expectedMetadata.chromaticities.isSome : Bool) = false :=
    s.expectedMetadata_chromaticities_isSome
  unfold Png.decodeBitmap
  rcases s.hInflated with hStored | ⟨hStoredNone, hZlib⟩
  · simpa [s.container.bytes_size_ge_8, hParseForDecode, hStored,
      ct, bd, hbdNoReject, hbitDepthEq, hbitDepthEqHeader, hnoDownsample, hpngBpp',
      hctbd', hBdNot1', normalizeRawByInterlace?, PngMetadata.pixelOnlyColorSpace,
      s.hIdatMin, s.hInterlace, s.hWidth, s.hHeight, hBitDepth,
      s.hTargetBitDepth, hChrmIsSome, hMetaChrm, hMetaGamma] using
      (And.intro hmetadataNoTransparency
        (And.intro hctbdHdr8
          (And.intro hCtCases
            (And.intro h8eq
              (And.intro hCt4Reject hBppChain)))))
  · simpa [s.container.bytes_size_ge_8, hParseForDecode, hStoredNone, hZlib,
      ct, bd, hbdNoReject, hbitDepthEq, hbitDepthEqHeader, hnoDownsample, hpngBpp',
      hctbd', hBdNot1', normalizeRawByInterlace?, PngMetadata.pixelOnlyColorSpace,
      s.hIdatMin, s.hInterlace, s.hWidth, s.hHeight, hBitDepth,
      s.hTargetBitDepth, hChrmIsSome, hMetaChrm, hMetaGamma] using
      (And.intro hmetadataNoTransparency
        (And.intro hctbdHdr8
          (And.intro hCtCases
            (And.intro h8eq
              (And.intro hCt4Reject hBppChain)))))

end ExternalPngMultiIdatSrgbSpec

end Lemmas

end Bitmaps
