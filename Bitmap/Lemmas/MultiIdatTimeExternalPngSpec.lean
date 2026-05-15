import Bitmap.Lemmas.MultiIdatExternalPngSpec
import Bitmap.Lemmas.Png.MultiIdatTimeContainerSpec

universe u

namespace Bitmaps

namespace Lemmas

open Png

/-! ## End-to-end multi-IDAT + tIME spec (Step 2a end-to-end)

`ExternalPngMultiIdatTimeSpec` is the natural generalisation of
`ExternalPngMultiIdatSpec` to byte streams that include an optional
`tIME` chunk. Because the recorded modification timestamp does not
flow through `applyPngColorSpaceTransform` (which inspects only
`srgb`/`chromaticities`/`gamma`), the end-to-end proof is essentially
the multi-IDAT one with the empty-metadata discharge swapped for the
`expectedMetadata`-with-`modificationTime` form. -/

/-- A description of an external PNG byte stream with multiple IDAT
chunks plus an optional `tIME` chunk between IHDR and the first IDAT. -/
structure ExternalPngMultiIdatTimeSpec (px : Type u) [Pixel px] [PngPixel px] where
  bitmap : Bitmap px
  container : MultiIdatTimeContainerSpec
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

namespace ExternalPngMultiIdatTimeSpec

variable {px : Type u} [Pixel px] [PngPixel px]

/-- For our spec the `expectedMetadata` has at most a `modificationTime`
set; the color-space-affecting fields (srgb / chromaticities / gamma)
are all `none`. -/
lemma expectedMetadata_srgb_none (s : ExternalPngMultiIdatTimeSpec px) :
    s.container.expectedMetadata.srgb = none := by
  unfold MultiIdatTimeContainerSpec.expectedMetadata
  rcases s.container.tIME with _ | _ <;> simp [PngMetadata.empty]

lemma expectedMetadata_chromaticities_none (s : ExternalPngMultiIdatTimeSpec px) :
    s.container.expectedMetadata.chromaticities = none := by
  unfold MultiIdatTimeContainerSpec.expectedMetadata
  rcases s.container.tIME with _ | _ <;> simp [PngMetadata.empty]

lemma expectedMetadata_gamma_none (s : ExternalPngMultiIdatTimeSpec px) :
    s.container.expectedMetadata.gamma = none := by
  unfold MultiIdatTimeContainerSpec.expectedMetadata
  rcases s.container.tIME with _ | _ <;> simp [PngMetadata.empty]

lemma expectedMetadata_transparency_none (s : ExternalPngMultiIdatTimeSpec px) :
    s.container.expectedMetadata.transparency = none := by
  unfold MultiIdatTimeContainerSpec.expectedMetadata
  rcases s.container.tIME with _ | _ <;> simp [PngMetadata.empty]

lemma expectedMetadata_chromaticities_isSome (s : ExternalPngMultiIdatTimeSpec px) :
    (s.container.expectedMetadata.chromaticities.isSome : Bool) = false := by
  rw [s.expectedMetadata_chromaticities_none]; rfl

/-! ### Container layer -/

theorem parsePngForDecode_multiIdatTime_external (s : ExternalPngMultiIdatTimeSpec px) :
    parsePngForDecode s.container.bytes s.container.bytes_size_ge_8 =
      some
        { header := s.container.header
          idat := s.container.idatData
          metadata := s.container.expectedMetadata } :=
  s.container.parsePngForDecode_multiIdatTimeContainerSpec_correct

/-! ### Zlib layer -/

theorem zlibInflate_multiIdatTime_external {α : Type} (s : ExternalPngMultiIdatTimeSpec px)
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

lemma pngColorTypeBitDepthSupported_multiIdatTime_external
    (s : ExternalPngMultiIdatTimeSpec px) :
    pngColorTypeBitDepthSupported s.container.header.colorType 8 = true := by
  rcases s.container.hColorType with h | h | h | h <;> rw [h] <;> decide

lemma colorTypeCases_multiIdatTime_external (s : ExternalPngMultiIdatTimeSpec px) :
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

lemma ct4_noReject_multiIdatTime_external (s : ExternalPngMultiIdatTimeSpec px) :
    s.container.header.colorType = 4 →
    ¬ PngPixel.colorType (α := px) = u8 4 →
    PngPixel.colorType (α := px) = u8 6 := by
  intro h4 hne
  have : PngPixel.colorType (α := px) = u8 4 := by rw [s.hPxColorType, h4]
  exact absurd this hne

/-! ### End-to-end forward correctness -/

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 4096 in
/-- The metadata's `modificationTime` doesn't perturb the decoder
color flow (`applyPngColorSpaceTransform` inspects only
srgb/chromaticities/gamma), so the proof mirrors
`decodeBitmap_external_multiIdat_correct`. -/
theorem decodeBitmap_external_multiIdatTime_correct (s : ExternalPngMultiIdatTimeSpec px) :
    Png.decodeBitmap s.container.bytes = some s.bitmap := by
  have hParseForDecode := s.parsePngForDecode_multiIdatTime_external
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
  -- expectedMetadata behaves like empty under applyPngColorSpaceTransform
  have hMetaSrgb : s.container.expectedMetadata.srgb = none :=
    s.expectedMetadata_srgb_none
  have hMetaChrm : s.container.expectedMetadata.chromaticities = none :=
    s.expectedMetadata_chromaticities_none
  have hMetaGamma : s.container.expectedMetadata.gamma = none :=
    s.expectedMetadata_gamma_none
  have hApplyId :
      applyPngColorSpaceTransform s.container.expectedMetadata
          s.container.header.colorType (PngPixel.colorType (α := px))
          (PngPixel.bitDepth (α := px)) s.bitmap.data =
        some s.bitmap.data := by
    unfold applyPngColorSpaceTransform
    rw [hMetaSrgb, hMetaChrm, hMetaGamma]
  have hrowsEq :
      ((PngPixel.decodeRowsLoop (α := px) s.inflatedRaw s.bitmap.size.width
            s.bitmap.size.height bpp (s.bitmap.size.width * bpp) 0 0 ByteArray.empty
            { data := Array.replicate
                (s.bitmap.size.width * s.bitmap.size.height * Pixel.bytesPerPixel (α := px))
                0 }).bind
        fun decodedPixels ↦
          (applyPngColorSpaceTransform s.container.expectedMetadata
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
    simp [s.hPixels, hvalid, applyPngColorSpaceTransform, hMetaSrgb, hMetaChrm,
      hMetaGamma, bpp]
  have hctbdHdr8 :
      pngColorTypeBitDepthSupported s.container.header.colorType 8 = true :=
    s.pngColorTypeBitDepthSupported_multiIdatTime_external
  have h8eq : (8 : Nat) = (u8 8).toNat := by decide
  -- The decoder normalises metadata through `pixelOnlyColorSpace`, which
  -- keeps only gamma/chromaticities/srgb. For tIME-only metadata, all three
  -- are `none`, so the normalised metadata equals `PngMetadata.empty`.
  have hPixelOnly :
      PngMetadata.pixelOnlyColorSpace s.container.expectedMetadata =
        PngMetadata.empty := by
    unfold PngMetadata.pixelOnlyColorSpace
    rw [hMetaSrgb, hMetaChrm, hMetaGamma]
    rfl
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
    rw [hPixelOnly]
    simp [hsize, s.hPixels, applyPngColorSpaceTransform, PngMetadata.empty,
      s.bitmap.valid]
  have hCtCases := s.colorTypeCases_multiIdatTime_external
  have hCt4Reject := s.ct4_noReject_multiIdatTime_external
  have hChrmIsSome : (s.container.expectedMetadata.chromaticities.isSome : Bool) = false :=
    s.expectedMetadata_chromaticities_isSome
  unfold Png.decodeBitmap
  rcases s.hInflated with hStored | ⟨hStoredNone, hZlib⟩
  · simpa [s.container.bytes_size_ge_8, hParseForDecode, hStored,
      ct, bd, hbdNoReject, hbitDepthEq, hbitDepthEqHeader, hnoDownsample, hpngBpp',
      hctbd', hBdNot1', normalizeRawByInterlace?, PngMetadata.pixelOnlyColorSpace,
      s.hIdatMin, s.hInterlace, s.hWidth, s.hHeight, hBitDepth,
      s.hTargetBitDepth, hChrmIsSome, hMetaSrgb, hMetaChrm, hMetaGamma] using
      (And.intro hmetadataNoTransparency
        (And.intro hctbdHdr8
          (And.intro hCtCases
            (And.intro h8eq
              (And.intro hCt4Reject hBppChain)))))
  · simpa [s.container.bytes_size_ge_8, hParseForDecode, hStoredNone, hZlib,
      ct, bd, hbdNoReject, hbitDepthEq, hbitDepthEqHeader, hnoDownsample, hpngBpp',
      hctbd', hBdNot1', normalizeRawByInterlace?, PngMetadata.pixelOnlyColorSpace,
      s.hIdatMin, s.hInterlace, s.hWidth, s.hHeight, hBitDepth,
      s.hTargetBitDepth, hChrmIsSome, hMetaSrgb, hMetaChrm, hMetaGamma] using
      (And.intro hmetadataNoTransparency
        (And.intro hctbdHdr8
          (And.intro hCtCases
            (And.intro h8eq
              (And.intro hCt4Reject hBppChain)))))

end ExternalPngMultiIdatTimeSpec

end Lemmas

end Bitmaps
