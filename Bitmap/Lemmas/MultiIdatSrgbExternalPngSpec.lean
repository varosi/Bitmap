import Bitmap.Lemmas.MultiIdatExternalPngSpec
import Bitmap.Lemmas.ExternalPngCore
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

theorem decodeBitmap_external_multiIdatSrgb_correct (s : ExternalPngMultiIdatSrgbSpec px) :
    Png.decodeBitmap s.container.bytes = some s.bitmap := by
  have hMetaChrm : s.container.expectedMetadata.chromaticities = none :=
    s.expectedMetadata_chromaticities_none
  have hMetaGamma : s.container.expectedMetadata.gamma = none :=
    s.expectedMetadata_gamma_none
  have hPixelOnlyChrm :
      (PngMetadata.pixelOnlyColorSpace s.container.expectedMetadata).chromaticities = none := by
    unfold PngMetadata.pixelOnlyColorSpace; exact hMetaChrm
  have hPixelOnlyGamma :
      (PngMetadata.pixelOnlyColorSpace s.container.expectedMetadata).gamma = none := by
    unfold PngMetadata.pixelOnlyColorSpace; exact hMetaGamma
  have hChrmIsSome :
      (s.container.expectedMetadata.pixelOnlyColorSpace.chromaticities.isSome : Bool) = false := by
    rw [hPixelOnlyChrm]; rfl
  -- For sRGB-only metadata, the color-space transform is identity in both
  -- srgb=none and srgb=some w cases: srgb=some short-circuits, srgb=none
  -- falls through with chrm/gamma both none.
  have hTransform :
      applyPngColorSpaceTransform
        (PngMetadata.pixelOnlyColorSpace s.container.expectedMetadata)
        s.container.header.colorType (PngPixel.colorType (α := px))
        (u8 8) s.bitmap.data = some s.bitmap.data := by
    unfold applyPngColorSpaceTransform
    rcases h : (PngMetadata.pixelOnlyColorSpace s.container.expectedMetadata).srgb with _ | _
    · rw [hPixelOnlyChrm, hPixelOnlyGamma]
    · rfl
  exact decodeBitmap_correct_of_witnesses s.container.bytes_size_ge_8
    s.container.hBitDepth s.container.hColorType
    s.hWidth s.hHeight s.hInterlace s.hPxColorType s.hTargetBitDepth s.hBppLookup
    s.expectedMetadata_transparency_none
    hChrmIsSome
    s.parsePngForDecode_multiIdatSrgb_external
    s.hIdatMin s.hInflated s.hRawSize s.hPixels hTransform

end ExternalPngMultiIdatSrgbSpec

end Lemmas

end Bitmaps
