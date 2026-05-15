import Bitmap.Lemmas.MultiIdatExternalPngSpec
import Bitmap.Lemmas.ExternalPngCore
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

/-! ### End-to-end forward correctness

A one-line wrapper around the generic `decodeBitmap_correct_of_witnesses`
core: supply the spec's witnesses, plus a derived `hTransform` proving
the color-space transform is identity (because tIME-only metadata has
gamma/chromaticities/srgb all `none`). -/

theorem decodeBitmap_external_multiIdatTime_correct (s : ExternalPngMultiIdatTimeSpec px) :
    Png.decodeBitmap s.container.bytes = some s.bitmap := by
  have hMetaSrgb : s.container.expectedMetadata.srgb = none :=
    s.expectedMetadata_srgb_none
  have hMetaChrm : s.container.expectedMetadata.chromaticities = none :=
    s.expectedMetadata_chromaticities_none
  have hMetaGamma : s.container.expectedMetadata.gamma = none :=
    s.expectedMetadata_gamma_none
  have hChrmGrayInactive :
      ¬ (((s.container.expectedMetadata.pixelOnlyColorSpace.srgb = none ∧
            s.container.expectedMetadata.pixelOnlyColorSpace.chromaticities.isSome = true) ∧
          (s.container.header.colorType = 2 ∨ s.container.header.colorType = 6)) ∧
        (PngPixel.colorType (α := px) = u8 0 ∨ PngPixel.colorType (α := px) = u8 4)) := by
    intro ⟨⟨⟨_, h⟩, _⟩, _⟩
    have : s.container.expectedMetadata.pixelOnlyColorSpace.chromaticities.isSome = false := by
      unfold PngMetadata.pixelOnlyColorSpace
      show s.container.expectedMetadata.chromaticities.isSome = false
      rw [hMetaChrm]; rfl
    rw [this] at h; exact absurd h (by decide)
  have hPixelOnlySrgb :
      (PngMetadata.pixelOnlyColorSpace s.container.expectedMetadata).srgb = none := by
    unfold PngMetadata.pixelOnlyColorSpace; exact hMetaSrgb
  have hPixelOnlyChrm :
      (PngMetadata.pixelOnlyColorSpace s.container.expectedMetadata).chromaticities = none := by
    unfold PngMetadata.pixelOnlyColorSpace; exact hMetaChrm
  have hPixelOnlyGamma :
      (PngMetadata.pixelOnlyColorSpace s.container.expectedMetadata).gamma = none := by
    unfold PngMetadata.pixelOnlyColorSpace; exact hMetaGamma
  have hBitDepthMatch :
      s.container.header.bitDepth = (PngPixel.bitDepth (α := px)).toNat := by
    rw [s.container.hBitDepth, s.hTargetBitDepth]; decide
  have hTransform :
      applyPngColorSpaceTransform
        (PngMetadata.pixelOnlyColorSpace s.container.expectedMetadata)
        s.container.header.colorType (PngPixel.colorType (α := px))
        (PngPixel.bitDepth (α := px)) s.bitmap.data = some s.bitmap.data := by
    rw [s.hTargetBitDepth]
    unfold applyPngColorSpaceTransform
    rw [hPixelOnlySrgb, hPixelOnlyChrm, hPixelOnlyGamma]
  exact decodeBitmap_correct_of_witnesses s.container.bytes_size_ge_8
    hBitDepthMatch (Or.inl s.hTargetBitDepth) s.container.hColorType
    s.hWidth s.hHeight s.hInterlace s.hPxColorType s.hBppLookup
    s.expectedMetadata_transparency_none
    hChrmGrayInactive
    s.parsePngForDecode_multiIdatTime_external
    s.hIdatMin s.hInflated s.hRawSize s.hPixels hTransform

end ExternalPngMultiIdatTimeSpec

end Lemmas

end Bitmaps
