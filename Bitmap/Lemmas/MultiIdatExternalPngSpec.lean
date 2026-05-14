import Bitmap.Lemmas.ExternalPngSpec
import Bitmap.Lemmas.Png.MultiIdatContainerSpec

universe u

namespace Bitmaps

namespace Lemmas

open Png

/-! ## Multi-IDAT external-PNG spec (Phase 6c)

`ExternalPngMultiIdatSpec` is the natural generalisation of
`ExternalPngSpec` to byte streams that contain *any positive number* of
consecutive `IDAT` chunks, matching the PNG specification. The
container layer is captured by `MultiIdatContainerSpec`; all other
layers (`zlib`, row-filter / pixel extraction) are unchanged because
they consume the concatenated `container.idatData` rather than the
individual chunks.

The end-to-end theorem `decodeBitmap_external_multiIdat_correct`
threads the multi-IDAT container layer through the same
`zlib`/row-filter witnesses used by Phase 5 (`decodeBitmap_external_correct`),
via the metadata-aware Phase 6c bridge
`parsePngForDecode_multiIdatContainerSpec_correct`. -/

/-- A description of an external PNG byte stream with multiple IDAT
chunks, decomposed into its container / zlib / row-decoding layers.

Each layer is captured via a witness — identical to `ExternalPngSpec`
except the container field uses `MultiIdatContainerSpec`. -/
structure ExternalPngMultiIdatSpec (px : Type u) [Pixel px] [PngPixel px] where
  /-- The bitmap the byte stream should decode to. -/
  bitmap : Bitmap px
  /-- The container layer (signature + IHDR + IDAT* + IEND chunks). -/
  container : MultiIdatContainerSpec
  /-- Container width matches bitmap width. -/
  hWidth : container.header.width = bitmap.size.width
  /-- Container height matches bitmap height. -/
  hHeight : container.header.height = bitmap.size.height
  /-- Container color type matches the pixel type's `PngPixel.colorType`. -/
  hColorType :
    container.header.colorType = (PngPixel.colorType (α := px)).toNat
  /-- Non-interlaced. -/
  hInterlace : container.header.interlace = 0
  /-- Target pixel type matches source color type. Used by the decoder
      to avoid alpha-drop/add conversions and to follow the
      `PngPixel.decodeRowsLoop` path. -/
  hPxColorType : PngPixel.colorType (α := px) = u8 container.header.colorType
  /-- Target pixel type uses 8-bit depth. -/
  hTargetBitDepth : PngPixel.bitDepth (α := px) = u8 8
  /-- `Pixel.bytesPerPixel` matches the PNG bpp table for the
      container's (colorType, bitDepth) pair. -/
  hBppLookup :
    pngBytesPerPixelForColorTypeAndBitDepth?
      container.header.colorType container.header.bitDepth =
        some (Pixel.bytesPerPixel (α := px))
  /-- The concatenated IDAT data has at least two bytes (zlib CMF+FLG). -/
  hIdatMin : 2 ≤ container.idatData.size
  /-- The deflate-inflated bytes — one filter byte plus one row payload
      per row, totaling `height × (width × bpp + 1)`. -/
  inflatedRaw : ByteArray
  /-- The container's concatenated IDAT bytes decompress (under the zlib
      envelope) to `inflatedRaw`. Either path is acceptable. -/
  hInflated :
    zlibDecompressStored container.idatData hIdatMin = some inflatedRaw ∨
    (zlibDecompressStored container.idatData hIdatMin = none ∧
     zlibDecompress container.idatData hIdatMin = some inflatedRaw)
  /-- `inflatedRaw` has the expected size. -/
  hRawSize :
    inflatedRaw.size =
      bitmap.size.height *
        (bitmap.size.width * Pixel.bytesPerPixel (α := px) + 1)
  /-- The pixel-extraction loop on `inflatedRaw` produces the bitmap's
      pixel data. -/
  hPixels :
    PngPixel.decodeRowsLoop (α := px) inflatedRaw bitmap.size.width
        bitmap.size.height (Pixel.bytesPerPixel (α := px))
        (bitmap.size.width * Pixel.bytesPerPixel (α := px))
        0 0 ByteArray.empty
        { data := Array.replicate
            (bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px)) 0 } =
      some bitmap.data

namespace ExternalPngMultiIdatSpec

variable {px : Type u} [Pixel px] [PngPixel px]

/-! ### Layer-1 (container) composition -/

/-- Phase 6c routing: `parsePngForDecode` accepts `s.container.bytes`
and produces the parsed header + IDAT data + empty metadata. Routes
through `parsePngForDecode_multiIdatContainerSpec_correct`. -/
theorem parsePngForDecode_multiIdat_external (s : ExternalPngMultiIdatSpec px) :
    parsePngForDecode s.container.bytes s.container.bytes_size_ge_8 =
      some
        { header := s.container.header
          idat := s.container.idatData
          metadata := PngMetadata.empty } :=
  s.container.parsePngForDecode_multiIdatContainerSpec_correct

/-! ### Layer-2 (zlib) composition -/

/-- The `do`-bind on the zlib inflate step reduces to `f s.inflatedRaw`
under either branch of the `hInflated` disjunction. -/
theorem zlibInflate_multiIdat_external {α : Type} (s : ExternalPngMultiIdatSpec px)
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

/-! ### Concrete-form discharging lemmas -/

lemma pngColorTypeBitDepthSupported_multiIdat_external
    (s : ExternalPngMultiIdatSpec px) :
    pngColorTypeBitDepthSupported s.container.header.colorType 8 = true := by
  rcases s.container.hColorType with h | h | h | h <;> rw [h] <;> decide

lemma colorTypeCases_multiIdat_external (s : ExternalPngMultiIdatSpec px) :
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

lemma ct4_noReject_multiIdat_external (s : ExternalPngMultiIdatSpec px) :
    s.container.header.colorType = 4 →
    ¬ PngPixel.colorType (α := px) = u8 4 →
    PngPixel.colorType (α := px) = u8 6 := by
  intro h4 hne
  have : PngPixel.colorType (α := px) = u8 4 := by rw [s.hPxColorType, h4]
  exact absurd this hne

/-! ### End-to-end forward correctness -/

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 4096 in
/-- Phase 6c closure: any `ExternalPngMultiIdatSpec` is accepted by
`decodeBitmap` and decodes to the spec's bitmap. -/
theorem decodeBitmap_external_multiIdat_correct (s : ExternalPngMultiIdatSpec px) :
    Png.decodeBitmap s.container.bytes = some s.bitmap := by
  -- Container layer (Phase 6c).
  have hParseForDecode := s.parsePngForDecode_multiIdat_external
  -- Local abbreviations matching the round-trip proof.
  let ct := (PngPixel.colorType (α := px)).toNat
  let bd := (PngPixel.bitDepth (α := px)).toNat
  let bpp := Pixel.bytesPerPixel (α := px)
  -- Container header facts.
  have hBitDepth : s.container.header.bitDepth = 8 := s.container.hBitDepth
  have hCtSet : s.container.header.colorType = 0 ∨ s.container.header.colorType = 2 ∨
      s.container.header.colorType = 4 ∨ s.container.header.colorType = 6 :=
    s.container.hColorType
  -- Bit-depth facts.
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
  -- Color-type facts.
  have hct'eq : ct = s.container.header.colorType := by simp [ct, s.hColorType]
  have hct' : ct = 0 ∨ ct = 2 ∨ ct = 4 ∨ ct = 6 := by rw [hct'eq]; exact hCtSet
  have hctProp : ¬ ct = 0 → ¬ ct = 2 → ¬ ct = 4 → ct = 6 := by
    intro h0 h2 h4
    rcases hct' with hc | hc | hc | hc
    · exact absurd hc h0
    · exact absurd hc h2
    · exact absurd hc h4
    · exact hc
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
  -- Metadata facts.
  have hmetadataNoTransparency : PngMetadata.empty.transparency = none := rfl
  -- Inflated bytes size.
  have hrawEq' :
      s.inflatedRaw.size = s.bitmap.size.height * (s.bitmap.size.width * bpp + 1) := by
    simpa [bpp] using s.hRawSize
  have hvalid :
      s.bitmap.data.size = s.bitmap.size.width * s.bitmap.size.height * bpp := by
    simpa [bpp] using s.bitmap.valid
  -- Composed pixel-decoding equation.
  have hrowsEq :
      ((PngPixel.decodeRowsLoop (α := px) s.inflatedRaw s.bitmap.size.width
            s.bitmap.size.height bpp (s.bitmap.size.width * bpp) 0 0 ByteArray.empty
            { data := Array.replicate
                (s.bitmap.size.width * s.bitmap.size.height * Pixel.bytesPerPixel (α := px))
                0 }).bind
        fun decodedPixels ↦
          (applyPngColorSpaceTransform PngMetadata.empty
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
    simp [s.hPixels, hvalid, applyPngColorSpaceTransform, PngMetadata.empty, bpp]
  have hctbdHdr8 :
      pngColorTypeBitDepthSupported s.container.header.colorType 8 = true :=
    s.pngColorTypeBitDepthSupported_multiIdat_external
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
                (applyPngColorSpaceTransform PngMetadata.empty
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
    simp [hsize, s.hPixels, applyPngColorSpaceTransform, PngMetadata.empty,
      s.bitmap.valid]
  have hCtCases := s.colorTypeCases_multiIdat_external
  have hCt4Reject := s.ct4_noReject_multiIdat_external
  have hChrmIsSome : (PngMetadata.empty.chromaticities.isSome : Bool) = false := by decide
  unfold Png.decodeBitmap
  rcases s.hInflated with hStored | ⟨hStoredNone, hZlib⟩
  · simpa [s.container.bytes_size_ge_8, hParseForDecode, hStored,
      ct, bd, hbdNoReject, hbitDepthEq, hbitDepthEqHeader, hnoDownsample, hpngBpp',
      hctbd', hBdNot1', normalizeRawByInterlace?, PngMetadata.pixelOnlyColorSpace,
      s.hIdatMin, s.hInterlace, s.hWidth, s.hHeight, hBitDepth,
      s.hTargetBitDepth, hChrmIsSome] using
      (And.intro hmetadataNoTransparency
        (And.intro hctbdHdr8
          (And.intro hCtCases
            (And.intro h8eq
              (And.intro hCt4Reject hBppChain)))))
  · simpa [s.container.bytes_size_ge_8, hParseForDecode, hStoredNone, hZlib,
      ct, bd, hbdNoReject, hbitDepthEq, hbitDepthEqHeader, hnoDownsample, hpngBpp',
      hctbd', hBdNot1', normalizeRawByInterlace?, PngMetadata.pixelOnlyColorSpace,
      s.hIdatMin, s.hInterlace, s.hWidth, s.hHeight, hBitDepth,
      s.hTargetBitDepth, hChrmIsSome] using
      (And.intro hmetadataNoTransparency
        (And.intro hctbdHdr8
          (And.intro hCtCases
            (And.intro h8eq
              (And.intro hCt4Reject hBppChain)))))

end ExternalPngMultiIdatSpec

end Lemmas

end Bitmaps
