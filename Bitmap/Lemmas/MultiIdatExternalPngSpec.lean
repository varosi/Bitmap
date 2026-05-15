import Bitmap.Lemmas.ExternalPngSpec
import Bitmap.Lemmas.ExternalPngCore
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

/-- Phase 6c closure: any `ExternalPngMultiIdatSpec` is accepted by
`decodeBitmap` and decodes to the spec's bitmap. Thin wrapper around
the generic `decodeBitmap_correct_of_witnesses`. -/
theorem decodeBitmap_external_multiIdat_correct (s : ExternalPngMultiIdatSpec px) :
    Png.decodeBitmap s.container.bytes = some s.bitmap := by
  have hChrmIsSome :
      (PngMetadata.empty.pixelOnlyColorSpace.chromaticities.isSome : Bool) = false := by decide
  have hTransform :
      applyPngColorSpaceTransform
        (PngMetadata.pixelOnlyColorSpace PngMetadata.empty)
        s.container.header.colorType (PngPixel.colorType (α := px))
        (u8 8) s.bitmap.data = some s.bitmap.data := by
    unfold applyPngColorSpaceTransform PngMetadata.pixelOnlyColorSpace
    rfl
  exact decodeBitmap_correct_of_witnesses s.container.bytes_size_ge_8
    s.container.hBitDepth s.container.hColorType
    s.hWidth s.hHeight s.hInterlace s.hPxColorType s.hTargetBitDepth s.hBppLookup
    (show (PngMetadata.empty : PngMetadata).transparency = none from rfl)
    hChrmIsSome
    s.parsePngForDecode_multiIdat_external
    s.hIdatMin s.hInflated s.hRawSize s.hPixels hTransform

end ExternalPngMultiIdatSpec

/-! ## Phase 5 → Phase 6 bridge

Every `ExternalPngSpec` is the singleton case of an
`ExternalPngMultiIdatSpec`: lifting wraps the container via
`SimpleContainerSpec.toMulti`. This makes `decodeBitmap_external_correct`
a corollary of `decodeBitmap_external_multiIdat_correct`. -/

/-- Lift an `ExternalPngSpec` to a singleton `ExternalPngMultiIdatSpec`,
preserving all decode-side witnesses. -/
def ExternalPngSpec.toMultiIdat {px : Type u} [Pixel px] [PngPixel px]
    (s : ExternalPngSpec px) : ExternalPngMultiIdatSpec px where
  bitmap := s.bitmap
  container := s.container.toMulti s.hIdatSize
  hWidth := s.hWidth
  hHeight := s.hHeight
  hColorType := s.hColorType
  hInterlace := s.hInterlace
  hPxColorType := s.hPxColorType
  hTargetBitDepth := s.hTargetBitDepth
  hBppLookup := s.hBppLookup
  hIdatMin := by
    rw [s.container.toMulti_idatData s.hIdatSize]
    exact s.hIdatMin
  inflatedRaw := s.inflatedRaw
  hInflated := by
    simp only [s.container.toMulti_idatData s.hIdatSize]
    exact s.hInflated
  hRawSize := s.hRawSize
  hPixels := s.hPixels

/-- The lifted multi-spec's container bytes equal the simple spec's
container bytes. -/
lemma ExternalPngSpec.toMultiIdat_bytes {px : Type u} [Pixel px] [PngPixel px]
    (s : ExternalPngSpec px) :
    s.toMultiIdat.container.bytes = s.container.bytes :=
  s.container.toMulti_bytes s.hIdatSize

/-- Phase 5 reduces to Phase 6: `decodeBitmap_external_correct` follows
from `decodeBitmap_external_multiIdat_correct` applied to the singleton
lift. -/
theorem decodeBitmap_external_correct_via_multiIdat
    {px : Type u} [Pixel px] [PngPixel px] (s : ExternalPngSpec px) :
    Png.decodeBitmap s.container.bytes = some s.bitmap := by
  have h := s.toMultiIdat.decodeBitmap_external_multiIdat_correct
  rw [s.toMultiIdat_bytes] at h
  exact h

end Lemmas

end Bitmaps
