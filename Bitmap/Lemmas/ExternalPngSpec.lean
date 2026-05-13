import Bitmap.Lemmas.Png.ContainerSpec
import Bitmap.Lemmas.Png.DeflateStreamProofs
import Bitmap.Lemmas.Png.RowFilterSpec
import Bitmap.Lemmas.Bitmap

universe u

namespace Bitmaps

namespace Lemmas

open Png

/-! ## End-to-end external-PNG spec (Phase 5)

`ExternalPngSpec px` describes a byte stream that the runtime
`decodeBitmap` accepts as a valid PNG of the supported subset and that
decodes to a specific `Bitmap px`. Unlike `decodeBitmap_encodeBitmap`,
this spec is independent of this library's encoder — any byte sequence
matching the spec's constraints is accepted, regardless of which tool
produced it.

The spec is restricted to the simplest decoder path:

  * 8-bit depth (no 1-bit or 16-bit conversions).
  * Color types 0 (gray), 2 (RGB), 4 (gray+alpha), 6 (RGBA).
  * Interlace 0 (no Adam7).
  * Container shape: signature + IHDR + single IDAT + IEND (no
    ancillary chunks), via `SimpleContainerSpec`.
  * Empty metadata (no tRNS / bKGD / gAMA / cHRM / sRGB).
  * Source color type matches target pixel type (no alpha-drop /
    alpha-add conversions, no 16→8 downsampling).

The structural composition is captured by witness fields on the spec;
the closure theorem `decodeBitmap_external_correct` threads them
through the runtime decoder. -/

/-- A description of an external PNG byte stream, decomposed into its
container / zlib / row-decoding layers.

Each layer is captured via a witness:

  * `container` (Phase 3) — the PNG byte layout.
  * `hInflated` — zlib decompression of `container.idatData` returns
    `inflatedRaw`.
  * `hPixels` — `PngPixel.decodeRowsLoop` over `inflatedRaw` returns
    the bitmap's pixel data. This single witness combines RFC 2083
    §6.2 row-filter reconstruction with pixel-format unpacking; the
    `RowFilterSpec.lean` lemmas can be composed to discharge it.

Color-type-specific witnesses (`hBppLookup`, `hTargetBitDepth`,
`hPxColorType`) account for the typeclass-dispatched
`Pixel.bytesPerPixel` and `PngPixel.bitDepth` values; each concrete
pixel type (`PixelGray8`, `PixelRGB8`, `PixelGrayAlpha8`, `PixelRGBA8`)
satisfies them by `rfl` / `decide`. -/
structure ExternalPngSpec (px : Type u) [Pixel px] [PngPixel px] where
  /-- The bitmap the byte stream should decode to. -/
  bitmap : Bitmap px
  /-- The container layer (signature + IHDR + IDAT + IEND chunks). -/
  container : SimpleContainerSpec
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
  /-- The IDAT data size fits in the PNG u32 length field. -/
  hIdatSize : container.idatData.size < 2 ^ 32
  /-- The IDAT data has at least two bytes (the zlib CMF + FLG header). -/
  hIdatMin : 2 ≤ container.idatData.size
  /-- The deflate-inflated bytes — one filter byte plus one row payload
      per row, totaling `height × (width × bpp + 1)`. -/
  inflatedRaw : ByteArray
  /-- The container's IDAT bytes decompress (under the zlib envelope)
      to `inflatedRaw`. Either the byte-aligned stored fast path or the
      general zlib loop is sufficient — the spec accepts either. -/
  hInflated :
    zlibDecompressStored container.idatData hIdatMin = some inflatedRaw ∨
    (zlibDecompressStored container.idatData hIdatMin = none ∧
     zlibDecompress container.idatData hIdatMin = some inflatedRaw)
  /-- `inflatedRaw` is the expected size for a filter-byte + row-payload
      stream of `height` rows. -/
  hRawSize :
    inflatedRaw.size =
      bitmap.size.height *
        (bitmap.size.width * Pixel.bytesPerPixel (α := px) + 1)
  /-- The pixel-extraction loop on `inflatedRaw` produces the bitmap's
      pixel data. This is the row-filter-reconstruction + pixel-format
      decoding obligation. The `RowFilterSpec.lean` lemmas can build
      this witness by chaining `unfilterRow_eq_spec` with the
      pixel-extraction loop. -/
  hPixels :
    PngPixel.decodeRowsLoop (α := px) inflatedRaw bitmap.size.width
        bitmap.size.height (Pixel.bytesPerPixel (α := px))
        (bitmap.size.width * Pixel.bytesPerPixel (α := px))
        0 0 ByteArray.empty
        { data := Array.replicate
            (bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px)) 0 } =
      some bitmap.data

namespace ExternalPngSpec

variable {px : Type u} [Pixel px] [PngPixel px]

/-! ### Layer-1 (container) composition

`parsePngForDecode` accepts the byte stream and returns the parsed
header / IDAT / empty metadata. This is a direct corollary of Phase 3
applied through the metadata-aware front-door. -/

/-- Phase 3 routing: `parsePngForDecode` accepts `s.container.bytes`
and produces the parsed header + IDAT data + empty metadata. -/
theorem parsePngForDecode_external (s : ExternalPngSpec px) :
    parsePngForDecode s.container.bytes s.container.bytes_size_ge_8 =
      some
        { header := s.container.header
          idat := s.container.idatData
          metadata := PngMetadata.empty } := by
  have hSimple :
      parsePngSimple s.container.bytes s.container.bytes_size_ge_8 =
        some (s.container.header, s.container.idatData) :=
    parsePngSimple_simpleContainerSpec_correct s.container s.hIdatSize
  unfold parsePngForDecode parsePngSimpleWithMetadata
  simp [hSimple]

/-! ### Layer-2 (zlib) composition

`decodeBitmap` calls `zlibDecompressStored` first, falling back to
`zlibDecompress` if it returns `none`. Either path through the
`hInflated` witness yields `some s.inflatedRaw`. This composition
lemma resolves the inflate `do`-bind down to the inflated bytes. -/

/-- The `do`-bind on the zlib inflate step reduces to `f s.inflatedRaw`
under either branch of the `hInflated` disjunction. -/
theorem zlibInflate_external {α : Type} (s : ExternalPngSpec px)
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

/-! ### Concrete-form discharging lemmas

These lemmas restate the spec's witnesses in the exact form
`decodeBitmap`'s simp normalisation produces (with `bitDepth = 8`,
`colorType` as the raw nat, and `Pixel.bytesPerPixel` unfolded), so
simp can consume them directly during the end-to-end proof. -/

lemma pngColorTypeBitDepthSupported_external (s : ExternalPngSpec px) :
    pngColorTypeBitDepthSupported s.container.header.colorType 8 = true := by
  rcases s.container.hColorType with h | h | h | h <;> rw [h] <;> decide

lemma colorTypeCases_external (s : ExternalPngSpec px) :
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

lemma ct4_noReject_external (s : ExternalPngSpec px) :
    s.container.header.colorType = 4 →
    ¬ PngPixel.colorType (α := px) = u8 4 →
    PngPixel.colorType (α := px) = u8 6 := by
  intro h4 hne
  have : PngPixel.colorType (α := px) = u8 4 := by rw [s.hPxColorType, h4]
  exact absurd this hne

/-! ### End-to-end forward correctness -/

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 4096 in
/-- Phase 5 closure: any `ExternalPngSpec` is accepted by `decodeBitmap`
and decodes to the spec's bitmap. -/
theorem decodeBitmap_external_correct (s : ExternalPngSpec px) :
    Png.decodeBitmap s.container.bytes = some s.bitmap := by
  -- Container layer.
  have hParseForDecode := s.parsePngForDecode_external
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
  -- Color-type facts (in `ct`-form, matching the round-trip's vocabulary).
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
  -- Color-type/bit-depth joint check passes.
  have hctbd' : pngColorTypeBitDepthSupported ct bd = true := by
    rw [hct'eq, hbd_8]
    rcases hCtSet with h | h | h | h <;> rw [h] <;> decide
  -- bpp lookup matches.
  have hpngBpp' : pngBytesPerPixelForColorTypeAndBitDepth? ct bd = some bpp := by
    rw [hct'eq, hbd_8, ← hBitDepth]; exact s.hBppLookup
  -- Metadata + transparency facts.
  have hmetadataNoTransparency : PngMetadata.empty.transparency = none := rfl
  -- Inflated bytes size in the round-trip's form.
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
  -- Conjunct #2 from the round-trip's simp residual: the joint check (in
  -- container-header form, with bitDepth already reduced to 8 by simp).
  have hctbdHdr8 :
      pngColorTypeBitDepthSupported s.container.header.colorType 8 = true :=
    s.pngColorTypeBitDepthSupported_external
  -- Conjunct #4: `8 = (u8 8).toNat` (a triviality simp doesn't auto-discharge).
  have h8eq : (8 : Nat) = (u8 8).toNat := by decide
  -- Inner bpp-lookup chain reducing to `some s.bitmap` (conjunct #6).
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
  -- Conjuncts #3 and #5: container-header forms (using helper lemmas).
  have hCtCases := s.colorTypeCases_external
  have hCt4Reject := s.ct4_noReject_external
  -- chrm-gray-active is false (no chromaticities under empty metadata).
  have hChrmIsSome : (PngMetadata.empty.chromaticities.isSome : Bool) = false := by decide
  -- Finish via simpa using.
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

end ExternalPngSpec

end Lemmas

end Bitmaps
