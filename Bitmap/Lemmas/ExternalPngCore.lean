import Bitmap.Lemmas.Png.ContainerSpec
import Bitmap.Lemmas.Png.DeflateStreamProofs
import Bitmap.Lemmas.Png.RowFilterSpec
import Bitmap.Lemmas.Bitmap

universe u

namespace Bitmaps

namespace Lemmas

open Png

/-! ## Generic decode-side composition core

Two complementary theorems describe `decodeBitmap`'s behavior on any
byte stream:

* `decodeBitmap_correct_of_witnesses` — accepts when the parsed
  metadata has `transparency = none` (and all the structural
  decoder-layer witnesses line up), returning `some bitmap`. The
  core is generalised over the target bit depth: it accepts a
  disjunction `PngPixel.bitDepth (α := px) = u8 8 ∨ ... = u8 16`,
  so the same theorem proves 8-bit AND 16-bit success cases. The
  `hTransform` witness uses `(PngPixel.bitDepth (α := px))` rather
  than `(u8 8)`, so it adapts automatically. (Source bit depth must
  equal target bit depth; the 16→8 downsample path is not covered
  here.)
* `decodeBitmap_rejects_of_transparency` — rejects (returns `none`)
  whenever the parsed metadata has `transparency.isSome = true`.
  This handles `tRNS`-bearing byte streams: the parser accepts the
  chunk via `parsePngLoopFuelWithMetadata_accepts_tRNS`, the
  container-layer theorem (`parsePngForDecode_…_correct`) records
  the transparency, and this lemma then closes the end-to-end
  story with the decoder's deliberate `transparency.isSome` guard.

Each per-spec end-to-end theorem (`decodeBitmap_external_*_correct`)
is a one-line corollary that supplies the witnesses for the matching
core. The spec's `hTargetBitDepth` is itself the
`u8 8 ∨ u8 16` disjunction passed to the core; consistency with the
container's `header.bitDepth` is recorded by the spec's
`hBitDepthMatch` field. Both 8-bit and 16-bit pixel types
(`PixelGray8`, `PixelGray16`, …) satisfy the disjunction by
`Or.inl rfl` / `Or.inr rfl` respectively. -/

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 4096 in
/-- The decode-side core, generalised over the supported target bit
depth (8 or 16, with source = target). Every byte stream whose
decoder-layer witnesses line up with the bitmap is accepted by
`decodeBitmap`. The case where source bit depth ≠ target bit depth
(i.e., 16→8 downsampling or 1→8 upsampling) is not covered here. -/
theorem decodeBitmap_correct_of_witnesses
    {px : Type u} [Pixel px] [PngPixel px]
    {bitmap : Bitmap px}
    {header : PngHeader} {idat : ByteArray} {metadata : PngMetadata}
    {inflatedRaw preTransformPixels : ByteArray}
    {bytes : ByteArray} (hSize : 8 ≤ bytes.size)
    (hBitDepthMatch : header.bitDepth = (PngPixel.bitDepth (α := px)).toNat)
    (hTargetBitDepth : PngPixel.bitDepth (α := px) = u8 8 ∨
                       PngPixel.bitDepth (α := px) = u8 16)
    (hColorType : header.colorType = 0 ∨ header.colorType = 2 ∨
      header.colorType = 4 ∨ header.colorType = 6)
    (hWidth : header.width = bitmap.size.width)
    (hHeight : header.height = bitmap.size.height)
    (hInterlace : header.interlace = 0)
    (hPxColorType : PngPixel.colorType (α := px) = u8 header.colorType)
    (hBppLookup : pngBytesPerPixelForColorTypeAndBitDepth?
      header.colorType header.bitDepth = some (Pixel.bytesPerPixel (α := px)))
    (hMetaTransparency : metadata.transparency = none)
    (hChrmGrayInactive :
      ¬ (((metadata.pixelOnlyColorSpace.srgb = none ∧
            metadata.pixelOnlyColorSpace.chromaticities.isSome = true) ∧
          (header.colorType = 2 ∨ header.colorType = 6)) ∧
        (PngPixel.colorType (α := px) = u8 0 ∨ PngPixel.colorType (α := px) = u8 4)))
    (hParse : parsePngForDecode bytes hSize =
      some { header := header, idat := idat, metadata := metadata })
    (hIdatMin : 2 ≤ idat.size)
    (hInflated :
      zlibDecompressStored idat hIdatMin = some inflatedRaw ∨
      (zlibDecompressStored idat hIdatMin = none ∧
       zlibDecompress idat hIdatMin = some inflatedRaw))
    (hRawSize :
      inflatedRaw.size = bitmap.size.height *
        (bitmap.size.width * Pixel.bytesPerPixel (α := px) + 1))
    (hPixels :
      PngPixel.decodeRowsLoop (α := px) inflatedRaw bitmap.size.width
          bitmap.size.height (Pixel.bytesPerPixel (α := px))
          (bitmap.size.width * Pixel.bytesPerPixel (α := px))
          0 0 ByteArray.empty
          { data := Array.replicate
              (bitmap.size.width * bitmap.size.height *
                Pixel.bytesPerPixel (α := px)) 0 } =
        some preTransformPixels)
    (hTransform :
      applyPngColorSpaceTransform (PngMetadata.pixelOnlyColorSpace metadata)
        header.colorType (PngPixel.colorType (α := px))
        (PngPixel.bitDepth (α := px)) preTransformPixels = some bitmap.data) :
    Png.decodeBitmap bytes = some bitmap := by
  let ct := (PngPixel.colorType (α := px)).toNat
  let bd := (PngPixel.bitDepth (α := px)).toNat
  let bpp := Pixel.bytesPerPixel (α := px)
  -- Derive bit-depth facts from the disjunction.
  have hbd_in : bd = 8 ∨ bd = 16 := by
    show (PngPixel.bitDepth (α := px)).toNat = 8 ∨
         (PngPixel.bitDepth (α := px)).toNat = 16
    rcases hTargetBitDepth with h | h
    · left; rw [h]; decide
    · right; rw [h]; decide
  have hBdNot1' : ¬ bd = 1 := by rcases hbd_in with h | h <;> rw [h] <;> decide
  have hbdNoReject : pngBitDepthSupported bd = true := by
    rcases hbd_in with h | h <;> rw [h] <;> decide
  have hbitDepthEq :
      ((PngPixel.bitDepth (α := px)).toNat != bd) = false := by simp [bd]
  have hbitDepthEqHeader :
      (bd != (PngPixel.bitDepth (α := px)).toNat) = false := by simp [bd]
  have hnoDownsample :
      ¬((PngPixel.bitDepth (α := px)).toNat = 16 ∧
        PngPixel.bitDepth (α := px) = u8 8) := by
    rintro ⟨h16, h8⟩
    rcases hTargetBitDepth with h | h <;> rw [h] at h8
    · -- target = u8 8 ⇒ u8 8 = u8 8 ✓, but then bit depth = 8 ≠ 16
      rw [h] at h16; revert h16; decide
    · -- target = u8 16 ⇒ u8 16 = u8 8 contradicts
      revert h8; decide
  have hct'eq : ct = header.colorType := by
    show (PngPixel.colorType (α := px)).toNat = header.colorType
    rw [hPxColorType]
    rcases hColorType with h | h | h | h <;> rw [h] <;> decide
  have hct' : ct = 0 ∨ ct = 2 ∨ ct = 4 ∨ ct = 6 := by rw [hct'eq]; exact hColorType
  have hCt4Reject :
      header.colorType = 4 → ¬ PngPixel.colorType (α := px) = u8 4 →
        PngPixel.colorType (α := px) = u8 6 := by
    intro h4 hne
    have : PngPixel.colorType (α := px) = u8 4 := by rw [hPxColorType, h4]
    exact absurd this hne
  have hctbd' : pngColorTypeBitDepthSupported ct bd = true := by
    rw [hct'eq]
    rcases hbd_in with hb | hb <;> rw [hb] <;>
      rcases hColorType with h | h | h | h <;> rw [h] <;> decide
  have hpngBpp' : pngBytesPerPixelForColorTypeAndBitDepth? ct bd = some bpp := by
    rw [hct'eq, show bd = header.bitDepth from hBitDepthMatch.symm]
    exact hBppLookup
  have hCtCases :
      ¬ header.colorType = 0 → ¬ header.colorType = 2 →
        ¬ header.colorType = 4 → header.colorType = 6 := by
    intro h0 h2 h4
    rcases hColorType with hc | hc | hc | hc
    · exact absurd hc h0
    · exact absurd hc h2
    · exact absurd hc h4
    · exact hc
  have hctbdHdr_bd :
      pngColorTypeBitDepthSupported header.colorType bd = true := by
    rcases hbd_in with hb | hb <;> rw [hb] <;>
      rcases hColorType with h | h | h | h <;> rw [h] <;> decide
  have hctbdHdr_match :
      pngColorTypeBitDepthSupported header.colorType
        (PngPixel.bitDepth (α := px)).toNat = true := by
    show pngColorTypeBitDepthSupported header.colorType bd = true
    exact hctbdHdr_bd
  have hbdMatchEq :
      (PngPixel.bitDepth (α := px)).toNat = (PngPixel.bitDepth (α := px)).toNat := rfl
  have hrowsEq :
      ((PngPixel.decodeRowsLoop (α := px) inflatedRaw bitmap.size.width
            bitmap.size.height bpp (bitmap.size.width * bpp) 0 0 ByteArray.empty
            { data := Array.replicate
                (bitmap.size.width * bitmap.size.height * Pixel.bytesPerPixel (α := px))
                0 }).bind
        fun decodedPixels ↦
          (applyPngColorSpaceTransform
              (PngMetadata.pixelOnlyColorSpace metadata)
              header.colorType
              (PngPixel.colorType (α := px))
              (PngPixel.bitDepth (α := px)) decodedPixels).bind
            fun pixels ↦
              if h : pixels.size = bitmap.size.width * bitmap.size.height *
                  Pixel.bytesPerPixel (α := px) then
                some { size := { width := bitmap.size.width,
                                 height := bitmap.size.height },
                       data := pixels, valid := h }
              else none) =
      some bitmap := by
    rw [hPixels, Option.bind_some]
    rw [hTransform, Option.bind_some]
    have hvalid :
        bitmap.data.size = bitmap.size.width * bitmap.size.height * bpp := by
      simpa [bpp] using bitmap.valid
    simp [hvalid, bpp]
  have hBppChain :
      ((pngBytesPerPixelForColorTypeAndBitDepth? header.colorType
            (PngPixel.bitDepth (α := px)).toNat).bind
        fun bpp ↦
          if inflatedRaw.size = bitmap.size.height * (bitmap.size.width * bpp + 1) then
            (PngPixel.decodeRowsLoop (α := px) inflatedRaw bitmap.size.width
                  bitmap.size.height bpp (bitmap.size.width * bpp) 0 0 ByteArray.empty
                  { data := Array.replicate
                      (bitmap.size.width * bitmap.size.height *
                        Pixel.bytesPerPixel (α := px)) 0 }).bind
              fun y ↦
                (applyPngColorSpaceTransform
                    (PngMetadata.pixelOnlyColorSpace metadata)
                    header.colorType (PngPixel.colorType (α := px))
                    (PngPixel.bitDepth (α := px)) y).bind
                  fun pixels ↦
                    if h : pixels.size = bitmap.size.width * bitmap.size.height *
                        Pixel.bytesPerPixel (α := px) then
                      some { size := { width := bitmap.size.width,
                                       height := bitmap.size.height },
                             data := pixels, valid := h }
                    else none
          else none) = some bitmap := by
    have hBpp_match : pngBytesPerPixelForColorTypeAndBitDepth?
        header.colorType (PngPixel.bitDepth (α := px)).toNat =
          some (Pixel.bytesPerPixel (α := px)) := by
      rw [show (PngPixel.bitDepth (α := px)).toNat = header.bitDepth from hBitDepthMatch.symm]
      exact hBppLookup
    rw [hBpp_match]
    simp only [Option.bind_some]
    rw [if_pos hRawSize]
    exact hrowsEq
  unfold Png.decodeBitmap
  rcases hInflated with hStored | ⟨hStoredNone, hZlib⟩
  · simpa [hSize, hParse, hStored,
      ct, bd, hbdNoReject, hbitDepthEq, hbitDepthEqHeader, hnoDownsample, hpngBpp',
      hctbd', hBdNot1', normalizeRawByInterlace?,
      hIdatMin, hInterlace, hWidth, hHeight, hBitDepthMatch,
      hChrmGrayInactive] using
      (And.intro hMetaTransparency
        (And.intro hctbdHdr_match
          (And.intro hCtCases
            (And.intro hbdMatchEq
              (And.intro hCt4Reject hBppChain)))))
  · simpa [hSize, hParse, hStoredNone, hZlib,
      ct, bd, hbdNoReject, hbitDepthEq, hbitDepthEqHeader, hnoDownsample, hpngBpp',
      hctbd', hBdNot1', normalizeRawByInterlace?,
      hIdatMin, hInterlace, hWidth, hHeight, hBitDepthMatch,
      hChrmGrayInactive] using
      (And.intro hMetaTransparency
        (And.intro hctbdHdr_match
          (And.intro hCtCases
            (And.intro hbdMatchEq
              (And.intro hCt4Reject hBppChain)))))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 4096 in
/-- The Adam7 interlaced decode core (match-depth path). Accepts a
byte stream with `header.interlace = 1` and `bitDepth ∈ {8, 16}`
matching the target pixel type. The witness chain mirrors the
match-depth core, but `inflatedRaw` is the *interlaced* byte stream
and the new `flatRaw` witness is the result of running
`decodeAdam7ToFlatRaw?` to produce the row-major sample raw consumed
by the standard per-pixel decode loop. -/
theorem decodeBitmap_correct_of_witnesses_adam7
    {px : Type u} [Pixel px] [PngPixel px]
    {bitmap : Bitmap px}
    {header : PngHeader} {idat : ByteArray} {metadata : PngMetadata}
    {inflatedRaw flatRaw preTransformPixels : ByteArray}
    {bytes : ByteArray} (hSize : 8 ≤ bytes.size)
    (hBitDepthMatch : header.bitDepth = (PngPixel.bitDepth (α := px)).toNat)
    (hTargetBitDepth : PngPixel.bitDepth (α := px) = u8 8 ∨
                       PngPixel.bitDepth (α := px) = u8 16)
    (hColorType : header.colorType = 0 ∨ header.colorType = 2 ∨
      header.colorType = 4 ∨ header.colorType = 6)
    (hWidth : header.width = bitmap.size.width)
    (hHeight : header.height = bitmap.size.height)
    (hInterlace1 : header.interlace = 1)
    (hPxColorType : PngPixel.colorType (α := px) = u8 header.colorType)
    (hBppLookup : pngBytesPerPixelForColorTypeAndBitDepth?
      header.colorType header.bitDepth = some (Pixel.bytesPerPixel (α := px)))
    (hMetaTransparency : metadata.transparency = none)
    (hChrmGrayInactive :
      ¬ (((metadata.pixelOnlyColorSpace.srgb = none ∧
            metadata.pixelOnlyColorSpace.chromaticities.isSome = true) ∧
          (header.colorType = 2 ∨ header.colorType = 6)) ∧
        (PngPixel.colorType (α := px) = u8 0 ∨ PngPixel.colorType (α := px) = u8 4)))
    (hParse : parsePngForDecode bytes hSize =
      some { header := header, idat := idat, metadata := metadata })
    (hIdatMin : 2 ≤ idat.size)
    (hInflated :
      zlibDecompressStored idat hIdatMin = some inflatedRaw ∨
      (zlibDecompressStored idat hIdatMin = none ∧
       zlibDecompress idat hIdatMin = some inflatedRaw))
    -- The Adam7 deinterlace witness: `decodeAdam7ToFlatRaw?` on the
    -- inflated byte stream produces the row-major sample-raw bytes.
    (hAdam7 :
      decodeAdam7ToFlatRaw? inflatedRaw bitmap.size.width bitmap.size.height
        (Pixel.bytesPerPixel (α := px)) = some flatRaw)
    (hRawSize :
      flatRaw.size = bitmap.size.height *
        (bitmap.size.width * Pixel.bytesPerPixel (α := px) + 1))
    (hPixels :
      PngPixel.decodeRowsLoop (α := px) flatRaw bitmap.size.width
          bitmap.size.height (Pixel.bytesPerPixel (α := px))
          (bitmap.size.width * Pixel.bytesPerPixel (α := px))
          0 0 ByteArray.empty
          { data := Array.replicate
              (bitmap.size.width * bitmap.size.height *
                Pixel.bytesPerPixel (α := px)) 0 } =
        some preTransformPixels)
    (hTransform :
      applyPngColorSpaceTransform (PngMetadata.pixelOnlyColorSpace metadata)
        header.colorType (PngPixel.colorType (α := px))
        (PngPixel.bitDepth (α := px)) preTransformPixels = some bitmap.data) :
    Png.decodeBitmap bytes = some bitmap := by
  let ct := (PngPixel.colorType (α := px)).toNat
  let bd := (PngPixel.bitDepth (α := px)).toNat
  let bpp := Pixel.bytesPerPixel (α := px)
  have hbd_in : bd = 8 ∨ bd = 16 := by
    show (PngPixel.bitDepth (α := px)).toNat = 8 ∨
         (PngPixel.bitDepth (α := px)).toNat = 16
    rcases hTargetBitDepth with h | h
    · left; rw [h]; decide
    · right; rw [h]; decide
  have hBdNot1' : ¬ bd = 1 := by rcases hbd_in with h | h <;> rw [h] <;> decide
  have hbdNoReject : pngBitDepthSupported bd = true := by
    rcases hbd_in with h | h <;> rw [h] <;> decide
  have hbitDepthEq :
      ((PngPixel.bitDepth (α := px)).toNat != bd) = false := by simp [bd]
  have hnoDownsample :
      ¬((PngPixel.bitDepth (α := px)).toNat = 16 ∧
        PngPixel.bitDepth (α := px) = u8 8) := by
    rintro ⟨h16, h8⟩
    rcases hTargetBitDepth with h | h <;> rw [h] at h8
    · rw [h] at h16; revert h16; decide
    · revert h8; decide
  have hct'eq : ct = header.colorType := by
    show (PngPixel.colorType (α := px)).toNat = header.colorType
    rw [hPxColorType]
    rcases hColorType with h | h | h | h <;> rw [h] <;> decide
  have hCt4Reject :
      header.colorType = 4 → ¬ PngPixel.colorType (α := px) = u8 4 →
        PngPixel.colorType (α := px) = u8 6 := by
    intro h4 hne
    have : PngPixel.colorType (α := px) = u8 4 := by rw [hPxColorType, h4]
    exact absurd this hne
  have hctbd' : pngColorTypeBitDepthSupported ct bd = true := by
    rw [hct'eq]
    rcases hbd_in with hb | hb <;> rw [hb] <;>
      rcases hColorType with h | h | h | h <;> rw [h] <;> decide
  have hpngBpp' : pngBytesPerPixelForColorTypeAndBitDepth? ct bd = some bpp := by
    rw [hct'eq, show bd = header.bitDepth from hBitDepthMatch.symm]
    exact hBppLookup
  have hCtCases :
      ¬ header.colorType = 0 → ¬ header.colorType = 2 →
        ¬ header.colorType = 4 → header.colorType = 6 := by
    intro h0 h2 h4
    rcases hColorType with hc | hc | hc | hc
    · exact absurd hc h0
    · exact absurd hc h2
    · exact absurd hc h4
    · exact hc
  have hctbdHdr_match :
      pngColorTypeBitDepthSupported header.colorType
        (PngPixel.bitDepth (α := px)).toNat = true := by
    rcases hbd_in with hb | hb <;>
      (show pngColorTypeBitDepthSupported header.colorType bd = true) <;>
      rw [hb] <;>
      rcases hColorType with h | h | h | h <;> rw [h] <;> decide
  have hbdMatchEq :
      (PngPixel.bitDepth (α := px)).toNat = (PngPixel.bitDepth (α := px)).toNat := rfl
  -- Adam7 normalization rewrites to `decodeAdam7ToFlatRaw?` result.
  have hRawNorm :
      normalizeRawByInterlace? inflatedRaw header bpp = some flatRaw := by
    unfold normalizeRawByInterlace?
    rw [hInterlace1]
    simp
    rw [hWidth, hHeight]
    exact hAdam7
  have hrowsEq :
      ((PngPixel.decodeRowsLoop (α := px) flatRaw bitmap.size.width
            bitmap.size.height bpp (bitmap.size.width * bpp) 0 0 ByteArray.empty
            { data := Array.replicate
                (bitmap.size.width * bitmap.size.height * Pixel.bytesPerPixel (α := px))
                0 }).bind
        fun decodedPixels ↦
          (applyPngColorSpaceTransform
              (PngMetadata.pixelOnlyColorSpace metadata)
              header.colorType
              (PngPixel.colorType (α := px))
              (PngPixel.bitDepth (α := px)) decodedPixels).bind
            fun pixels ↦
              if h : pixels.size = bitmap.size.width * bitmap.size.height *
                  Pixel.bytesPerPixel (α := px) then
                some { size := { width := bitmap.size.width,
                                 height := bitmap.size.height },
                       data := pixels, valid := h }
              else none) =
      some bitmap := by
    rw [hPixels, Option.bind_some]
    rw [hTransform, Option.bind_some]
    have hvalid :
        bitmap.data.size = bitmap.size.width * bitmap.size.height * bpp := by
      simpa [bpp] using bitmap.valid
    simp [hvalid, bpp]
  have hBppChain :
      ((pngBytesPerPixelForColorTypeAndBitDepth? header.colorType
            (PngPixel.bitDepth (α := px)).toNat).bind
        fun bpp ↦
          (normalizeRawByInterlace? inflatedRaw header bpp).bind fun rawN =>
            if rawN.size = bitmap.size.height * (bitmap.size.width * bpp + 1) then
              (PngPixel.decodeRowsLoop (α := px) rawN bitmap.size.width
                    bitmap.size.height bpp (bitmap.size.width * bpp) 0 0 ByteArray.empty
                    { data := Array.replicate
                        (bitmap.size.width * bitmap.size.height *
                          Pixel.bytesPerPixel (α := px)) 0 }).bind
                fun y ↦
                  (applyPngColorSpaceTransform
                      (PngMetadata.pixelOnlyColorSpace metadata)
                      header.colorType (PngPixel.colorType (α := px))
                      (PngPixel.bitDepth (α := px)) y).bind
                    fun pixels ↦
                      if h : pixels.size = bitmap.size.width * bitmap.size.height *
                          Pixel.bytesPerPixel (α := px) then
                        some { size := { width := bitmap.size.width,
                                         height := bitmap.size.height },
                               data := pixels, valid := h }
                      else none
            else none) = some bitmap := by
    have hBpp_match : pngBytesPerPixelForColorTypeAndBitDepth?
        header.colorType (PngPixel.bitDepth (α := px)).toNat =
          some (Pixel.bytesPerPixel (α := px)) := by
      rw [show (PngPixel.bitDepth (α := px)).toNat = header.bitDepth from hBitDepthMatch.symm]
      exact hBppLookup
    rw [hBpp_match]
    simp only [Option.bind_some]
    rw [hRawNorm, Option.bind_some]
    rw [if_pos hRawSize]
    exact hrowsEq
  unfold Png.decodeBitmap
  rcases hInflated with hStored | ⟨hStoredNone, hZlib⟩
  · simpa [hSize, hParse, hStored,
      ct, bd, hbdNoReject, hbitDepthEq, hnoDownsample, hpngBpp',
      hctbd', hBdNot1', hInterlace1,
      hIdatMin, hWidth, hHeight, hBitDepthMatch,
      hChrmGrayInactive] using
      (And.intro hMetaTransparency
        (And.intro hctbdHdr_match
          (And.intro hCtCases
            (And.intro hbdMatchEq
              (And.intro hCt4Reject hBppChain)))))
  · simpa [hSize, hParse, hStoredNone, hZlib,
      ct, bd, hbdNoReject, hbitDepthEq, hnoDownsample, hpngBpp',
      hctbd', hBdNot1', hInterlace1,
      hIdatMin, hWidth, hHeight, hBitDepthMatch,
      hChrmGrayInactive] using
      (And.intro hMetaTransparency
        (And.intro hctbdHdr_match
          (And.intro hCtCases
            (And.intro hbdMatchEq
              (And.intro hCt4Reject hBppChain)))))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 4096 in
/-- The 16→8 downsampling decode core: `decodeBitmap` accepts a byte
stream whose container declares `bitDepth = 16` while the target pixel
type is 8-bit. The runtime takes the `decodeRowsLoopDown16To8` branch
(no `chrmGrayActive`, no `source1`); the witness chain mirrors the
match-depth core except that `hPixels` is provided in terms of
`decodeRowsLoopDown16To8` and the IDAT raw size is computed against
the source 16-bit bpp. -/
theorem decodeBitmap_correct_of_witnesses_down16to8
    {px : Type u} [Pixel px] [PngPixel px]
    {bitmap : Bitmap px}
    {header : PngHeader} {idat : ByteArray} {metadata : PngMetadata}
    {inflatedRaw preTransformPixels : ByteArray}
    {bytes : ByteArray} (hSize : 8 ≤ bytes.size)
    (hSourceBitDepth : header.bitDepth = 16)
    (hTargetBitDepth : PngPixel.bitDepth (α := px) = u8 8)
    (hColorType : header.colorType = 0 ∨ header.colorType = 2 ∨
      header.colorType = 4 ∨ header.colorType = 6)
    (hWidth : header.width = bitmap.size.width)
    (hHeight : header.height = bitmap.size.height)
    (hInterlace : header.interlace = 0)
    (hPxColorType : PngPixel.colorType (α := px) = u8 header.colorType)
    {sourceBpp : Nat}
    (hBppLookup : pngBytesPerPixelForColorTypeAndBitDepth?
      header.colorType 16 = some sourceBpp)
    (hMetaTransparency : metadata.transparency = none)
    (hChrmGrayInactive :
      ¬ (((metadata.pixelOnlyColorSpace.srgb = none ∧
            metadata.pixelOnlyColorSpace.chromaticities.isSome = true) ∧
          (header.colorType = 2 ∨ header.colorType = 6)) ∧
        (PngPixel.colorType (α := px) = u8 0 ∨ PngPixel.colorType (α := px) = u8 4)))
    (hParse : parsePngForDecode bytes hSize =
      some { header := header, idat := idat, metadata := metadata })
    (hIdatMin : 2 ≤ idat.size)
    (hInflated :
      zlibDecompressStored idat hIdatMin = some inflatedRaw ∨
      (zlibDecompressStored idat hIdatMin = none ∧
       zlibDecompress idat hIdatMin = some inflatedRaw))
    (hRawSize :
      inflatedRaw.size = bitmap.size.height *
        (bitmap.size.width * sourceBpp + 1))
    (hPixels :
      decodeRowsLoopDown16To8 (PngPixel.colorType (α := px)) header.colorType
          inflatedRaw bitmap.size.width bitmap.size.height
          sourceBpp (bitmap.size.width * sourceBpp) 0 0 ByteArray.empty
          { data := Array.replicate
              (bitmap.size.width * bitmap.size.height *
                Pixel.bytesPerPixel (α := px)) 0 } =
        some preTransformPixels)
    (hTransform :
      applyPngColorSpaceTransform (PngMetadata.pixelOnlyColorSpace metadata)
        header.colorType (PngPixel.colorType (α := px))
        (PngPixel.bitDepth (α := px)) preTransformPixels = some bitmap.data) :
    Png.decodeBitmap bytes = some bitmap := by
  let ct := (PngPixel.colorType (α := px)).toNat
  -- Bit-depth flags
  have hBdNot1 : (header.bitDepth != 1) = true := by rw [hSourceBitDepth]; decide
  have hbdNoReject : pngBitDepthSupported header.bitDepth = true := by
    rw [hSourceBitDepth]; decide
  have hsource1 : (header.bitDepth == 1) = false := by rw [hSourceBitDepth]; decide
  have hsource16 : (header.bitDepth == 16) = true := by rw [hSourceBitDepth]; decide
  have htarget8 : (PngPixel.bitDepth (α := px) == u8 8) = true := by
    rw [hTargetBitDepth]; decide
  have hHeaderBdNeTarget :
      (header.bitDepth == (PngPixel.bitDepth (α := px)).toNat) = false := by
    rw [hSourceBitDepth, hTargetBitDepth]; decide
  have hctbdHdr :
      pngColorTypeBitDepthSupported header.colorType header.bitDepth = true := by
    rw [hSourceBitDepth]
    rcases hColorType with h | h | h | h <;> rw [h] <;> decide
  have hct'eq : ct = header.colorType := by
    show (PngPixel.colorType (α := px)).toNat = header.colorType
    rw [hPxColorType]
    rcases hColorType with h | h | h | h <;> rw [h] <;> decide
  have hCt4Reject :
      header.colorType = 4 → ¬ PngPixel.colorType (α := px) = u8 4 →
        PngPixel.colorType (α := px) = u8 6 := by
    intro h4 hne
    have : PngPixel.colorType (α := px) = u8 4 := by rw [hPxColorType, h4]
    exact absurd this hne
  have hCtCases :
      ¬ header.colorType = 0 → ¬ header.colorType = 2 →
        ¬ header.colorType = 4 → header.colorType = 6 := by
    intro h0 h2 h4
    rcases hColorType with hc | hc | hc | hc
    · exact absurd hc h0
    · exact absurd hc h2
    · exact absurd hc h4
    · exact hc
  -- Per-direction simpa goes through, building the same shape of nested
  -- `And.intro` chain as the match-depth core. The key flag differences
  -- (source16 = true, target8 = true, source1 = false, header.bitDepth ≠ target)
  -- are absorbed via the rewriting hypotheses below.
  have hbdEqHeader :
      (header.bitDepth != (PngPixel.bitDepth (α := px)).toNat) = true := by
    rw [hSourceBitDepth, hTargetBitDepth]; decide
  have hSourceBpp_pos : True := trivial
  have hctbdHdr_match :
      pngColorTypeBitDepthSupported header.colorType
        (PngPixel.bitDepth (α := px)).toNat = true := by
    rw [hTargetBitDepth]
    rcases hColorType with h | h | h | h <;> rw [h] <;> decide
  have hRowsChain :
      ((decodeRowsLoopDown16To8 (PngPixel.colorType (α := px)) header.colorType
            inflatedRaw bitmap.size.width bitmap.size.height
            sourceBpp (bitmap.size.width * sourceBpp) 0 0 ByteArray.empty
            { data := Array.replicate
                (bitmap.size.width * bitmap.size.height *
                  Pixel.bytesPerPixel (α := px)) 0 }).bind
        fun decodedPixels ↦
          (applyPngColorSpaceTransform
              (PngMetadata.pixelOnlyColorSpace metadata)
              header.colorType
              (PngPixel.colorType (α := px))
              (PngPixel.bitDepth (α := px)) decodedPixels).bind
            fun pixels ↦
              if h : pixels.size = bitmap.size.width * bitmap.size.height *
                  Pixel.bytesPerPixel (α := px) then
                some { size := { width := bitmap.size.width,
                                 height := bitmap.size.height },
                       data := pixels, valid := h }
              else none) = some bitmap := by
    rw [hPixels, Option.bind_some]
    rw [hTransform, Option.bind_some]
    have hvalid :
        bitmap.data.size = bitmap.size.width * bitmap.size.height *
          Pixel.bytesPerPixel (α := px) := by simpa using bitmap.valid
    simp [hvalid]
  have hBppChain :
      ((pngBytesPerPixelForColorTypeAndBitDepth? header.colorType header.bitDepth).bind
        fun bpp ↦
          if inflatedRaw.size = bitmap.size.height * (bitmap.size.width * bpp + 1) then
            (decodeRowsLoopDown16To8 (PngPixel.colorType (α := px)) header.colorType
                  inflatedRaw bitmap.size.width bitmap.size.height
                  bpp (bitmap.size.width * bpp) 0 0 ByteArray.empty
                  { data := Array.replicate
                      (bitmap.size.width * bitmap.size.height *
                        Pixel.bytesPerPixel (α := px)) 0 }).bind
              fun y ↦
                (applyPngColorSpaceTransform
                    (PngMetadata.pixelOnlyColorSpace metadata)
                    header.colorType (PngPixel.colorType (α := px))
                    (PngPixel.bitDepth (α := px)) y).bind
                  fun pixels ↦
                    if h : pixels.size = bitmap.size.width * bitmap.size.height *
                        Pixel.bytesPerPixel (α := px) then
                      some { size := { width := bitmap.size.width,
                                       height := bitmap.size.height },
                             data := pixels, valid := h }
                    else none
          else none) = some bitmap := by
    rw [hSourceBitDepth, hBppLookup]
    simp only [Option.bind_some]
    rw [if_pos hRawSize]
    exact hRowsChain
  unfold Png.decodeBitmap
  rcases hInflated with hStored | ⟨hStoredNone, hZlib⟩
  · simpa [hSize, hParse, hStored, hSourceBitDepth, hTargetBitDepth, hbdNoReject,
      hctbdHdr, hctbdHdr_match, normalizeRawByInterlace?,
      hIdatMin, hInterlace, hWidth, hHeight,
      hChrmGrayInactive, hMetaTransparency] using
      (And.intro hctbdHdr (And.intro hCtCases (And.intro hCt4Reject hBppChain)))
  · simpa [hSize, hParse, hStoredNone, hZlib, hSourceBitDepth, hTargetBitDepth, hbdNoReject,
      hctbdHdr, hctbdHdr_match, normalizeRawByInterlace?,
      hIdatMin, hInterlace, hWidth, hHeight,
      hChrmGrayInactive, hMetaTransparency] using
      (And.intro hctbdHdr (And.intro hCtCases (And.intro hCt4Reject hBppChain)))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 4096 in
/-- The 1-bit → 8-bit upsampling decode core. The container declares
1-bit grayscale; the target pixel type is 8-bit. The runtime unpacks
packed bits into an 8-bit sample raw, then runs the standard per-pixel
decode loop. Only color type 0 (grayscale) is supported at 1-bit. -/
theorem decodeBitmap_correct_of_witnesses_gray1_to8
    {px : Type u} [Pixel px] [PngPixel px]
    {bitmap : Bitmap px}
    {header : PngHeader} {idat : ByteArray} {metadata : PngMetadata}
    {inflatedRaw flat preTransformPixels : ByteArray}
    {bytes : ByteArray} (hSize : 8 ≤ bytes.size)
    (hSourceBitDepth : header.bitDepth = 1)
    (hTargetBitDepth : PngPixel.bitDepth (α := px) = u8 8)
    (hColorType0 : header.colorType = 0)
    (hWidth : header.width = bitmap.size.width)
    (hHeight : header.height = bitmap.size.height)
    (hInterlace : header.interlace = 0)
    (hPxColorType : PngPixel.colorType (α := px) = u8 0)
    (hMetaTransparency : metadata.transparency = none)
    (hParse : parsePngForDecode bytes hSize =
      some { header := header, idat := idat, metadata := metadata })
    (hIdatMin : 2 ≤ idat.size)
    (hInflated :
      zlibDecompressStored idat hIdatMin = some inflatedRaw ∨
      (zlibDecompressStored idat hIdatMin = none ∧
       zlibDecompress idat hIdatMin = some inflatedRaw))
    (hPackedSize :
      inflatedRaw.size =
        bitmap.size.height * (gray1RowBytes bitmap.size.width + 1))
    (hFlat :
      decodeRowsLoopGray1Packed inflatedRaw bitmap.size.width
        bitmap.size.height = some flat)
    (hPixels :
      PngPixel.decodeRowsLoop (α := px)
          (gray1FlatToSampleRaw flat bitmap.size.width bitmap.size.height 8)
          bitmap.size.width bitmap.size.height 1 bitmap.size.width
          0 0 ByteArray.empty
          { data := Array.replicate
              (bitmap.size.width * bitmap.size.height *
                Pixel.bytesPerPixel (α := px)) 0 } =
        some preTransformPixels)
    (hTransform :
      applyPngColorSpaceTransform (PngMetadata.pixelOnlyColorSpace metadata)
        header.colorType (PngPixel.colorType (α := px))
        (PngPixel.bitDepth (α := px)) preTransformPixels = some bitmap.data) :
    Png.decodeBitmap bytes = some bitmap := by
  have hbdNoReject : pngBitDepthSupported header.bitDepth = true := by
    rw [hSourceBitDepth]; decide
  have hctbdHdr :
      pngColorTypeBitDepthSupported header.colorType header.bitDepth = true := by
    rw [hSourceBitDepth, hColorType0]; decide
  have hctbdHdr_match :
      pngColorTypeBitDepthSupported header.colorType
        (PngPixel.bitDepth (α := px)).toNat = true := by
    rw [hColorType0, hTargetBitDepth]; decide
  have hCtCases :
      ¬ header.colorType = 0 → ¬ header.colorType = 2 →
        ¬ header.colorType = 4 → header.colorType = 6 := fun h0 _ _ => absurd hColorType0 h0
  have hCt4Reject :
      header.colorType = 4 → ¬ PngPixel.colorType (α := px) = u8 4 →
        PngPixel.colorType (α := px) = u8 6 := by
    intro h4 _; rw [hColorType0] at h4; exact absurd h4 (by decide)
  have hChrmGrayInactive :
      ¬ ((metadata.pixelOnlyColorSpace.srgb = none ∧
            metadata.pixelOnlyColorSpace.chromaticities.isSome = true) ∧
          (header.colorType = 2 ∨ header.colorType = 6)) := by
    intro ⟨_, hCt⟩
    rcases hCt with h | h
    · rw [hColorType0] at h; exact absurd h (by decide)
    · rw [hColorType0] at h; exact absurd h (by decide)
  have hRowsChain :
      ((PngPixel.decodeRowsLoop (α := px)
            (gray1FlatToSampleRaw flat bitmap.size.width bitmap.size.height 8)
            bitmap.size.width bitmap.size.height 1 bitmap.size.width
            0 0 ByteArray.empty
            { data := Array.replicate
                (bitmap.size.width * bitmap.size.height *
                  Pixel.bytesPerPixel (α := px)) 0 }).bind
        fun decodedPixels ↦
          (applyPngColorSpaceTransform
              (PngMetadata.pixelOnlyColorSpace metadata)
              header.colorType (PngPixel.colorType (α := px))
              (PngPixel.bitDepth (α := px)) decodedPixels).bind
            fun pixels ↦
              if h : pixels.size = bitmap.size.width * bitmap.size.height *
                  Pixel.bytesPerPixel (α := px) then
                some { size := { width := bitmap.size.width,
                                 height := bitmap.size.height },
                       data := pixels, valid := h }
              else none) = some bitmap := by
    rw [hPixels, Option.bind_some]
    rw [hTransform, Option.bind_some]
    have hvalid :
        bitmap.data.size = bitmap.size.width * bitmap.size.height *
          Pixel.bytesPerPixel (α := px) := by simpa using bitmap.valid
    simp [hvalid]
  have hGrayNorm :
      normalizeGray1RawByInterlace? inflatedRaw header = some inflatedRaw := by
    unfold normalizeGray1RawByInterlace?
    rw [hInterlace]; rfl
  have hTarget8Bool : (PngPixel.bitDepth (α := px) == u8 8) = true := by
    rw [hTargetBitDepth]; decide
  have hTarget16Bool : (PngPixel.bitDepth (α := px) == u8 16) = false := by
    rw [hTargetBitDepth]; decide
  have hu8_ne : ¬ (u8 8 : UInt8) = u8 16 := by decide
  unfold Png.decodeBitmap
  rcases hInflated with hStored | ⟨hStoredNone, hZlib⟩
  · simpa [hSize, hParse, hStored, hSourceBitDepth, hTargetBitDepth, hbdNoReject,
      hctbdHdr, hctbdHdr_match, normalizeRawByInterlace?,
      normalizeGray1RawByInterlace?, hIdatMin, hInterlace, hWidth, hHeight,
      hChrmGrayInactive, hMetaTransparency, hPxColorType, hPackedSize, hFlat,
      hu8_ne] using
      (And.intro hctbdHdr (And.intro hCtCases (And.intro hCt4Reject hRowsChain)))
  · simpa [hSize, hParse, hStoredNone, hZlib, hSourceBitDepth, hTargetBitDepth, hbdNoReject,
      hctbdHdr, hctbdHdr_match, normalizeRawByInterlace?,
      normalizeGray1RawByInterlace?, hIdatMin, hInterlace, hWidth, hHeight,
      hChrmGrayInactive, hMetaTransparency, hPxColorType, hPackedSize, hFlat,
      hu8_ne] using
      (And.intro hctbdHdr (And.intro hCtCases (And.intro hCt4Reject hRowsChain)))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 4096 in
/-- The 1-bit → 16-bit upsampling decode core. The container declares
1-bit grayscale; the target pixel type is 16-bit. The runtime unpacks
packed bits into a 16-bit sample raw (2 bytes/pixel), then runs the
standard per-pixel decode loop. -/
theorem decodeBitmap_correct_of_witnesses_gray1_to16
    {px : Type u} [Pixel px] [PngPixel px]
    {bitmap : Bitmap px}
    {header : PngHeader} {idat : ByteArray} {metadata : PngMetadata}
    {inflatedRaw flat preTransformPixels : ByteArray}
    {bytes : ByteArray} (hSize : 8 ≤ bytes.size)
    (hSourceBitDepth : header.bitDepth = 1)
    (hTargetBitDepth : PngPixel.bitDepth (α := px) = u8 16)
    (hColorType0 : header.colorType = 0)
    (hWidth : header.width = bitmap.size.width)
    (hHeight : header.height = bitmap.size.height)
    (hInterlace : header.interlace = 0)
    (hPxColorType : PngPixel.colorType (α := px) = u8 0)
    (hMetaTransparency : metadata.transparency = none)
    (hParse : parsePngForDecode bytes hSize =
      some { header := header, idat := idat, metadata := metadata })
    (hIdatMin : 2 ≤ idat.size)
    (hInflated :
      zlibDecompressStored idat hIdatMin = some inflatedRaw ∨
      (zlibDecompressStored idat hIdatMin = none ∧
       zlibDecompress idat hIdatMin = some inflatedRaw))
    (hPackedSize :
      inflatedRaw.size =
        bitmap.size.height * (gray1RowBytes bitmap.size.width + 1))
    (hFlat :
      decodeRowsLoopGray1Packed inflatedRaw bitmap.size.width
        bitmap.size.height = some flat)
    (hPixels :
      PngPixel.decodeRowsLoop (α := px)
          (gray1FlatToSampleRaw flat bitmap.size.width bitmap.size.height 16)
          bitmap.size.width bitmap.size.height 2 (bitmap.size.width * 2)
          0 0 ByteArray.empty
          { data := Array.replicate
              (bitmap.size.width * bitmap.size.height *
                Pixel.bytesPerPixel (α := px)) 0 } =
        some preTransformPixels)
    (hTransform :
      applyPngColorSpaceTransform (PngMetadata.pixelOnlyColorSpace metadata)
        header.colorType (PngPixel.colorType (α := px))
        (PngPixel.bitDepth (α := px)) preTransformPixels = some bitmap.data) :
    Png.decodeBitmap bytes = some bitmap := by
  have hbdNoReject : pngBitDepthSupported header.bitDepth = true := by
    rw [hSourceBitDepth]; decide
  have hctbdHdr :
      pngColorTypeBitDepthSupported header.colorType header.bitDepth = true := by
    rw [hSourceBitDepth, hColorType0]; decide
  have hctbdHdr_match :
      pngColorTypeBitDepthSupported header.colorType
        (PngPixel.bitDepth (α := px)).toNat = true := by
    rw [hColorType0, hTargetBitDepth]; decide
  have hCtCases :
      ¬ header.colorType = 0 → ¬ header.colorType = 2 →
        ¬ header.colorType = 4 → header.colorType = 6 := fun h0 _ _ => absurd hColorType0 h0
  have hCt4Reject :
      header.colorType = 4 → ¬ PngPixel.colorType (α := px) = u8 4 →
        PngPixel.colorType (α := px) = u8 6 := by
    intro h4 _; rw [hColorType0] at h4; exact absurd h4 (by decide)
  have hChrmGrayInactive :
      ¬ ((metadata.pixelOnlyColorSpace.srgb = none ∧
            metadata.pixelOnlyColorSpace.chromaticities.isSome = true) ∧
          (header.colorType = 2 ∨ header.colorType = 6)) := by
    intro ⟨_, hCt⟩
    rcases hCt with h | h
    · rw [hColorType0] at h; exact absurd h (by decide)
    · rw [hColorType0] at h; exact absurd h (by decide)
  have hRowsChain :
      ((PngPixel.decodeRowsLoop (α := px)
            (gray1FlatToSampleRaw flat bitmap.size.width bitmap.size.height 16)
            bitmap.size.width bitmap.size.height 2 (bitmap.size.width * 2)
            0 0 ByteArray.empty
            { data := Array.replicate
                (bitmap.size.width * bitmap.size.height *
                  Pixel.bytesPerPixel (α := px)) 0 }).bind
        fun decodedPixels ↦
          (applyPngColorSpaceTransform
              (PngMetadata.pixelOnlyColorSpace metadata)
              header.colorType (PngPixel.colorType (α := px))
              (PngPixel.bitDepth (α := px)) decodedPixels).bind
            fun pixels ↦
              if h : pixels.size = bitmap.size.width * bitmap.size.height *
                  Pixel.bytesPerPixel (α := px) then
                some { size := { width := bitmap.size.width,
                                 height := bitmap.size.height },
                       data := pixels, valid := h }
              else none) = some bitmap := by
    rw [hPixels, Option.bind_some]
    rw [hTransform, Option.bind_some]
    have hvalid :
        bitmap.data.size = bitmap.size.width * bitmap.size.height *
          Pixel.bytesPerPixel (α := px) := by simpa using bitmap.valid
    simp [hvalid]
  have hGrayNorm :
      normalizeGray1RawByInterlace? inflatedRaw header = some inflatedRaw := by
    unfold normalizeGray1RawByInterlace?
    rw [hInterlace]; rfl
  have hTarget16Bool : (PngPixel.bitDepth (α := px) == u8 16) = true := by
    rw [hTargetBitDepth]; decide
  unfold Png.decodeBitmap
  rcases hInflated with hStored | ⟨hStoredNone, hZlib⟩
  · simpa [hSize, hParse, hStored, hSourceBitDepth, hTargetBitDepth, hbdNoReject,
      hctbdHdr, hctbdHdr_match, normalizeRawByInterlace?,
      normalizeGray1RawByInterlace?, hIdatMin, hInterlace, hWidth, hHeight,
      hChrmGrayInactive, hMetaTransparency, hPxColorType, hPackedSize, hFlat,
      hTarget16Bool] using
      (And.intro hctbdHdr (And.intro hCtCases (And.intro hCt4Reject hRowsChain)))
  · simpa [hSize, hParse, hStoredNone, hZlib, hSourceBitDepth, hTargetBitDepth, hbdNoReject,
      hctbdHdr, hctbdHdr_match, normalizeRawByInterlace?,
      normalizeGray1RawByInterlace?, hIdatMin, hInterlace, hWidth, hHeight,
      hChrmGrayInactive, hMetaTransparency, hPxColorType, hPackedSize, hFlat,
      hTarget16Bool] using
      (And.intro hctbdHdr (And.intro hCtCases (And.intro hCt4Reject hRowsChain)))

/-- `parsePngForDecode` and `parsePngWithMetadata` agree. Both call
`parsePngSimpleWithMetadata` first and fall through to
`parsePngLoopFuelWithMetadata` on the slow path. -/
lemma parsePngForDecode_eq_parsePngWithMetadata
    (bytes : ByteArray) (hsize : 8 ≤ bytes.size) :
    Png.parsePngForDecode bytes hsize = Png.parsePngWithMetadata bytes hsize := by
  unfold Png.parsePngForDecode Png.parsePngWithMetadata
  rcases h : parsePngSimpleWithMetadata bytes hsize with _ | parsed
  · simp [h, Png.parsePngWithMetadata]
  · simp [h, Png.parsePngWithMetadata]

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 4096 in
/-- The tRNS forward-decode core for RGBA8 target: when the parsed
metadata has `transparency = some trns` and the user wants an RGBA
8-bit pixel type (e.g. `PixelRGBA8`), `decodeBitmapWithMetadata`
routes through `decodeRowsLoopRGBAWithTransparency`. Restricted to
source bit depth 8 (no down/up-sampling) and the metadata to only
carry the transparency (no chrm/srgb/gamma/bg). -/
theorem decodeBitmapWithMetadata_correct_of_witnesses_trnsRgba8
    {px : Type u} [Pixel px] [PngPixel px]
    {bitmap : Bitmap px}
    {header : PngHeader} {idat : ByteArray} {trns : PngTransparency}
    {inflatedRaw : ByteArray}
    {bytes : ByteArray} (hSize : 8 ≤ bytes.size)
    (hSourceBitDepth : header.bitDepth = 8)
    (hTargetBitDepth : PngPixel.bitDepth (α := px) = u8 8)
    (hSourceColorType : header.colorType = 0 ∨ header.colorType = 2 ∨
      header.colorType = 4 ∨ header.colorType = 6)
    (hTargetColorType : PngPixel.colorType (α := px) = u8 6)
    (hWidth : header.width = bitmap.size.width)
    (hHeight : header.height = bitmap.size.height)
    (hInterlace : header.interlace = 0)
    (hPxColorType : PngPixel.colorType (α := px) = u8 header.colorType)
    (hBppLookup : pngBytesPerPixelForColorTypeAndBitDepth?
      header.colorType header.bitDepth = some (Pixel.bytesPerPixel (α := px)))
    (hParse : parsePngWithMetadata bytes hSize =
      some { header := header, idat := idat,
             metadata := { PngMetadata.empty with transparency := some trns } })
    (hIdatMin : 2 ≤ idat.size)
    (hInflated :
      zlibDecompressStored idat hIdatMin = some inflatedRaw ∨
      (zlibDecompressStored idat hIdatMin = none ∧
       zlibDecompress idat hIdatMin = some inflatedRaw))
    (hRawSize :
      inflatedRaw.size = bitmap.size.height *
        (bitmap.size.width * Pixel.bytesPerPixel (α := px) + 1))
    (hPixels :
      decodeRowsLoopRGBAWithTransparency (some trns) inflatedRaw
          bitmap.size.width bitmap.size.height (Pixel.bytesPerPixel (α := px))
          (bitmap.size.width * Pixel.bytesPerPixel (α := px))
          0 0 ByteArray.empty
          { data := Array.replicate
              (bitmap.size.width * bitmap.size.height *
                Pixel.bytesPerPixel (α := px)) 0 } =
        some bitmap.data) :
    Png.decodeBitmapWithMetadata bytes =
      some { bitmap := bitmap
             metadata := { PngMetadata.empty with transparency := some trns } } := by
  -- Header-side facts.
  have hbdNoReject : pngBitDepthSupported header.bitDepth = true := by
    rw [hSourceBitDepth]; decide
  have hctbdHdr :
      pngColorTypeBitDepthSupported header.colorType header.bitDepth = true := by
    rw [hSourceBitDepth]
    rcases hSourceColorType with h | h | h | h <;> rw [h] <;> decide
  have hbitDepthEq :
      (header.bitDepth == (PngPixel.bitDepth (α := px)).toNat) = true := by
    rw [hSourceBitDepth, hTargetBitDepth]; rfl
  have hbitDepthCompatible :
      (header.bitDepth == (PngPixel.bitDepth (α := px)).toNat ||
        (header.bitDepth == 16 && PngPixel.bitDepth (α := px) == u8 8) ||
        (header.bitDepth == 1 &&
          (PngPixel.bitDepth (α := px) == u8 8 ||
            PngPixel.bitDepth (α := px) == u8 16))) = true := by
    simp [hbitDepthEq]
  have hCtCases :
      ¬ header.colorType = 0 → ¬ header.colorType = 2 →
        ¬ header.colorType = 4 → header.colorType = 6 := by
    intro h0 h2 h4
    rcases hSourceColorType with hc | hc | hc | hc
    · exact absurd hc h0
    · exact absurd hc h2
    · exact absurd hc h4
    · exact hc
  have hSourceNot1 : (header.bitDepth == 1) = false := by
    rw [hSourceBitDepth]; decide
  have hSourceNot16 : (header.bitDepth == 16) = false := by
    rw [hSourceBitDepth]; decide
  have hTargetIs8 : (PngPixel.bitDepth (α := px) == u8 8) = true := by
    rw [hTargetBitDepth]; decide
  have hTargetNot16 : (PngPixel.bitDepth (α := px) == u8 16) = false := by
    rw [hTargetBitDepth]; decide
  have hTargetIs6 : (PngPixel.colorType (α := px) == u8 6) = true := by
    rw [hTargetColorType]; decide
  have hTargetNot4 : (PngPixel.colorType (α := px) == u8 4) = false := by
    rw [hTargetColorType]; decide
  have hTargetNot0 : (PngPixel.colorType (α := px) == u8 0) = false := by
    rw [hTargetColorType]; decide
  -- chrmGrayActive is false: target colorType is u8 6, not u8 0 or u8 4.
  have hChrmGrayInactive :
      (PngMetadata.empty.srgb.isNone &&
        PngMetadata.empty.chromaticities.isSome &&
        (header.colorType == 2 || header.colorType == 6) &&
        (PngPixel.colorType (α := px) == u8 0 ||
          PngPixel.colorType (α := px) == u8 4)) = false := by
    simp [PngMetadata.empty, hTargetNot0, hTargetNot4]
  -- normalizeRawByInterlace? for interlace=0 is identity.
  have hRawNorm :
      normalizeRawByInterlace? inflatedRaw header
        (Pixel.bytesPerPixel (α := px)) = some inflatedRaw := by
    unfold normalizeRawByInterlace?
    rw [hInterlace]; rfl
  -- The color-space transform is identity (metadata has no chrm/srgb/gamma).
  have hTransform :
      applyPngColorSpaceTransform
        { PngMetadata.empty with transparency := some trns }
        header.colorType (PngPixel.colorType (α := px))
        (PngPixel.bitDepth (α := px)) bitmap.data = some bitmap.data := by
    unfold applyPngColorSpaceTransform
    rfl
  have hValid : bitmap.data.size =
      bitmap.size.width * bitmap.size.height *
        Pixel.bytesPerPixel (α := px) := by simpa using bitmap.valid
  have hbdMatchEq : header.bitDepth = (PngPixel.bitDepth (α := px)).toNat := by
    rw [hSourceBitDepth, hTargetBitDepth]; decide
  -- Build the inner row-decode chain explicitly.
  have hRowsChain :
      ((decodeRowsLoopRGBAWithTransparency (some trns) inflatedRaw
            bitmap.size.width bitmap.size.height (Pixel.bytesPerPixel (α := px))
            (bitmap.size.width * Pixel.bytesPerPixel (α := px))
            0 0 ByteArray.empty
            { data := Array.replicate
                (bitmap.size.width * bitmap.size.height *
                  Pixel.bytesPerPixel (α := px)) 0 }).bind fun y ↦
        (applyPngColorSpaceTransform
            { PngMetadata.empty with transparency := some trns }
            header.colorType (PngPixel.colorType (α := px))
            (PngPixel.bitDepth (α := px)) y).bind fun pixels ↦
          if h : pixels.size = bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px) then
            some ({ bitmap := { size := { width := bitmap.size.width,
                                            height := bitmap.size.height },
                                  data := pixels, valid := h },
                    metadata := { PngMetadata.empty with transparency := some trns } } : PngDecodeResult px)
          else none) =
      some ({ bitmap := bitmap
              metadata := { PngMetadata.empty with transparency := some trns } } : PngDecodeResult px) := by
    rw [hPixels, Option.bind_some]
    rw [hTransform, Option.bind_some]
    simp [hValid]
  have hPxIsU8_6 : u8 header.colorType = u8 6 := by
    rw [← hPxColorType, hTargetColorType]
  have hBppChain :
      ((pngBytesPerPixelForColorTypeAndBitDepth? header.colorType header.bitDepth).bind
        fun bpp ↦
          (normalizeRawByInterlace? inflatedRaw header bpp).bind fun raw ↦
            if raw.size = bitmap.size.height * (bitmap.size.width * bpp + 1) then
              if u8 header.colorType = u8 6 then
                (decodeRowsLoopRGBAWithTransparency (some trns) raw bitmap.size.width
                      bitmap.size.height bpp (bitmap.size.width * bpp) 0 0 ByteArray.empty
                      { data := Array.replicate
                          (bitmap.size.width * bitmap.size.height *
                            Pixel.bytesPerPixel (α := px)) 0 }).bind fun y ↦
                  (applyPngColorSpaceTransform
                      { PngMetadata.empty with transparency := some trns }
                      header.colorType (u8 header.colorType)
                      (u8 8) y).bind fun pixels ↦
                    if h : pixels.size = bitmap.size.width * bitmap.size.height *
                        Pixel.bytesPerPixel (α := px) then
                      some ({ bitmap := { size := { width := bitmap.size.width,
                                                     height := bitmap.size.height },
                                           data := pixels, valid := h },
                              metadata := { PngMetadata.empty with transparency := some trns } } : PngDecodeResult px)
                    else none
              else none
            else none) =
        some ({ bitmap := bitmap
                metadata := { PngMetadata.empty with transparency := some trns } } : PngDecodeResult px) := by
    rw [hBppLookup]
    simp only [Option.bind_some]
    rw [hRawNorm, Option.bind_some]
    rw [if_pos hRawSize, if_pos hPxIsU8_6]
    -- Rewrite to align with hRowsChain (which uses PngPixel.colorType px and bitDepth px).
    rw [show (u8 header.colorType) = PngPixel.colorType (α := px) from hPxColorType.symm]
    rw [show (u8 8 : UInt8) = PngPixel.bitDepth (α := px) from hTargetBitDepth.symm]
    exact hRowsChain
  -- Drive the body.
  unfold Png.decodeBitmapWithMetadata Png.decodeParsedBitmapWithMetadata
  simp only [hSize, dite_true, hParse, Option.bind_eq_bind, Option.bind_some]
  rcases hInflated with hStored | ⟨hStoredNone, hZlib⟩
  · simpa [hctbdHdr, hSourceBitDepth, hTargetBitDepth, hbitDepthCompatible,
      hSourceNot1, hSourceNot16, hTargetIs8, hTargetNot16, hTargetIs6,
      hTargetNot0, hTargetNot4, hChrmGrayInactive,
      hWidth, hHeight, hInterlace, hIdatMin, hStored, PngMetadata.empty,
      hPxColorType] using
      (And.intro hctbdHdr (And.intro hCtCases (And.intro hbdMatchEq hBppChain)))
  · simpa [hctbdHdr, hSourceBitDepth, hTargetBitDepth, hbitDepthCompatible,
      hSourceNot1, hSourceNot16, hTargetIs8, hTargetNot16, hTargetIs6,
      hTargetNot0, hTargetNot4, hChrmGrayInactive,
      hWidth, hHeight, hInterlace, hIdatMin, hStoredNone, hZlib,
      PngMetadata.empty, hPxColorType] using
      (And.intro hctbdHdr (And.intro hCtCases (And.intro hbdMatchEq hBppChain)))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 4096 in
/-- The tRNS forward-decode core for RGBA16 target: source bitDepth = 16,
target = 16-bit RGBA (e.g. `PixelRGBA16`). Routes through
`decodeRowsLoopRGBA16WithTransparency`. -/
theorem decodeBitmapWithMetadata_correct_of_witnesses_trnsRgba16
    {px : Type u} [Pixel px] [PngPixel px]
    {bitmap : Bitmap px}
    {header : PngHeader} {idat : ByteArray} {trns : PngTransparency}
    {inflatedRaw : ByteArray}
    {bytes : ByteArray} (hSize : 8 ≤ bytes.size)
    (hSourceBitDepth : header.bitDepth = 16)
    (hTargetBitDepth : PngPixel.bitDepth (α := px) = u8 16)
    (hSourceColorType : header.colorType = 0 ∨ header.colorType = 2 ∨
      header.colorType = 4 ∨ header.colorType = 6)
    (hTargetColorType : PngPixel.colorType (α := px) = u8 6)
    (hWidth : header.width = bitmap.size.width)
    (hHeight : header.height = bitmap.size.height)
    (hInterlace : header.interlace = 0)
    (hPxColorType : PngPixel.colorType (α := px) = u8 header.colorType)
    (hBppLookup : pngBytesPerPixelForColorTypeAndBitDepth?
      header.colorType header.bitDepth = some (Pixel.bytesPerPixel (α := px)))
    (hParse : parsePngWithMetadata bytes hSize =
      some { header := header, idat := idat,
             metadata := { PngMetadata.empty with transparency := some trns } })
    (hIdatMin : 2 ≤ idat.size)
    (hInflated :
      zlibDecompressStored idat hIdatMin = some inflatedRaw ∨
      (zlibDecompressStored idat hIdatMin = none ∧
       zlibDecompress idat hIdatMin = some inflatedRaw))
    (hRawSize :
      inflatedRaw.size = bitmap.size.height *
        (bitmap.size.width * Pixel.bytesPerPixel (α := px) + 1))
    (hPixels :
      decodeRowsLoopRGBA16WithTransparency (some trns) header.colorType
          inflatedRaw bitmap.size.width bitmap.size.height
          (Pixel.bytesPerPixel (α := px))
          (bitmap.size.width * Pixel.bytesPerPixel (α := px))
          0 0 ByteArray.empty
          { data := Array.replicate
              (bitmap.size.width * bitmap.size.height *
                Pixel.bytesPerPixel (α := px)) 0 } =
        some bitmap.data) :
    Png.decodeBitmapWithMetadata bytes =
      some { bitmap := bitmap
             metadata := { PngMetadata.empty with transparency := some trns } } := by
  have hbdNoReject : pngBitDepthSupported header.bitDepth = true := by
    rw [hSourceBitDepth]; decide
  have hctbdHdr :
      pngColorTypeBitDepthSupported header.colorType header.bitDepth = true := by
    rw [hSourceBitDepth]
    rcases hSourceColorType with h | h | h | h <;> rw [h] <;> decide
  have hbitDepthEq :
      (header.bitDepth == (PngPixel.bitDepth (α := px)).toNat) = true := by
    rw [hSourceBitDepth, hTargetBitDepth]; rfl
  have hbitDepthCompatible :
      (header.bitDepth == (PngPixel.bitDepth (α := px)).toNat ||
        (header.bitDepth == 16 && PngPixel.bitDepth (α := px) == u8 8) ||
        (header.bitDepth == 1 &&
          (PngPixel.bitDepth (α := px) == u8 8 ||
            PngPixel.bitDepth (α := px) == u8 16))) = true := by
    simp [hbitDepthEq]
  have hCtCases :
      ¬ header.colorType = 0 → ¬ header.colorType = 2 →
        ¬ header.colorType = 4 → header.colorType = 6 := by
    intro h0 h2 h4
    rcases hSourceColorType with hc | hc | hc | hc
    · exact absurd hc h0
    · exact absurd hc h2
    · exact absurd hc h4
    · exact hc
  have hSourceNot1 : (header.bitDepth == 1) = false := by
    rw [hSourceBitDepth]; decide
  have hSourceIs16 : (header.bitDepth == 16) = true := by
    rw [hSourceBitDepth]; decide
  have hTargetNot8 : (PngPixel.bitDepth (α := px) == u8 8) = false := by
    rw [hTargetBitDepth]; decide
  have hTargetIs16 : (PngPixel.bitDepth (α := px) == u8 16) = true := by
    rw [hTargetBitDepth]; decide
  have hTargetIs6 : (PngPixel.colorType (α := px) == u8 6) = true := by
    rw [hTargetColorType]; decide
  have hTargetNot4 : (PngPixel.colorType (α := px) == u8 4) = false := by
    rw [hTargetColorType]; decide
  have hTargetNot0 : (PngPixel.colorType (α := px) == u8 0) = false := by
    rw [hTargetColorType]; decide
  have hChrmGrayInactive :
      (PngMetadata.empty.srgb.isNone &&
        PngMetadata.empty.chromaticities.isSome &&
        (header.colorType == 2 || header.colorType == 6) &&
        (PngPixel.colorType (α := px) == u8 0 ||
          PngPixel.colorType (α := px) == u8 4)) = false := by
    simp [PngMetadata.empty, hTargetNot0, hTargetNot4]
  have hRawNorm :
      normalizeRawByInterlace? inflatedRaw header
        (Pixel.bytesPerPixel (α := px)) = some inflatedRaw := by
    unfold normalizeRawByInterlace?
    rw [hInterlace]; rfl
  have hTransform :
      applyPngColorSpaceTransform
        { PngMetadata.empty with transparency := some trns }
        header.colorType (PngPixel.colorType (α := px))
        (PngPixel.bitDepth (α := px)) bitmap.data = some bitmap.data := by
    unfold applyPngColorSpaceTransform
    rfl
  have hValid : bitmap.data.size =
      bitmap.size.width * bitmap.size.height *
        Pixel.bytesPerPixel (α := px) := by simpa using bitmap.valid
  have hbdMatchEq : header.bitDepth = (PngPixel.bitDepth (α := px)).toNat := by
    rw [hSourceBitDepth, hTargetBitDepth]; decide
  have hRowsChain :
      ((decodeRowsLoopRGBA16WithTransparency (some trns) header.colorType
            inflatedRaw bitmap.size.width bitmap.size.height
            (Pixel.bytesPerPixel (α := px))
            (bitmap.size.width * Pixel.bytesPerPixel (α := px))
            0 0 ByteArray.empty
            { data := Array.replicate
                (bitmap.size.width * bitmap.size.height *
                  Pixel.bytesPerPixel (α := px)) 0 }).bind fun y ↦
        (applyPngColorSpaceTransform
            { PngMetadata.empty with transparency := some trns }
            header.colorType (PngPixel.colorType (α := px))
            (PngPixel.bitDepth (α := px)) y).bind fun pixels ↦
          if h : pixels.size = bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px) then
            some ({ bitmap := { size := { width := bitmap.size.width,
                                            height := bitmap.size.height },
                                  data := pixels, valid := h },
                    metadata := { PngMetadata.empty with transparency := some trns } } : PngDecodeResult px)
          else none) =
      some ({ bitmap := bitmap
              metadata := { PngMetadata.empty with transparency := some trns } } : PngDecodeResult px) := by
    rw [hPixels, Option.bind_some]
    rw [hTransform, Option.bind_some]
    simp [hValid]
  have hPxIsU8_6 : u8 header.colorType = u8 6 := by
    rw [← hPxColorType, hTargetColorType]
  have hU16NeU8 : ¬ (u8 16 : UInt8) = u8 8 := by decide
  have hbdMatchImpl : ¬ 16 = (u8 16).toNat → u8 16 = u8 8 := by
    intro h; exact absurd (by decide : (16 : Nat) = (u8 16).toNat) h
  have hBppChain :
      ((pngBytesPerPixelForColorTypeAndBitDepth? header.colorType header.bitDepth).bind
        fun bpp ↦
          (normalizeRawByInterlace? inflatedRaw header bpp).bind fun raw ↦
            if raw.size = bitmap.size.height * (bitmap.size.width * bpp + 1) then
              if u8 header.colorType = u8 6 then
                (if u8 16 = u8 8 then
                  decodeRowsLoopDown16ToRGBA8WithTransparency (some trns) header.colorType
                    raw bitmap.size.width bitmap.size.height bpp
                    (bitmap.size.width * bpp) 0 0 ByteArray.empty
                    { data := Array.replicate
                        (bitmap.size.width * bitmap.size.height *
                          Pixel.bytesPerPixel (α := px)) 0 }
                else
                  decodeRowsLoopRGBA16WithTransparency (some trns) header.colorType
                    raw bitmap.size.width bitmap.size.height bpp
                    (bitmap.size.width * bpp) 0 0 ByteArray.empty
                    { data := Array.replicate
                        (bitmap.size.width * bitmap.size.height *
                          Pixel.bytesPerPixel (α := px)) 0 }).bind fun y ↦
                  (applyPngColorSpaceTransform
                      { PngMetadata.empty with transparency := some trns }
                      header.colorType (u8 header.colorType)
                      (u8 16) y).bind fun pixels ↦
                    if h : pixels.size = bitmap.size.width * bitmap.size.height *
                        Pixel.bytesPerPixel (α := px) then
                      some ({ bitmap := { size := { width := bitmap.size.width,
                                                     height := bitmap.size.height },
                                           data := pixels, valid := h },
                              metadata := { PngMetadata.empty with transparency := some trns } } : PngDecodeResult px)
                    else none
              else none
            else none) =
        some ({ bitmap := bitmap
                metadata := { PngMetadata.empty with transparency := some trns } } : PngDecodeResult px) := by
    rw [hBppLookup]
    simp only [Option.bind_some]
    rw [hRawNorm, Option.bind_some]
    rw [if_pos hRawSize, if_pos hPxIsU8_6, if_neg hU16NeU8]
    rw [show (u8 header.colorType) = PngPixel.colorType (α := px) from hPxColorType.symm]
    rw [show (u8 16 : UInt8) = PngPixel.bitDepth (α := px) from hTargetBitDepth.symm]
    exact hRowsChain
  unfold Png.decodeBitmapWithMetadata Png.decodeParsedBitmapWithMetadata
  simp only [hSize, dite_true, hParse, Option.bind_eq_bind, Option.bind_some]
  rcases hInflated with hStored | ⟨hStoredNone, hZlib⟩
  · simpa [hctbdHdr, hSourceBitDepth, hTargetBitDepth, hbitDepthCompatible,
      hSourceNot1, hSourceIs16, hTargetNot8, hTargetIs16, hTargetIs6,
      hTargetNot0, hTargetNot4, hChrmGrayInactive,
      hWidth, hHeight, hInterlace, hIdatMin, hStored, PngMetadata.empty,
      hPxColorType] using
      (And.intro hctbdHdr (And.intro hCtCases (And.intro hbdMatchImpl hBppChain)))
  · simpa [hctbdHdr, hSourceBitDepth, hTargetBitDepth, hbitDepthCompatible,
      hSourceNot1, hSourceIs16, hTargetNot8, hTargetIs16, hTargetIs6,
      hTargetNot0, hTargetNot4, hChrmGrayInactive,
      hWidth, hHeight, hInterlace, hIdatMin, hStoredNone, hZlib,
      PngMetadata.empty, hPxColorType] using
      (And.intro hctbdHdr (And.intro hCtCases (And.intro hbdMatchImpl hBppChain)))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 4096 in
/-- The tRNS forward-decode core for 16→8 RGBA: source bitDepth = 16,
target = 8-bit RGBA. Routes through `decodeRowsLoopDown16ToRGBA8WithTransparency`. -/
theorem decodeBitmapWithMetadata_correct_of_witnesses_trnsRgba16To8
    {px : Type u} [Pixel px] [PngPixel px]
    {bitmap : Bitmap px}
    {header : PngHeader} {idat : ByteArray} {trns : PngTransparency}
    {inflatedRaw : ByteArray}
    {bytes : ByteArray} (hSize : 8 ≤ bytes.size)
    (hSourceBitDepth : header.bitDepth = 16)
    (hTargetBitDepth : PngPixel.bitDepth (α := px) = u8 8)
    (hSourceColorType : header.colorType = 0 ∨ header.colorType = 2 ∨
      header.colorType = 4 ∨ header.colorType = 6)
    (hTargetColorType : PngPixel.colorType (α := px) = u8 6)
    (hWidth : header.width = bitmap.size.width)
    (hHeight : header.height = bitmap.size.height)
    (hInterlace : header.interlace = 0)
    (hPxColorType : PngPixel.colorType (α := px) = u8 header.colorType)
    {sourceBpp : Nat}
    (hBppLookup : pngBytesPerPixelForColorTypeAndBitDepth?
      header.colorType 16 = some sourceBpp)
    (hParse : parsePngWithMetadata bytes hSize =
      some { header := header, idat := idat,
             metadata := { PngMetadata.empty with transparency := some trns } })
    (hIdatMin : 2 ≤ idat.size)
    (hInflated :
      zlibDecompressStored idat hIdatMin = some inflatedRaw ∨
      (zlibDecompressStored idat hIdatMin = none ∧
       zlibDecompress idat hIdatMin = some inflatedRaw))
    (hRawSize :
      inflatedRaw.size = bitmap.size.height *
        (bitmap.size.width * sourceBpp + 1))
    (hPixels :
      decodeRowsLoopDown16ToRGBA8WithTransparency (some trns) header.colorType
          inflatedRaw bitmap.size.width bitmap.size.height
          sourceBpp (bitmap.size.width * sourceBpp)
          0 0 ByteArray.empty
          { data := Array.replicate
              (bitmap.size.width * bitmap.size.height *
                Pixel.bytesPerPixel (α := px)) 0 } =
        some bitmap.data) :
    Png.decodeBitmapWithMetadata bytes =
      some { bitmap := bitmap
             metadata := { PngMetadata.empty with transparency := some trns } } := by
  have hbdNoReject : pngBitDepthSupported header.bitDepth = true := by
    rw [hSourceBitDepth]; decide
  have hctbdHdr :
      pngColorTypeBitDepthSupported header.colorType header.bitDepth = true := by
    rw [hSourceBitDepth]
    rcases hSourceColorType with h | h | h | h <;> rw [h] <;> decide
  have hbitDepthCompatible :
      (header.bitDepth == (PngPixel.bitDepth (α := px)).toNat ||
        (header.bitDepth == 16 && PngPixel.bitDepth (α := px) == u8 8) ||
        (header.bitDepth == 1 &&
          (PngPixel.bitDepth (α := px) == u8 8 ||
            PngPixel.bitDepth (α := px) == u8 16))) = true := by
    rw [hSourceBitDepth, hTargetBitDepth]; decide
  have hCtCases :
      ¬ header.colorType = 0 → ¬ header.colorType = 2 →
        ¬ header.colorType = 4 → header.colorType = 6 := by
    intro h0 h2 h4
    rcases hSourceColorType with hc | hc | hc | hc
    · exact absurd hc h0
    · exact absurd hc h2
    · exact absurd hc h4
    · exact hc
  have hSourceNot1 : (header.bitDepth == 1) = false := by
    rw [hSourceBitDepth]; decide
  have hSourceIs16 : (header.bitDepth == 16) = true := by
    rw [hSourceBitDepth]; decide
  have hTargetIs8 : (PngPixel.bitDepth (α := px) == u8 8) = true := by
    rw [hTargetBitDepth]; decide
  have hTargetNot16 : (PngPixel.bitDepth (α := px) == u8 16) = false := by
    rw [hTargetBitDepth]; decide
  have hTargetIs6 : (PngPixel.colorType (α := px) == u8 6) = true := by
    rw [hTargetColorType]; decide
  have hTargetNot4 : (PngPixel.colorType (α := px) == u8 4) = false := by
    rw [hTargetColorType]; decide
  have hTargetNot0 : (PngPixel.colorType (α := px) == u8 0) = false := by
    rw [hTargetColorType]; decide
  have hChrmGrayInactive :
      (PngMetadata.empty.srgb.isNone &&
        PngMetadata.empty.chromaticities.isSome &&
        (header.colorType == 2 || header.colorType == 6) &&
        (PngPixel.colorType (α := px) == u8 0 ||
          PngPixel.colorType (α := px) == u8 4)) = false := by
    simp [PngMetadata.empty, hTargetNot0, hTargetNot4]
  have hRawNorm :
      normalizeRawByInterlace? inflatedRaw header sourceBpp = some inflatedRaw := by
    unfold normalizeRawByInterlace?
    rw [hInterlace]; rfl
  have hTransform :
      applyPngColorSpaceTransform
        { PngMetadata.empty with transparency := some trns }
        header.colorType (PngPixel.colorType (α := px))
        (PngPixel.bitDepth (α := px)) bitmap.data = some bitmap.data := by
    unfold applyPngColorSpaceTransform
    rfl
  have hValid : bitmap.data.size =
      bitmap.size.width * bitmap.size.height *
        Pixel.bytesPerPixel (α := px) := by simpa using bitmap.valid
  have hRowsChain :
      ((decodeRowsLoopDown16ToRGBA8WithTransparency (some trns) header.colorType
            inflatedRaw bitmap.size.width bitmap.size.height
            sourceBpp (bitmap.size.width * sourceBpp)
            0 0 ByteArray.empty
            { data := Array.replicate
                (bitmap.size.width * bitmap.size.height *
                  Pixel.bytesPerPixel (α := px)) 0 }).bind fun y ↦
        (applyPngColorSpaceTransform
            { PngMetadata.empty with transparency := some trns }
            header.colorType (PngPixel.colorType (α := px))
            (PngPixel.bitDepth (α := px)) y).bind fun pixels ↦
          if h : pixels.size = bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px) then
            some ({ bitmap := { size := { width := bitmap.size.width,
                                            height := bitmap.size.height },
                                  data := pixels, valid := h },
                    metadata := { PngMetadata.empty with transparency := some trns } } : PngDecodeResult px)
          else none) =
      some ({ bitmap := bitmap
              metadata := { PngMetadata.empty with transparency := some trns } } : PngDecodeResult px) := by
    rw [hPixels, Option.bind_some]
    rw [hTransform, Option.bind_some]
    simp [hValid]
  have hPxIsU8_6 : u8 header.colorType = u8 6 := by
    rw [← hPxColorType, hTargetColorType]
  have hU8Eq : (u8 8 : UInt8) = u8 8 := rfl
  have hbdMatchImpl : ¬ 16 = (u8 8).toNat → u8 8 = u8 8 := fun _ => rfl
  have hBppChain :
      ((pngBytesPerPixelForColorTypeAndBitDepth? header.colorType header.bitDepth).bind
        fun bpp ↦
          (normalizeRawByInterlace? inflatedRaw header bpp).bind fun raw ↦
            if raw.size = bitmap.size.height * (bitmap.size.width * bpp + 1) then
              if u8 header.colorType = u8 6 then
                (if u8 8 = u8 8 then
                  decodeRowsLoopDown16ToRGBA8WithTransparency (some trns) header.colorType
                    raw bitmap.size.width bitmap.size.height bpp
                    (bitmap.size.width * bpp) 0 0 ByteArray.empty
                    { data := Array.replicate
                        (bitmap.size.width * bitmap.size.height *
                          Pixel.bytesPerPixel (α := px)) 0 }
                else
                  decodeRowsLoopRGBA16WithTransparency (some trns) header.colorType
                    raw bitmap.size.width bitmap.size.height bpp
                    (bitmap.size.width * bpp) 0 0 ByteArray.empty
                    { data := Array.replicate
                        (bitmap.size.width * bitmap.size.height *
                          Pixel.bytesPerPixel (α := px)) 0 }).bind fun y ↦
                  (applyPngColorSpaceTransform
                      { PngMetadata.empty with transparency := some trns }
                      header.colorType (u8 header.colorType)
                      (u8 8) y).bind fun pixels ↦
                    if h : pixels.size = bitmap.size.width * bitmap.size.height *
                        Pixel.bytesPerPixel (α := px) then
                      some ({ bitmap := { size := { width := bitmap.size.width,
                                                     height := bitmap.size.height },
                                           data := pixels, valid := h },
                              metadata := { PngMetadata.empty with transparency := some trns } } : PngDecodeResult px)
                    else none
              else none
            else none) =
        some ({ bitmap := bitmap
                metadata := { PngMetadata.empty with transparency := some trns } } : PngDecodeResult px) := by
    rw [hSourceBitDepth, hBppLookup]
    simp only [Option.bind_some]
    rw [hRawNorm, Option.bind_some]
    rw [if_pos hRawSize, if_pos hPxIsU8_6]
    simp only [if_true]
    rw [show (u8 header.colorType) = PngPixel.colorType (α := px) from hPxColorType.symm]
    rw [show (u8 8 : UInt8) = PngPixel.bitDepth (α := px) from hTargetBitDepth.symm]
    exact hRowsChain
  unfold Png.decodeBitmapWithMetadata Png.decodeParsedBitmapWithMetadata
  simp only [hSize, dite_true, hParse, Option.bind_eq_bind, Option.bind_some]
  rcases hInflated with hStored | ⟨hStoredNone, hZlib⟩
  · simpa [hctbdHdr, hSourceBitDepth, hTargetBitDepth, hbitDepthCompatible,
      hSourceNot1, hSourceIs16, hTargetIs8, hTargetNot16, hTargetIs6,
      hTargetNot0, hTargetNot4, hChrmGrayInactive,
      hWidth, hHeight, hInterlace, hIdatMin, hStored, PngMetadata.empty,
      hPxColorType] using
      (And.intro hctbdHdr (And.intro hCtCases (And.intro hbdMatchImpl hBppChain)))
  · simpa [hctbdHdr, hSourceBitDepth, hTargetBitDepth, hbitDepthCompatible,
      hSourceNot1, hSourceIs16, hTargetIs8, hTargetNot16, hTargetIs6,
      hTargetNot0, hTargetNot4, hChrmGrayInactive,
      hWidth, hHeight, hInterlace, hIdatMin, hStoredNone, hZlib,
      PngMetadata.empty, hPxColorType] using
      (And.intro hctbdHdr (And.intro hCtCases (And.intro hbdMatchImpl hBppChain)))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 4096 in
/-- The tRNS forward-decode core for RGB8 target (compositing tRNS
over a background): source bitDepth = 8, target = 8-bit RGB
(e.g. `PixelRGB8`). Requires both `transparency = some trns` and
`background = some bg` in the parsed metadata. Routes through
`decodeRowsLoopTrnsOverBackground`. -/
theorem decodeBitmapWithMetadata_correct_of_witnesses_trnsRgb8
    {px : Type u} [Pixel px] [PngPixel px]
    {bitmap : Bitmap px}
    {header : PngHeader} {idat : ByteArray}
    {trns : PngTransparency} {bg : PngBackground}
    {inflatedRaw : ByteArray}
    {bytes : ByteArray} (hSize : 8 ≤ bytes.size)
    (hSourceBitDepth : header.bitDepth = 8)
    (hTargetBitDepth : PngPixel.bitDepth (α := px) = u8 8)
    (hSourceColorType : header.colorType = 0 ∨ header.colorType = 2 ∨
      header.colorType = 4 ∨ header.colorType = 6)
    (hTargetColorType : PngPixel.colorType (α := px) = u8 2)
    (hWidth : header.width = bitmap.size.width)
    (hHeight : header.height = bitmap.size.height)
    (hInterlace : header.interlace = 0)
    (hPxColorType : PngPixel.colorType (α := px) = u8 header.colorType)
    (hBppLookup : pngBytesPerPixelForColorTypeAndBitDepth?
      header.colorType header.bitDepth = some (Pixel.bytesPerPixel (α := px)))
    (hParse : parsePngWithMetadata bytes hSize =
      some { header := header, idat := idat,
             metadata := { PngMetadata.empty with
                             transparency := some trns
                             background := some bg } })
    (hIdatMin : 2 ≤ idat.size)
    (hInflated :
      zlibDecompressStored idat hIdatMin = some inflatedRaw ∨
      (zlibDecompressStored idat hIdatMin = none ∧
       zlibDecompress idat hIdatMin = some inflatedRaw))
    (hRawSize :
      inflatedRaw.size = bitmap.size.height *
        (bitmap.size.width * Pixel.bytesPerPixel (α := px) + 1))
    (hPixels :
      decodeRowsLoopTrnsOverBackground trns bg inflatedRaw
          bitmap.size.width bitmap.size.height (Pixel.bytesPerPixel (α := px))
          (bitmap.size.width * Pixel.bytesPerPixel (α := px))
          0 0 ByteArray.empty
          { data := Array.replicate
              (bitmap.size.width * bitmap.size.height *
                Pixel.bytesPerPixel (α := px)) 0 } =
        some bitmap.data) :
    Png.decodeBitmapWithMetadata bytes =
      some { bitmap := bitmap
             metadata := { PngMetadata.empty with
                             transparency := some trns
                             background := some bg } } := by
  have hbdNoReject : pngBitDepthSupported header.bitDepth = true := by
    rw [hSourceBitDepth]; decide
  have hctbdHdr :
      pngColorTypeBitDepthSupported header.colorType header.bitDepth = true := by
    rw [hSourceBitDepth]
    rcases hSourceColorType with h | h | h | h <;> rw [h] <;> decide
  have hbitDepthEq :
      (header.bitDepth == (PngPixel.bitDepth (α := px)).toNat) = true := by
    rw [hSourceBitDepth, hTargetBitDepth]; rfl
  have hbitDepthCompatible :
      (header.bitDepth == (PngPixel.bitDepth (α := px)).toNat ||
        (header.bitDepth == 16 && PngPixel.bitDepth (α := px) == u8 8) ||
        (header.bitDepth == 1 &&
          (PngPixel.bitDepth (α := px) == u8 8 ||
            PngPixel.bitDepth (α := px) == u8 16))) = true := by
    simp [hbitDepthEq]
  have hCtCases :
      ¬ header.colorType = 0 → ¬ header.colorType = 2 →
        ¬ header.colorType = 4 → header.colorType = 6 := by
    intro h0 h2 h4
    rcases hSourceColorType with hc | hc | hc | hc
    · exact absurd hc h0
    · exact absurd hc h2
    · exact absurd hc h4
    · exact hc
  have hSourceNot1 : (header.bitDepth == 1) = false := by
    rw [hSourceBitDepth]; decide
  have hSourceNot16 : (header.bitDepth == 16) = false := by
    rw [hSourceBitDepth]; decide
  have hTargetIs8 : (PngPixel.bitDepth (α := px) == u8 8) = true := by
    rw [hTargetBitDepth]; decide
  have hTargetNot16 : (PngPixel.bitDepth (α := px) == u8 16) = false := by
    rw [hTargetBitDepth]; decide
  have hTargetNot6 : (PngPixel.colorType (α := px) == u8 6) = false := by
    rw [hTargetColorType]; decide
  have hTargetIs2 : (PngPixel.colorType (α := px) == u8 2) = true := by
    rw [hTargetColorType]; decide
  have hTargetNot4 : (PngPixel.colorType (α := px) == u8 4) = false := by
    rw [hTargetColorType]; decide
  have hTargetNot0 : (PngPixel.colorType (α := px) == u8 0) = false := by
    rw [hTargetColorType]; decide
  have hChrmGrayInactive :
      (PngMetadata.empty.srgb.isNone &&
        PngMetadata.empty.chromaticities.isSome &&
        (header.colorType == 2 || header.colorType == 6) &&
        (PngPixel.colorType (α := px) == u8 0 ||
          PngPixel.colorType (α := px) == u8 4)) = false := by
    simp [PngMetadata.empty, hTargetNot0, hTargetNot4]
  have hRawNorm :
      normalizeRawByInterlace? inflatedRaw header
        (Pixel.bytesPerPixel (α := px)) = some inflatedRaw := by
    unfold normalizeRawByInterlace?
    rw [hInterlace]; rfl
  have hTransform :
      applyPngColorSpaceTransform
        { PngMetadata.empty with transparency := some trns, background := some bg }
        header.colorType (PngPixel.colorType (α := px))
        (PngPixel.bitDepth (α := px)) bitmap.data = some bitmap.data := by
    unfold applyPngColorSpaceTransform
    rfl
  have hValid : bitmap.data.size =
      bitmap.size.width * bitmap.size.height *
        Pixel.bytesPerPixel (α := px) := by simpa using bitmap.valid
  have hbdMatchEq : header.bitDepth = (PngPixel.bitDepth (α := px)).toNat := by
    rw [hSourceBitDepth, hTargetBitDepth]; decide
  have hPxIsU8_2 : u8 header.colorType = u8 2 := by
    rw [← hPxColorType, hTargetColorType]
  have hU8_2_ne_6 : ¬ (u8 2 : UInt8) = u8 6 := by decide
  have hRowsChain :
      ((decodeRowsLoopTrnsOverBackground trns bg inflatedRaw
            bitmap.size.width bitmap.size.height (Pixel.bytesPerPixel (α := px))
            (bitmap.size.width * Pixel.bytesPerPixel (α := px))
            0 0 ByteArray.empty
            { data := Array.replicate
                (bitmap.size.width * bitmap.size.height *
                  Pixel.bytesPerPixel (α := px)) 0 }).bind fun y ↦
        (applyPngColorSpaceTransform
            { PngMetadata.empty with
                transparency := some trns, background := some bg }
            header.colorType (PngPixel.colorType (α := px))
            (PngPixel.bitDepth (α := px)) y).bind fun pixels ↦
          if h : pixels.size = bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px) then
            some ({ bitmap := { size := { width := bitmap.size.width,
                                            height := bitmap.size.height },
                                  data := pixels, valid := h },
                    metadata := { PngMetadata.empty with
                                    transparency := some trns
                                    background := some bg } } : PngDecodeResult px)
          else none) =
      some ({ bitmap := bitmap
              metadata := { PngMetadata.empty with
                              transparency := some trns
                              background := some bg } } : PngDecodeResult px) := by
    rw [hPixels, Option.bind_some]
    rw [hTransform, Option.bind_some]
    simp [hValid]
  -- The full big-chain has BOTH the c=6 (RGBA) branch and the c=2 (RGB+bg)
  -- branch, even though for our case (target=u8 2) only c=2 fires.
  have hBppChain :
      ((pngBytesPerPixelForColorTypeAndBitDepth? header.colorType header.bitDepth).bind
        fun bpp ↦
          (normalizeRawByInterlace? inflatedRaw header bpp).bind fun raw ↦
            if raw.size = bitmap.size.height * (bitmap.size.width * bpp + 1) then
              if u8 header.colorType = u8 6 then
                (decodeRowsLoopRGBAWithTransparency (some trns) raw bitmap.size.width
                      bitmap.size.height bpp (bitmap.size.width * bpp) 0 0 ByteArray.empty
                      { data := Array.replicate
                          (bitmap.size.width * bitmap.size.height *
                            Pixel.bytesPerPixel (α := px)) 0 }).bind fun y ↦
                  (applyPngColorSpaceTransform
                      { PngMetadata.empty with
                          transparency := some trns, background := some bg }
                      header.colorType (u8 header.colorType)
                      (u8 8) y).bind fun pixels ↦
                    if h : pixels.size = bitmap.size.width * bitmap.size.height *
                        Pixel.bytesPerPixel (α := px) then
                      some ({ bitmap := { size := { width := bitmap.size.width,
                                                     height := bitmap.size.height },
                                           data := pixels, valid := h },
                              metadata := { PngMetadata.empty with
                                              transparency := some trns
                                              background := some bg } } : PngDecodeResult px)
                    else none
              else if u8 header.colorType = u8 2 then
                (decodeRowsLoopTrnsOverBackground trns bg raw bitmap.size.width
                      bitmap.size.height bpp (bitmap.size.width * bpp) 0 0 ByteArray.empty
                      { data := Array.replicate
                          (bitmap.size.width * bitmap.size.height *
                            Pixel.bytesPerPixel (α := px)) 0 }).bind fun y ↦
                  (applyPngColorSpaceTransform
                      { PngMetadata.empty with
                          transparency := some trns, background := some bg }
                      header.colorType (u8 header.colorType)
                      (u8 8) y).bind fun pixels ↦
                    if h : pixels.size = bitmap.size.width * bitmap.size.height *
                        Pixel.bytesPerPixel (α := px) then
                      some ({ bitmap := { size := { width := bitmap.size.width,
                                                     height := bitmap.size.height },
                                           data := pixels, valid := h },
                              metadata := { PngMetadata.empty with
                                              transparency := some trns
                                              background := some bg } } : PngDecodeResult px)
                    else none
              else none
            else none) =
        some ({ bitmap := bitmap
                metadata := { PngMetadata.empty with
                                transparency := some trns
                                background := some bg } } : PngDecodeResult px) := by
    rw [hBppLookup]
    simp only [Option.bind_some]
    rw [hRawNorm, Option.bind_some]
    rw [if_pos hRawSize]
    have hNotSix : ¬ u8 header.colorType = u8 6 := by
      intro h
      have : u8 2 = u8 6 := hPxIsU8_2 ▸ h
      exact hU8_2_ne_6 this
    rw [if_neg hNotSix]
    rw [if_pos hPxIsU8_2]
    rw [show (u8 header.colorType) = PngPixel.colorType (α := px) from hPxColorType.symm]
    rw [show (u8 8 : UInt8) = PngPixel.bitDepth (α := px) from hTargetBitDepth.symm]
    exact hRowsChain
  unfold Png.decodeBitmapWithMetadata Png.decodeParsedBitmapWithMetadata
  simp only [hSize, dite_true, hParse, Option.bind_eq_bind, Option.bind_some]
  rcases hInflated with hStored | ⟨hStoredNone, hZlib⟩
  · simpa [hctbdHdr, hSourceBitDepth, hTargetBitDepth, hbitDepthCompatible,
      hSourceNot1, hSourceNot16, hTargetIs8, hTargetNot16, hTargetIs2, hTargetNot6,
      hTargetNot0, hTargetNot4, hChrmGrayInactive,
      hWidth, hHeight, hInterlace, hIdatMin, hStored, PngMetadata.empty,
      hPxColorType] using
      (And.intro hctbdHdr (And.intro hCtCases (And.intro hbdMatchEq hBppChain)))
  · simpa [hctbdHdr, hSourceBitDepth, hTargetBitDepth, hbitDepthCompatible,
      hSourceNot1, hSourceNot16, hTargetIs8, hTargetNot16, hTargetIs2, hTargetNot6,
      hTargetNot0, hTargetNot4, hChrmGrayInactive,
      hWidth, hHeight, hInterlace, hIdatMin, hStoredNone, hZlib,
      PngMetadata.empty, hPxColorType] using
      (And.intro hctbdHdr (And.intro hCtCases (And.intro hbdMatchEq hBppChain)))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 4096 in
/-- The AlphaOverBackground forward-decode core for source-colorType-4
(gray+alpha) → target-colorType-0 (gray): transparency = none but
background = some bg, source bitDepth = 8, target = `u8 8`. Routes
through `decodeRowsLoopGrayAlphaOverBackground`. -/
theorem decodeBitmapWithMetadata_correct_of_witnesses_alphaBgGray8
    {px : Type u} [Pixel px] [PngPixel px]
    {bitmap : Bitmap px}
    {header : PngHeader} {idat : ByteArray} {bg : PngBackground}
    {inflatedRaw : ByteArray}
    {bytes : ByteArray} (hSize : 8 ≤ bytes.size)
    (hSourceBitDepth : header.bitDepth = 8)
    (hTargetBitDepth : PngPixel.bitDepth (α := px) = u8 8)
    (hSourceColorType : header.colorType = 4)
    (hTargetColorType : PngPixel.colorType (α := px) = u8 0)
    (hWidth : header.width = bitmap.size.width)
    (hHeight : header.height = bitmap.size.height)
    (hInterlace : header.interlace = 0)
    (hBppLookup : pngBytesPerPixelForColorTypeAndBitDepth?
      header.colorType header.bitDepth = some (Pixel.bytesPerPixel (α := px)))
    (hParse : parsePngWithMetadata bytes hSize =
      some { header := header, idat := idat,
             metadata := { PngMetadata.empty with background := some bg } })
    (hIdatMin : 2 ≤ idat.size)
    (hInflated :
      zlibDecompressStored idat hIdatMin = some inflatedRaw ∨
      (zlibDecompressStored idat hIdatMin = none ∧
       zlibDecompress idat hIdatMin = some inflatedRaw))
    (hRawSize :
      inflatedRaw.size = bitmap.size.height *
        (bitmap.size.width * Pixel.bytesPerPixel (α := px) + 1))
    (hPixels :
      decodeRowsLoopGrayAlphaOverBackground bg inflatedRaw
          bitmap.size.width bitmap.size.height (Pixel.bytesPerPixel (α := px))
          (bitmap.size.width * Pixel.bytesPerPixel (α := px))
          0 0 ByteArray.empty
          { data := Array.replicate
              (bitmap.size.width * bitmap.size.height *
                Pixel.bytesPerPixel (α := px)) 0 } =
        some bitmap.data) :
    Png.decodeBitmapWithMetadata bytes =
      some { bitmap := bitmap
             metadata := { PngMetadata.empty with background := some bg } } := by
  have hbdNoReject : pngBitDepthSupported header.bitDepth = true := by
    rw [hSourceBitDepth]; decide
  have hctbdHdr :
      pngColorTypeBitDepthSupported header.colorType header.bitDepth = true := by
    rw [hSourceBitDepth, hSourceColorType]; decide
  have hbitDepthEq :
      (header.bitDepth == (PngPixel.bitDepth (α := px)).toNat) = true := by
    rw [hSourceBitDepth, hTargetBitDepth]; rfl
  have hbitDepthCompatible :
      (header.bitDepth == (PngPixel.bitDepth (α := px)).toNat ||
        (header.bitDepth == 16 && PngPixel.bitDepth (α := px) == u8 8) ||
        (header.bitDepth == 1 &&
          (PngPixel.bitDepth (α := px) == u8 8 ||
            PngPixel.bitDepth (α := px) == u8 16))) = true := by
    simp [hbitDepthEq]
  have hCtIs4 : (header.colorType == 4) = true := by
    rw [hSourceColorType]; decide
  have hCtNot6 : (header.colorType == 6) = false := by
    rw [hSourceColorType]; decide
  have hSourceNot1 : (header.bitDepth == 1) = false := by
    rw [hSourceBitDepth]; decide
  have hSourceNot16 : (header.bitDepth == 16) = false := by
    rw [hSourceBitDepth]; decide
  have hTargetIs8 : (PngPixel.bitDepth (α := px) == u8 8) = true := by
    rw [hTargetBitDepth]; decide
  have hTargetNot16 : (PngPixel.bitDepth (α := px) == u8 16) = false := by
    rw [hTargetBitDepth]; decide
  have hTargetNot6 : (PngPixel.colorType (α := px) == u8 6) = false := by
    rw [hTargetColorType]; decide
  have hTargetNot2 : (PngPixel.colorType (α := px) == u8 2) = false := by
    rw [hTargetColorType]; decide
  have hTargetIs0 : (PngPixel.colorType (α := px) == u8 0) = true := by
    rw [hTargetColorType]; decide
  have hTargetNot4 : (PngPixel.colorType (α := px) == u8 4) = false := by
    rw [hTargetColorType]; decide
  -- chrmGrayActive is false: hChromaticities is none (metadata only has bg).
  have hChrmGrayInactive :
      ({ PngMetadata.empty with background := some bg : PngMetadata }.srgb.isNone &&
        { PngMetadata.empty with background := some bg : PngMetadata }.chromaticities.isSome &&
        (header.colorType == 2 || header.colorType == 6) &&
        (PngPixel.colorType (α := px) == u8 0 ||
          PngPixel.colorType (α := px) == u8 4)) = false := by
    simp [PngMetadata.empty]
  have hRawNorm :
      normalizeRawByInterlace? inflatedRaw header
        (Pixel.bytesPerPixel (α := px)) = some inflatedRaw := by
    unfold normalizeRawByInterlace?
    rw [hInterlace]; rfl
  have hTransform :
      applyPngColorSpaceTransform
        { PngMetadata.empty with background := some bg }
        header.colorType (PngPixel.colorType (α := px))
        (PngPixel.bitDepth (α := px)) bitmap.data = some bitmap.data := by
    unfold applyPngColorSpaceTransform
    rfl
  have hValid : bitmap.data.size =
      bitmap.size.width * bitmap.size.height *
        Pixel.bytesPerPixel (α := px) := by simpa using bitmap.valid
  have hbdMatchEq : header.bitDepth = (PngPixel.bitDepth (α := px)).toNat := by
    rw [hSourceBitDepth, hTargetBitDepth]; decide
  have hCt4IsAlpha : header.colorType = 4 := hSourceColorType
  have hRowsChain :
      ((decodeRowsLoopGrayAlphaOverBackground bg inflatedRaw
            bitmap.size.width bitmap.size.height (Pixel.bytesPerPixel (α := px))
            (bitmap.size.width * Pixel.bytesPerPixel (α := px))
            0 0 ByteArray.empty
            { data := Array.replicate
                (bitmap.size.width * bitmap.size.height *
                  Pixel.bytesPerPixel (α := px)) 0 }).bind fun y ↦
        (applyPngColorSpaceTransform
            { PngMetadata.empty with background := some bg }
            header.colorType (PngPixel.colorType (α := px))
            (PngPixel.bitDepth (α := px)) y).bind fun pixels ↦
          if h : pixels.size = bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px) then
            some ({ bitmap := { size := { width := bitmap.size.width,
                                            height := bitmap.size.height },
                                  data := pixels, valid := h },
                    metadata := { PngMetadata.empty with background := some bg } } : PngDecodeResult px)
          else none) =
      some ({ bitmap := bitmap
              metadata := { PngMetadata.empty with background := some bg } } : PngDecodeResult px) := by
    rw [hPixels, Option.bind_some]
    rw [hTransform, Option.bind_some]
    simp [hValid]
  have hU0_ne_2 : ¬ (u8 0 : UInt8) = u8 2 := by decide
  have hBppChain :
      ((pngBytesPerPixelForColorTypeAndBitDepth? header.colorType header.bitDepth).bind
        fun bpp ↦
          (normalizeRawByInterlace? inflatedRaw header bpp).bind fun raw ↦
            if raw.size = bitmap.size.height * (bitmap.size.width * bpp + 1) then
              if (PngPixel.colorType (α := px)) = u8 2 then
                (decodeRowsLoopAlphaOverBackground bg raw
                      bitmap.size.width bitmap.size.height bpp
                      (bitmap.size.width * bpp) 0 0 ByteArray.empty
                      { data := Array.replicate
                          (bitmap.size.width * bitmap.size.height *
                            Pixel.bytesPerPixel (α := px)) 0 }).bind fun y ↦
                  (applyPngColorSpaceTransform
                      { PngMetadata.empty with background := some bg }
                      header.colorType (PngPixel.colorType (α := px))
                      (u8 8) y).bind fun pixels ↦
                    if h : pixels.size = bitmap.size.width * bitmap.size.height *
                        Pixel.bytesPerPixel (α := px) then
                      some ({ bitmap := { size := { width := bitmap.size.width,
                                                     height := bitmap.size.height },
                                           data := pixels, valid := h },
                              metadata := { PngMetadata.empty with background := some bg } } : PngDecodeResult px)
                    else none
              else
                (decodeRowsLoopGrayAlphaOverBackground bg raw
                      bitmap.size.width bitmap.size.height bpp
                      (bitmap.size.width * bpp) 0 0 ByteArray.empty
                      { data := Array.replicate
                          (bitmap.size.width * bitmap.size.height *
                            Pixel.bytesPerPixel (α := px)) 0 }).bind fun y ↦
                  (applyPngColorSpaceTransform
                      { PngMetadata.empty with background := some bg }
                      header.colorType (PngPixel.colorType (α := px))
                      (u8 8) y).bind fun pixels ↦
                    if h : pixels.size = bitmap.size.width * bitmap.size.height *
                        Pixel.bytesPerPixel (α := px) then
                      some ({ bitmap := { size := { width := bitmap.size.width,
                                                     height := bitmap.size.height },
                                           data := pixels, valid := h },
                              metadata := { PngMetadata.empty with background := some bg } } : PngDecodeResult px)
                    else none
            else none) =
        some ({ bitmap := bitmap
                metadata := { PngMetadata.empty with background := some bg } } : PngDecodeResult px) := by
    rw [hBppLookup]
    simp only [Option.bind_some]
    rw [hRawNorm, Option.bind_some]
    rw [if_pos hRawSize]
    have hPxNot2 : ¬ PngPixel.colorType (α := px) = u8 2 := by
      rw [hTargetColorType]; exact hU0_ne_2
    rw [if_neg hPxNot2]
    rw [show (u8 8 : UInt8) = PngPixel.bitDepth (α := px) from hTargetBitDepth.symm]
    exact hRowsChain
  unfold Png.decodeBitmapWithMetadata Png.decodeParsedBitmapWithMetadata
  simp only [hSize, dite_true, hParse, Option.bind_eq_bind, Option.bind_some]
  rcases hInflated with hStored | ⟨hStoredNone, hZlib⟩
  · simpa [hctbdHdr, hSourceBitDepth, hTargetBitDepth, hSourceColorType,
      hTargetColorType, hbitDepthCompatible,
      hCtIs4, hCtNot6, hSourceNot1, hSourceNot16, hTargetIs8, hTargetNot16,
      hTargetIs0, hTargetNot2, hTargetNot4, hTargetNot6, hChrmGrayInactive,
      hWidth, hHeight, hInterlace, hIdatMin, hStored, PngMetadata.empty] using
      (And.intro hctbdHdr (And.intro hbdMatchEq hBppChain))
  · simpa [hctbdHdr, hSourceBitDepth, hTargetBitDepth, hSourceColorType,
      hTargetColorType, hbitDepthCompatible,
      hCtIs4, hCtNot6, hSourceNot1, hSourceNot16, hTargetIs8, hTargetNot16,
      hTargetIs0, hTargetNot2, hTargetNot4, hTargetNot6, hChrmGrayInactive,
      hWidth, hHeight, hInterlace, hIdatMin, hStoredNone, hZlib,
      PngMetadata.empty] using
      (And.intro hctbdHdr (And.intro hbdMatchEq hBppChain))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 4096 in
/-- AlphaOverBackground core for source-colorType-4 (gray+alpha) →
target-colorType-2 (RGB): transparency = none, background = some bg,
source bd=8, target = u8 8. Routes through
`decodeRowsLoopAlphaOverBackground`. -/
theorem decodeBitmapWithMetadata_correct_of_witnesses_alphaBgRgb8
    {px : Type u} [Pixel px] [PngPixel px]
    {bitmap : Bitmap px}
    {header : PngHeader} {idat : ByteArray} {bg : PngBackground}
    {inflatedRaw : ByteArray}
    {bytes : ByteArray} (hSize : 8 ≤ bytes.size)
    (hSourceBitDepth : header.bitDepth = 8)
    (hTargetBitDepth : PngPixel.bitDepth (α := px) = u8 8)
    (hSourceColorType : header.colorType = 4)
    (hTargetColorType : PngPixel.colorType (α := px) = u8 2)
    (hWidth : header.width = bitmap.size.width)
    (hHeight : header.height = bitmap.size.height)
    (hInterlace : header.interlace = 0)
    (hBppLookup : pngBytesPerPixelForColorTypeAndBitDepth?
      header.colorType header.bitDepth = some (Pixel.bytesPerPixel (α := px)))
    (hParse : parsePngWithMetadata bytes hSize =
      some { header := header, idat := idat,
             metadata := { PngMetadata.empty with background := some bg } })
    (hIdatMin : 2 ≤ idat.size)
    (hInflated :
      zlibDecompressStored idat hIdatMin = some inflatedRaw ∨
      (zlibDecompressStored idat hIdatMin = none ∧
       zlibDecompress idat hIdatMin = some inflatedRaw))
    (hRawSize :
      inflatedRaw.size = bitmap.size.height *
        (bitmap.size.width * Pixel.bytesPerPixel (α := px) + 1))
    (hPixels :
      decodeRowsLoopAlphaOverBackground bg inflatedRaw
          bitmap.size.width bitmap.size.height (Pixel.bytesPerPixel (α := px))
          (bitmap.size.width * Pixel.bytesPerPixel (α := px))
          0 0 ByteArray.empty
          { data := Array.replicate
              (bitmap.size.width * bitmap.size.height *
                Pixel.bytesPerPixel (α := px)) 0 } =
        some bitmap.data) :
    Png.decodeBitmapWithMetadata bytes =
      some { bitmap := bitmap
             metadata := { PngMetadata.empty with background := some bg } } := by
  have hbdNoReject : pngBitDepthSupported header.bitDepth = true := by
    rw [hSourceBitDepth]; decide
  have hctbdHdr :
      pngColorTypeBitDepthSupported header.colorType header.bitDepth = true := by
    rw [hSourceBitDepth, hSourceColorType]; decide
  have hbitDepthEq :
      (header.bitDepth == (PngPixel.bitDepth (α := px)).toNat) = true := by
    rw [hSourceBitDepth, hTargetBitDepth]; rfl
  have hbitDepthCompatible :
      (header.bitDepth == (PngPixel.bitDepth (α := px)).toNat ||
        (header.bitDepth == 16 && PngPixel.bitDepth (α := px) == u8 8) ||
        (header.bitDepth == 1 &&
          (PngPixel.bitDepth (α := px) == u8 8 ||
            PngPixel.bitDepth (α := px) == u8 16))) = true := by
    simp [hbitDepthEq]
  have hCtIs4 : (header.colorType == 4) = true := by rw [hSourceColorType]; decide
  have hCtNot6 : (header.colorType == 6) = false := by rw [hSourceColorType]; decide
  have hSourceNot1 : (header.bitDepth == 1) = false := by rw [hSourceBitDepth]; decide
  have hSourceNot16 : (header.bitDepth == 16) = false := by rw [hSourceBitDepth]; decide
  have hTargetIs8 : (PngPixel.bitDepth (α := px) == u8 8) = true := by
    rw [hTargetBitDepth]; decide
  have hTargetNot16 : (PngPixel.bitDepth (α := px) == u8 16) = false := by
    rw [hTargetBitDepth]; decide
  have hTargetIs2 : (PngPixel.colorType (α := px) == u8 2) = true := by
    rw [hTargetColorType]; decide
  have hTargetNot0 : (PngPixel.colorType (α := px) == u8 0) = false := by
    rw [hTargetColorType]; decide
  have hTargetNot4 : (PngPixel.colorType (α := px) == u8 4) = false := by
    rw [hTargetColorType]; decide
  have hTargetNot6 : (PngPixel.colorType (α := px) == u8 6) = false := by
    rw [hTargetColorType]; decide
  have hChrmGrayInactive :
      ({ PngMetadata.empty with background := some bg : PngMetadata }.srgb.isNone &&
        { PngMetadata.empty with background := some bg : PngMetadata }.chromaticities.isSome &&
        (header.colorType == 2 || header.colorType == 6) &&
        (PngPixel.colorType (α := px) == u8 0 ||
          PngPixel.colorType (α := px) == u8 4)) = false := by
    simp [PngMetadata.empty]
  have hRawNorm :
      normalizeRawByInterlace? inflatedRaw header
        (Pixel.bytesPerPixel (α := px)) = some inflatedRaw := by
    unfold normalizeRawByInterlace?; rw [hInterlace]; rfl
  have hTransform :
      applyPngColorSpaceTransform
        { PngMetadata.empty with background := some bg }
        header.colorType (PngPixel.colorType (α := px))
        (PngPixel.bitDepth (α := px)) bitmap.data = some bitmap.data := by
    unfold applyPngColorSpaceTransform; rfl
  have hValid : bitmap.data.size =
      bitmap.size.width * bitmap.size.height *
        Pixel.bytesPerPixel (α := px) := by simpa using bitmap.valid
  have hbdMatchEq : header.bitDepth = (PngPixel.bitDepth (α := px)).toNat := by
    rw [hSourceBitDepth, hTargetBitDepth]; decide
  have hRowsChain :
      ((decodeRowsLoopAlphaOverBackground bg inflatedRaw
            bitmap.size.width bitmap.size.height (Pixel.bytesPerPixel (α := px))
            (bitmap.size.width * Pixel.bytesPerPixel (α := px))
            0 0 ByteArray.empty
            { data := Array.replicate
                (bitmap.size.width * bitmap.size.height *
                  Pixel.bytesPerPixel (α := px)) 0 }).bind fun y ↦
        (applyPngColorSpaceTransform
            { PngMetadata.empty with background := some bg }
            header.colorType (PngPixel.colorType (α := px))
            (PngPixel.bitDepth (α := px)) y).bind fun pixels ↦
          if h : pixels.size = bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px) then
            some ({ bitmap := { size := { width := bitmap.size.width,
                                            height := bitmap.size.height },
                                  data := pixels, valid := h },
                    metadata := { PngMetadata.empty with background := some bg } } : PngDecodeResult px)
          else none) =
      some ({ bitmap := bitmap
              metadata := { PngMetadata.empty with background := some bg } } : PngDecodeResult px) := by
    rw [hPixels, Option.bind_some]
    rw [hTransform, Option.bind_some]
    simp [hValid]
  have hPxIsU8_2 : PngPixel.colorType (α := px) = u8 2 := hTargetColorType
  have hBppChain :
      ((pngBytesPerPixelForColorTypeAndBitDepth? header.colorType header.bitDepth).bind
        fun bpp ↦
          (normalizeRawByInterlace? inflatedRaw header bpp).bind fun raw ↦
            if raw.size = bitmap.size.height * (bitmap.size.width * bpp + 1) then
              if (PngPixel.colorType (α := px)) = u8 2 then
                (decodeRowsLoopAlphaOverBackground bg raw
                      bitmap.size.width bitmap.size.height bpp
                      (bitmap.size.width * bpp) 0 0 ByteArray.empty
                      { data := Array.replicate
                          (bitmap.size.width * bitmap.size.height *
                            Pixel.bytesPerPixel (α := px)) 0 }).bind fun y ↦
                  (applyPngColorSpaceTransform
                      { PngMetadata.empty with background := some bg }
                      header.colorType (PngPixel.colorType (α := px))
                      (u8 8) y).bind fun pixels ↦
                    if h : pixels.size = bitmap.size.width * bitmap.size.height *
                        Pixel.bytesPerPixel (α := px) then
                      some ({ bitmap := { size := { width := bitmap.size.width,
                                                     height := bitmap.size.height },
                                           data := pixels, valid := h },
                              metadata := { PngMetadata.empty with background := some bg } } : PngDecodeResult px)
                    else none
              else
                (decodeRowsLoopGrayAlphaOverBackground bg raw
                      bitmap.size.width bitmap.size.height bpp
                      (bitmap.size.width * bpp) 0 0 ByteArray.empty
                      { data := Array.replicate
                          (bitmap.size.width * bitmap.size.height *
                            Pixel.bytesPerPixel (α := px)) 0 }).bind fun y ↦
                  (applyPngColorSpaceTransform
                      { PngMetadata.empty with background := some bg }
                      header.colorType (PngPixel.colorType (α := px))
                      (u8 8) y).bind fun pixels ↦
                    if h : pixels.size = bitmap.size.width * bitmap.size.height *
                        Pixel.bytesPerPixel (α := px) then
                      some ({ bitmap := { size := { width := bitmap.size.width,
                                                     height := bitmap.size.height },
                                           data := pixels, valid := h },
                              metadata := { PngMetadata.empty with background := some bg } } : PngDecodeResult px)
                    else none
            else none) =
        some ({ bitmap := bitmap
                metadata := { PngMetadata.empty with background := some bg } } : PngDecodeResult px) := by
    rw [hBppLookup]
    simp only [Option.bind_some]
    rw [hRawNorm, Option.bind_some]
    rw [if_pos hRawSize, if_pos hPxIsU8_2]
    rw [show (u8 8 : UInt8) = PngPixel.bitDepth (α := px) from hTargetBitDepth.symm]
    exact hRowsChain
  unfold Png.decodeBitmapWithMetadata Png.decodeParsedBitmapWithMetadata
  simp only [hSize, dite_true, hParse, Option.bind_eq_bind, Option.bind_some]
  rcases hInflated with hStored | ⟨hStoredNone, hZlib⟩
  · simpa [hctbdHdr, hSourceBitDepth, hTargetBitDepth, hSourceColorType,
      hTargetColorType, hbitDepthCompatible,
      hCtIs4, hCtNot6, hSourceNot1, hSourceNot16, hTargetIs8, hTargetNot16,
      hTargetIs2, hTargetNot0, hTargetNot4, hTargetNot6, hChrmGrayInactive,
      hWidth, hHeight, hInterlace, hIdatMin, hStored, PngMetadata.empty] using
      (And.intro hctbdHdr (And.intro hbdMatchEq hBppChain))
  · simpa [hctbdHdr, hSourceBitDepth, hTargetBitDepth, hSourceColorType,
      hTargetColorType, hbitDepthCompatible,
      hCtIs4, hCtNot6, hSourceNot1, hSourceNot16, hTargetIs8, hTargetNot16,
      hTargetIs2, hTargetNot0, hTargetNot4, hTargetNot6, hChrmGrayInactive,
      hWidth, hHeight, hInterlace, hIdatMin, hStoredNone, hZlib,
      PngMetadata.empty] using
      (And.intro hctbdHdr (And.intro hbdMatchEq hBppChain))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 4096 in
/-- AlphaOverBackground for source-colorType-6 (RGBA) → target-colorType-2
(RGB), source bd=8, target = u8 8. Composites the source alpha against
the background. Routes through `decodeRowsLoopAlphaOverBackground`. -/
theorem decodeBitmapWithMetadata_correct_of_witnesses_alphaBgRgba6To2
    {px : Type u} [Pixel px] [PngPixel px]
    {bitmap : Bitmap px}
    {header : PngHeader} {idat : ByteArray} {bg : PngBackground}
    {inflatedRaw : ByteArray}
    {bytes : ByteArray} (hSize : 8 ≤ bytes.size)
    (hSourceBitDepth : header.bitDepth = 8)
    (hTargetBitDepth : PngPixel.bitDepth (α := px) = u8 8)
    (hSourceColorType : header.colorType = 6)
    (hTargetColorType : PngPixel.colorType (α := px) = u8 2)
    (hWidth : header.width = bitmap.size.width)
    (hHeight : header.height = bitmap.size.height)
    (hInterlace : header.interlace = 0)
    (hBppLookup : pngBytesPerPixelForColorTypeAndBitDepth?
      header.colorType header.bitDepth = some (Pixel.bytesPerPixel (α := px)))
    (hParse : parsePngWithMetadata bytes hSize =
      some { header := header, idat := idat,
             metadata := { PngMetadata.empty with background := some bg } })
    (hIdatMin : 2 ≤ idat.size)
    (hInflated :
      zlibDecompressStored idat hIdatMin = some inflatedRaw ∨
      (zlibDecompressStored idat hIdatMin = none ∧
       zlibDecompress idat hIdatMin = some inflatedRaw))
    (hRawSize :
      inflatedRaw.size = bitmap.size.height *
        (bitmap.size.width * Pixel.bytesPerPixel (α := px) + 1))
    (hPixels :
      decodeRowsLoopAlphaOverBackground bg inflatedRaw
          bitmap.size.width bitmap.size.height (Pixel.bytesPerPixel (α := px))
          (bitmap.size.width * Pixel.bytesPerPixel (α := px))
          0 0 ByteArray.empty
          { data := Array.replicate
              (bitmap.size.width * bitmap.size.height *
                Pixel.bytesPerPixel (α := px)) 0 } =
        some bitmap.data) :
    Png.decodeBitmapWithMetadata bytes =
      some { bitmap := bitmap
             metadata := { PngMetadata.empty with background := some bg } } := by
  have hbdNoReject : pngBitDepthSupported header.bitDepth = true := by
    rw [hSourceBitDepth]; decide
  have hctbdHdr :
      pngColorTypeBitDepthSupported header.colorType header.bitDepth = true := by
    rw [hSourceBitDepth, hSourceColorType]; decide
  have hbitDepthEq :
      (header.bitDepth == (PngPixel.bitDepth (α := px)).toNat) = true := by
    rw [hSourceBitDepth, hTargetBitDepth]; rfl
  have hbitDepthCompatible :
      (header.bitDepth == (PngPixel.bitDepth (α := px)).toNat ||
        (header.bitDepth == 16 && PngPixel.bitDepth (α := px) == u8 8) ||
        (header.bitDepth == 1 &&
          (PngPixel.bitDepth (α := px) == u8 8 ||
            PngPixel.bitDepth (α := px) == u8 16))) = true := by
    simp [hbitDepthEq]
  have hCtNot4 : (header.colorType == 4) = false := by
    rw [hSourceColorType]; decide
  have hCtIs6 : (header.colorType == 6) = true := by
    rw [hSourceColorType]; decide
  have hSourceNot1 : (header.bitDepth == 1) = false := by
    rw [hSourceBitDepth]; decide
  have hSourceNot16 : (header.bitDepth == 16) = false := by
    rw [hSourceBitDepth]; decide
  have hTargetIs8 : (PngPixel.bitDepth (α := px) == u8 8) = true := by
    rw [hTargetBitDepth]; decide
  have hTargetNot16 : (PngPixel.bitDepth (α := px) == u8 16) = false := by
    rw [hTargetBitDepth]; decide
  have hTargetIs2 : (PngPixel.colorType (α := px) == u8 2) = true := by
    rw [hTargetColorType]; decide
  have hTargetNot0 : (PngPixel.colorType (α := px) == u8 0) = false := by
    rw [hTargetColorType]; decide
  have hTargetNot4 : (PngPixel.colorType (α := px) == u8 4) = false := by
    rw [hTargetColorType]; decide
  have hTargetNot6 : (PngPixel.colorType (α := px) == u8 6) = false := by
    rw [hTargetColorType]; decide
  have hChrmGrayInactive :
      ({ PngMetadata.empty with background := some bg : PngMetadata }.srgb.isNone &&
        { PngMetadata.empty with background := some bg : PngMetadata }.chromaticities.isSome &&
        (header.colorType == 2 || header.colorType == 6) &&
        (PngPixel.colorType (α := px) == u8 0 ||
          PngPixel.colorType (α := px) == u8 4)) = false := by
    simp [PngMetadata.empty]
  have hRawNorm :
      normalizeRawByInterlace? inflatedRaw header
        (Pixel.bytesPerPixel (α := px)) = some inflatedRaw := by
    unfold normalizeRawByInterlace?; rw [hInterlace]; rfl
  have hTransform :
      applyPngColorSpaceTransform
        { PngMetadata.empty with background := some bg }
        header.colorType (PngPixel.colorType (α := px))
        (PngPixel.bitDepth (α := px)) bitmap.data = some bitmap.data := by
    unfold applyPngColorSpaceTransform; rfl
  have hValid : bitmap.data.size =
      bitmap.size.width * bitmap.size.height *
        Pixel.bytesPerPixel (α := px) := by simpa using bitmap.valid
  have hbdMatchEq : header.bitDepth = (PngPixel.bitDepth (α := px)).toNat := by
    rw [hSourceBitDepth, hTargetBitDepth]; decide
  have hRowsChain :
      ((decodeRowsLoopAlphaOverBackground bg inflatedRaw
            bitmap.size.width bitmap.size.height (Pixel.bytesPerPixel (α := px))
            (bitmap.size.width * Pixel.bytesPerPixel (α := px))
            0 0 ByteArray.empty
            { data := Array.replicate
                (bitmap.size.width * bitmap.size.height *
                  Pixel.bytesPerPixel (α := px)) 0 }).bind fun y ↦
        (applyPngColorSpaceTransform
            { PngMetadata.empty with background := some bg }
            header.colorType (PngPixel.colorType (α := px))
            (PngPixel.bitDepth (α := px)) y).bind fun pixels ↦
          if h : pixels.size = bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px) then
            some ({ bitmap := { size := { width := bitmap.size.width,
                                            height := bitmap.size.height },
                                  data := pixels, valid := h },
                    metadata := { PngMetadata.empty with background := some bg } } : PngDecodeResult px)
          else none) =
      some ({ bitmap := bitmap
              metadata := { PngMetadata.empty with background := some bg } } : PngDecodeResult px) := by
    rw [hPixels, Option.bind_some]
    rw [hTransform, Option.bind_some]
    simp [hValid]
  have hBppChain :
      ((pngBytesPerPixelForColorTypeAndBitDepth? header.colorType header.bitDepth).bind
        fun bpp ↦
          (normalizeRawByInterlace? inflatedRaw header bpp).bind fun raw ↦
            if raw.size = bitmap.size.height * (bitmap.size.width * bpp + 1) then
              (decodeRowsLoopAlphaOverBackground bg raw
                    bitmap.size.width bitmap.size.height bpp
                    (bitmap.size.width * bpp) 0 0 ByteArray.empty
                    { data := Array.replicate
                        (bitmap.size.width * bitmap.size.height *
                          Pixel.bytesPerPixel (α := px)) 0 }).bind fun y ↦
                (applyPngColorSpaceTransform
                    { PngMetadata.empty with background := some bg }
                    header.colorType (PngPixel.colorType (α := px))
                    (u8 8) y).bind fun pixels ↦
                  if h : pixels.size = bitmap.size.width * bitmap.size.height *
                      Pixel.bytesPerPixel (α := px) then
                    some ({ bitmap := { size := { width := bitmap.size.width,
                                                   height := bitmap.size.height },
                                         data := pixels, valid := h },
                            metadata := { PngMetadata.empty with background := some bg } } : PngDecodeResult px)
                  else none
            else none) =
        some ({ bitmap := bitmap
                metadata := { PngMetadata.empty with background := some bg } } : PngDecodeResult px) := by
    rw [hBppLookup]
    simp only [Option.bind_some]
    rw [hRawNorm, Option.bind_some]
    rw [if_pos hRawSize]
    rw [show (u8 8 : UInt8) = PngPixel.bitDepth (α := px) from hTargetBitDepth.symm]
    exact hRowsChain
  unfold Png.decodeBitmapWithMetadata Png.decodeParsedBitmapWithMetadata
  simp only [hSize, dite_true, hParse, Option.bind_eq_bind, Option.bind_some]
  rcases hInflated with hStored | ⟨hStoredNone, hZlib⟩
  · simpa [hctbdHdr, hSourceBitDepth, hTargetBitDepth, hSourceColorType,
      hTargetColorType, hbitDepthCompatible,
      hCtIs6, hCtNot4, hSourceNot1, hSourceNot16, hTargetIs8, hTargetNot16,
      hTargetIs2, hTargetNot0, hTargetNot4, hTargetNot6, hChrmGrayInactive,
      hWidth, hHeight, hInterlace, hIdatMin, hStored, PngMetadata.empty] using
      (And.intro hctbdHdr (And.intro hbdMatchEq hBppChain))
  · simpa [hctbdHdr, hSourceBitDepth, hTargetBitDepth, hSourceColorType,
      hTargetColorType, hbitDepthCompatible,
      hCtIs6, hCtNot4, hSourceNot1, hSourceNot16, hTargetIs8, hTargetNot16,
      hTargetIs2, hTargetNot0, hTargetNot4, hTargetNot6, hChrmGrayInactive,
      hWidth, hHeight, hInterlace, hIdatMin, hStoredNone, hZlib,
      PngMetadata.empty] using
      (And.intro hctbdHdr (And.intro hbdMatchEq hBppChain))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 4096 in
/-- tRNS forward-decode for RGB16 target (source = 16-bit, target = u8 16
RGB with tRNS + bg). Routes through `decodeRowsLoopTrnsOverBackground16`. -/
theorem decodeBitmapWithMetadata_correct_of_witnesses_trnsRgb16
    {px : Type u} [Pixel px] [PngPixel px]
    {bitmap : Bitmap px}
    {header : PngHeader} {idat : ByteArray}
    {trns : PngTransparency} {bg : PngBackground}
    {inflatedRaw : ByteArray}
    {bytes : ByteArray} (hSize : 8 ≤ bytes.size)
    (hSourceBitDepth : header.bitDepth = 16)
    (hTargetBitDepth : PngPixel.bitDepth (α := px) = u8 16)
    (hSourceColorType : header.colorType = 0 ∨ header.colorType = 2 ∨
      header.colorType = 4 ∨ header.colorType = 6)
    (hTargetColorType : PngPixel.colorType (α := px) = u8 2)
    (hWidth : header.width = bitmap.size.width)
    (hHeight : header.height = bitmap.size.height)
    (hInterlace : header.interlace = 0)
    (hPxColorType : PngPixel.colorType (α := px) = u8 header.colorType)
    (hBppLookup : pngBytesPerPixelForColorTypeAndBitDepth?
      header.colorType header.bitDepth = some (Pixel.bytesPerPixel (α := px)))
    (hParse : parsePngWithMetadata bytes hSize =
      some { header := header, idat := idat,
             metadata := { PngMetadata.empty with
                             transparency := some trns
                             background := some bg } })
    (hIdatMin : 2 ≤ idat.size)
    (hInflated :
      zlibDecompressStored idat hIdatMin = some inflatedRaw ∨
      (zlibDecompressStored idat hIdatMin = none ∧
       zlibDecompress idat hIdatMin = some inflatedRaw))
    (hRawSize :
      inflatedRaw.size = bitmap.size.height *
        (bitmap.size.width * Pixel.bytesPerPixel (α := px) + 1))
    (hPixels :
      decodeRowsLoopTrnsOverBackground16 trns bg header.colorType inflatedRaw
          bitmap.size.width bitmap.size.height (Pixel.bytesPerPixel (α := px))
          (bitmap.size.width * Pixel.bytesPerPixel (α := px))
          0 0 ByteArray.empty
          { data := Array.replicate
              (bitmap.size.width * bitmap.size.height *
                Pixel.bytesPerPixel (α := px)) 0 } =
        some bitmap.data) :
    Png.decodeBitmapWithMetadata bytes =
      some { bitmap := bitmap
             metadata := { PngMetadata.empty with
                             transparency := some trns
                             background := some bg } } := by
  have hbdNoReject : pngBitDepthSupported header.bitDepth = true := by
    rw [hSourceBitDepth]; decide
  have hctbdHdr :
      pngColorTypeBitDepthSupported header.colorType header.bitDepth = true := by
    rw [hSourceBitDepth]
    rcases hSourceColorType with h | h | h | h <;> rw [h] <;> decide
  have hbitDepthEq :
      (header.bitDepth == (PngPixel.bitDepth (α := px)).toNat) = true := by
    rw [hSourceBitDepth, hTargetBitDepth]; rfl
  have hbitDepthCompatible :
      (header.bitDepth == (PngPixel.bitDepth (α := px)).toNat ||
        (header.bitDepth == 16 && PngPixel.bitDepth (α := px) == u8 8) ||
        (header.bitDepth == 1 &&
          (PngPixel.bitDepth (α := px) == u8 8 ||
            PngPixel.bitDepth (α := px) == u8 16))) = true := by
    simp [hbitDepthEq]
  have hCtCases :
      ¬ header.colorType = 0 → ¬ header.colorType = 2 →
        ¬ header.colorType = 4 → header.colorType = 6 := by
    intro h0 h2 h4
    rcases hSourceColorType with hc | hc | hc | hc
    · exact absurd hc h0
    · exact absurd hc h2
    · exact absurd hc h4
    · exact hc
  have hSourceNot1 : (header.bitDepth == 1) = false := by rw [hSourceBitDepth]; decide
  have hSourceIs16 : (header.bitDepth == 16) = true := by rw [hSourceBitDepth]; decide
  have hTargetNot8 : (PngPixel.bitDepth (α := px) == u8 8) = false := by
    rw [hTargetBitDepth]; decide
  have hTargetIs16 : (PngPixel.bitDepth (α := px) == u8 16) = true := by
    rw [hTargetBitDepth]; decide
  have hTargetIs2 : (PngPixel.colorType (α := px) == u8 2) = true := by
    rw [hTargetColorType]; decide
  have hTargetNot6 : (PngPixel.colorType (α := px) == u8 6) = false := by
    rw [hTargetColorType]; decide
  have hTargetNot4 : (PngPixel.colorType (α := px) == u8 4) = false := by
    rw [hTargetColorType]; decide
  have hTargetNot0 : (PngPixel.colorType (α := px) == u8 0) = false := by
    rw [hTargetColorType]; decide
  have hChrmGrayInactive :
      ({ PngMetadata.empty with
           transparency := some trns
           background := some bg : PngMetadata }.srgb.isNone &&
        { PngMetadata.empty with
            transparency := some trns
            background := some bg : PngMetadata }.chromaticities.isSome &&
        (header.colorType == 2 || header.colorType == 6) &&
        (PngPixel.colorType (α := px) == u8 0 ||
          PngPixel.colorType (α := px) == u8 4)) = false := by
    simp [PngMetadata.empty]
  have hRawNorm :
      normalizeRawByInterlace? inflatedRaw header
        (Pixel.bytesPerPixel (α := px)) = some inflatedRaw := by
    unfold normalizeRawByInterlace?; rw [hInterlace]; rfl
  have hTransform :
      applyPngColorSpaceTransform
        { PngMetadata.empty with
            transparency := some trns, background := some bg }
        header.colorType (PngPixel.colorType (α := px))
        (PngPixel.bitDepth (α := px)) bitmap.data = some bitmap.data := by
    unfold applyPngColorSpaceTransform; rfl
  have hValid : bitmap.data.size =
      bitmap.size.width * bitmap.size.height *
        Pixel.bytesPerPixel (α := px) := by simpa using bitmap.valid
  have hbdMatchImpl : ¬ 16 = (u8 16).toNat → u8 16 = u8 8 := by
    intro h; exact absurd (by decide : (16 : Nat) = (u8 16).toNat) h
  have hPxIsU8_2 : u8 header.colorType = u8 2 := by
    rw [← hPxColorType, hTargetColorType]
  have hU16NeU8 : ¬ (u8 16 : UInt8) = u8 8 := by decide
  have hU8_2_ne_6 : ¬ (u8 2 : UInt8) = u8 6 := by decide
  have hRowsChain :
      ((decodeRowsLoopTrnsOverBackground16 trns bg header.colorType inflatedRaw
            bitmap.size.width bitmap.size.height (Pixel.bytesPerPixel (α := px))
            (bitmap.size.width * Pixel.bytesPerPixel (α := px))
            0 0 ByteArray.empty
            { data := Array.replicate
                (bitmap.size.width * bitmap.size.height *
                  Pixel.bytesPerPixel (α := px)) 0 }).bind fun y ↦
        (applyPngColorSpaceTransform
            { PngMetadata.empty with
                transparency := some trns, background := some bg }
            header.colorType (PngPixel.colorType (α := px))
            (PngPixel.bitDepth (α := px)) y).bind fun pixels ↦
          if h : pixels.size = bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px) then
            some ({ bitmap := { size := { width := bitmap.size.width,
                                            height := bitmap.size.height },
                                  data := pixels, valid := h },
                    metadata := { PngMetadata.empty with
                                    transparency := some trns
                                    background := some bg } } : PngDecodeResult px)
          else none) =
      some ({ bitmap := bitmap
              metadata := { PngMetadata.empty with
                              transparency := some trns
                              background := some bg } } : PngDecodeResult px) := by
    rw [hPixels, Option.bind_some]
    rw [hTransform, Option.bind_some]
    simp [hValid]
  have hBppChain :
      ((pngBytesPerPixelForColorTypeAndBitDepth? header.colorType header.bitDepth).bind
        fun bpp ↦
          (normalizeRawByInterlace? inflatedRaw header bpp).bind fun raw ↦
            if raw.size = bitmap.size.height * (bitmap.size.width * bpp + 1) then
              if u8 header.colorType = u8 6 then
                (if u8 16 = u8 8 then
                  decodeRowsLoopDown16ToRGBA8WithTransparency (some trns) header.colorType
                    raw bitmap.size.width bitmap.size.height bpp
                    (bitmap.size.width * bpp) 0 0 ByteArray.empty
                    { data := Array.replicate
                        (bitmap.size.width * bitmap.size.height *
                          Pixel.bytesPerPixel (α := px)) 0 }
                else
                  decodeRowsLoopRGBA16WithTransparency (some trns) header.colorType
                    raw bitmap.size.width bitmap.size.height bpp
                    (bitmap.size.width * bpp) 0 0 ByteArray.empty
                    { data := Array.replicate
                        (bitmap.size.width * bitmap.size.height *
                          Pixel.bytesPerPixel (α := px)) 0 }).bind fun y ↦
                  (applyPngColorSpaceTransform
                      { PngMetadata.empty with
                          transparency := some trns, background := some bg }
                      header.colorType (u8 header.colorType)
                      (u8 16) y).bind fun pixels ↦
                    if h : pixels.size = bitmap.size.width * bitmap.size.height *
                        Pixel.bytesPerPixel (α := px) then
                      some ({ bitmap := { size := { width := bitmap.size.width,
                                                     height := bitmap.size.height },
                                           data := pixels, valid := h },
                              metadata := { PngMetadata.empty with
                                              transparency := some trns
                                              background := some bg } } : PngDecodeResult px)
                    else none
              else if u8 header.colorType = u8 2 then
                (if u8 16 = u8 8 then
                  decodeRowsLoopDown16TrnsOverBackgroundRGB8 trns bg header.colorType
                    raw bitmap.size.width bitmap.size.height bpp
                    (bitmap.size.width * bpp) 0 0 ByteArray.empty
                    { data := Array.replicate
                        (bitmap.size.width * bitmap.size.height *
                          Pixel.bytesPerPixel (α := px)) 0 }
                else
                  decodeRowsLoopTrnsOverBackground16 trns bg header.colorType
                    raw bitmap.size.width bitmap.size.height bpp
                    (bitmap.size.width * bpp) 0 0 ByteArray.empty
                    { data := Array.replicate
                        (bitmap.size.width * bitmap.size.height *
                          Pixel.bytesPerPixel (α := px)) 0 }).bind fun y ↦
                  (applyPngColorSpaceTransform
                      { PngMetadata.empty with
                          transparency := some trns, background := some bg }
                      header.colorType (u8 header.colorType)
                      (u8 16) y).bind fun pixels ↦
                    if h : pixels.size = bitmap.size.width * bitmap.size.height *
                        Pixel.bytesPerPixel (α := px) then
                      some ({ bitmap := { size := { width := bitmap.size.width,
                                                     height := bitmap.size.height },
                                           data := pixels, valid := h },
                              metadata := { PngMetadata.empty with
                                              transparency := some trns
                                              background := some bg } } : PngDecodeResult px)
                    else none
              else none
            else none) =
        some ({ bitmap := bitmap
                metadata := { PngMetadata.empty with
                                transparency := some trns
                                background := some bg } } : PngDecodeResult px) := by
    rw [hBppLookup]
    simp only [Option.bind_some]
    rw [hRawNorm, Option.bind_some]
    rw [if_pos hRawSize]
    have hNotSix : ¬ u8 header.colorType = u8 6 := by
      intro h
      have : u8 2 = u8 6 := hPxIsU8_2 ▸ h
      exact hU8_2_ne_6 this
    rw [if_neg hNotSix, if_pos hPxIsU8_2, if_neg hU16NeU8]
    rw [show (u8 header.colorType) = PngPixel.colorType (α := px) from hPxColorType.symm]
    rw [show (u8 16 : UInt8) = PngPixel.bitDepth (α := px) from hTargetBitDepth.symm]
    exact hRowsChain
  unfold Png.decodeBitmapWithMetadata Png.decodeParsedBitmapWithMetadata
  simp only [hSize, dite_true, hParse, Option.bind_eq_bind, Option.bind_some]
  rcases hInflated with hStored | ⟨hStoredNone, hZlib⟩
  · simpa [hctbdHdr, hSourceBitDepth, hTargetBitDepth, hbitDepthCompatible,
      hSourceNot1, hSourceIs16, hTargetNot8, hTargetIs16, hTargetIs2,
      hTargetNot6, hTargetNot0, hTargetNot4, hChrmGrayInactive,
      hWidth, hHeight, hInterlace, hIdatMin, hStored, PngMetadata.empty,
      hPxColorType] using
      (And.intro hctbdHdr (And.intro hCtCases (And.intro hbdMatchImpl hBppChain)))
  · simpa [hctbdHdr, hSourceBitDepth, hTargetBitDepth, hbitDepthCompatible,
      hSourceNot1, hSourceIs16, hTargetNot8, hTargetIs16, hTargetIs2,
      hTargetNot6, hTargetNot0, hTargetNot4, hChrmGrayInactive,
      hWidth, hHeight, hInterlace, hIdatMin, hStoredNone, hZlib,
      PngMetadata.empty, hPxColorType] using
      (And.intro hctbdHdr (And.intro hCtCases (And.intro hbdMatchImpl hBppChain)))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 4096 in
/-- tRNS forward-decode for 16→8 RGB downsample (source = 16-bit RGB,
target = u8 8 RGB with tRNS + bg). Routes through
`decodeRowsLoopDown16TrnsOverBackgroundRGB8`. -/
theorem decodeBitmapWithMetadata_correct_of_witnesses_trnsRgb16To8
    {px : Type u} [Pixel px] [PngPixel px]
    {bitmap : Bitmap px}
    {header : PngHeader} {idat : ByteArray}
    {trns : PngTransparency} {bg : PngBackground}
    {inflatedRaw : ByteArray}
    {bytes : ByteArray} (hSize : 8 ≤ bytes.size)
    (hSourceBitDepth : header.bitDepth = 16)
    (hTargetBitDepth : PngPixel.bitDepth (α := px) = u8 8)
    (hSourceColorType : header.colorType = 0 ∨ header.colorType = 2 ∨
      header.colorType = 4 ∨ header.colorType = 6)
    (hTargetColorType : PngPixel.colorType (α := px) = u8 2)
    (hWidth : header.width = bitmap.size.width)
    (hHeight : header.height = bitmap.size.height)
    (hInterlace : header.interlace = 0)
    (hPxColorType : PngPixel.colorType (α := px) = u8 header.colorType)
    {sourceBpp : Nat}
    (hBppLookup : pngBytesPerPixelForColorTypeAndBitDepth?
      header.colorType 16 = some sourceBpp)
    (hParse : parsePngWithMetadata bytes hSize =
      some { header := header, idat := idat,
             metadata := { PngMetadata.empty with
                             transparency := some trns
                             background := some bg } })
    (hIdatMin : 2 ≤ idat.size)
    (hInflated :
      zlibDecompressStored idat hIdatMin = some inflatedRaw ∨
      (zlibDecompressStored idat hIdatMin = none ∧
       zlibDecompress idat hIdatMin = some inflatedRaw))
    (hRawSize :
      inflatedRaw.size = bitmap.size.height *
        (bitmap.size.width * sourceBpp + 1))
    (hPixels :
      decodeRowsLoopDown16TrnsOverBackgroundRGB8 trns bg header.colorType
          inflatedRaw bitmap.size.width bitmap.size.height
          sourceBpp (bitmap.size.width * sourceBpp)
          0 0 ByteArray.empty
          { data := Array.replicate
              (bitmap.size.width * bitmap.size.height *
                Pixel.bytesPerPixel (α := px)) 0 } =
        some bitmap.data) :
    Png.decodeBitmapWithMetadata bytes =
      some { bitmap := bitmap
             metadata := { PngMetadata.empty with
                             transparency := some trns
                             background := some bg } } := by
  have hbdNoReject : pngBitDepthSupported header.bitDepth = true := by
    rw [hSourceBitDepth]; decide
  have hctbdHdr :
      pngColorTypeBitDepthSupported header.colorType header.bitDepth = true := by
    rw [hSourceBitDepth]
    rcases hSourceColorType with h | h | h | h <;> rw [h] <;> decide
  have hbitDepthCompatible :
      (header.bitDepth == (PngPixel.bitDepth (α := px)).toNat ||
        (header.bitDepth == 16 && PngPixel.bitDepth (α := px) == u8 8) ||
        (header.bitDepth == 1 &&
          (PngPixel.bitDepth (α := px) == u8 8 ||
            PngPixel.bitDepth (α := px) == u8 16))) = true := by
    rw [hSourceBitDepth, hTargetBitDepth]; decide
  have hCtCases :
      ¬ header.colorType = 0 → ¬ header.colorType = 2 →
        ¬ header.colorType = 4 → header.colorType = 6 := by
    intro h0 h2 h4
    rcases hSourceColorType with hc | hc | hc | hc
    · exact absurd hc h0
    · exact absurd hc h2
    · exact absurd hc h4
    · exact hc
  have hSourceNot1 : (header.bitDepth == 1) = false := by rw [hSourceBitDepth]; decide
  have hSourceIs16 : (header.bitDepth == 16) = true := by rw [hSourceBitDepth]; decide
  have hTargetIs8 : (PngPixel.bitDepth (α := px) == u8 8) = true := by
    rw [hTargetBitDepth]; decide
  have hTargetNot16 : (PngPixel.bitDepth (α := px) == u8 16) = false := by
    rw [hTargetBitDepth]; decide
  have hTargetIs2 : (PngPixel.colorType (α := px) == u8 2) = true := by
    rw [hTargetColorType]; decide
  have hTargetNot6 : (PngPixel.colorType (α := px) == u8 6) = false := by
    rw [hTargetColorType]; decide
  have hTargetNot4 : (PngPixel.colorType (α := px) == u8 4) = false := by
    rw [hTargetColorType]; decide
  have hTargetNot0 : (PngPixel.colorType (α := px) == u8 0) = false := by
    rw [hTargetColorType]; decide
  have hChrmGrayInactive :
      ({ PngMetadata.empty with
           transparency := some trns
           background := some bg : PngMetadata }.srgb.isNone &&
        { PngMetadata.empty with
            transparency := some trns
            background := some bg : PngMetadata }.chromaticities.isSome &&
        (header.colorType == 2 || header.colorType == 6) &&
        (PngPixel.colorType (α := px) == u8 0 ||
          PngPixel.colorType (α := px) == u8 4)) = false := by
    simp [PngMetadata.empty]
  have hRawNorm :
      normalizeRawByInterlace? inflatedRaw header sourceBpp = some inflatedRaw := by
    unfold normalizeRawByInterlace?; rw [hInterlace]; rfl
  have hTransform :
      applyPngColorSpaceTransform
        { PngMetadata.empty with
            transparency := some trns, background := some bg }
        header.colorType (PngPixel.colorType (α := px))
        (PngPixel.bitDepth (α := px)) bitmap.data = some bitmap.data := by
    unfold applyPngColorSpaceTransform; rfl
  have hValid : bitmap.data.size =
      bitmap.size.width * bitmap.size.height *
        Pixel.bytesPerPixel (α := px) := by simpa using bitmap.valid
  have hPxIsU8_2 : u8 header.colorType = u8 2 := by
    rw [← hPxColorType, hTargetColorType]
  have hU8_2_ne_6 : ¬ (u8 2 : UInt8) = u8 6 := by decide
  have hRowsChain :
      ((decodeRowsLoopDown16TrnsOverBackgroundRGB8 trns bg header.colorType
            inflatedRaw bitmap.size.width bitmap.size.height
            sourceBpp (bitmap.size.width * sourceBpp)
            0 0 ByteArray.empty
            { data := Array.replicate
                (bitmap.size.width * bitmap.size.height *
                  Pixel.bytesPerPixel (α := px)) 0 }).bind fun y ↦
        (applyPngColorSpaceTransform
            { PngMetadata.empty with
                transparency := some trns, background := some bg }
            header.colorType (PngPixel.colorType (α := px))
            (PngPixel.bitDepth (α := px)) y).bind fun pixels ↦
          if h : pixels.size = bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px) then
            some ({ bitmap := { size := { width := bitmap.size.width,
                                            height := bitmap.size.height },
                                  data := pixels, valid := h },
                    metadata := { PngMetadata.empty with
                                    transparency := some trns
                                    background := some bg } } : PngDecodeResult px)
          else none) =
      some ({ bitmap := bitmap
              metadata := { PngMetadata.empty with
                              transparency := some trns
                              background := some bg } } : PngDecodeResult px) := by
    rw [hPixels, Option.bind_some]
    rw [hTransform, Option.bind_some]
    simp [hValid]
  have hbdMatchImpl : ¬ 16 = (u8 8).toNat → u8 8 = u8 8 := fun _ => rfl
  have hBppChain :
      ((pngBytesPerPixelForColorTypeAndBitDepth? header.colorType header.bitDepth).bind
        fun bpp ↦
          (normalizeRawByInterlace? inflatedRaw header bpp).bind fun raw ↦
            if raw.size = bitmap.size.height * (bitmap.size.width * bpp + 1) then
              if u8 header.colorType = u8 6 then
                (if u8 8 = u8 8 then
                  decodeRowsLoopDown16ToRGBA8WithTransparency (some trns) header.colorType
                    raw bitmap.size.width bitmap.size.height bpp
                    (bitmap.size.width * bpp) 0 0 ByteArray.empty
                    { data := Array.replicate
                        (bitmap.size.width * bitmap.size.height *
                          Pixel.bytesPerPixel (α := px)) 0 }
                else
                  decodeRowsLoopRGBA16WithTransparency (some trns) header.colorType
                    raw bitmap.size.width bitmap.size.height bpp
                    (bitmap.size.width * bpp) 0 0 ByteArray.empty
                    { data := Array.replicate
                        (bitmap.size.width * bitmap.size.height *
                          Pixel.bytesPerPixel (α := px)) 0 }).bind fun y ↦
                  (applyPngColorSpaceTransform
                      { PngMetadata.empty with
                          transparency := some trns, background := some bg }
                      header.colorType (u8 header.colorType)
                      (u8 8) y).bind fun pixels ↦
                    if h : pixels.size = bitmap.size.width * bitmap.size.height *
                        Pixel.bytesPerPixel (α := px) then
                      some ({ bitmap := { size := { width := bitmap.size.width,
                                                     height := bitmap.size.height },
                                           data := pixels, valid := h },
                              metadata := { PngMetadata.empty with
                                              transparency := some trns
                                              background := some bg } } : PngDecodeResult px)
                    else none
              else if u8 header.colorType = u8 2 then
                (if u8 8 = u8 8 then
                  decodeRowsLoopDown16TrnsOverBackgroundRGB8 trns bg header.colorType
                    raw bitmap.size.width bitmap.size.height bpp
                    (bitmap.size.width * bpp) 0 0 ByteArray.empty
                    { data := Array.replicate
                        (bitmap.size.width * bitmap.size.height *
                          Pixel.bytesPerPixel (α := px)) 0 }
                else
                  decodeRowsLoopTrnsOverBackground16 trns bg header.colorType
                    raw bitmap.size.width bitmap.size.height bpp
                    (bitmap.size.width * bpp) 0 0 ByteArray.empty
                    { data := Array.replicate
                        (bitmap.size.width * bitmap.size.height *
                          Pixel.bytesPerPixel (α := px)) 0 }).bind fun y ↦
                  (applyPngColorSpaceTransform
                      { PngMetadata.empty with
                          transparency := some trns, background := some bg }
                      header.colorType (u8 header.colorType)
                      (u8 8) y).bind fun pixels ↦
                    if h : pixels.size = bitmap.size.width * bitmap.size.height *
                        Pixel.bytesPerPixel (α := px) then
                      some ({ bitmap := { size := { width := bitmap.size.width,
                                                     height := bitmap.size.height },
                                           data := pixels, valid := h },
                              metadata := { PngMetadata.empty with
                                              transparency := some trns
                                              background := some bg } } : PngDecodeResult px)
                    else none
              else none
            else none) =
        some ({ bitmap := bitmap
                metadata := { PngMetadata.empty with
                                transparency := some trns
                                background := some bg } } : PngDecodeResult px) := by
    rw [hSourceBitDepth, hBppLookup]
    simp only [Option.bind_some]
    rw [hRawNorm, Option.bind_some]
    rw [if_pos hRawSize]
    have hNotSix : ¬ u8 header.colorType = u8 6 := by
      intro h
      have : u8 2 = u8 6 := hPxIsU8_2 ▸ h
      exact hU8_2_ne_6 this
    rw [if_neg hNotSix, if_pos hPxIsU8_2]
    simp only [if_true]
    rw [show (u8 header.colorType) = PngPixel.colorType (α := px) from hPxColorType.symm]
    rw [show (u8 8 : UInt8) = PngPixel.bitDepth (α := px) from hTargetBitDepth.symm]
    exact hRowsChain
  unfold Png.decodeBitmapWithMetadata Png.decodeParsedBitmapWithMetadata
  simp only [hSize, dite_true, hParse, Option.bind_eq_bind, Option.bind_some]
  rcases hInflated with hStored | ⟨hStoredNone, hZlib⟩
  · simpa [hctbdHdr, hSourceBitDepth, hTargetBitDepth, hbitDepthCompatible,
      hSourceNot1, hSourceIs16, hTargetIs8, hTargetNot16, hTargetIs2,
      hTargetNot6, hTargetNot0, hTargetNot4, hChrmGrayInactive,
      hWidth, hHeight, hInterlace, hIdatMin, hStored, PngMetadata.empty,
      hPxColorType] using
      (And.intro hctbdHdr (And.intro hCtCases (And.intro hbdMatchImpl hBppChain)))
  · simpa [hctbdHdr, hSourceBitDepth, hTargetBitDepth, hbitDepthCompatible,
      hSourceNot1, hSourceIs16, hTargetIs8, hTargetNot16, hTargetIs2,
      hTargetNot6, hTargetNot0, hTargetNot4, hChrmGrayInactive,
      hWidth, hHeight, hInterlace, hIdatMin, hStoredNone, hZlib,
      PngMetadata.empty, hPxColorType] using
      (And.intro hctbdHdr (And.intro hCtCases (And.intro hbdMatchImpl hBppChain)))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 4096 in
/-- AlphaOverBackground for source-colorType-4 (gray+alpha) →
target-colorType-0 (gray), source bd=16, target = u8 16. Routes
through `decodeRowsLoopGrayAlphaOverBackground16`. -/
theorem decodeBitmapWithMetadata_correct_of_witnesses_alphaBgGray16
    {px : Type u} [Pixel px] [PngPixel px]
    {bitmap : Bitmap px}
    {header : PngHeader} {idat : ByteArray} {bg : PngBackground}
    {inflatedRaw : ByteArray}
    {bytes : ByteArray} (hSize : 8 ≤ bytes.size)
    (hSourceBitDepth : header.bitDepth = 16)
    (hTargetBitDepth : PngPixel.bitDepth (α := px) = u8 16)
    (hSourceColorType : header.colorType = 4)
    (hTargetColorType : PngPixel.colorType (α := px) = u8 0)
    (hWidth : header.width = bitmap.size.width)
    (hHeight : header.height = bitmap.size.height)
    (hInterlace : header.interlace = 0)
    (hBppLookup : pngBytesPerPixelForColorTypeAndBitDepth?
      header.colorType header.bitDepth = some (Pixel.bytesPerPixel (α := px)))
    (hParse : parsePngWithMetadata bytes hSize =
      some { header := header, idat := idat,
             metadata := { PngMetadata.empty with background := some bg } })
    (hIdatMin : 2 ≤ idat.size)
    (hInflated :
      zlibDecompressStored idat hIdatMin = some inflatedRaw ∨
      (zlibDecompressStored idat hIdatMin = none ∧
       zlibDecompress idat hIdatMin = some inflatedRaw))
    (hRawSize :
      inflatedRaw.size = bitmap.size.height *
        (bitmap.size.width * Pixel.bytesPerPixel (α := px) + 1))
    (hPixels :
      decodeRowsLoopGrayAlphaOverBackground16 bg header.colorType inflatedRaw
          bitmap.size.width bitmap.size.height (Pixel.bytesPerPixel (α := px))
          (bitmap.size.width * Pixel.bytesPerPixel (α := px))
          0 0 ByteArray.empty
          { data := Array.replicate
              (bitmap.size.width * bitmap.size.height *
                Pixel.bytesPerPixel (α := px)) 0 } =
        some bitmap.data) :
    Png.decodeBitmapWithMetadata bytes =
      some { bitmap := bitmap
             metadata := { PngMetadata.empty with background := some bg } } := by
  have hbdNoReject : pngBitDepthSupported header.bitDepth = true := by
    rw [hSourceBitDepth]; decide
  have hctbdHdr :
      pngColorTypeBitDepthSupported header.colorType header.bitDepth = true := by
    rw [hSourceBitDepth, hSourceColorType]; decide
  have hbitDepthEq :
      (header.bitDepth == (PngPixel.bitDepth (α := px)).toNat) = true := by
    rw [hSourceBitDepth, hTargetBitDepth]; rfl
  have hbitDepthCompatible :
      (header.bitDepth == (PngPixel.bitDepth (α := px)).toNat ||
        (header.bitDepth == 16 && PngPixel.bitDepth (α := px) == u8 8) ||
        (header.bitDepth == 1 &&
          (PngPixel.bitDepth (α := px) == u8 8 ||
            PngPixel.bitDepth (α := px) == u8 16))) = true := by
    simp [hbitDepthEq]
  have hCtIs4 : (header.colorType == 4) = true := by rw [hSourceColorType]; decide
  have hCtNot6 : (header.colorType == 6) = false := by rw [hSourceColorType]; decide
  have hSourceNot1 : (header.bitDepth == 1) = false := by rw [hSourceBitDepth]; decide
  have hSourceIs16 : (header.bitDepth == 16) = true := by rw [hSourceBitDepth]; decide
  have hTargetNot8 : (PngPixel.bitDepth (α := px) == u8 8) = false := by
    rw [hTargetBitDepth]; decide
  have hTargetIs16 : (PngPixel.bitDepth (α := px) == u8 16) = true := by
    rw [hTargetBitDepth]; decide
  have hTargetNot6 : (PngPixel.colorType (α := px) == u8 6) = false := by
    rw [hTargetColorType]; decide
  have hTargetNot2 : (PngPixel.colorType (α := px) == u8 2) = false := by
    rw [hTargetColorType]; decide
  have hTargetIs0 : (PngPixel.colorType (α := px) == u8 0) = true := by
    rw [hTargetColorType]; decide
  have hTargetNot4 : (PngPixel.colorType (α := px) == u8 4) = false := by
    rw [hTargetColorType]; decide
  have hChrmGrayInactive :
      ({ PngMetadata.empty with background := some bg : PngMetadata }.srgb.isNone &&
        { PngMetadata.empty with background := some bg : PngMetadata }.chromaticities.isSome &&
        (header.colorType == 2 || header.colorType == 6) &&
        (PngPixel.colorType (α := px) == u8 0 ||
          PngPixel.colorType (α := px) == u8 4)) = false := by
    simp [PngMetadata.empty]
  have hRawNorm :
      normalizeRawByInterlace? inflatedRaw header
        (Pixel.bytesPerPixel (α := px)) = some inflatedRaw := by
    unfold normalizeRawByInterlace?; rw [hInterlace]; rfl
  have hTransform :
      applyPngColorSpaceTransform
        { PngMetadata.empty with background := some bg }
        header.colorType (PngPixel.colorType (α := px))
        (PngPixel.bitDepth (α := px)) bitmap.data = some bitmap.data := by
    unfold applyPngColorSpaceTransform; rfl
  have hValid : bitmap.data.size =
      bitmap.size.width * bitmap.size.height *
        Pixel.bytesPerPixel (α := px) := by simpa using bitmap.valid
  have hbdMatchImpl : ¬ 16 = (u8 16).toNat → u8 16 = u8 8 := by
    intro h; exact absurd (by decide : (16 : Nat) = (u8 16).toNat) h
  have hU16NeU8 : ¬ (u8 16 : UInt8) = u8 8 := by decide
  have hRowsChain :
      ((decodeRowsLoopGrayAlphaOverBackground16 bg header.colorType inflatedRaw
            bitmap.size.width bitmap.size.height (Pixel.bytesPerPixel (α := px))
            (bitmap.size.width * Pixel.bytesPerPixel (α := px))
            0 0 ByteArray.empty
            { data := Array.replicate
                (bitmap.size.width * bitmap.size.height *
                  Pixel.bytesPerPixel (α := px)) 0 }).bind fun y ↦
        (applyPngColorSpaceTransform
            { PngMetadata.empty with background := some bg }
            header.colorType (PngPixel.colorType (α := px))
            (PngPixel.bitDepth (α := px)) y).bind fun pixels ↦
          if h : pixels.size = bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px) then
            some ({ bitmap := { size := { width := bitmap.size.width,
                                            height := bitmap.size.height },
                                  data := pixels, valid := h },
                    metadata := { PngMetadata.empty with background := some bg } } : PngDecodeResult px)
          else none) =
      some ({ bitmap := bitmap
              metadata := { PngMetadata.empty with background := some bg } } : PngDecodeResult px) := by
    rw [hPixels, Option.bind_some]
    rw [hTransform, Option.bind_some]
    simp [hValid]
  have hPxNot2 : ¬ PngPixel.colorType (α := px) = u8 2 := by
    rw [hTargetColorType]; decide
  have hBppChain :
      ((pngBytesPerPixelForColorTypeAndBitDepth? header.colorType header.bitDepth).bind
        fun bpp ↦
          (normalizeRawByInterlace? inflatedRaw header bpp).bind fun raw ↦
            if raw.size = bitmap.size.height * (bitmap.size.width * bpp + 1) then
              if (PngPixel.colorType (α := px)) = u8 2 then
                if u8 16 = u8 8 then
                  (decodeRowsLoopDown16AlphaOverBackgroundRGB8 bg header.colorType
                        raw bitmap.size.width bitmap.size.height bpp
                        (bitmap.size.width * bpp) 0 0 ByteArray.empty
                        { data := Array.replicate
                            (bitmap.size.width * bitmap.size.height *
                              Pixel.bytesPerPixel (α := px)) 0 }).bind fun y ↦
                    (applyPngColorSpaceTransform
                        { PngMetadata.empty with background := some bg }
                        header.colorType (PngPixel.colorType (α := px))
                        (u8 16) y).bind fun pixels ↦
                      if h : pixels.size = bitmap.size.width * bitmap.size.height *
                          Pixel.bytesPerPixel (α := px) then
                        some ({ bitmap := { size := { width := bitmap.size.width,
                                                       height := bitmap.size.height },
                                             data := pixels, valid := h },
                                metadata := { PngMetadata.empty with background := some bg } } : PngDecodeResult px)
                      else none
                else
                  (decodeRowsLoopAlphaOverBackground16 bg header.colorType
                        raw bitmap.size.width bitmap.size.height bpp
                        (bitmap.size.width * bpp) 0 0 ByteArray.empty
                        { data := Array.replicate
                            (bitmap.size.width * bitmap.size.height *
                              Pixel.bytesPerPixel (α := px)) 0 }).bind fun y ↦
                    (applyPngColorSpaceTransform
                        { PngMetadata.empty with background := some bg }
                        header.colorType (PngPixel.colorType (α := px))
                        (u8 16) y).bind fun pixels ↦
                      if h : pixels.size = bitmap.size.width * bitmap.size.height *
                          Pixel.bytesPerPixel (α := px) then
                        some ({ bitmap := { size := { width := bitmap.size.width,
                                                       height := bitmap.size.height },
                                             data := pixels, valid := h },
                                metadata := { PngMetadata.empty with background := some bg } } : PngDecodeResult px)
                      else none
              else
                if u8 16 = u8 8 then
                  (decodeRowsLoopDown16GrayAlphaOverBackgroundGray8 bg header.colorType
                        raw bitmap.size.width bitmap.size.height bpp
                        (bitmap.size.width * bpp) 0 0 ByteArray.empty
                        { data := Array.replicate
                            (bitmap.size.width * bitmap.size.height *
                              Pixel.bytesPerPixel (α := px)) 0 }).bind fun y ↦
                    (applyPngColorSpaceTransform
                        { PngMetadata.empty with background := some bg }
                        header.colorType (PngPixel.colorType (α := px))
                        (u8 16) y).bind fun pixels ↦
                      if h : pixels.size = bitmap.size.width * bitmap.size.height *
                          Pixel.bytesPerPixel (α := px) then
                        some ({ bitmap := { size := { width := bitmap.size.width,
                                                       height := bitmap.size.height },
                                             data := pixels, valid := h },
                                metadata := { PngMetadata.empty with background := some bg } } : PngDecodeResult px)
                      else none
                else
                  (decodeRowsLoopGrayAlphaOverBackground16 bg header.colorType
                        raw bitmap.size.width bitmap.size.height bpp
                        (bitmap.size.width * bpp) 0 0 ByteArray.empty
                        { data := Array.replicate
                            (bitmap.size.width * bitmap.size.height *
                              Pixel.bytesPerPixel (α := px)) 0 }).bind fun y ↦
                    (applyPngColorSpaceTransform
                        { PngMetadata.empty with background := some bg }
                        header.colorType (PngPixel.colorType (α := px))
                        (u8 16) y).bind fun pixels ↦
                      if h : pixels.size = bitmap.size.width * bitmap.size.height *
                          Pixel.bytesPerPixel (α := px) then
                        some ({ bitmap := { size := { width := bitmap.size.width,
                                                       height := bitmap.size.height },
                                             data := pixels, valid := h },
                                metadata := { PngMetadata.empty with background := some bg } } : PngDecodeResult px)
                      else none
            else none) =
        some ({ bitmap := bitmap
                metadata := { PngMetadata.empty with background := some bg } } : PngDecodeResult px) := by
    rw [hBppLookup]
    simp only [Option.bind_some]
    rw [hRawNorm, Option.bind_some]
    rw [if_pos hRawSize, if_neg hPxNot2, if_neg hU16NeU8]
    rw [show (u8 16 : UInt8) = PngPixel.bitDepth (α := px) from hTargetBitDepth.symm]
    exact hRowsChain
  unfold Png.decodeBitmapWithMetadata Png.decodeParsedBitmapWithMetadata
  simp only [hSize, dite_true, hParse, Option.bind_eq_bind, Option.bind_some]
  rcases hInflated with hStored | ⟨hStoredNone, hZlib⟩
  · simpa [hctbdHdr, hSourceBitDepth, hTargetBitDepth, hSourceColorType,
      hTargetColorType, hbitDepthCompatible,
      hCtIs4, hCtNot6, hSourceNot1, hSourceIs16, hTargetNot8, hTargetIs16,
      hTargetIs0, hTargetNot2, hTargetNot4, hTargetNot6, hChrmGrayInactive,
      hWidth, hHeight, hInterlace, hIdatMin, hStored, PngMetadata.empty] using
      (And.intro hctbdHdr (And.intro hbdMatchImpl hBppChain))
  · simpa [hctbdHdr, hSourceBitDepth, hTargetBitDepth, hSourceColorType,
      hTargetColorType, hbitDepthCompatible,
      hCtIs4, hCtNot6, hSourceNot1, hSourceIs16, hTargetNot8, hTargetIs16,
      hTargetIs0, hTargetNot2, hTargetNot4, hTargetNot6, hChrmGrayInactive,
      hWidth, hHeight, hInterlace, hIdatMin, hStoredNone, hZlib,
      PngMetadata.empty] using
      (And.intro hctbdHdr (And.intro hbdMatchImpl hBppChain))

/-- The rejection core: any byte stream whose parsed metadata has
`transparency.isSome = true` is rejected by `decodeBitmap`. This is
the end-to-end story for `tRNS`: combined with a container-layer
theorem proving the parser records the transparency, this closes
the decoder behavior.

Note that the witness fields needed are far fewer than the success
case — no zlib / row-filter / color-space transform reasoning is
required because `decodeBitmap`'s early-return on transparency
fires before those steps. -/
theorem decodeBitmap_rejects_of_transparency
    {px : Type u} [Pixel px] [PngPixel px]
    {header : PngHeader} {idat : ByteArray} {metadata : PngMetadata}
    {bytes : ByteArray} (hSize : 8 ≤ bytes.size)
    (hParse : parsePngForDecode bytes hSize =
      some { header := header, idat := idat, metadata := metadata })
    (hTransparency : metadata.transparency.isSome = true) :
    Png.decodeBitmap (px := px) bytes = none := by
  unfold Png.decodeBitmap
  simp [hSize, hParse, hTransparency]

end Lemmas

end Bitmaps
