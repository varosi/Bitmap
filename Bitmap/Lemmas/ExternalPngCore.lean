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
