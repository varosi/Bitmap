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
  decoder-layer witnesses line up), returning `some bitmap`.
* `decodeBitmap_rejects_of_transparency` — rejects (returns `none`)
  whenever the parsed metadata has `transparency.isSome = true`.
  This handles `tRNS`-bearing byte streams: the parser accepts the
  chunk via `parsePngLoopFuelWithMetadata_accepts_tRNS`, the
  container-layer theorem (`parsePngForDecode_…_correct`) records
  the transparency, and this lemma then closes the end-to-end
  story with the decoder's deliberate `transparency.isSome` guard.

Each per-spec end-to-end theorem (`decodeBitmap_external_*_correct`)
is a one-line corollary that supplies the witnesses for the matching
core. -/

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 4096 in
/-- The decode-side core: every byte stream whose decoder-layer
witnesses line up with the bitmap is accepted by `decodeBitmap`. -/
theorem decodeBitmap_correct_of_witnesses
    {px : Type u} [Pixel px] [PngPixel px]
    {bitmap : Bitmap px}
    {header : PngHeader} {idat : ByteArray} {metadata : PngMetadata}
    {inflatedRaw preTransformPixels : ByteArray}
    {bytes : ByteArray} (hSize : 8 ≤ bytes.size)
    (hBitDepth : header.bitDepth = 8)
    (hColorType : header.colorType = 0 ∨ header.colorType = 2 ∨
      header.colorType = 4 ∨ header.colorType = 6)
    (hWidth : header.width = bitmap.size.width)
    (hHeight : header.height = bitmap.size.height)
    (hInterlace : header.interlace = 0)
    (hPxColorType : PngPixel.colorType (α := px) = u8 header.colorType)
    (hTargetBitDepth : PngPixel.bitDepth (α := px) = u8 8)
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
        (u8 8) preTransformPixels = some bitmap.data) :
    Png.decodeBitmap bytes = some bitmap := by
  let ct := (PngPixel.colorType (α := px)).toNat
  let bd := (PngPixel.bitDepth (α := px)).toNat
  let bpp := Pixel.bytesPerPixel (α := px)
  have hbd_8 : bd = 8 := by
    show (PngPixel.bitDepth (α := px)).toNat = 8
    rw [hTargetBitDepth]; decide
  have hBdNot1' : ¬ bd = 1 := by rw [hbd_8]; decide
  have hbdNoReject : pngBitDepthSupported bd = true := by rw [hbd_8]; decide
  have hbitDepthEq :
      ((PngPixel.bitDepth (α := px)).toNat != bd) = false := by simp [bd]
  have hbitDepthEqHeader :
      (bd != (PngPixel.bitDepth (α := px)).toNat) = false := by simp [bd]
  have hnoDownsample :
      ¬((PngPixel.bitDepth (α := px)).toNat = 16 ∧
        PngPixel.bitDepth (α := px) = u8 8) := by
    rintro ⟨h16, _⟩
    rw [hTargetBitDepth] at h16
    revert h16; decide
  have hct'eq : ct = header.colorType := by
    show (PngPixel.colorType (α := px)).toNat = header.colorType
    rw [hPxColorType]
    rcases hColorType with h | h | h | h <;> rw [h] <;> decide
  have hct' : ct = 0 ∨ ct = 2 ∨ ct = 4 ∨ ct = 6 := by rw [hct'eq]; exact hColorType
  have hctNoReject :
      ct = 4 → ¬ PngPixel.colorType (α := px) = u8 4 →
        PngPixel.colorType (α := px) = u8 6 := by
    intro h4 hne
    have hCtH : header.colorType = 4 := by rw [← hct'eq]; exact h4
    have : PngPixel.colorType (α := px) = u8 4 := by rw [hPxColorType, hCtH]
    exact absurd this hne
  have hCt4Reject :
      header.colorType = 4 → ¬ PngPixel.colorType (α := px) = u8 4 →
        PngPixel.colorType (α := px) = u8 6 := by
    intro h4 hne
    have : PngPixel.colorType (α := px) = u8 4 := by rw [hPxColorType, h4]
    exact absurd this hne
  have hctbd' : pngColorTypeBitDepthSupported ct bd = true := by
    rw [hct'eq, hbd_8]
    rcases hColorType with h | h | h | h <;> rw [h] <;> decide
  have hpngBpp' : pngBytesPerPixelForColorTypeAndBitDepth? ct bd = some bpp := by
    rw [hct'eq, hbd_8, ← hBitDepth]; exact hBppLookup
  have hCtCases :
      ¬ header.colorType = 0 → ¬ header.colorType = 2 →
        ¬ header.colorType = 4 → header.colorType = 6 := by
    intro h0 h2 h4
    rcases hColorType with hc | hc | hc | hc
    · exact absurd hc h0
    · exact absurd hc h2
    · exact absurd hc h4
    · exact hc
  have hctbdHdr8 :
      pngColorTypeBitDepthSupported header.colorType 8 = true := by
    rcases hColorType with h | h | h | h <;> rw [h] <;> decide
  have h8eq : (8 : Nat) = (u8 8).toNat := by decide
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
              (PngPixel.colorType (α := px)) (u8 8) decodedPixels).bind
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
      ((pngBytesPerPixelForColorTypeAndBitDepth? header.colorType 8).bind
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
                    (u8 8) y).bind
                  fun pixels ↦
                    if h : pixels.size = bitmap.size.width * bitmap.size.height *
                        Pixel.bytesPerPixel (α := px) then
                      some { size := { width := bitmap.size.width,
                                       height := bitmap.size.height },
                             data := pixels, valid := h }
                    else none
          else none) = some bitmap := by
    have hBpp8 : pngBytesPerPixelForColorTypeAndBitDepth?
        header.colorType 8 = some (Pixel.bytesPerPixel (α := px)) := by
      rw [← hBitDepth]; exact hBppLookup
    rw [hBpp8]
    simp only [Option.bind_some]
    rw [if_pos hRawSize]
    exact hrowsEq
  unfold Png.decodeBitmap
  rcases hInflated with hStored | ⟨hStoredNone, hZlib⟩
  · simpa [hSize, hParse, hStored,
      ct, bd, hbdNoReject, hbitDepthEq, hbitDepthEqHeader, hnoDownsample, hpngBpp',
      hctbd', hBdNot1', normalizeRawByInterlace?,
      hIdatMin, hInterlace, hWidth, hHeight, hBitDepth,
      hTargetBitDepth, hChrmGrayInactive] using
      (And.intro hMetaTransparency
        (And.intro hctbdHdr8
          (And.intro hCtCases
            (And.intro h8eq
              (And.intro hCt4Reject hBppChain)))))
  · simpa [hSize, hParse, hStoredNone, hZlib,
      ct, bd, hbdNoReject, hbitDepthEq, hbitDepthEqHeader, hnoDownsample, hpngBpp',
      hctbd', hBdNot1', normalizeRawByInterlace?,
      hIdatMin, hInterlace, hWidth, hHeight, hBitDepth,
      hTargetBitDepth, hChrmGrayInactive] using
      (And.intro hMetaTransparency
        (And.intro hctbdHdr8
          (And.intro hCtCases
            (And.intro h8eq
              (And.intro hCt4Reject hBppChain)))))

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
