import Bitmap.Lemmas.Png.Palette

namespace Bitmaps

namespace Lemmas

open Png

/-! ## Symbolic palette transparency/background expansion facts

These theorems generalize the concrete palette `tRNS`/`bKGD` runtime fixtures:
they prove the expansion branch for arbitrary palette entries, alpha payloads,
and palette background indices on a one-sample indexed image. -/

private lemma singleton_index_get! (idx : UInt8) :
    (ByteArray.mk #[idx]).get! 0 = idx := by
  simp [ByteArray.get!]

/-- Palette `tRNS` plus a valid palette `bKGD` composites arbitrary RGB8 output.
This is the symbolic version of the palette transparency/background RGB fixture. -/
lemma expandPaletteIndicesToPixels_paletteAlpha_bKGD_RGB8_singleton
    (idx bgIdx r g b br bg bb : UInt8) (alpha : ByteArray) (palette : PngPalette)
    (hrgb : palette.rgbAt? idx.toNat = some (r, g, b))
    (hbg : palette.rgbAt? bgIdx.toNat = some (br, bg, bb)) :
    expandPaletteIndicesToPixels (ByteArray.mk #[idx]) palette
      { PngMetadata.empty with
        transparency := some (.paletteAlpha alpha)
        background := some (.paletteIndex bgIdx) }
      (u8 2) (u8 8) =
        some (ByteArray.mk #[
          alphaCompositeByte r br (paletteAlphaAt (some alpha) idx.toNat),
          alphaCompositeByte g bg (paletteAlphaAt (some alpha) idx.toNat),
          alphaCompositeByte b bb (paletteAlphaAt (some alpha) idx.toNat)]) := by
  have hget := singleton_index_get! idx
  unfold expandPaletteIndicesToPixels expandPaletteIndicesToPixels8
  simp [paletteAlphaBytes?, paletteBackgroundRGB?,
    Std.Legacy.Range.forIn_eq_forIn_range', ByteArray.size, hget, hrgb, hbg, u8,
    bytesPerPixelRGB]
  rfl

/-- Palette `tRNS` without a valid background rejects RGB8 expansion.
This pins the non-alpha-target policy independently of concrete fixtures. -/
lemma expandPaletteIndicesToPixels_paletteAlpha_no_bKGD_RGB8_singleton
    (idx r g b : UInt8) (alpha : ByteArray) (palette : PngPalette)
    (hrgb : palette.rgbAt? idx.toNat = some (r, g, b)) :
    expandPaletteIndicesToPixels (ByteArray.mk #[idx]) palette
      { PngMetadata.empty with transparency := some (.paletteAlpha alpha) }
      (u8 2) (u8 8) = none := by
  have hget := singleton_index_get! idx
  unfold expandPaletteIndicesToPixels expandPaletteIndicesToPixels8
  simp [PngMetadata.empty, paletteAlphaBytes?, paletteBackgroundRGB?,
    Std.Legacy.Range.forIn_eq_forIn_range', ByteArray.size, hget, hrgb, u8,
    bytesPerPixelRGB]
  rfl

/-- Palette `tRNS` plus a valid palette `bKGD` composites arbitrary Gray8 output.
This covers the grayscale non-alpha branch that also requires a background. -/
lemma expandPaletteIndicesToPixels_paletteAlpha_bKGD_Gray8_singleton
    (idx bgIdx r g b br bg bb : UInt8) (alpha : ByteArray) (palette : PngPalette)
    (hrgb : palette.rgbAt? idx.toNat = some (r, g, b))
    (hbg : palette.rgbAt? bgIdx.toNat = some (br, bg, bb)) :
    expandPaletteIndicesToPixels (ByteArray.mk #[idx]) palette
      { PngMetadata.empty with
        transparency := some (.paletteAlpha alpha)
        background := some (.paletteIndex bgIdx) }
      (u8 0) (u8 8) =
        some (ByteArray.mk #[
          grayFromRGB8
            (alphaCompositeByte r br (paletteAlphaAt (some alpha) idx.toNat))
            (alphaCompositeByte g bg (paletteAlphaAt (some alpha) idx.toNat))
            (alphaCompositeByte b bb (paletteAlphaAt (some alpha) idx.toNat))]) := by
  have hget := singleton_index_get! idx
  unfold expandPaletteIndicesToPixels expandPaletteIndicesToPixels8
  simp [paletteAlphaBytes?, paletteBackgroundRGB?,
    Std.Legacy.Range.forIn_eq_forIn_range', ByteArray.size, hget, hrgb, hbg, u8,
    bytesPerPixelGray]
  rfl

/-- Palette `tRNS` without a valid background rejects Gray8 expansion.
This is the grayscale analogue of the RGB8 non-alpha rejection policy. -/
lemma expandPaletteIndicesToPixels_paletteAlpha_no_bKGD_Gray8_singleton
    (idx r g b : UInt8) (alpha : ByteArray) (palette : PngPalette)
    (hrgb : palette.rgbAt? idx.toNat = some (r, g, b)) :
    expandPaletteIndicesToPixels (ByteArray.mk #[idx]) palette
      { PngMetadata.empty with transparency := some (.paletteAlpha alpha) }
      (u8 0) (u8 8) = none := by
  have hget := singleton_index_get! idx
  unfold expandPaletteIndicesToPixels expandPaletteIndicesToPixels8
  simp [PngMetadata.empty, paletteAlphaBytes?, paletteBackgroundRGB?,
    Std.Legacy.Range.forIn_eq_forIn_range', ByteArray.size, hget, hrgb, u8,
    bytesPerPixelGray]
  rfl

/-- Palette `tRNS` expands directly to RGBA8 alpha output without requiring
`bKGD`. This proves the alpha-target branch for arbitrary palette data. -/
lemma expandPaletteIndicesToPixels_paletteAlpha_RGBA8_singleton
    (idx r g b : UInt8) (alpha : ByteArray) (palette : PngPalette)
    (hrgb : palette.rgbAt? idx.toNat = some (r, g, b)) :
    expandPaletteIndicesToPixels (ByteArray.mk #[idx]) palette
      { PngMetadata.empty with transparency := some (.paletteAlpha alpha) }
      (u8 6) (u8 8) =
        some (ByteArray.mk #[r, g, b, paletteAlphaAt (some alpha) idx.toNat]) := by
  have hget := singleton_index_get! idx
  unfold expandPaletteIndicesToPixels expandPaletteIndicesToPixels8
  simp [paletteAlphaBytes?,
    Std.Legacy.Range.forIn_eq_forIn_range', ByteArray.size, hget, hrgb, u8,
    bytesPerPixelRGBA]
  rfl

/-- Palette `tRNS` expands directly to GrayAlpha8 without requiring `bKGD`.
This proves the grayscale alpha-target branch for arbitrary palette data. -/
lemma expandPaletteIndicesToPixels_paletteAlpha_GrayAlpha8_singleton
    (idx r g b : UInt8) (alpha : ByteArray) (palette : PngPalette)
    (hrgb : palette.rgbAt? idx.toNat = some (r, g, b)) :
    expandPaletteIndicesToPixels (ByteArray.mk #[idx]) palette
      { PngMetadata.empty with transparency := some (.paletteAlpha alpha) }
      (u8 4) (u8 8) =
        some (ByteArray.mk #[
          grayFromRGB8 r g b,
          paletteAlphaAt (some alpha) idx.toNat]) := by
  have hget := singleton_index_get! idx
  unfold expandPaletteIndicesToPixels expandPaletteIndicesToPixels8
  simp [paletteAlphaBytes?,
    Std.Legacy.Range.forIn_eq_forIn_range', ByteArray.size, hget, hrgb, u8,
    bytesPerPixelGrayAlpha]
  rfl

/-- Palette `tRNS` plus `bKGD` composites arbitrary RGB16 output using the
same full-range `u8 * 257` channel expansion as non-transparent palette data. -/
lemma expandPaletteIndicesToPixels_paletteAlpha_bKGD_RGB16_singleton
    (idx bgIdx r g b br bg bb : UInt8) (alpha : ByteArray) (palette : PngPalette)
    (hrgb : palette.rgbAt? idx.toNat = some (r, g, b))
    (hbg : palette.rgbAt? bgIdx.toNat = some (br, bg, bb)) :
    expandPaletteIndicesToPixels (ByteArray.mk #[idx]) palette
      { PngMetadata.empty with
        transparency := some (.paletteAlpha alpha)
        background := some (.paletteIndex bgIdx) }
      (u8 2) (u8 16) =
        some
          (pushU16Full
            (pushU16Full
              (pushU16Full ByteArray.empty
                (alphaCompositeByte r br (paletteAlphaAt (some alpha) idx.toNat)))
              (alphaCompositeByte g bg (paletteAlphaAt (some alpha) idx.toNat)))
            (alphaCompositeByte b bb (paletteAlphaAt (some alpha) idx.toNat))) := by
  have hget := singleton_index_get! idx
  unfold expandPaletteIndicesToPixels expandPaletteIndicesToPixels16
  simp [paletteAlphaBytes?, paletteBackgroundRGB?,
    Std.Legacy.Range.forIn_eq_forIn_range', ByteArray.size, hget, hrgb, hbg, u8,
    bytesPerPixelRGB16]
  rfl

/-- Palette `tRNS` expands directly to RGBA16 alpha output without requiring
`bKGD`. This is the 16-bit alpha-target counterpart of the RGBA8 theorem. -/
lemma expandPaletteIndicesToPixels_paletteAlpha_RGBA16_singleton
    (idx r g b : UInt8) (alpha : ByteArray) (palette : PngPalette)
    (hrgb : palette.rgbAt? idx.toNat = some (r, g, b)) :
    expandPaletteIndicesToPixels (ByteArray.mk #[idx]) palette
      { PngMetadata.empty with transparency := some (.paletteAlpha alpha) }
      (u8 6) (u8 16) =
        some
          (pushU16Full
            (pushU16Full
              (pushU16Full
                (pushU16Full ByteArray.empty r)
                g)
              b)
            (paletteAlphaAt (some alpha) idx.toNat)) := by
  have hget := singleton_index_get! idx
  unfold expandPaletteIndicesToPixels expandPaletteIndicesToPixels16
  simp [paletteAlphaBytes?,
    Std.Legacy.Range.forIn_eq_forIn_range', ByteArray.size, hget, hrgb, u8,
    bytesPerPixelRGBA16]
  rfl

end Lemmas

end Bitmaps
