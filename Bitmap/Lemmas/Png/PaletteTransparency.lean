import Bitmap.Lemmas.Png.Palette

namespace Bitmaps

namespace Lemmas

open Png

/-! ## Symbolic palette transparency/background expansion facts

These theorems generalize the concrete palette `tRNS`/`bKGD` runtime fixtures:
they prove the expansion branch for arbitrary palette entries, alpha payloads,
palette background indices, and indexed image data. -/

/-- Symbolic 8-bit palette-alpha expansion over an arbitrary index buffer.
This records how `tRNS` and an optional resolved `bKGD` affect each output byte. -/
def paletteAlphaExpansion8Spec (indices : ByteArray) (palette : PngPalette)
    (alpha : ByteArray) (background? : Option (UInt8 × UInt8 × UInt8))
    (targetColorType : UInt8) : Option ByteArray :=
  Id.run do
    let alpha? := some alpha
    let count := indices.size
    let outBpp :=
      if targetColorType == u8 0 then bytesPerPixelGray
      else if targetColorType == u8 2 then bytesPerPixelRGB
      else if targetColorType == u8 4 then bytesPerPixelGrayAlpha
      else if targetColorType == u8 6 then bytesPerPixelRGBA
      else 0
    if outBpp == 0 then
      none
    else
      let needsBackground :=
        alpha?.isSome && (targetColorType == u8 0 || targetColorType == u8 2)
      let mut out := ByteArray.emptyWithCapacity (count * outBpp)
      let mut ok := true
      for i in [0:count] do
        let idx := (indices.get! i).toNat
        match palette.rgbAt? idx with
        | some (r0, g0, b0) =>
            let a := paletteAlphaAt alpha? idx
            let mut r := r0
            let mut g := g0
            let mut b := b0
            if needsBackground then
              match background? with
              | some (br, bg, bb) =>
                  r := alphaCompositeByte r0 br a
                  g := alphaCompositeByte g0 bg a
                  b := alphaCompositeByte b0 bb a
              | none =>
                  ok := false
            if targetColorType == u8 0 then
              out := out.push (grayFromRGB8 r g b)
            else if targetColorType == u8 2 then
              out := out.push r
              out := out.push g
              out := out.push b
            else if targetColorType == u8 4 then
              out := out.push (grayFromRGB8 r g b)
              out := out.push a
            else
              out := out.push r
              out := out.push g
              out := out.push b
              out := out.push a
        | none =>
            ok := false
      if ok then
        some out
      else
        none

/-- Symbolic 16-bit palette-alpha expansion over an arbitrary index buffer.
This is the full-range `u8 * 257` counterpart of `paletteAlphaExpansion8Spec`. -/
def paletteAlphaExpansion16Spec (indices : ByteArray) (palette : PngPalette)
    (alpha : ByteArray) (background? : Option (UInt8 × UInt8 × UInt8))
    (targetColorType : UInt8) : Option ByteArray :=
  Id.run do
    let alpha? := some alpha
    let count := indices.size
    let outBpp :=
      if targetColorType == u8 0 then bytesPerPixelGray16
      else if targetColorType == u8 2 then bytesPerPixelRGB16
      else if targetColorType == u8 4 then bytesPerPixelGrayAlpha16
      else if targetColorType == u8 6 then bytesPerPixelRGBA16
      else 0
    if outBpp == 0 then
      none
    else
      let needsBackground :=
        alpha?.isSome && (targetColorType == u8 0 || targetColorType == u8 2)
      let mut out := ByteArray.emptyWithCapacity (count * outBpp)
      let mut ok := true
      for i in [0:count] do
        let idx := (indices.get! i).toNat
        match palette.rgbAt? idx with
        | some (r0, g0, b0) =>
            let a := paletteAlphaAt alpha? idx
            let mut r := r0
            let mut g := g0
            let mut b := b0
            if needsBackground then
              match background? with
              | some (br, bg, bb) =>
                  r := alphaCompositeByte r0 br a
                  g := alphaCompositeByte g0 bg a
                  b := alphaCompositeByte b0 bb a
              | none =>
                  ok := false
            if targetColorType == u8 0 then
              out := pushU16Full out (grayFromRGB8 r g b)
            else if targetColorType == u8 2 then
              out := pushU16Full out r
              out := pushU16Full out g
              out := pushU16Full out b
            else if targetColorType == u8 4 then
              out := pushU16Full out (grayFromRGB8 r g b)
              out := pushU16Full out a
            else
              out := pushU16Full out r
              out := pushU16Full out g
              out := pushU16Full out b
              out := pushU16Full out a
        | none =>
            ok := false
      if ok then
        some out
      else
        none

/-- The 8-bit implementation agrees with the symbolic palette-alpha expansion
spec for every index buffer and every target color type. -/
lemma expandPaletteIndicesToPixels8_paletteAlpha_symbolic
    (indices : ByteArray) (palette : PngPalette) (alpha : ByteArray)
    (background? : Option (UInt8 × UInt8 × UInt8)) (targetColorType : UInt8) :
    expandPaletteIndicesToPixels8 indices palette (some alpha) background? targetColorType =
      paletteAlphaExpansion8Spec indices palette alpha background? targetColorType := by
  rfl

/-- The 16-bit implementation agrees with the symbolic palette-alpha expansion
spec for every index buffer and every target color type. -/
lemma expandPaletteIndicesToPixels16_paletteAlpha_symbolic
    (indices : ByteArray) (palette : PngPalette) (alpha : ByteArray)
    (background? : Option (UInt8 × UInt8 × UInt8)) (targetColorType : UInt8) :
    expandPaletteIndicesToPixels16 indices palette (some alpha) background? targetColorType =
      paletteAlphaExpansion16Spec indices palette alpha background? targetColorType := by
  rfl

/-- Palette `tRNS` without a palette `bKGD` has an all-image symbolic expansion
for every supported output bit depth and target color type. -/
lemma expandPaletteIndicesToPixels_paletteAlpha_no_bKGD_symbolic
    (indices : ByteArray) (palette : PngPalette) (alpha : ByteArray)
    (targetColorType targetBitDepth : UInt8) :
    expandPaletteIndicesToPixels indices palette
      { PngMetadata.empty with transparency := some (.paletteAlpha alpha) }
      targetColorType targetBitDepth =
        if targetBitDepth == u8 8 then
          paletteAlphaExpansion8Spec indices palette alpha none targetColorType
        else if targetBitDepth == u8 16 then
          paletteAlphaExpansion16Spec indices palette alpha none targetColorType
        else
          none := by
  unfold expandPaletteIndicesToPixels
  simp [PngMetadata.empty, paletteAlphaBytes?, paletteBackgroundRGB?,
    expandPaletteIndicesToPixels8_paletteAlpha_symbolic,
    expandPaletteIndicesToPixels16_paletteAlpha_symbolic]

/-- Palette `tRNS` plus a valid palette `bKGD` has an all-image symbolic
expansion for every supported output bit depth and target color type. -/
lemma expandPaletteIndicesToPixels_paletteAlpha_bKGD_symbolic
    (indices : ByteArray) (palette : PngPalette) (alpha : ByteArray)
    (bgIdx br bg bb targetColorType targetBitDepth : UInt8)
    (hbg : palette.rgbAt? bgIdx.toNat = some (br, bg, bb)) :
    expandPaletteIndicesToPixels indices palette
      { PngMetadata.empty with
        transparency := some (.paletteAlpha alpha)
        background := some (.paletteIndex bgIdx) }
      targetColorType targetBitDepth =
        if targetBitDepth == u8 8 then
          paletteAlphaExpansion8Spec indices palette alpha (some (br, bg, bb)) targetColorType
        else if targetBitDepth == u8 16 then
          paletteAlphaExpansion16Spec indices palette alpha (some (br, bg, bb)) targetColorType
        else
          none := by
  unfold expandPaletteIndicesToPixels
  simp [paletteAlphaBytes?, paletteBackgroundRGB?, hbg,
    expandPaletteIndicesToPixels8_paletteAlpha_symbolic,
    expandPaletteIndicesToPixels16_paletteAlpha_symbolic]

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
