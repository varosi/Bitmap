import Bitmap.Lemmas.Png.Palette

namespace Bitmaps

namespace Lemmas

open Png

/-! ## Symbolic palette transparency/background expansion facts

These theorems generalize the concrete palette `tRNS`/`bKGD` runtime fixtures:
they prove the expansion branch for arbitrary palette entries, alpha payloads,
palette background indices, and indexed image data. -/

/-- Symbolic 8-bit palette expansion over an arbitrary index buffer. This records
plain `PLTE` expansion, optional `tRNS` alpha, and optional resolved `bKGD`. -/
def paletteExpansion8Spec (indices : ByteArray) (palette : PngPalette)
    (alpha? : Option ByteArray) (background? : Option (UInt8 × UInt8 × UInt8))
    (targetColorType : UInt8) : Option ByteArray :=
  Id.run do
    let count := indices.size
    let outBpp :=
      if targetColorType == u8 0 then Gray8.bytesPerPixel
      else if targetColorType == u8 2 then RGB8.bytesPerPixel
      else if targetColorType == u8 4 then GrayAlpha8.bytesPerPixel
      else if targetColorType == u8 6 then RGBA8.bytesPerPixel
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

/-- Symbolic 8-bit palette-alpha expansion over an arbitrary index buffer.
This records how `tRNS` and an optional resolved `bKGD` affect each output byte. -/
def paletteAlphaExpansion8Spec (indices : ByteArray) (palette : PngPalette)
    (alpha : ByteArray) (background? : Option (UInt8 × UInt8 × UInt8))
    (targetColorType : UInt8) : Option ByteArray :=
  paletteExpansion8Spec indices palette (some alpha) background? targetColorType

/-- Symbolic 16-bit palette expansion over an arbitrary index buffer. This is the
full-range `u8 * 257` counterpart of `paletteExpansion8Spec`. -/
def paletteExpansion16Spec (indices : ByteArray) (palette : PngPalette)
    (alpha? : Option ByteArray) (background? : Option (UInt8 × UInt8 × UInt8))
    (targetColorType : UInt8) : Option ByteArray :=
  Id.run do
    let count := indices.size
    let outBpp :=
      if targetColorType == u8 0 then Gray16.bytesPerPixel
      else if targetColorType == u8 2 then RGB16.bytesPerPixel
      else if targetColorType == u8 4 then GrayAlpha16.bytesPerPixel
      else if targetColorType == u8 6 then RGBA16.bytesPerPixel
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

/-- Symbolic 16-bit palette-alpha expansion over an arbitrary index buffer.
This is the full-range `u8 * 257` counterpart of `paletteAlphaExpansion8Spec`. -/
def paletteAlphaExpansion16Spec (indices : ByteArray) (palette : PngPalette)
    (alpha : ByteArray) (background? : Option (UInt8 × UInt8 × UInt8))
    (targetColorType : UInt8) : Option ByteArray :=
  paletteExpansion16Spec indices palette (some alpha) background? targetColorType

/-- The 8-bit implementation agrees with the symbolic palette expansion spec for
plain `PLTE`, palette `tRNS`, and palette `bKGD` cases over every index buffer. -/
lemma expandPaletteIndicesToPixels8_symbolic
    (indices : ByteArray) (palette : PngPalette) (alpha? : Option ByteArray)
    (background? : Option (UInt8 × UInt8 × UInt8)) (targetColorType : UInt8) :
    expandPaletteIndicesToPixels8 indices palette alpha? background? targetColorType =
      paletteExpansion8Spec indices palette alpha? background? targetColorType := by
  rfl

/-- The 16-bit implementation agrees with the symbolic palette expansion spec for
all supported target formats, using full-range `u8 * 257` sample expansion. -/
lemma expandPaletteIndicesToPixels16_symbolic
    (indices : ByteArray) (palette : PngPalette) (alpha? : Option ByteArray)
    (background? : Option (UInt8 × UInt8 × UInt8)) (targetColorType : UInt8) :
    expandPaletteIndicesToPixels16 indices palette alpha? background? targetColorType =
      paletteExpansion16Spec indices palette alpha? background? targetColorType := by
  rfl

/-- When metadata contributes no palette alpha and no palette background, public
palette expansion is exactly the symbolic plain-`PLTE` expansion for 8/16-bit
RGB, gray, RGBA, and gray-alpha targets. -/
lemma expandPaletteIndicesToPixels_plain_symbolic
    (indices : ByteArray) (palette : PngPalette) (metadata : PngMetadata)
    (targetColorType targetBitDepth : UInt8)
    (halpha : paletteAlphaBytes? metadata = none)
    (hbackground : paletteBackgroundRGB? palette metadata = none) :
    expandPaletteIndicesToPixels indices palette metadata targetColorType targetBitDepth =
        if targetBitDepth == u8 8 then
          paletteExpansion8Spec indices palette none none targetColorType
        else if targetBitDepth == u8 16 then
          paletteExpansion16Spec indices palette none none targetColorType
        else
          none := by
  unfold expandPaletteIndicesToPixels
  simp [halpha, hbackground, expandPaletteIndicesToPixels8_symbolic,
    expandPaletteIndicesToPixels16_symbolic]

/-- Palette-only metadata, the normal metadata shape after parsing `PLTE` without
`tRNS`/`bKGD`, expands symbolically for every target color type and bit depth. -/
lemma expandPaletteIndicesToPixels_paletteOnly_symbolic
    (indices : ByteArray) (palette : PngPalette)
    (targetColorType targetBitDepth : UInt8) :
    expandPaletteIndicesToPixels indices palette
      { PngMetadata.empty with palette := some palette }
      targetColorType targetBitDepth =
        if targetBitDepth == u8 8 then
          paletteExpansion8Spec indices palette none none targetColorType
        else if targetBitDepth == u8 16 then
          paletteExpansion16Spec indices palette none none targetColorType
        else
          none := by
  exact
    expandPaletteIndicesToPixels_plain_symbolic indices palette
      { PngMetadata.empty with palette := some palette } targetColorType targetBitDepth
      (by simp [PngMetadata.empty, paletteAlphaBytes?])
      (by simp [PngMetadata.empty, paletteBackgroundRGB?])

/-- Plain palette expansion to RGB8 is the symbolic `PLTE` RGB byte stream for
every indexed image, not just the runtime RGB8 fixture. -/
lemma expandPaletteIndicesToPixels_paletteOnly_RGB8_symbolic
    (indices : ByteArray) (palette : PngPalette) :
    expandPaletteIndicesToPixels indices palette
      { PngMetadata.empty with palette := some palette } (u8 2) (u8 8) =
        paletteExpansion8Spec indices palette none none (u8 2) := by
  simpa [u8] using
    expandPaletteIndicesToPixels_paletteOnly_symbolic indices palette (u8 2) (u8 8)

/-- Plain palette expansion to Gray8 is the symbolic grayscale conversion of
every looked-up `PLTE` entry. -/
lemma expandPaletteIndicesToPixels_paletteOnly_Gray8_symbolic
    (indices : ByteArray) (palette : PngPalette) :
    expandPaletteIndicesToPixels indices palette
      { PngMetadata.empty with palette := some palette } (u8 0) (u8 8) =
        paletteExpansion8Spec indices palette none none (u8 0) := by
  simpa [u8] using
    expandPaletteIndicesToPixels_paletteOnly_symbolic indices palette (u8 0) (u8 8)

/-- Plain palette expansion to RGBA8 appends the default opaque alpha byte for
every indexed image. -/
lemma expandPaletteIndicesToPixels_paletteOnly_RGBA8_symbolic
    (indices : ByteArray) (palette : PngPalette) :
    expandPaletteIndicesToPixels indices palette
      { PngMetadata.empty with palette := some palette } (u8 6) (u8 8) =
        paletteExpansion8Spec indices palette none none (u8 6) := by
  simpa [u8] using
    expandPaletteIndicesToPixels_paletteOnly_symbolic indices palette (u8 6) (u8 8)

/-- Plain palette expansion to GrayAlpha8 combines symbolic grayscale conversion
with the default opaque alpha byte for every indexed image. -/
lemma expandPaletteIndicesToPixels_paletteOnly_GrayAlpha8_symbolic
    (indices : ByteArray) (palette : PngPalette) :
    expandPaletteIndicesToPixels indices palette
      { PngMetadata.empty with palette := some palette } (u8 4) (u8 8) =
        paletteExpansion8Spec indices palette none none (u8 4) := by
  simpa [u8] using
    expandPaletteIndicesToPixels_paletteOnly_symbolic indices palette (u8 4) (u8 8)

/-- Plain palette expansion to RGB16 is the symbolic full-range expansion of
each looked-up RGB palette sample. -/
lemma expandPaletteIndicesToPixels_paletteOnly_RGB16_symbolic
    (indices : ByteArray) (palette : PngPalette) :
    expandPaletteIndicesToPixels indices palette
      { PngMetadata.empty with palette := some palette } (u8 2) (u8 16) =
        paletteExpansion16Spec indices palette none none (u8 2) := by
  simpa [u8] using
    expandPaletteIndicesToPixels_paletteOnly_symbolic indices palette (u8 2) (u8 16)

/-- Plain palette expansion to Gray16 is the symbolic full-range expansion of the
grayscale conversion of every `PLTE` entry. -/
lemma expandPaletteIndicesToPixels_paletteOnly_Gray16_symbolic
    (indices : ByteArray) (palette : PngPalette) :
    expandPaletteIndicesToPixels indices palette
      { PngMetadata.empty with palette := some palette } (u8 0) (u8 16) =
        paletteExpansion16Spec indices palette none none (u8 0) := by
  simpa [u8] using
    expandPaletteIndicesToPixels_paletteOnly_symbolic indices palette (u8 0) (u8 16)

/-- Plain palette expansion to RGBA16 adds a full-range opaque alpha sample after
the symbolic full-range RGB samples. -/
lemma expandPaletteIndicesToPixels_paletteOnly_RGBA16_symbolic
    (indices : ByteArray) (palette : PngPalette) :
    expandPaletteIndicesToPixels indices palette
      { PngMetadata.empty with palette := some palette } (u8 6) (u8 16) =
        paletteExpansion16Spec indices palette none none (u8 6) := by
  simpa [u8] using
    expandPaletteIndicesToPixels_paletteOnly_symbolic indices palette (u8 6) (u8 16)

/-- Plain palette expansion to GrayAlpha16 combines symbolic full-range grayscale
conversion with a full-range opaque alpha sample. -/
lemma expandPaletteIndicesToPixels_paletteOnly_GrayAlpha16_symbolic
    (indices : ByteArray) (palette : PngPalette) :
    expandPaletteIndicesToPixels indices palette
      { PngMetadata.empty with palette := some palette } (u8 4) (u8 16) =
        paletteExpansion16Spec indices palette none none (u8 4) := by
  simpa [u8] using
    expandPaletteIndicesToPixels_paletteOnly_symbolic indices palette (u8 4) (u8 16)

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
    RGB8.bytesPerPixel]
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
    RGB8.bytesPerPixel]
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
    Gray8.bytesPerPixel]
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
    Gray8.bytesPerPixel]
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
    RGBA8.bytesPerPixel]
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
    GrayAlpha8.bytesPerPixel]
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
    RGB16.bytesPerPixel]
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
    RGBA16.bytesPerPixel]
  rfl

end Lemmas

end Bitmaps
