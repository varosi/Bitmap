import Bitmap.Png

namespace Bitmaps

namespace Lemmas

open Png

/-! ## Packed indexed-palette public API examples

These computational theorems exercise the public checked indexed encoder and
both indexed decode APIs for packed 1-, 2-, and 4-bit palette rows.  They
complement the general 8-bit proof by pinning the packed paths end to end. -/

namespace PalettePackedRoundTrip

private def palette2 : PngPalette :=
  { entries := ByteArray.mk #[
      u8 0, u8 0, u8 0,
      u8 255, u8 255, u8 255] }

private def palette4 : PngPalette :=
  { entries := ByteArray.mk #[
      u8 0, u8 0, u8 0,
      u8 85, u8 0, u8 0,
      u8 0, u8 85, u8 0,
      u8 0, u8 0, u8 85] }

private def palette16 : PngPalette :=
  { entries := ByteArray.mk #[
      u8 0, u8 0, u8 0,
      u8 17, u8 0, u8 0,
      u8 34, u8 0, u8 0,
      u8 51, u8 0, u8 0,
      u8 68, u8 0, u8 0,
      u8 85, u8 0, u8 0,
      u8 102, u8 0, u8 0,
      u8 119, u8 0, u8 0,
      u8 136, u8 0, u8 0,
      u8 153, u8 0, u8 0,
      u8 170, u8 0, u8 0,
      u8 187, u8 0, u8 0,
      u8 204, u8 0, u8 0,
      u8 221, u8 0, u8 0,
      u8 238, u8 0, u8 0,
      u8 255, u8 0, u8 0] }

private def indexed1 : PngIndexedBitmap :=
  { size := { width := 8, height := 1 }
    bitDepth := 1
    palette := palette2
    data := ByteArray.mk #[u8 0, u8 1, u8 0, u8 1, u8 1, u8 0, u8 1, u8 0]
    transparency := none
    background := none
    valid := by native_decide }

private def indexed2 : PngIndexedBitmap :=
  { size := { width := 4, height := 1 }
    bitDepth := 2
    palette := palette4
    data := ByteArray.mk #[u8 0, u8 1, u8 2, u8 3]
    transparency := none
    background := none
    valid := by native_decide }

private def indexed4 : PngIndexedBitmap :=
  { size := { width := 4, height := 1 }
    bitDepth := 4
    palette := palette16
    data := ByteArray.mk #[u8 0, u8 3, u8 12, u8 15]
    transparency := none
    background := none
    valid := by native_decide }

private def indexed8 : PngIndexedBitmap :=
  { size := { width := 4, height := 1 }
    bitDepth := 8
    palette := palette16
    data := ByteArray.mk #[u8 0, u8 3, u8 12, u8 15]
    transparency := none
    background := none
    valid := by native_decide }

private def fixturePaletteRGB (idx : Nat) : UInt8 × UInt8 × UInt8 :=
  match idx with
  | 0 => (u8 0, u8 0, u8 0)
  | 1 => (u8 220, u8 20, u8 30)
  | 2 => (u8 20, u8 180, u8 70)
  | 3 => (u8 30, u8 60, u8 210)
  | n => (u8 (17 * n + 11), u8 (29 * n + 7), u8 (43 * n + 19))

private def fixturePaletteEntries (count : Nat) : ByteArray :=
  Id.run do
    let mut out := ByteArray.emptyWithCapacity (count * 3)
    for i in [0:count] do
      let (r, g, b) := fixturePaletteRGB i
      out := out.push r
      out := out.push g
      out := out.push b
    return out

private def fixturePalette (count : Nat) : PngPalette :=
  { entries := fixturePaletteEntries count }

private def fixtureIndex (entryCount x y : Nat) : UInt8 :=
  u8 ((x * 3 + y * 5 + x * y) % entryCount)

private def fixtureData (w h entryCount : Nat) : ByteArray :=
  ByteArray.mk <| Array.ofFn (fun i : Fin (w * h) =>
    let x := i.val % w
    let y := i.val / w
    fixtureIndex entryCount x y)

private def fixtureBitmap (w h bitDepth entryCount : Nat)
    (transparency : Option ByteArray := none) (background : Option UInt8 := none) :
    PngIndexedBitmap :=
  let data := fixtureData w h entryCount
  have hvalid : data.size = w * h := by
    simp [data, fixtureData, ByteArray.size]
  { size := { width := w, height := h }
    bitDepth
    palette := fixturePalette entryCount
    data
    transparency
    background
    valid := hvalid }

private def fixturePngWithChunks (w h bitDepth interlace : Nat)
    (preIdat : ByteArray) (raw : ByteArray) : ByteArray :=
  let ihdr := u32be w ++ u32be h ++
    ByteArray.mk #[u8 bitDepth, u8 3, u8 0, u8 0, u8 interlace]
  pngSignature ++ mkChunkBytes ihdrTypeBytes ihdr ++ preIdat ++
    mkChunkBytes idatTypeBytes (zlibCompressFixed raw) ++
    mkChunkBytes iendTypeBytes ByteArray.empty

private def fixturePngWithSplitIdat (w h bitDepth interlace : Nat)
    (preIdat : ByteArray) (raw : ByteArray) : ByteArray :=
  let ihdr := u32be w ++ u32be h ++
    ByteArray.mk #[u8 bitDepth, u8 3, u8 0, u8 0, u8 interlace]
  let idat := zlibCompressFixed raw
  let split := idat.size / 2
  pngSignature ++ mkChunkBytes ihdrTypeBytes ihdr ++ preIdat ++
    mkChunkBytes idatTypeBytes (idat.extract 0 split) ++
    mkChunkBytes idatTypeBytes (idat.extract split idat.size) ++
    mkChunkBytes iendTypeBytes ByteArray.empty

private def packFixtureRowFromFn (width bitDepth : Nat) (f : Nat -> UInt8) :
    ByteArray :=
  Id.run do
    let rowBytes := paletteRowBytes width bitDepth
    let mut row := ByteArray.mk <| Array.replicate rowBytes 0
    for x in [0:width] do
      row := palettePackIndexIntoRow row bitDepth x (f x)
    return row

private def fixtureAdam7Raw (w h bitDepth entryCount : Nat) : ByteArray :=
  Id.run do
    let mut raw := ByteArray.empty
    for pass in adam7Passes do
      let passWidth := adam7PassDim w pass.startX pass.stepX
      let passHeight :=
        if passWidth == 0 then
          0
        else
          adam7PassDim h pass.startY pass.stepY
      for passY in [0:passHeight] do
        raw := raw.push 0
        raw := raw ++ packFixtureRowFromFn passWidth bitDepth (fun passX =>
          let x := pass.startX + passX * pass.stepX
          let y := pass.startY + passY * pass.stepY
          fixtureIndex entryCount x y)
    return raw

private def fixtureAlphaAt (alpha? : Option ByteArray) (idx : Nat) : UInt8 :=
  match alpha? with
  | some alpha =>
      if idx < alpha.size then alpha.get! idx else 0xff
  | none => 0xff

private def fixtureExpectedRGBA8Data (w h entryCount : Nat)
    (alpha? : Option ByteArray := none) : ByteArray :=
  Id.run do
    let mut out := ByteArray.emptyWithCapacity (w * h * bytesPerPixelRGBA)
    for y in [0:h] do
      for x in [0:w] do
        let idx := (fixtureIndex entryCount x y).toNat
        let (r, g, b) := fixturePaletteRGB idx
        out := out.push r
        out := out.push g
        out := out.push b
        out := out.push (fixtureAlphaAt alpha? idx)
    return out

private def fixtureExpectedRGB8Data (w h entryCount : Nat)
    (alpha? : Option ByteArray := none) (background? : Option UInt8 := none) :
    ByteArray :=
  Id.run do
    let mut out := ByteArray.emptyWithCapacity (w * h * bytesPerPixelRGB)
    let bgRGB :=
      match background? with
      | some bg => fixturePaletteRGB bg.toNat
      | none => (u8 0, u8 0, u8 0)
    for y in [0:h] do
      for x in [0:w] do
        let idx := (fixtureIndex entryCount x y).toNat
        let (r0, g0, b0) := fixturePaletteRGB idx
        let a := fixtureAlphaAt alpha? idx
        let (r, g, b) :=
          if alpha?.isSome then
            let (br, bg, bb) := bgRGB
            (alphaCompositeByte r0 br a,
              alphaCompositeByte g0 bg a,
              alphaCompositeByte b0 bb a)
          else
            (r0, g0, b0)
        out := out.push r
        out := out.push g
        out := out.push b
    return out

private def fixtureExpectedRGB16Data (w h entryCount : Nat) : ByteArray :=
  Id.run do
    let mut out := ByteArray.emptyWithCapacity (w * h * bytesPerPixelRGB16)
    for y in [0:h] do
      for x in [0:w] do
        let idx := (fixtureIndex entryCount x y).toNat
        let (r, g, b) := fixturePaletteRGB idx
        out := pushU16Full out r
        out := pushU16Full out g
        out := pushU16Full out b
    return out

private def fixtureExpectedRGBA16Data (w h entryCount : Nat)
    (alpha? : Option ByteArray := none) : ByteArray :=
  Id.run do
    let mut out := ByteArray.emptyWithCapacity (w * h * bytesPerPixelRGBA16)
    for y in [0:h] do
      for x in [0:w] do
        let idx := (fixtureIndex entryCount x y).toNat
        let (r, g, b) := fixturePaletteRGB idx
        out := pushU16Full out r
        out := pushU16Full out g
        out := pushU16Full out b
        out := pushU16Full out (fixtureAlphaAt alpha? idx)
    return out

private def fixtureExpectedGray16Data (w h entryCount : Nat) : ByteArray :=
  Id.run do
    let mut out := ByteArray.emptyWithCapacity (w * h * bytesPerPixelGray16)
    for y in [0:h] do
      for x in [0:w] do
        let idx := (fixtureIndex entryCount x y).toNat
        let (r, g, b) := fixturePaletteRGB idx
        out := pushU16Full out (grayFromRGB8 r g b)
    return out

private def fixtureExpectedGrayAlpha16Data (w h entryCount : Nat)
    (alpha? : Option ByteArray := none) : ByteArray :=
  Id.run do
    let mut out := ByteArray.emptyWithCapacity (w * h * bytesPerPixelGrayAlpha16)
    for y in [0:h] do
      for x in [0:w] do
        let idx := (fixtureIndex entryCount x y).toNat
        let (r, g, b) := fixturePaletteRGB idx
        out := pushU16Full out (grayFromRGB8 r g b)
        out := pushU16Full out (fixtureAlphaAt alpha? idx)
    return out

private def fixtureAdam7BytesFor (bitDepth : Nat) : ByteArray :=
  let entryCount := paletteIndexLimit bitDepth
  fixturePngWithChunks 9 7 bitDepth 1
    (mkChunkBytes plteTypeBytes (fixturePaletteEntries entryCount))
    (fixtureAdam7Raw 9 7 bitDepth entryCount)

private def fixtureAdam7Bytes : ByteArray :=
  fixtureAdam7BytesFor 2

private def multiIdatFixtureBitmap : PngIndexedBitmap :=
  fixtureBitmap 7 3 4 16

private def multiIdatFixtureBytes : ByteArray :=
  fixturePngWithSplitIdat 7 3 4 0
    (mkChunkBytes plteTypeBytes multiIdatFixtureBitmap.palette.entries)
    (encodeRawIndexedWithFilter multiIdatFixtureBitmap .none)

private def fixture16Bytes? : Option ByteArray :=
  match encodeIndexedBitmapChecked multiIdatFixtureBitmap .fixed with
  | .ok bytes => some bytes
  | .error _ => none

private def alphaFixture : ByteArray :=
  ByteArray.mk #[u8 0, u8 255, u8 128, u8 255]

private def alphaFixtureBitmap : PngIndexedBitmap :=
  fixtureBitmap 5 4 2 4 (some alphaFixture) (some (u8 1))

private def alphaFixtureBytes? : Option ByteArray :=
  match encodeIndexedBitmapChecked alphaFixtureBitmap .fixed with
  | .ok bytes => some bytes
  | .error _ => none

private def colorSpaceFixtureBitmap : PngIndexedBitmap :=
  fixtureBitmap 4 2 2 4

private def paletteGamma : Nat :=
  100000

private def wideChromaticities : PngChromaticities :=
  { white := { x := 31270, y := 32900 }
    red := { x := 68000, y := 32000 }
    green := { x := 21000, y := 71000 }
    blue := { x := 15000, y := 6000 } }

private def gammaFixtureBytes? : Option ByteArray :=
  match encodeIndexedBitmapWithOptionsChecked colorSpaceFixtureBitmap
      { mode := .fixed, colorSpace := some (.gamma paletteGamma) } with
  | .ok bytes => some bytes
  | .error _ => none

private def srgbFixtureBytes? : Option ByteArray :=
  match encodeIndexedBitmapWithOptionsChecked colorSpaceFixtureBitmap
      { mode := .fixed, colorSpace := some (.srgb .perceptual true),
        chromaticities := some PngChromaticities.srgb } with
  | .ok bytes => some bytes
  | .error _ => none

private def chrmGammaFixtureBytes? : Option ByteArray :=
  match encodeIndexedBitmapWithOptionsChecked colorSpaceFixtureBitmap
      { mode := .fixed, colorSpace := some (.gamma paletteGamma),
        chromaticities := some wideChromaticities } with
  | .ok bytes => some bytes
  | .error _ => none

private def chrmGammaExpectedRGB8? : Option ByteArray := do
  let matrix ← wideChromaticities.sourceToSrgbMatrix?
  applyChrm8ToPixels matrix (some paletteGamma) (u8 2) (fixtureExpectedRGB8Data 4 2 4)

private def decodeIndexedDataAfterCheckedEncode
    (bmp : PngIndexedBitmap) (mode : PngEncodeMode) : Option ByteArray :=
  match encodeIndexedBitmapChecked bmp mode with
  | .ok bytes => (decodeIndexedBitmap bytes).map (fun bitmap => bitmap.data)
  | .error _ => none

private def decodeIndexedMetadataDataAfterCheckedEncode
    (bmp : PngIndexedBitmap) (mode : PngEncodeMode) : Option ByteArray :=
  match encodeIndexedBitmapChecked bmp mode with
  | .ok bytes =>
      (decodeIndexedBitmapWithMetadata bytes).map (fun result => result.bitmap.data)
  | .error _ => none

private def decodeIndexedDataAfterCheckedEncodeWithOptions
    (bmp : PngIndexedBitmap) (options : PngEncodeOptions) : Option ByteArray :=
  match encodeIndexedBitmapWithOptionsChecked bmp options with
  | .ok bytes => (decodeIndexedBitmap bytes).map (fun bitmap => bitmap.data)
  | .error _ => none

private def decodeIndexedMetadataDataAfterCheckedEncodeWithOptions
    (bmp : PngIndexedBitmap) (options : PngEncodeOptions) : Option ByteArray :=
  match encodeIndexedBitmapWithOptionsChecked bmp options with
  | .ok bytes =>
      (decodeIndexedBitmapWithMetadata bytes).map (fun result => result.bitmap.data)
  | .error _ => none

private def indexedBitmapRuntimeMatches (actual expected : PngIndexedBitmap) : Bool :=
  actual.size == expected.size &&
    actual.bitDepth == expected.bitDepth &&
    decide (actual.palette = expected.palette) &&
    decide (actual.data = expected.data) &&
    decide (actual.transparency = expected.transparency) &&
    decide (actual.background = expected.background)

private def decodeIndexedShapeMatchesAfterCheckedEncodeWithOptions
    (bmp : PngIndexedBitmap) (options : PngEncodeOptions) : Bool :=
  match encodeIndexedBitmapWithOptionsChecked bmp options with
  | .ok bytes =>
      match decodeIndexedBitmap bytes with
      | some decoded => indexedBitmapRuntimeMatches decoded bmp
      | none => false
  | .error _ => false

private def decodeIndexedMetadataShapeMatchesAfterCheckedEncodeWithOptions
    (bmp : PngIndexedBitmap) (expectedMetadata : PngMetadata)
    (options : PngEncodeOptions) : Bool :=
  match encodeIndexedBitmapWithOptionsChecked bmp options with
  | .ok bytes =>
      match decodeIndexedBitmapWithMetadata bytes with
      | some decoded =>
          indexedBitmapRuntimeMatches decoded.bitmap bmp &&
            decide (decoded.metadata = expectedMetadata)
      | none => false
  | .error _ => false

private def paletteOnlyMetadata (palette : PngPalette) : PngMetadata :=
  { PngMetadata.empty with palette := some palette }

private def alphaFixtureMetadata : PngMetadata :=
  { PngMetadata.empty with
    palette := some alphaFixtureBitmap.palette
    transparency := some (.paletteAlpha alphaFixture)
    background := some (.paletteIndex (u8 1)) }

/-- For every supported PNG palette bit depth, there is an explicit indexed
bitmap whose checked encoder round-trips through both exact indexed decoders.
This quantifies over all compression modes and covers the packed 1/2/4-bit
paths plus the byte-wide 8-bit path. -/
theorem checked_roundtrip_fixture_for_supported_bitDepth
    (bitDepth : Nat) (mode : PngEncodeMode)
    (hbd : bitDepth = 1 ∨ bitDepth = 2 ∨ bitDepth = 4 ∨ bitDepth = 8) :
    ∃ bmp,
      bmp.bitDepth = bitDepth ∧
        decodeIndexedDataAfterCheckedEncode bmp mode = some bmp.data ∧
        decodeIndexedMetadataDataAfterCheckedEncode bmp mode = some bmp.data := by
  rcases hbd with rfl | rfl | rfl | rfl
  · refine ⟨indexed1, rfl, ?_, ?_⟩ <;> cases mode <;> native_decide
  · refine ⟨indexed2, rfl, ?_, ?_⟩ <;> cases mode <;> native_decide
  · refine ⟨indexed4, rfl, ?_, ?_⟩ <;> cases mode <;> native_decide
  · refine ⟨indexed8, rfl, ?_, ?_⟩ <;> cases mode <;> native_decide

/-- For every supported PNG palette bit depth and every PNG row filter, there
is an explicit indexed bitmap whose fixed-Huffman checked encoder round-trips
through both exact indexed decoders. This pins the filtered packed paths. -/
theorem checked_fixed_filter_roundtrip_fixture_for_supported_bitDepth
    (bitDepth : Nat) (rowFilter : PngRowFilter)
    (hbd : bitDepth = 1 ∨ bitDepth = 2 ∨ bitDepth = 4 ∨ bitDepth = 8) :
    ∃ bmp,
      bmp.bitDepth = bitDepth ∧
        decodeIndexedDataAfterCheckedEncodeWithOptions bmp
          { mode := .fixed, filter := .fixed rowFilter } = some bmp.data ∧
        decodeIndexedMetadataDataAfterCheckedEncodeWithOptions bmp
          { mode := .fixed, filter := .fixed rowFilter } = some bmp.data := by
  rcases hbd with rfl | rfl | rfl | rfl
  · refine ⟨indexed1, rfl, ?_, ?_⟩ <;> cases rowFilter <;> native_decide
  · refine ⟨indexed2, rfl, ?_, ?_⟩ <;> cases rowFilter <;> native_decide
  · refine ⟨indexed4, rfl, ?_, ?_⟩ <;> cases rowFilter <;> native_decide
  · refine ⟨indexed8, rfl, ?_, ?_⟩ <;> cases rowFilter <;> native_decide

/-- For every supported PNG palette bit depth and every fixed PNG row filter, a
concrete checked indexed encode/decode round-trip preserves the complete exact
indexed bitmap shape and parsed palette metadata. This strengthens the
data-only fixed-filter fixture theorem. -/
theorem checked_fixed_filter_shape_fixture_for_supported_bitDepth
    (bitDepth : Nat) (rowFilter : PngRowFilter)
    (hbd : bitDepth = 1 ∨ bitDepth = 2 ∨ bitDepth = 4 ∨ bitDepth = 8) :
    ∃ bmp,
      bmp.bitDepth = bitDepth ∧
        decodeIndexedShapeMatchesAfterCheckedEncodeWithOptions bmp
          { mode := .fixed, filter := .fixed rowFilter } = true ∧
        decodeIndexedMetadataShapeMatchesAfterCheckedEncodeWithOptions bmp
          (paletteOnlyMetadata bmp.palette)
          { mode := .fixed, filter := .fixed rowFilter } = true := by
  rcases hbd with rfl | rfl | rfl | rfl
  · refine ⟨indexed1, rfl, ?_, ?_⟩ <;> cases rowFilter <;> native_decide
  · refine ⟨indexed2, rfl, ?_, ?_⟩ <;> cases rowFilter <;> native_decide
  · refine ⟨indexed4, rfl, ?_, ?_⟩ <;> cases rowFilter <;> native_decide
  · refine ⟨indexed8, rfl, ?_, ?_⟩ <;> cases rowFilter <;> native_decide

/-- For every supported PNG palette bit depth and compression mode, adaptive
row filtering preserves the exact indexed bitmap shape and parsed palette
metadata. This covers the non-fixed filter strategy on packed palette rows. -/
theorem checked_adaptive_filter_shape_fixture_for_supported_bitDepth
    (bitDepth : Nat) (mode : PngEncodeMode)
    (hbd : bitDepth = 1 ∨ bitDepth = 2 ∨ bitDepth = 4 ∨ bitDepth = 8) :
    ∃ bmp,
      bmp.bitDepth = bitDepth ∧
        decodeIndexedShapeMatchesAfterCheckedEncodeWithOptions bmp
          { mode, filter := .adaptive } = true ∧
        decodeIndexedMetadataShapeMatchesAfterCheckedEncodeWithOptions bmp
          (paletteOnlyMetadata bmp.palette)
          { mode, filter := .adaptive } = true := by
  rcases hbd with rfl | rfl | rfl | rfl
  · refine ⟨indexed1, rfl, ?_, ?_⟩ <;> cases mode <;> native_decide
  · refine ⟨indexed2, rfl, ?_, ?_⟩ <;> cases mode <;> native_decide
  · refine ⟨indexed4, rfl, ?_, ?_⟩ <;> cases mode <;> native_decide
  · refine ⟨indexed8, rfl, ?_, ?_⟩ <;> cases mode <;> native_decide

/-- Stored-zlib checked encode/decode round-trips a concrete 1-bit indexed row
through both exact indexed decode APIs. -/
theorem checked_stored_1bit_fixture_data :
    decodeIndexedDataAfterCheckedEncode indexed1 .stored = some indexed1.data ∧
      decodeIndexedMetadataDataAfterCheckedEncode indexed1 .stored = some indexed1.data := by
  native_decide

/-- Fixed-Huffman checked encode/decode round-trips a concrete 1-bit indexed row
through both exact indexed decode APIs. -/
theorem checked_fixed_1bit_fixture_data :
    decodeIndexedDataAfterCheckedEncode indexed1 .fixed = some indexed1.data ∧
      decodeIndexedMetadataDataAfterCheckedEncode indexed1 .fixed = some indexed1.data := by
  native_decide

/-- Dynamic-Huffman checked encode/decode round-trips a concrete 1-bit indexed
row through both exact indexed decode APIs. -/
theorem checked_dynamic_1bit_fixture_data :
    decodeIndexedDataAfterCheckedEncode indexed1 .dynamic = some indexed1.data ∧
      decodeIndexedMetadataDataAfterCheckedEncode indexed1 .dynamic = some indexed1.data := by
  native_decide

/-- Stored-zlib checked encode/decode round-trips a concrete 2-bit indexed row
through both exact indexed decode APIs. -/
theorem checked_stored_2bit_fixture_data :
    decodeIndexedDataAfterCheckedEncode indexed2 .stored = some indexed2.data ∧
      decodeIndexedMetadataDataAfterCheckedEncode indexed2 .stored = some indexed2.data := by
  native_decide

/-- Fixed-Huffman checked encode/decode round-trips a concrete 2-bit indexed row
through both exact indexed decode APIs. -/
theorem checked_fixed_2bit_fixture_data :
    decodeIndexedDataAfterCheckedEncode indexed2 .fixed = some indexed2.data ∧
      decodeIndexedMetadataDataAfterCheckedEncode indexed2 .fixed = some indexed2.data := by
  native_decide

/-- Dynamic-Huffman checked encode/decode round-trips a concrete 2-bit indexed
row through both exact indexed decode APIs. -/
theorem checked_dynamic_2bit_fixture_data :
    decodeIndexedDataAfterCheckedEncode indexed2 .dynamic = some indexed2.data ∧
      decodeIndexedMetadataDataAfterCheckedEncode indexed2 .dynamic = some indexed2.data := by
  native_decide

/-- Stored-zlib checked encode/decode round-trips a concrete 4-bit indexed row
through both exact indexed decode APIs. -/
theorem checked_stored_4bit_fixture_data :
    decodeIndexedDataAfterCheckedEncode indexed4 .stored = some indexed4.data ∧
      decodeIndexedMetadataDataAfterCheckedEncode indexed4 .stored = some indexed4.data := by
  native_decide

/-- Fixed-Huffman checked encode/decode round-trips a concrete 4-bit indexed row
through both exact indexed decode APIs. -/
theorem checked_fixed_4bit_fixture_data :
    decodeIndexedDataAfterCheckedEncode indexed4 .fixed = some indexed4.data ∧
      decodeIndexedMetadataDataAfterCheckedEncode indexed4 .fixed = some indexed4.data := by
  native_decide

/-- Dynamic-Huffman checked encode/decode round-trips a concrete 4-bit indexed
row through both exact indexed decode APIs. -/
theorem checked_dynamic_4bit_fixture_data :
    decodeIndexedDataAfterCheckedEncode indexed4 .dynamic = some indexed4.data ∧
      decodeIndexedMetadataDataAfterCheckedEncode indexed4 .dynamic = some indexed4.data := by
  native_decide

/-- Stored-zlib checked encode/decode round-trips a concrete 8-bit indexed row
through both exact indexed decode APIs. -/
theorem checked_stored_8bit_fixture_data :
    decodeIndexedDataAfterCheckedEncode indexed8 .stored = some indexed8.data ∧
      decodeIndexedMetadataDataAfterCheckedEncode indexed8 .stored = some indexed8.data := by
  native_decide

/-- Fixed-Huffman checked encode/decode round-trips a concrete 8-bit indexed row
through both exact indexed decode APIs. -/
theorem checked_fixed_8bit_fixture_data :
    decodeIndexedDataAfterCheckedEncode indexed8 .fixed = some indexed8.data ∧
      decodeIndexedMetadataDataAfterCheckedEncode indexed8 .fixed = some indexed8.data := by
  native_decide

/-- Dynamic-Huffman checked encode/decode round-trips a concrete 8-bit indexed
row through both exact indexed decode APIs. -/
theorem checked_dynamic_8bit_fixture_data :
    decodeIndexedDataAfterCheckedEncode indexed8 .dynamic = some indexed8.data ∧
      decodeIndexedMetadataDataAfterCheckedEncode indexed8 .dynamic = some indexed8.data := by
  native_decide

/-- For every supported indexed bit depth, Adam7 palette fixture decoding
reconstructs the exact one-byte-per-pixel index buffer. This generalizes the
interlaced packed-path fixture beyond the original 2-bit case. -/
theorem decodeIndexedBitmap_adam7_fixture_for_supported_bitDepth
    (bitDepth : Nat)
    (hbd : bitDepth = 1 ∨ bitDepth = 2 ∨ bitDepth = 4 ∨ bitDepth = 8) :
    (decodeIndexedBitmap (fixtureAdam7BytesFor bitDepth)).map
      (fun decoded => (decoded.bitDepth, decoded.palette, decoded.data)) =
        some
          (bitDepth, fixturePalette (paletteIndexLimit bitDepth),
            fixtureData 9 7 (paletteIndexLimit bitDepth)) := by
  rcases hbd with rfl | rfl | rfl | rfl <;> native_decide

/-- For every supported indexed bit depth, metadata-aware Adam7 palette fixture
decoding reconstructs the complete exact indexed bitmap shape and preserves the
parsed palette metadata. -/
theorem decodeIndexedBitmapWithMetadata_adam7_fixture_for_supported_bitDepth_shape
    (bitDepth : Nat)
    (hbd : bitDepth = 1 ∨ bitDepth = 2 ∨ bitDepth = 4 ∨ bitDepth = 8) :
    (match decodeIndexedBitmapWithMetadata (fixtureAdam7BytesFor bitDepth) with
    | some decoded =>
        indexedBitmapRuntimeMatches decoded.bitmap
          (fixtureBitmap 9 7 bitDepth (paletteIndexLimit bitDepth)) &&
          decide (decoded.metadata = paletteOnlyMetadata
            (fixturePalette (paletteIndexLimit bitDepth)))
    | none => false) = true := by
  rcases hbd with rfl | rfl | rfl | rfl <;> native_decide

/-- Adam7 interlaced 2-bit palette fixture decoding reconstructs the exact
one-byte-per-pixel index buffer. This compatibility wrapper is covered by the
all-supported-bit-depth Adam7 theorem. -/
theorem decodeIndexedBitmap_adam7_2bit_fixture :
    (decodeIndexedBitmap fixtureAdam7Bytes).map
      (fun decoded => (decoded.bitDepth, decoded.palette, decoded.data)) =
        some (2, fixturePalette 4, fixtureData 9 7 4) := by
  simpa [fixtureAdam7Bytes, fixtureAdam7BytesFor, paletteIndexLimit] using
    decodeIndexedBitmap_adam7_fixture_for_supported_bitDepth 2 (by simp)

/-- Split-IDAT 4-bit palette fixture decoding reconstructs the exact indexed
bitmap data and palette. This pins multi-IDAT palette accumulation. -/
theorem decodeIndexedBitmap_multiIDAT_4bit_fixture :
    (decodeIndexedBitmap multiIdatFixtureBytes).map
      (fun decoded => (decoded.bitDepth, decoded.palette, decoded.data)) =
        some (4, multiIdatFixtureBitmap.palette, multiIdatFixtureBitmap.data) := by
  native_decide

/-- Split-IDAT 4-bit palette fixture decoding also reconstructs the complete
metadata-aware indexed bitmap shape. -/
theorem decodeIndexedBitmapWithMetadata_multiIDAT_4bit_fixture_shape :
    (match decodeIndexedBitmapWithMetadata multiIdatFixtureBytes with
    | some decoded =>
        indexedBitmapRuntimeMatches decoded.bitmap multiIdatFixtureBitmap &&
          decide (decoded.metadata = paletteOnlyMetadata multiIdatFixtureBitmap.palette)
    | none => false) = true := by
  native_decide

/-- Palette `tRNS` metadata expands to RGBA8 alpha bytes for the fixture and
preserves the parsed palette metadata. -/
theorem decodeBitmapWithMetadata_palette_tRNS_RGBA8_fixture :
    (alphaFixtureBytes?.bind (fun bytes =>
      (decodeBitmapWithMetadata (px := PixelRGBA8) bytes).map
        (fun decoded =>
          (decoded.bitmap.data, decoded.metadata.transparency, decoded.metadata.background)))) =
        some
          (fixtureExpectedRGBA8Data 5 4 4 (some alphaFixture),
            some (.paletteAlpha alphaFixture), some (.paletteIndex (u8 1))) := by
  native_decide

/-- Palette `tRNS` plus `bKGD` metadata composites into RGB8 fixture output for
non-alpha decode targets. -/
theorem decodeBitmapWithMetadata_palette_tRNS_bKGD_RGB8_fixture :
    (alphaFixtureBytes?.bind (fun bytes =>
      (decodeBitmapWithMetadata (px := PixelRGB8) bytes).map
        (fun decoded => decoded.bitmap.data))) =
        some (fixtureExpectedRGB8Data 5 4 4 (some alphaFixture) (some (u8 1))) := by
  native_decide

/-- Pixel-only palette bitmap decode rejects `tRNS` for the alpha fixture; callers
must use the metadata-aware API to opt into palette transparency handling. -/
theorem decodeBitmap_palette_tRNS_pixelOnly_rejects_RGBA8_fixture :
    (alphaFixtureBytes?.bind (fun bytes =>
      (decodeBitmap (px := PixelRGBA8) bytes).map (fun _ => ()))) = none := by
  native_decide

/-- Exact indexed metadata decode preserves palette alpha and background index
fields on the returned indexed bitmap without expanding the index buffer. -/
theorem decodeIndexedBitmapWithMetadata_palette_tRNS_bKGD_fixture :
    (alphaFixtureBytes?.bind (fun bytes =>
      (decodeIndexedBitmapWithMetadata bytes).map
        (fun decoded =>
          (decoded.bitmap.data, decoded.bitmap.transparency, decoded.bitmap.background)))) =
        some (alphaFixtureBitmap.data, some alphaFixture, some (u8 1)) := by
  native_decide

/-- Exact indexed metadata decode also preserves parsed palette `tRNS` and
`bKGD` metadata alongside the indexed bitmap. -/
theorem decodeIndexedBitmapWithMetadata_palette_metadata_fixture :
    (alphaFixtureBytes?.bind (fun bytes =>
      (decodeIndexedBitmapWithMetadata bytes).map
        (fun decoded => (decoded.metadata.transparency, decoded.metadata.background)))) =
        some (some (.paletteAlpha alphaFixture), some (.paletteIndex (u8 1))) := by
  native_decide

/-- Exact indexed metadata decode preserves the complete indexed bitmap runtime
shape and parsed palette alpha/background metadata for the alpha fixture. -/
theorem decodeIndexedBitmapWithMetadata_palette_tRNS_bKGD_shape_fixture :
    (alphaFixtureBytes?.bind (fun bytes =>
      (decodeIndexedBitmapWithMetadata bytes).map (fun decoded =>
        indexedBitmapRuntimeMatches decoded.bitmap alphaFixtureBitmap &&
          decide (decoded.metadata = alphaFixtureMetadata)))) = some true := by
  native_decide

/-- Palette decode expands 8-bit `PLTE` entries into full-range RGB16 samples
for the 16-bit RGB target fixture. -/
theorem decodeBitmap_palette_RGB16_fixture :
    (fixture16Bytes?.bind (fun bytes =>
      (decodeBitmap (px := PixelRGB16) bytes).map (fun decoded => decoded.data))) =
        some (fixtureExpectedRGB16Data 7 3 16) := by
  native_decide

/-- Palette decode expands 8-bit `PLTE` entries and default opaque alpha into
full-range RGBA16 samples for the 16-bit RGBA target fixture. -/
theorem decodeBitmap_palette_RGBA16_fixture :
    (fixture16Bytes?.bind (fun bytes =>
      (decodeBitmap (px := PixelRGBA16) bytes).map (fun decoded => decoded.data))) =
        some (fixtureExpectedRGBA16Data 7 3 16) := by
  native_decide

/-- Palette decode expands grayscale-converted `PLTE` entries into full-range
Gray16 samples for the 16-bit grayscale target fixture. -/
theorem decodeBitmap_palette_Gray16_fixture :
    (fixture16Bytes?.bind (fun bytes =>
      (decodeBitmap (px := PixelGray16) bytes).map (fun decoded => decoded.data))) =
        some (fixtureExpectedGray16Data 7 3 16) := by
  native_decide

/-- Palette decode expands grayscale-converted `PLTE` entries and default
opaque alpha into full-range GrayAlpha16 samples for the fixture. -/
theorem decodeBitmap_palette_GrayAlpha16_fixture :
    (fixture16Bytes?.bind (fun bytes =>
      (decodeBitmap (px := PixelGrayAlpha16) bytes).map (fun decoded => decoded.data))) =
        some (fixtureExpectedGrayAlpha16Data 7 3 16) := by
  native_decide

/-- Palette `gAMA` metadata is applied after `PLTE` lookup when decoding the
RGB8 fixture, and the scaled gamma value is preserved. -/
theorem decodeBitmapWithMetadata_palette_gAMA_RGB8_fixture :
    (gammaFixtureBytes?.bind (fun bytes =>
      (decodeBitmapWithMetadata (px := PixelRGB8) bytes).map
        (fun decoded => (decoded.bitmap.data, decoded.metadata.gamma)))) =
        (applyGamma8ToPixels paletteGamma (u8 2) (fixtureExpectedRGB8Data 4 2 4)).map
          (fun expected => (expected, some paletteGamma)) := by
  native_decide

/-- Palette `sRGB` metadata leaves already-sRGB palette samples unchanged after
`PLTE` lookup when decoding the RGB8 fixture. -/
theorem decodeBitmapWithMetadata_palette_sRGB_RGB8_fixture :
    (srgbFixtureBytes?.bind (fun bytes =>
      (decodeBitmapWithMetadata (px := PixelRGB8) bytes).map
        (fun decoded => decoded.bitmap.data))) =
        some (fixtureExpectedRGB8Data 4 2 4) := by
  native_decide

/-- Palette `sRGB` fixture decoding preserves rendering intent, compatible
gamma, and compatible chromaticities metadata. -/
theorem decodeBitmapWithMetadata_palette_sRGB_metadata_fixture :
    (srgbFixtureBytes?.bind (fun bytes =>
      (decodeBitmapWithMetadata (px := PixelRGB8) bytes).map
        (fun decoded =>
          (decoded.metadata.srgb, decoded.metadata.gamma, decoded.metadata.chromaticities)))) =
        some (some .perceptual, some 45455, some PngChromaticities.srgb) := by
  native_decide

/-- Palette `cHRM` plus `gAMA` metadata is applied after `PLTE` lookup when
decoding the RGB8 fixture. -/
theorem decodeBitmapWithMetadata_palette_cHRM_gAMA_RGB8_fixture :
    (chrmGammaFixtureBytes?.bind (fun bytes =>
      (decodeBitmapWithMetadata (px := PixelRGB8) bytes).map
        (fun decoded => decoded.bitmap.data))) =
        chrmGammaExpectedRGB8? := by
  native_decide

/-- Palette `cHRM` plus `gAMA` fixture decoding preserves both color-space
metadata values. -/
theorem decodeBitmapWithMetadata_palette_cHRM_gAMA_metadata_fixture :
    (chrmGammaFixtureBytes?.bind (fun bytes =>
      (decodeBitmapWithMetadata (px := PixelRGB8) bytes).map
        (fun decoded => (decoded.metadata.chromaticities, decoded.metadata.gamma)))) =
        some (some wideChromaticities, some paletteGamma) := by
  native_decide

end PalettePackedRoundTrip

end Lemmas

end Bitmaps
