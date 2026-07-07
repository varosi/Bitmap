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

private def fixtureAdam7Bytes : ByteArray :=
  fixturePngWithChunks 9 7 2 1
    (mkChunkBytes plteTypeBytes (fixturePaletteEntries 4))
    (fixtureAdam7Raw 9 7 2 4)

private def multiIdatFixtureBitmap : PngIndexedBitmap :=
  fixtureBitmap 7 3 4 16

private def multiIdatFixtureBytes : ByteArray :=
  fixturePngWithSplitIdat 7 3 4 0
    (mkChunkBytes plteTypeBytes multiIdatFixtureBitmap.palette.entries)
    (encodeRawIndexedWithFilter multiIdatFixtureBitmap .none)

private def alphaFixture : ByteArray :=
  ByteArray.mk #[u8 0, u8 255, u8 128, u8 255]

private def alphaFixtureBitmap : PngIndexedBitmap :=
  fixtureBitmap 5 4 2 4 (some alphaFixture) (some (u8 1))

private def alphaFixtureBytes? : Option ByteArray :=
  match encodeIndexedBitmapChecked alphaFixtureBitmap .fixed with
  | .ok bytes => some bytes
  | .error _ => none

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

/-- Adam7 interlaced 2-bit palette fixture decoding reconstructs the exact
one-byte-per-pixel index buffer. This covers the packed interlace path. -/
theorem decodeIndexedBitmap_adam7_2bit_fixture :
    (decodeIndexedBitmap fixtureAdam7Bytes).map
      (fun decoded => (decoded.bitDepth, decoded.palette, decoded.data)) =
        some (2, fixturePalette 4, fixtureData 9 7 4) := by
  native_decide

/-- Split-IDAT 4-bit palette fixture decoding reconstructs the exact indexed
bitmap data and palette. This pins multi-IDAT palette accumulation. -/
theorem decodeIndexedBitmap_multiIDAT_4bit_fixture :
    (decodeIndexedBitmap multiIdatFixtureBytes).map
      (fun decoded => (decoded.bitDepth, decoded.palette, decoded.data)) =
        some (4, multiIdatFixtureBitmap.palette, multiIdatFixtureBitmap.data) := by
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

end PalettePackedRoundTrip

end Lemmas

end Bitmaps
