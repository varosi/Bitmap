import Bitmap.Basic
import Bitmap.Png

open Bitmaps

namespace Bitmap.Tests

private def randByte (s : Nat) : UInt8 :=
  UInt8.ofNat (s % 256)

private def byteArrayOfNats (xs : List Nat) : ByteArray :=
  ByteArray.mk <| xs.toArray.map randByte

private def repeatBytes (chunk : ByteArray) (count : Nat) : ByteArray :=
  Id.run do
    let mut out := ByteArray.emptyWithCapacity (chunk.size * count)
    for _ in [0:count] do
      out := out ++ chunk
    return out

private def rangeBytes (count : Nat) : ByteArray :=
  ByteArray.mk <| (List.range count).toArray.map randByte

private def deterministicPrefix (size : Nat) : ByteArray :=
  ByteArray.mk <| (List.range size).toArray.map (fun i => randByte (17 * i + 3))

private def zlibFirstBlockType? (bytes : ByteArray) : Option Nat :=
  if h : 2 < bytes.size then
    some (((bytes.get 2 h).toNat >>> 1) % 4)
  else
    none

private def zlibDecompressFixture (bytes : ByteArray) : Option ByteArray :=
  if h : 2 ≤ bytes.size then
    Png.zlibDecompress bytes h
  else
    none

private def dynamicRepeatZlibFixture : ByteArray :=
  byteArrayOfNats
    [120, 218, 237, 195, 49, 13, 0, 0, 8, 3, 48, 109, 131, 249, 215, 132, 12, 158,
      54, 105, 102, 27, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85,
      245, 245, 1, 110, 73, 160, 241]

private def dynamicRepeatRawFixture : ByteArray :=
  repeatBytes "ABCD".toUTF8 4096

private def dynamicRepeatCodeZlibFixture : ByteArray :=
  byteArrayOfNats
    [120, 1, 5, 192, 39, 13, 0, 0, 0, 3, 48, 206, 57, 231, 28, 237, 248, 231, 156,
      115, 220, 164, 59, 2, 152, 1, 11]

private def dynamicRepeatCodeRawFixture : ByteArray :=
  "ABCD".toUTF8

private def dynamicLiteralOnlyZeroDistZlibFixture : ByteArray :=
  byteArrayOfNats
    [120, 1, 5, 192, 129, 8, 0, 0, 0, 0, 32, 182, 253, 165, 78, 0, 66, 0, 66]

private def dynamicLiteralOnlyZeroDistRawFixture : ByteArray :=
  byteArrayOfNats [65]

private def dynamicMixedZlibFixture : ByteArray :=
  byteArrayOfNats
    [120, 218, 237, 203, 201, 82, 1, 0, 0, 0, 80, 145, 173, 100, 45, 42, 251, 90,
      18, 217, 74, 40, 102, 58, 251, 9, 135, 14, 14, 153, 14, 254, 127, 252, 131,
      147, 195, 187, 189, 203, 219, 252, 110, 247, 63, 187, 195, 223, 246, 191, 191,
      65, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68,
      68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68,
      68, 68, 196, 211, 25, 184, 8, 134, 46, 195, 145, 104, 44, 126, 117, 157, 184,
      73, 166, 210, 153, 108, 238, 246, 46, 95, 184, 127, 120, 44, 150, 202, 149, 106,
      173, 222, 104, 182, 218, 157, 167, 231, 238, 75, 239, 181, 63, 120, 27, 142,
      198, 147, 233, 251, 199, 236, 115, 190, 88, 126, 125, 175, 214, 190, 239, 251,
      190, 239, 251, 190, 239, 251, 190, 239, 251, 190, 239, 251, 190, 239, 251, 231,
      246, 143, 26, 166, 163, 159]

private def dynamicMixedRawFixture : ByteArray :=
  repeatBytes "LeanBitmap-".toUTF8 2000 ++ repeatBytes (rangeBytes 64) 100

private def dynamicMultiBlockZlibFixture : ByteArray :=
  byteArrayOfNats
    [120, 218, 236, 195, 1, 9, 0, 0, 8, 3, 176, 108, 215, 247, 207, 100, 14, 97,
      131, 101, 182, 81, 85, 85, 85, 85, 85, 85, 85, 95, 63, 0, 0, 0, 255, 255, 236,
      194, 1, 13, 0, 0, 12, 2, 160, 218, 247, 233, 237, 225, 96, 92, 94, 85, 85, 85,
      85, 85, 85, 85, 85, 231, 23, 0, 0, 255, 255, 99, 96, 100, 98, 102, 97, 101, 99,
      231, 224, 228, 226, 230, 225, 229, 227, 23, 16, 20, 18, 22, 17, 21, 19, 151,
      144, 148, 146, 150, 145, 149, 147, 87, 80, 84, 82, 86, 81, 85, 83, 215, 208,
      212, 210, 214, 209, 213, 211, 55, 48, 52, 50, 54, 49, 53, 51, 183, 176, 180,
      178, 182, 177, 181, 179, 119, 0, 45, 182, 113, 117, 115, 247, 240, 244, 242,
      246, 241, 245, 243, 15, 8, 12, 10, 14, 9, 13, 11, 143, 136, 140, 138, 142, 137,
      141, 139, 79, 72, 76, 74, 78, 73, 77, 75, 207, 200, 204, 202, 206, 201, 205,
      203, 47, 40, 44, 42, 46, 41, 45, 43, 7, 90, 93, 93, 83, 91, 87, 223, 208, 216,
      212, 220, 210, 218, 214, 222, 209, 217, 213, 221, 211, 219, 215, 63, 97, 226,
      164, 201, 83, 166, 78, 155, 62, 99, 230, 172, 217, 115, 230, 206, 155, 191, 96,
      225, 162, 197, 75, 150, 46, 91, 190, 98, 229, 170, 213, 107, 214, 174, 91, 191,
      97, 227, 166, 205, 91, 182, 110, 219, 190, 99, 231, 174, 221, 123, 246, 238,
      219, 127, 224, 224, 161, 195, 71, 142, 30, 59, 126, 226, 228, 169, 211, 103,
      206, 158, 59, 127, 225, 226, 165, 203, 87, 174, 94, 187, 126, 227, 230, 173,
      219, 119, 238, 222, 187, 255, 224, 225, 163, 199, 79, 158, 62, 123, 254, 226,
      229, 171, 215, 111, 222, 190, 123, 255, 225, 227, 167, 207, 95, 190, 126, 251,
      254, 227, 231, 175, 223, 127, 254, 254, 251, 63, 234, 255, 81, 255, 143, 250,
      127, 212, 255, 163, 254, 31, 245, 255, 168, 255, 71, 253, 63, 234, 255, 81,
      255, 143, 250, 127, 212, 255, 163, 254, 31, 245, 255, 168, 255, 71, 253, 63,
      234, 255, 81, 255, 15, 103, 255, 3, 0, 52, 50, 229, 231]

private def dynamicMultiBlockRawFixture : ByteArray :=
  repeatBytes "ABCD".toUTF8 2048 ++
    repeatBytes "xyz".toUTF8 3000 ++
    repeatBytes (rangeBytes 256) 20

private def badHeaderChecksumZlibFixture : ByteArray :=
  byteArrayOfNats
    [120, 219, 237, 195, 49, 13, 0, 0, 8, 3, 48, 109, 131, 249, 215, 132, 12, 158,
      54, 105, 102, 27, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85,
      245, 245, 1, 110, 73, 160, 241]

private def invalidBitLengthRepeatZlibFixture : ByteArray :=
  byteArrayOfNats
    [120, 1, 13, 192, 129, 8, 0, 0, 0, 0, 32, 182, 253, 165, 78, 0, 66, 0, 66]

private def invalidCodeLengthsSetZlibFixture : ByteArray :=
  byteArrayOfNats
    [120, 1, 5, 224, 129, 8, 0, 0, 0, 0, 32, 182, 253, 165, 78, 0, 66, 0, 66]

private def truncatedDynamicZlibFixture : ByteArray :=
  byteArrayOfNats
    [120, 218, 237, 195, 49, 13, 0, 0, 8, 3, 48, 109, 131, 249, 215, 132, 12, 158,
      54, 105, 102, 27, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85,
      245, 245, 1, 110, 73]

private def incorrectDataCheckZlibFixture : ByteArray :=
  byteArrayOfNats
    [120, 1, 5, 192, 129, 8, 0, 0, 0, 0, 32, 182, 253, 165, 78, 0, 66, 0, 67]

private def copyDistanceSlow (out : ByteArray) (distance len : Nat) : Option ByteArray :=
  if _hbad : distance = 0 ∨ distance > out.size then
    none
  else
    some <| Id.run do
      let mut out := out
      for _ in [0:len] do
        let src := out.size - distance
        out := out.push (out.get! src)
      return out

private def validateDynamicZlibFixtures : IO Unit := do
  let cases :=
    [("literal-only-zero-distance", dynamicLiteralOnlyZeroDistZlibFixture,
        dynamicLiteralOnlyZeroDistRawFixture),
      ("repeat-codes", dynamicRepeatCodeZlibFixture, dynamicRepeatCodeRawFixture),
      ("repeat", dynamicRepeatZlibFixture, dynamicRepeatRawFixture),
      ("mixed", dynamicMixedZlibFixture, dynamicMixedRawFixture),
      ("multi-block", dynamicMultiBlockZlibFixture, dynamicMultiBlockRawFixture)]
  for case in cases do
    let name := case.1
    let zlibBytes := case.2.1
    let raw := case.2.2
    if zlibFirstBlockType? zlibBytes != some 2 then
      throw (IO.userError s!"dynamic zlib fixture {name} is not using a dynamic first block")
    match zlibDecompressFixture zlibBytes with
    | some raw' =>
        if raw' != raw then
          throw (IO.userError s!"dynamic zlib fixture {name} decompressed to the wrong payload")
    | none =>
        throw (IO.userError s!"dynamic zlib fixture {name} failed to decompress")

private def validateMalformedDynamicFixtures : IO Unit := do
  let cases :=
    [("bad-header-checksum", badHeaderChecksumZlibFixture),
      ("invalid-bit-length-repeat", invalidBitLengthRepeatZlibFixture),
      ("invalid-code-lengths-set", invalidCodeLengthsSetZlibFixture),
      ("truncated-dynamic", truncatedDynamicZlibFixture),
      ("incorrect-data-check", incorrectDataCheckZlibFixture)]
  for case in cases do
    let name := case.1
    let zlibBytes := case.2
    match zlibDecompressFixture zlibBytes with
    | none => pure ()
    | some _ =>
        throw (IO.userError s!"malformed dynamic fixture {name} unexpectedly decompressed")

/-- Exhaustively checks one `(base, distance)` pair against the slow overlap reference. -/
private def validateCopyDistanceLens (base : ByteArray) (size distance : Nat) :
    List Nat -> IO Unit :=
  fun lens =>
    match lens with
    | [] => pure ()
    | len :: lens => do
        let fast := Png.copyDistanceFast base distance len
        let slow := copyDistanceSlow base distance len
        if fast != slow then
          throw (IO.userError
            s!"copyDistanceFast mismatch for size={size}, distance={distance}, len={len}")
        validateCopyDistanceLens base size distance lens

/-- Runs the overlap regression across every valid distance for a fixed base size. -/
private def validateCopyDistanceDistances (base : ByteArray) (size : Nat) :
    List Nat -> IO Unit :=
  fun distances =>
    match distances with
    | [] => pure ()
    | distance0 :: distances => do
        let distance := distance0 + 1
        validateCopyDistanceLens base size distance (List.range 13)
        validateCopyDistanceDistances base size distances

/-- Walks the fixed family of bases used to validate `copyDistanceFast`. -/
private def validateCopyDistanceSizes : List Nat -> IO Unit :=
  fun sizes =>
    match sizes with
    | [] => pure ()
    | size0 :: sizes => do
        let size := size0 + 1
        let base := deterministicPrefix size
        validateCopyDistanceDistances base size (List.range size)
        validateCopyDistanceSizes sizes

private def validateCopyDistanceFast : IO Unit := do
  validateCopyDistanceSizes (List.range 8)
  let base := deterministicPrefix 4
  if Png.copyDistanceFast base 0 3 != none then
    throw (IO.userError "copyDistanceFast accepted distance = 0")
  if Png.copyDistanceFast base 5 3 != none then
    throw (IO.userError "copyDistanceFast accepted distance beyond the output size")

private def oneBitCodeLenHuffman (sym : Nat) : Png.Huffman :=
  { maxLen := 1
    table := #[#[], #[some sym, none]] }

private def bitReaderOfByte (bits : Nat) : Png.BitReader :=
  { data := byteArrayOfNats [bits]
    bytePos := 0
    bitPos := 0
    hpos := by exact Nat.zero_le _
    hend := by intro _; rfl
    hbit := by decide }

private def readSingleRepeatLengths? (sym bits total : Nat) (init : Array Nat) :
    Option (Array Nat × Png.BitReader) :=
  Png.readDynamicTablesLengthsFuel 4 total (oneBitCodeLenHuffman sym) (bitReaderOfByte bits) init

private def assertRepeatLengths
    (name : String) (sym bits total fill : Nat) (init : Array Nat) : IO Unit := do
  match readSingleRepeatLengths? sym bits total init with
  | some (lengths, _) =>
      if lengths.size == total && lengths.toList.all (fun len => len == fill) then
        pure ()
      else
        throw (IO.userError s!"dynamic repeat {name} produced unexpected lengths")
  | none =>
      throw (IO.userError s!"dynamic repeat {name} failed to decode")

private def validateDynamicRepeatEncodings : IO Unit := do
  assertRepeatLengths "16" 16 6 7 7 #[7]
  assertRepeatLengths "17" 17 14 10 0 #[]
  assertRepeatLengths "18" 18 254 138 0 #[]
  match readSingleRepeatLengths? 16 0 1 #[] with
  | none => pure ()
  | some _ =>
      throw (IO.userError "dynamic repeat 16 accepted without a previous length")
  match readSingleRepeatLengths? 18 254 137 #[] with
  | some (lengths, _) =>
      if lengths.size > 137 then
        pure ()
      else
        throw (IO.userError "dynamic repeat 18 overflow did not exceed the requested length total")
  | none =>
      throw (IO.userError "dynamic repeat 18 overflow failed before exact-size validation")

private def validateDynamicTableValidationBoundary : IO Unit := do
  if Png.mkHuffman #[1, 1, 1] != none then
    throw (IO.userError "mkHuffman accepted an oversubscribed 1-bit code set")
  if Png.mkHuffman #[2, 2, 2, 2, 2] != none then
    throw (IO.userError "mkHuffman accepted an oversubscribed 2-bit code set")
  if Png.buildDynamicDistTable #[0] != some Png.emptyHuffman then
    throw (IO.userError "buildDynamicDistTable rejected the all-zero distance alphabet")
  match Png.buildDynamicDistTable #[1, 1] with
  | some _ => pure ()
  | none =>
      throw (IO.userError "buildDynamicDistTable rejected a valid non-empty distance alphabet")
  validateDynamicRepeatEncodings

-- Decode PNG fixtures that use fixed-Huffman deflate blocks.
private def pngDecodeFixedHuffmanFixtures : IO Unit := do
  let grayBytes <- IO.FS.readBinFile "test_gray.png"
  match Png.decodeBitmap (px := PixelGray8) grayBytes with
  | some bmp =>
      if bmp.size.width != 8 || bmp.size.height != 8 then
        throw (IO.userError "fixed-huffman gray fixture has unexpected size")
  | none =>
      throw (IO.userError "fixed-huffman gray fixture failed to decode")
  let rgbaBytes <- IO.FS.readBinFile "test_rgba.png"
  match Png.decodeBitmap (px := PixelRGBA8) rgbaBytes with
  | some bmp =>
      if bmp.size.width != 4 || bmp.size.height != 4 then
        throw (IO.userError "fixed-huffman RGBA fixture has unexpected size")
  | none =>
      throw (IO.userError "fixed-huffman RGBA fixture failed to decode")

-- All tolerated-chunk fixtures are 4x4 RGB images sharing the same pixel pattern,
-- so decoding any of them must yield this canonical reference bitmap.
-- Generated by `scripts/generate-anc-fixtures.py`; keep this matrix in sync.
private def ancFixtureReferenceData : ByteArray :=
  let nats : Array Nat := #[
    255, 0, 0,   0, 255, 0,   0, 0, 255,   255, 255, 255,
    0, 0, 0,   128, 128, 128,   192, 192, 192,   64, 64, 64,
    0, 255, 255,   255, 0, 255,   255, 255, 0,   255, 128, 0,
    128, 0, 0,   0, 128, 0,   0, 0, 128,   100, 100, 100
  ]
  ByteArray.mk (nats.map UInt8.ofNat)

private def ancFixtureReferenceDataTransparentBlack : ByteArray :=
  Id.run do
    let mut out := ByteArray.emptyWithCapacity (4 * 4 * 4)
    for i in [0:16] do
      let base := i * 3
      let r := ancFixtureReferenceData.get! base
      let g := ancFixtureReferenceData.get! (base + 1)
      let b := ancFixtureReferenceData.get! (base + 2)
      let a :=
        if r == Png.u8 0 && g == Png.u8 0 && b == Png.u8 0 then
          Png.u8 0
        else
          Png.u8 255
      out := out.push r
      out := out.push g
      out := out.push b
      out := out.push a
    return out

private def ancFixtureReferenceDataBlackOnBackground : ByteArray :=
  Id.run do
    let mut out := ByteArray.emptyWithCapacity (4 * 4 * 3)
    for i in [0:16] do
      let base := i * 3
      let r0 := ancFixtureReferenceData.get! base
      let g0 := ancFixtureReferenceData.get! (base + 1)
      let b0 := ancFixtureReferenceData.get! (base + 2)
      let (r, g, b) :=
        if r0 == Png.u8 0 && g0 == Png.u8 0 && b0 == Png.u8 0 then
          (Png.u8 100, Png.u8 100, Png.u8 100)
        else
          (r0, g0, b0)
      out := out.push r
      out := out.push g
      out := out.push b
    return out

private def ancFixtureRgbaOverBlueReferenceData : ByteArray :=
  Id.run do
    let mut out := ByteArray.emptyWithCapacity (4 * 4 * 3)
    for _ in [0:16] do
      out := out.push (Png.u8 128)
      out := out.push (Png.u8 0)
      out := out.push (Png.u8 127)
    return out

private def grayAlphaFixture : BitmapGrayAlpha8 :=
  BitmapGrayAlpha8.ofPixelFn 2 2 (fun idx : Fin (2 * 2) =>
    match idx.val with
    | 0 => { v := Png.u8 0, a := Png.u8 0 }
    | 1 => { v := Png.u8 64, a := Png.u8 128 }
    | 2 => { v := Png.u8 128, a := Png.u8 255 }
    | _ => { v := Png.u8 255, a := Png.u8 64 })

private def grayAlphaFixtureExpectedRGBAData : ByteArray :=
  Id.run do
    let mut out := ByteArray.emptyWithCapacity (2 * 2 * 4)
    for i in [0:4] do
      let base := i * 2
      let gray := grayAlphaFixture.data.get! base
      let alpha := grayAlphaFixture.data.get! (base + 1)
      out := out.push gray
      out := out.push gray
      out := out.push gray
      out := out.push alpha
    return out

private def grayAlphaOverBackgroundRGBData (background : UInt8) : ByteArray :=
  Id.run do
    let mut out := ByteArray.emptyWithCapacity (2 * 2 * 3)
    for i in [0:4] do
      let base := i * 2
      let gray := grayAlphaFixture.data.get! base
      let alpha := grayAlphaFixture.data.get! (base + 1)
      let composite := Png.alphaCompositeByte gray background alpha
      out := out.push composite
      out := out.push composite
      out := out.push composite
    return out

private def grayAlphaOverBackgroundGrayData (background : UInt8) : ByteArray :=
  Id.run do
    let mut out := ByteArray.emptyWithCapacity (2 * 2)
    for i in [0:4] do
      let base := i * 2
      let gray := grayAlphaFixture.data.get! base
      let alpha := grayAlphaFixture.data.get! (base + 1)
      out := out.push (Png.alphaCompositeByte gray background alpha)
    return out

private def grayAlphaPngWithAncillary (ancillary : ByteArray) : ByteArray :=
  let raw := Png.encodeRawFast grayAlphaFixture
  let idat := Png.zlibCompressFixed raw
  let ihdr :=
    Png.u32be grayAlphaFixture.size.width ++
    Png.u32be grayAlphaFixture.size.height ++
    ByteArray.mk #[Png.u8 8, Png.u8 4, Png.u8 0, Png.u8 0, Png.u8 0]
  Png.pngSignature ++
    Png.mkChunkBytes Png.ihdrTypeBytes ihdr ++
    ancillary ++
    Png.mkChunkBytes Png.idatTypeBytes idat ++
    Png.mkChunkBytes Png.iendTypeBytes ByteArray.empty

private def grayAlphaPng : ByteArray :=
  grayAlphaPngWithAncillary ByteArray.empty

private def grayAlphaPngWithBkgd : ByteArray :=
  grayAlphaPngWithAncillary
    (Png.mkChunkBytes Png.bkgdTypeBytes (ByteArray.mk #[Png.u8 0, Png.u8 100]))

private def grayAlphaPngWithTrns : ByteArray :=
  grayAlphaPngWithAncillary
    (Png.mkChunkBytes Png.trnsTypeBytes (ByteArray.mk #[Png.u8 0, Png.u8 0]))

private def u16 (n : Nat) : UInt16 :=
  UInt16.ofNat n

private def rgb16DownsampleFixture : BitmapRGB16 :=
  BitmapRGB16.ofPixelFn 2 1 (fun idx : Fin (2 * 1) =>
    match idx.val with
    | 0 => { r := u16 0x12ab, g := u16 0x3456, b := u16 0xfedc }
    | _ => { r := u16 0x0102, g := u16 0x8001, b := u16 0x00ff })

private def rgba16DownsampleFixture : BitmapRGBA16 :=
  BitmapRGBA16.ofPixelFn 2 1 (fun idx : Fin (2 * 1) =>
    match idx.val with
    | 0 => { r := u16 0x12ab, g := u16 0x3456, b := u16 0xfedc, a := u16 0x7788 }
    | _ => { r := u16 0x0102, g := u16 0x8001, b := u16 0x00ff, a := u16 0xffff })

private def gray16DownsampleFixture : BitmapGray16 :=
  BitmapGray16.ofPixelFn 3 1 (fun idx : Fin (3 * 1) =>
    match idx.val with
    | 0 => { v := u16 0x12ab }
    | 1 => { v := u16 0x8001 }
    | _ => { v := u16 0x00ff })

private def grayAlpha16DownsampleFixture : BitmapGrayAlpha16 :=
  BitmapGrayAlpha16.ofPixelFn 2 1 (fun idx : Fin (2 * 1) =>
    match idx.val with
    | 0 => { v := u16 0x12ab, a := u16 0x3456 }
    | _ => { v := u16 0x8001, a := u16 0x00ff })

private def encodeFixturePng {px : Type} [Pixel px] [Png.PngPixel px]
    (bmp : Bitmap px) : IO ByteArray := do
  match Png.encodeBitmapChecked (px := px) bmp .fixed with
  | Except.ok bytes => pure bytes
  | Except.error err => throw (IO.userError err)

private def expect16To8Downsample : IO Unit := do
  let rgbBytes ← encodeFixturePng rgb16DownsampleFixture
  match Png.decodeBitmap (px := PixelRGB8) rgbBytes with
  | some bmp =>
      if bmp.data != ByteArray.mk #[0x12, 0x34, 0xfe, 0x01, 0x80, 0x00] then
        throw (IO.userError "RGB16 -> RGB8 downsample used unexpected bytes")
  | none =>
      throw (IO.userError "RGB16 -> RGB8 downsample failed")
  let rgbaBytes ← encodeFixturePng rgba16DownsampleFixture
  match Png.decodeBitmap (px := PixelRGBA8) rgbaBytes with
  | some bmp =>
      if bmp.data != ByteArray.mk #[0x12, 0x34, 0xfe, 0x77, 0x01, 0x80, 0x00, 0xff] then
        throw (IO.userError "RGBA16 -> RGBA8 downsample used unexpected bytes")
  | none =>
      throw (IO.userError "RGBA16 -> RGBA8 downsample failed")
  let grayBytes ← encodeFixturePng gray16DownsampleFixture
  match Png.decodeBitmap (px := PixelGray8) grayBytes with
  | some bmp =>
      if bmp.data != ByteArray.mk #[0x12, 0x80, 0x00] then
        throw (IO.userError "Gray16 -> Gray8 downsample used unexpected bytes")
  | none =>
      throw (IO.userError "Gray16 -> Gray8 downsample failed")
  let grayAlphaBytes ← encodeFixturePng grayAlpha16DownsampleFixture
  match Png.decodeBitmap (px := PixelGrayAlpha8) grayAlphaBytes with
  | some bmp =>
      if bmp.data != ByteArray.mk #[0x12, 0x34, 0x80, 0x00] then
        throw (IO.userError "GrayAlpha16 -> GrayAlpha8 downsample used unexpected bytes")
  | none =>
      throw (IO.userError "GrayAlpha16 -> GrayAlpha8 downsample failed")

private def expectGrayAlphaFixtures : IO Unit := do
  match Png.decodeBitmap (px := PixelGrayAlpha8) grayAlphaPng with
  | some bmp =>
      if bmp != grayAlphaFixture then
        throw (IO.userError "gray+alpha PNG did not decode exactly")
  | none =>
      throw (IO.userError "gray+alpha PNG failed to decode")
  match Png.decodeBitmap (px := PixelRGBA8) grayAlphaPng with
  | some bmp =>
      if bmp.size.width != 2 || bmp.size.height != 2 ||
          bmp.data != grayAlphaFixtureExpectedRGBAData then
        throw (IO.userError "gray+alpha PNG did not expand to RGBA")
  | none =>
      throw (IO.userError "gray+alpha PNG failed to decode as RGBA")
  if (Png.decodeBitmap (px := PixelRGB8) grayAlphaPng).isSome then
    throw (IO.userError "pixel-only RGB decode accepted gray+alpha without bKGD")
  if (Png.decodeBitmap (px := PixelGray8) grayAlphaPng).isSome then
    throw (IO.userError "pixel-only Gray decode accepted gray+alpha without bKGD")
  match Png.decodeBitmapWithMetadata (px := PixelGrayAlpha8) grayAlphaPngWithBkgd with
  | some decoded =>
      if decoded.bitmap != grayAlphaFixture then
        throw (IO.userError "bKGD changed exact gray+alpha decode")
      match decoded.metadata.background with
      | some (Png.PngBackground.gray8 gray) =>
          if gray != Png.u8 100 then
            throw (IO.userError "gray+alpha bKGD metadata had wrong value")
      | _ =>
          throw (IO.userError "gray+alpha bKGD metadata was missing")
  | none =>
      throw (IO.userError "metadata-aware gray+alpha bKGD decode failed")
  match Png.decodeBitmapWithMetadata (px := PixelRGB8) grayAlphaPngWithBkgd with
  | some decoded =>
      if decoded.bitmap.data != grayAlphaOverBackgroundRGBData (Png.u8 100) then
        throw (IO.userError "gray+alpha bKGD RGB composition mismatch")
  | none =>
      throw (IO.userError "gray+alpha bKGD RGB decode failed")
  match Png.decodeBitmapWithMetadata (px := PixelGray8) grayAlphaPngWithBkgd with
  | some decoded =>
      if decoded.bitmap.data != grayAlphaOverBackgroundGrayData (Png.u8 100) then
        throw (IO.userError "gray+alpha bKGD Gray composition mismatch")
  | none =>
      throw (IO.userError "gray+alpha bKGD Gray decode failed")
  if (Png.decodeBitmapWithMetadata (px := PixelRGBA8) grayAlphaPngWithTrns).isSome then
    throw (IO.userError "metadata-aware decoder accepted tRNS for gray+alpha")

private def expectAncDecodeOk (path : System.FilePath) : IO Unit := do
  let bytes <- IO.FS.readBinFile path
  match Png.decodeBitmap (px := PixelRGB8) bytes with
  | some bmp =>
      if bmp.size.width != 4 || bmp.size.height != 4 then
        throw (IO.userError s!"{path}: unexpected dimensions {bmp.size.width}x{bmp.size.height}")
      if bmp.data != ancFixtureReferenceData then
        throw (IO.userError s!"{path}: pixel data mismatch against reference pattern")
  | none =>
      throw (IO.userError s!"{path}: tolerated-chunk fixture failed to decode")

private def expectAncTrnsRgbaOk (path : System.FilePath) : IO Unit := do
  let bytes <- IO.FS.readBinFile path
  match Png.decodeBitmapWithMetadata (px := PixelRGBA8) bytes with
  | some decoded =>
      if decoded.bitmap.size.width != 4 || decoded.bitmap.size.height != 4 then
        throw (IO.userError s!"{path}: unexpected dimensions {decoded.bitmap.size.width}x{decoded.bitmap.size.height}")
      if decoded.bitmap.data != ancFixtureReferenceDataTransparentBlack then
        throw (IO.userError s!"{path}: tRNS alpha did not match the transparent-black reference")
      match decoded.metadata.transparency with
      | some (Png.PngTransparency.rgb8 r g b) =>
          if r == Png.u8 0 && g == Png.u8 0 && b == Png.u8 0 then
            pure ()
          else
            throw (IO.userError s!"{path}: unexpected tRNS RGB value")
      | _ =>
          throw (IO.userError s!"{path}: missing tRNS metadata")
  | none =>
      throw (IO.userError s!"{path}: metadata-aware RGBA tRNS decode failed")

private def expectAncTrnsBkgdRgbOk (path : System.FilePath) : IO Unit := do
  let bytes <- IO.FS.readBinFile path
  match Png.decodeBitmapWithMetadata (px := PixelRGB8) bytes with
  | some decoded =>
      if decoded.bitmap.size.width != 4 || decoded.bitmap.size.height != 4 then
        throw (IO.userError s!"{path}: unexpected dimensions {decoded.bitmap.size.width}x{decoded.bitmap.size.height}")
      if decoded.bitmap.data != ancFixtureReferenceDataBlackOnBackground then
        throw (IO.userError s!"{path}: tRNS+bKGD RGB composition did not match reference")
      match decoded.metadata.transparency, decoded.metadata.background with
      | some (Png.PngTransparency.rgb8 tr tg tb), some (Png.PngBackground.rgb8 br bg bb) =>
          if tr == Png.u8 0 && tg == Png.u8 0 && tb == Png.u8 0 &&
              br == Png.u8 100 && bg == Png.u8 100 && bb == Png.u8 100 then
            pure ()
          else
            throw (IO.userError s!"{path}: unexpected tRNS+bKGD metadata")
      | _, _ =>
          throw (IO.userError s!"{path}: missing tRNS+bKGD metadata")
  | none =>
      throw (IO.userError s!"{path}: metadata-aware tRNS+bKGD RGB decode failed")

private def expectAncRgbaBkgdRgbOk (path : System.FilePath) : IO Unit := do
  let bytes <- IO.FS.readBinFile path
  match Png.decodeBitmapWithMetadata (px := PixelRGB8) bytes with
  | some decoded =>
      if decoded.bitmap.size.width != 4 || decoded.bitmap.size.height != 4 then
        throw (IO.userError s!"{path}: unexpected dimensions {decoded.bitmap.size.width}x{decoded.bitmap.size.height}")
      if decoded.bitmap.data != ancFixtureRgbaOverBlueReferenceData then
        throw (IO.userError s!"{path}: RGBA+bKGD RGB composition did not match reference")
      match decoded.metadata.background with
      | some (Png.PngBackground.rgb8 r g b) =>
          if r == Png.u8 0 && g == Png.u8 0 && b == Png.u8 255 then
            pure ()
          else
            throw (IO.userError s!"{path}: unexpected RGBA bKGD metadata")
      | _ =>
          throw (IO.userError s!"{path}: missing RGBA bKGD metadata")
  | none =>
      throw (IO.userError s!"{path}: metadata-aware RGBA+bKGD RGB decode failed")

private def expectAncBkgdRgbOk (path : System.FilePath) : IO Unit := do
  let bytes <- IO.FS.readBinFile path
  match Png.decodeBitmapWithMetadata (px := PixelRGB8) bytes with
  | some decoded =>
      if decoded.bitmap.size.width != 4 || decoded.bitmap.size.height != 4 then
        throw (IO.userError s!"{path}: unexpected dimensions {decoded.bitmap.size.width}x{decoded.bitmap.size.height}")
      if decoded.bitmap.data != ancFixtureReferenceData then
        throw (IO.userError s!"{path}: bKGD changed decoded RGB pixels")
      match decoded.metadata.background with
      | some (Png.PngBackground.rgb8 r g b) =>
          if r == Png.u8 100 && g == Png.u8 100 && b == Png.u8 100 then
            pure ()
          else
            throw (IO.userError s!"{path}: unexpected bKGD RGB value")
      | _ =>
          throw (IO.userError s!"{path}: missing bKGD RGB metadata")
  | none =>
      throw (IO.userError s!"{path}: metadata-aware bKGD RGB decode failed")

private def expectAncBkgdGrayOk (path : System.FilePath) : IO Unit := do
  let bytes <- IO.FS.readBinFile path
  match Png.decodeBitmapWithMetadata (px := PixelGray8) bytes with
  | some decoded =>
      if decoded.bitmap.size.width != 4 || decoded.bitmap.size.height != 4 then
        throw (IO.userError s!"{path}: unexpected dimensions {decoded.bitmap.size.width}x{decoded.bitmap.size.height}")
      match decoded.metadata.background with
      | some (Png.PngBackground.gray8 gray) =>
          if gray == Png.u8 64 then
            pure ()
          else
            throw (IO.userError s!"{path}: unexpected bKGD gray value")
      | _ =>
          throw (IO.userError s!"{path}: missing bKGD gray metadata")
  | none =>
      throw (IO.userError s!"{path}: metadata-aware bKGD gray decode failed")

private def expectAncDecodeNone (path : System.FilePath) (label : String) : IO Unit := do
  let bytes <- IO.FS.readBinFile path
  match Png.decodeBitmap (px := PixelRGB8) bytes with
  | some _ =>
      throw (IO.userError s!"{path}: decoder accepted a {label} fixture that should be rejected")
  | none =>
      pure ()

private def expectAncMetadataDecodeNone (path : System.FilePath) (label : String) : IO Unit := do
  let bytes <- IO.FS.readBinFile path
  match Png.decodeBitmapWithMetadata (px := PixelRGBA8) bytes with
  | some _ =>
      throw (IO.userError s!"{path}: metadata-aware decoder accepted a {label} fixture that should be rejected")
  | none =>
      pure ()

-- Verify the tolerate-and-skip behavior for ancillary chunks plus the
-- rejection guarantees for pixel-affecting chunks, unknown critical chunks,
-- and CRC mismatches. All fixtures live at the repo root next to test_*.png.
private def pngAncillaryChunkFixtures : IO Unit := do
  -- Tolerated: gAMA + pHYs metadata, tEXt comment, multiple consecutive IDATs,
  -- and an unknown ancillary chunk type ("myCh") all decode to the reference pattern.
  expectAncDecodeOk "test_anc_meta.png"
  expectAncDecodeOk "test_anc_text.png"
  expectAncDecodeOk "test_anc_multi_idat.png"
  expectAncDecodeOk "test_anc_unknown_anc.png"
  expectAncTrnsRgbaOk "test_anc_trns.png"
  expectAncDecodeNone "test_anc_trns.png" "tRNS dropped into RGB"
  expectAncBkgdRgbOk "test_anc_bkgd_rgb.png"
  expectAncTrnsBkgdRgbOk "test_anc_trns_bkgd.png"
  expectAncRgbaBkgdRgbOk "test_anc_rgba_bkgd.png"
  expectAncBkgdGrayOk "test_anc_bkgd_gray.png"
  -- Rejected: malformed or out-of-order metadata chunks, pixel-affecting chunks
  -- the decoder doesn't honor, an unknown critical chunk type ("MyCh"), and bad CRCs.
  expectAncDecodeNone "test_anc_unknown_critical.png" "unknown-critical"
  expectAncMetadataDecodeNone "test_anc_trns_bad_len.png" "bad tRNS length"
  expectAncMetadataDecodeNone "test_anc_trns_after_idat.png" "tRNS after IDAT"
  expectAncMetadataDecodeNone "test_anc_trns_duplicate.png" "duplicate tRNS"
  expectAncMetadataDecodeNone "test_anc_plte_after_trns.png" "PLTE after tRNS"
  expectAncMetadataDecodeNone "test_anc_trns_rgba.png" "tRNS in RGBA"
  expectAncMetadataDecodeNone "test_anc_bkgd_bad_len.png" "bad bKGD length"
  expectAncMetadataDecodeNone "test_anc_bkgd_after_idat.png" "bKGD after IDAT"
  expectAncMetadataDecodeNone "test_anc_bkgd_duplicate.png" "duplicate bKGD"
  expectAncMetadataDecodeNone "test_anc_plte_after_bkgd.png" "PLTE after bKGD"
  expectAncDecodeNone "test_anc_sbit.png" "sBIT"
  expectAncDecodeNone "test_anc_bad_crc.png" "bad-CRC"

-- Fill a bitmap with deterministic pixels using putPixel, then read all pixels back.
-- Returns elapsed time in nanoseconds and a checksum to prevent dead-code elimination.
private def perfFillRead (w h : Nat) : IO (Nat × Nat) := do
  let t0 <- IO.monoNanosNow
  let xs : Array (Fin w) := Array.finRange w
  let ys : Array (Fin h) := Array.finRange h
  let img0 := mkBlankBitmap w h { r := 0, g := 0, b := 0 }
  let acc0 :
      { img : BitmapRGB8 // img.size.width = w ∧ img.size.height = h } :=
    ⟨img0, by rfl, by rfl⟩
  let accFilled :=
    ys.foldl (init := acc0)
      (fun (acc : { img : BitmapRGB8 // img.size.width = w ∧ img.size.height = h }) (y : Fin h) =>
        xs.foldl (init := acc)
          (fun (acc : { img : BitmapRGB8 // img.size.width = w ∧ img.size.height = h }) (x : Fin w) =>
            let img := acc.1
            have hwidth : img.size.width = w := acc.2.1
            have hheight : img.size.height = h := acc.2.2
            have hx : x.val < img.size.width := by
              simp [hwidth]
            have hy : y.val < img.size.height := by
              simp [hheight]
            let r := UInt8.ofNat ((x.val + y.val) % 256)
            let g := UInt8.ofNat ((x.val * 3 + y.val) % 256)
            let b := UInt8.ofNat ((x.val + 2 * y.val) % 256)
            let img' := putPixel img x.val y.val { r := r, g := g, b := b } hx hy
            have hwidth' : img'.size.width = w := by
              have hsame : img'.size.width = img.size.width := by rfl
              exact hsame.trans hwidth
            have hheight' : img'.size.height = h := by
              have hsame : img'.size.height = img.size.height := by rfl
              exact hsame.trans hheight
            ⟨img', hwidth', hheight'⟩))
  let img := accFilled.1
  let hwidth : img.size.width = w := accFilled.2.1
  let hheight : img.size.height = h := accFilled.2.2
  let mut checksum : Nat := 0
  for y in ys do
    for x in xs do
      have hx : x.val < img.size.width := by
        simp [hwidth]
      have hy : y.val < img.size.height := by
        simp [hheight]
      let px := getPixel img x.val y.val hx hy
      checksum := checksum + px.r.toNat + px.g.toNat + px.b.toNat
  let t1 <- IO.monoNanosNow
  return (t1 - t0, checksum)

-- Encode a blank bitmap to PNG and decode it back.
-- Returns elapsed time in nanoseconds and whether the round-trip was exact.
private def perfPngRoundTrip (w h : Nat) : IO (Nat × Bool) := do
  let t0 <- IO.monoNanosNow
  let bmp := mkBlankBitmap w h { r := 0, g := 0, b := 0 }
  let bytes ←
    match Png.encodeBitmapChecked (px := PixelRGB8) bmp .fixed with
    | Except.ok bytes => pure bytes
    | Except.error err => throw (IO.userError err)
  let ok :=
    match Png.decodeBitmap bytes with
    | some bmp' => decide (bmp' = bmp)
    | none => false
  let t1 <- IO.monoNanosNow
  return (t1 - t0, ok)

-- Encode a blank bitmap using dynamic deflate blocks and decode it back.
-- Returns elapsed time in nanoseconds and whether the round-trip was exact.
private def perfPngRoundTripDynamic (w h : Nat) : IO (Nat × Bool) := do
  let t0 <- IO.monoNanosNow
  let bmp := mkBlankBitmap w h { r := 0, g := 0, b := 0 }
  let bytes ←
    match Png.encodeBitmapChecked (px := PixelRGB8) bmp .dynamic with
    | Except.ok bytes => pure bytes
    | Except.error err => throw (IO.userError err)
  let ok :=
    match Png.decodeBitmap bytes with
    | some bmp' => decide (bmp' = bmp)
    | none => false
  let t1 <- IO.monoNanosNow
  return (t1 - t0, ok)

-- Encode a blank bitmap using stored deflate blocks and decode it back.
-- Returns elapsed time in nanoseconds and whether the round-trip was exact.
private def perfPngRoundTripStored (w h : Nat) : IO (Nat × Bool) := do
  let t0 <- IO.monoNanosNow
  let bmp := mkBlankBitmap w h { r := 0, g := 0, b := 0 }
  let bytes ←
    match Png.encodeBitmapChecked (px := PixelRGB8) bmp .stored with
    | Except.ok bytes => pure bytes
    | Except.error err => throw (IO.userError err)
  let ok :=
    match Png.decodeBitmap bytes with
    | some bmp' => decide (bmp' = bmp)
    | none => false
  let t1 <- IO.monoNanosNow
  return (t1 - t0, ok)

-- Fixed-size performance test for putPixel/getPixel on this machine.
-- Shared with the PNG perf checks so all runtime comparisons use the same image size.
-- Calibrated so the full benchmark section lands near 30 seconds here.
private def perfResolution : Nat := 3200

private def perfIters : Nat := 10

-- Fixed-size performance test for putPixel/getPixel on this machine.
private def runPerfTest : IO Unit := do
  let w : Nat := perfResolution
  let h : Nat := perfResolution
  let iters : Nat := perfIters
  let hb0 <- IO.getNumHeartbeats
  let mut totalNs : Nat := 0
  let mut totalChecksum : Nat := 0
  for _ in [0:iters] do
    let (elapsedNs, checksum) <- perfFillRead w h
    totalNs := totalNs + elapsedNs
    totalChecksum := totalChecksum + checksum
  let hb1 <- IO.getNumHeartbeats
  let avgNs := totalNs / iters
  let avgMs := avgNs / 1_000_000
  IO.println s!"perf put/get: {w}x{h} pixels, avg {avgMs} ms over {iters} runs, checksum {totalChecksum}, heartbeats {hb1 - hb0}"

-- Fixed-size performance test for PNG encode/decode on this machine.
private def runPngPerfTest : IO Unit := do
  let w : Nat := perfResolution
  let h : Nat := perfResolution
  let iters : Nat := perfIters
  let hb0 <- IO.getNumHeartbeats
  let mut totalNs : Nat := 0
  for _ in [0:iters] do
    let (elapsedNs, ok) <- perfPngRoundTrip w h
    if !ok then
      throw (IO.userError "png perf round-trip failed")
    totalNs := totalNs + elapsedNs
  let hb1 <- IO.getNumHeartbeats
  let avgNs := totalNs / iters
  let avgMs := avgNs / 1_000_000
  IO.println s!"perf png round-trip: {w}x{h} pixels, avg {avgMs} ms over {iters} runs, heartbeats {hb1 - hb0}"

-- Fixed-size performance test for PNG encode/decode via dynamic blocks.
private def runPngPerfTestDynamic : IO Unit := do
  let w : Nat := perfResolution
  let h : Nat := perfResolution
  let iters : Nat := perfIters
  let hb0 <- IO.getNumHeartbeats
  let mut totalNs : Nat := 0
  for _ in [0:iters] do
    let (elapsedNs, ok) <- perfPngRoundTripDynamic w h
    if !ok then
      throw (IO.userError "png perf dynamic round-trip failed")
    totalNs := totalNs + elapsedNs
  let hb1 <- IO.getNumHeartbeats
  let avgNs := totalNs / iters
  let avgMs := avgNs / 1_000_000
  IO.println s!"perf png dynamic round-trip: {w}x{h} pixels, avg {avgMs} ms over {iters} runs, heartbeats {hb1 - hb0}"

-- Fixed-size performance test for PNG encode/decode via stored blocks.
private def runPngPerfTestStored : IO Unit := do
  let w : Nat := perfResolution
  let h : Nat := perfResolution
  let iters : Nat := perfIters
  let hb0 <- IO.getNumHeartbeats
  let mut totalNs : Nat := 0
  for _ in [0:iters] do
    let (elapsedNs, ok) <- perfPngRoundTripStored w h
    if !ok then
      throw (IO.userError "png perf stored round-trip failed")
    totalNs := totalNs + elapsedNs
  let hb1 <- IO.getNumHeartbeats
  let avgNs := totalNs / iters
  let avgMs := avgNs / 1_000_000
  IO.println s!"perf png stored round-trip: {w}x{h} pixels, avg {avgMs} ms over {iters} runs, heartbeats {hb1 - hb0}"

def run : IO Unit := do
  pngDecodeFixedHuffmanFixtures
  expectGrayAlphaFixtures
  IO.println "png gray+alpha fixtures: ok"
  expect16To8Downsample
  IO.println "png 16-to-8 downsample fixtures: ok"
  pngAncillaryChunkFixtures
  IO.println "png ancillary-chunk fixtures: ok"
  validateDynamicTableValidationBoundary
  validateDynamicZlibFixtures
  validateMalformedDynamicFixtures
  validateCopyDistanceFast
  runPerfTest
  runPngPerfTest
  runPngPerfTestDynamic
  runPngPerfTestStored

end Bitmap.Tests

def main : IO Unit :=
  Bitmap.Tests.run
