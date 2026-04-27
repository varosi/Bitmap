import Bitmap.Basic
import Bitmap.Png

open Bitmaps

namespace Bitmap.Tests

private def prngStep (s : Nat) : Nat :=
  (1103515245 * s + 12345) % 2147483648

private def randByte (s : Nat) : UInt8 :=
  UInt8.ofNat (s % 256)

private def pixelOfSeed (seed idx : Nat) : PixelRGB8 :=
  let s1 := prngStep (seed + idx)
  let s2 := prngStep (s1 + 1)
  let s3 := prngStep (s2 + 1)
  { r := randByte s1, g := randByte s2, b := randByte s3 }

private def pixelGrayOfSeed (seed idx : Nat) : PixelGray8 :=
  let s1 := prngStep (seed + idx)
  { v := randByte s1 }

def bitmapOfSeed (seed w h : Nat) : BitmapRGB8 :=
  Bitmap.ofPixelFn w h (fun i : Fin (w * h) => pixelOfSeed seed i.val)

def bitmapGrayOfSeed (seed w h : Nat) : BitmapGray8 :=
  BitmapGray8.ofPixelFn w h (fun i : Fin (w * h) => pixelGrayOfSeed seed i.val)

def pngRoundTripOk (bmp : BitmapRGB8) : Bool :=
  match Png.encodeBitmapChecked (px := PixelRGB8) bmp .dynamic with
  | Except.error _ => false
  | Except.ok bytes =>
      match Png.decodeBitmap bytes with
      | some bmp' => decide (bmp' = bmp)
      | none => false

def pngRoundTripOkStored (bmp : BitmapRGB8) : Bool :=
  match Png.encodeBitmapChecked (px := PixelRGB8) bmp .stored with
  | Except.error _ => false
  | Except.ok bytes =>
      match Png.decodeBitmap bytes with
      | some bmp' => decide (bmp' = bmp)
      | none => false

def pngRoundTripOkRGBA (bmp : BitmapRGBA8) : Bool :=
  match Png.encodeBitmapChecked (px := PixelRGBA8) bmp .fixed with
  | Except.error _ => false
  | Except.ok bytes =>
      match Png.decodeBitmap (px := PixelRGBA8) bytes with
      | some bmp' => decide (bmp' = bmp)
      | none => false

def pngRoundTripOkGray (bmp : BitmapGray8) : Bool :=
  match Png.encodeBitmapChecked (px := PixelGray8) bmp .fixed with
  | Except.error _ => false
  | Except.ok bytes =>
      match Png.decodeBitmap (px := PixelGray8) bytes with
      | some bmp' => decide (bmp' = bmp)
      | none => false

def pngRoundTripProperty (trials : Nat) : IO Bool := do
  let mut ok := true
  let mut i := 0
  while i < trials && ok do
    let w <- IO.rand 1 16
    let h <- IO.rand 1 16
    let seed <- IO.rand 0 1000000
    let bmp := bitmapOfSeed seed w h
    if pngRoundTripOk bmp then
      i := i + 1
    else
      ok := false
  return ok

def pngRoundTripPropertyStored (trials : Nat) : IO Bool := do
  let mut ok := true
  let mut i := 0
  while i < trials && ok do
    let w <- IO.rand 1 16
    let h <- IO.rand 1 16
    let seed <- IO.rand 0 1000000
    let bmp := bitmapOfSeed seed w h
    if pngRoundTripOkStored bmp then
      i := i + 1
    else
      ok := false
  return ok

def pngRoundTripPropertyRGBA (trials : Nat) : IO Bool := do
  let mut ok := true
  let mut i := 0
  while i < trials && ok do
    let w <- IO.rand 1 16
    let h <- IO.rand 1 16
    let seed <- IO.rand 0 1000000
    let bmp := BitmapRGBA8.ofPixelFn w h (fun idx : Fin (w * h) =>
      let px := pixelOfSeed seed idx.val
      let a := randByte (prngStep (seed + idx.val + 7))
      { r := px.r, g := px.g, b := px.b, a := a })
    if pngRoundTripOkRGBA bmp then
      i := i + 1
    else
      ok := false
  return ok

def pngRoundTripPropertyGray (trials : Nat) : IO Bool := do
  let mut ok := true
  let mut i := 0
  while i < trials && ok do
    let w <- IO.rand 1 16
    let h <- IO.rand 1 16
    let seed <- IO.rand 0 1000000
    let bmp := bitmapGrayOfSeed seed w h
    if pngRoundTripOkGray bmp then
      i := i + 1
    else
      ok := false
  return ok

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

private def expectAncDecodeNone (path : System.FilePath) (label : String) : IO Unit := do
  let bytes <- IO.FS.readBinFile path
  match Png.decodeBitmap (px := PixelRGB8) bytes with
  | some _ =>
      throw (IO.userError s!"{path}: decoder accepted a {label} fixture that should be rejected")
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
  -- Rejected: pixel-affecting chunks the decoder doesn't honor, an unknown
  -- critical chunk type ("MyCh"), and a chunk with a corrupted CRC.
  expectAncDecodeNone "test_anc_unknown_critical.png" "unknown-critical"
  expectAncDecodeNone "test_anc_trns.png" "tRNS"
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
  let ok <- pngRoundTripProperty 20
  if ok then
    IO.println "png round-trip property: ok"
  else
    throw (IO.userError "png round-trip property failed")
  let okStored <- pngRoundTripPropertyStored 20
  if okStored then
    IO.println "png round-trip stored property: ok"
  else
    throw (IO.userError "png round-trip stored property failed")
  let okRgba <- pngRoundTripPropertyRGBA 20
  if okRgba then
    IO.println "png round-trip RGBA property: ok"
  else
    throw (IO.userError "png round-trip RGBA property failed")
  let okGray <- pngRoundTripPropertyGray 20
  if okGray then
    IO.println "png round-trip Gray property: ok"
  else
    throw (IO.userError "png round-trip Gray property failed")
  pngDecodeFixedHuffmanFixtures
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
