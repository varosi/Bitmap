import Bitmap.Basic
import Bitmap.Png
import Bitmap.Png.Parallel
import Bitmap.Widget

open Bitmaps

namespace Bitmap.Tests

private def testFixturePath (name : String) : System.FilePath :=
  System.FilePath.mk s!"Bitmap/Tests/{name}"

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

private def repeatByteArray (count : Nat) (byte : UInt8) : ByteArray :=
  Id.run do
    let mut out := ByteArray.emptyWithCapacity count
    for _ in [0:count] do
      out := out.push byte
    return out

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

private def bitReaderOfBytes (bytes : ByteArray) : Png.BitReader :=
  { data := bytes
    bytePos := 0
    bitPos := 0
    hpos := by exact Nat.zero_le _
    hend := by intro _; rfl
    hbit := by decide }

private def dynamicTablesFromDeflate? (deflated : ByteArray) :
    Option (Png.Huffman × Png.Huffman) := do
  let br0 := bitReaderOfBytes deflated
  let (hdr, br1) ←
    if h : br0.bitIndex + 3 <= br0.data.size * 8 then
      some (br0.readBits 3 h)
    else
      none
  let btype := (hdr >>> 1) % 4
  if btype != 2 then
    none
  let (litLen, dist, _) ← Png.readDynamicTables br1
  some (litLen, dist)

private def zlibWrapDeflated (deflated raw : ByteArray) : ByteArray :=
  let header := ByteArray.mk #[Png.u8 0x78, Png.u8 0x01]
  header ++ deflated ++ Png.u32be (Png.adler32 raw).toNat

private def inflatedPngRaw? (bytes : ByteArray) : Option ByteArray := do
  let parsed ←
    if h : 8 ≤ bytes.size then
      Png.parsePngForDecode bytes h
    else
      none
  if hsize : 2 ≤ parsed.idat.size then
    match Png.zlibDecompressStored parsed.idat hsize with
    | some raw => some raw
    | none => Png.zlibDecompress parsed.idat hsize
  else
    none

private def allRowsHaveFilter (raw : ByteArray) (rowBytes h : Nat) (filter : UInt8) :
    Bool :=
  Id.run do
    let mut ok := true
    for y in [0:h] do
      let offset := y * (rowBytes + 1)
      if raw.get! offset != filter then
        ok := false
    return ok

private def rawHasNonzeroFilter (raw : ByteArray) (rowBytes h : Nat) : Bool :=
  Id.run do
    let mut found := false
    for y in [0:h] do
      let offset := y * (rowBytes + 1)
      if raw.get! offset != 0 then
        found := true
    return found

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

private def validateGeneratedDynamicEncoderCase
    (name : String) (raw : ByteArray) (expectDistance : Bool) : IO Unit := do
  let tokens := Png.deflateTokensDist1 raw
  if Png.deflateTokensExpand tokens != raw then
    throw (IO.userError s!"generated dynamic encoder {name}: token expansion mismatch")
  if Png.deflateTokensHasMatchDist1 tokens != expectDistance then
    throw (IO.userError s!"generated dynamic encoder {name}: unexpected match-token shape")
  let litLenLengths := Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)
  let distLengths := Png.generatedDynamicDistLengths (Png.distSymbolFreqs tokens)
  let litLenCount := Png.generatedDynamicLitLenCount litLenLengths
  let distCount := Png.generatedDynamicDistCount distLengths
  let headerLengths :=
    (litLenLengths.extract 0 litLenCount) ++ (distLengths.extract 0 distCount)
  match Png.codeLenTokensExpand? (Png.codeLenLiteralTokensOfLengths headerLengths) with
  | some headerLengths' =>
      if headerLengths' != headerLengths then
        throw (IO.userError s!"generated dynamic encoder {name}: code-length token expansion mismatch")
  | none =>
      throw (IO.userError s!"generated dynamic encoder {name}: invalid code-length token stream")
  let deflated := Png.deflateDynamicFullFast raw
  match dynamicTablesFromDeflate? deflated with
  | some (litLen, dist) =>
      if litLen == Png.fixedLitLenHuffman then
        throw (IO.userError s!"generated dynamic encoder {name}: reused the fixed literal/length table")
      if expectDistance && dist.maxLen == 0 then
        throw (IO.userError s!"generated dynamic encoder {name}: missing distance table")
      if !expectDistance && dist.maxLen != 0 then
        throw (IO.userError s!"generated dynamic encoder {name}: unexpected distance table")
  | none =>
      throw (IO.userError s!"generated dynamic encoder {name}: tables failed to parse")
  let zlibBytes := zlibWrapDeflated deflated raw
  match zlibDecompressFixture zlibBytes with
  | some raw' =>
      if raw' != raw then
        throw (IO.userError s!"generated dynamic encoder {name}: zlib round-trip mismatch")
  | none =>
      throw (IO.userError s!"generated dynamic encoder {name}: zlib round-trip failed")

private def validateGeneratedDynamicEncoder : IO Unit := do
  validateGeneratedDynamicEncoderCase
    "literal-only" (deterministicPrefix 160) false
  validateGeneratedDynamicEncoderCase
    "repeated-byte" (repeatBytes (byteArrayOfNats [65]) 600) true
  validateGeneratedDynamicEncoderCase
    "mixed-literals-and-runs"
    (deterministicPrefix 96 ++ repeatBytes (byteArrayOfNats [90]) 400 ++ deterministicPrefix 96)
    true

private def lz77HasDistance (tokens : Array Png.Lz77Token) (distance : Nat) : Bool :=
  Id.run do
    let mut found := false
    for token in tokens do
      match token with
      | .literal _ => pure ()
      | .match _ d =>
          if d == distance then
            found := true
    return found

private def lz77HasLongMatch (tokens : Array Png.Lz77Token) (len : Nat) : Bool :=
  Id.run do
    let mut found := false
    for token in tokens do
      match token with
      | .literal _ => pure ()
      | .match l _ =>
          if l == len then
            found := true
    return found

private def validateDeflateDistanceInfo : IO Unit := do
  for distance in
      #[1, 2, 3, 4, 5, 7, 9, 17, 33, 65, 129, 257, 513, 1025, 2049, 4097,
        8193, 16385, 24577, 32768] do
    match Png.deflateDistanceInfo? distance with
    | some (sym, extraBits, extraLen) =>
        let decoded := Png.deflateDistanceBases[sym]! + extraBits
        if decoded != distance then
          throw (IO.userError s!"distance info boundary {distance}: decoded {decoded}")
        if extraBits >= (1 <<< extraLen) then
          throw (IO.userError s!"distance info boundary {distance}: extra bits overflow")
    | none =>
        throw (IO.userError s!"distance info boundary {distance}: no encoding")
  if Png.deflateDistanceInfo? 0 != none then
    throw (IO.userError "distance info accepted distance 0")
  if Png.deflateDistanceInfo? 32769 != none then
    throw (IO.userError "distance info accepted distance beyond 32768")

private def validateLz77TokensCase
    (name : String) (raw : ByteArray) (check : Array Png.Lz77Token → IO Unit) : IO Unit := do
  let tokens := Png.deflateTokensLz77 raw
  match Png.deflateTokensExpandLz77? tokens with
  | some raw' =>
      if raw' != raw then
        throw (IO.userError s!"lz77 tokenizer {name}: expansion mismatch")
  | none =>
      throw (IO.userError s!"lz77 tokenizer {name}: invalid token expansion")
  check tokens

private def validateLz77Tokenizer : IO Unit := do
  validateLz77TokensCase "distance-1 repeated bytes"
    (repeatBytes (byteArrayOfNats [65]) 600)
    (fun tokens => do
      if !lz77HasDistance tokens 1 then
        throw (IO.userError "lz77 tokenizer repeated bytes: missing distance-1 match"))
  validateLz77TokensCase "multi-byte distance"
    (repeatBytes "ABCDEF".toUTF8 160)
    (fun tokens => do
      if !lz77HasDistance tokens 6 then
        throw (IO.userError "lz77 tokenizer multi-byte: missing distance-6 match"))
  validateLz77TokensCase "split long match"
    (repeatBytes "ABCD".toUTF8 240)
    (fun tokens => do
      if !lz77HasLongMatch tokens 258 then
        throw (IO.userError "lz77 tokenizer long match: missing 258-byte chunk"))
  let boundaryRaw := "ABC".toUTF8 ++ repeatBytes (byteArrayOfNats [0]) 32765 ++ "ABC".toUTF8
  validateLz77TokensCase "32k boundary"
    boundaryRaw
    (fun tokens => do
      if !lz77HasDistance tokens 32768 then
        throw (IO.userError "lz77 tokenizer boundary: missing distance 32768"))
  let beyondRaw := "ABC".toUTF8 ++ repeatBytes (byteArrayOfNats [0]) 32766 ++ "ABC".toUTF8
  validateLz77TokensCase "beyond 32k boundary"
    beyondRaw
    (fun tokens => do
      if lz77HasDistance tokens 32769 then
        throw (IO.userError "lz77 tokenizer boundary: used distance 32769"))
  let tieRaw := "ABCXABCYABCZ".toUTF8
  have hTieRaw : 8 < tieRaw.data.size := by native_decide
  let tieBucket : Array Nat := #[0, 4]
  have hTieBucket : 2 ≤ tieBucket.size := by native_decide
  match Png.lz77FindBestInBucket tieRaw.data 8 hTieRaw tieBucket 2 hTieBucket 0 0 with
  | some (3, 4) => pure ()
  | other =>
      throw (IO.userError s!"lz77 nearest tie break failed: {repr other}")
  let longestRaw := "ABCDABCXABCD".toUTF8
  have hLongestRaw : 8 < longestRaw.data.size := by native_decide
  let longestBucket : Array Nat := #[4, 0]
  have hLongestBucket : 2 ≤ longestBucket.size := by native_decide
  match Png.lz77FindBestInBucket longestRaw.data 8 hLongestRaw
      longestBucket 2 hLongestBucket 0 0 with
  | some (4, 8) => pure ()
  | other =>
      throw (IO.userError s!"lz77 longest match failed: {repr other}")

private def validateLz77PublicRoundTrips : IO Unit := do
  let rawSmall := repeatBytes "ABCDEF".toUTF8 200
  let rawBoundary := "ABC".toUTF8 ++ repeatBytes (byteArrayOfNats [0]) 32765 ++ "ABC".toUTF8
  for raw in #[rawSmall, rawBoundary] do
    match zlibDecompressFixture (Png.zlibCompressFixed raw) with
    | some raw' =>
        if raw' != raw then
          throw (IO.userError "lz77 fixed zlib round-trip mismatch")
    | none =>
        throw (IO.userError "lz77 fixed zlib round-trip failed")
    match zlibDecompressFixture (Png.zlibCompressDynamic raw) with
    | some raw' =>
        if raw' != raw then
          throw (IO.userError "lz77 dynamic zlib round-trip mismatch")
    | none =>
        throw (IO.userError "lz77 dynamic zlib round-trip failed")
  match dynamicTablesFromDeflate? (Png.deflateDynamic rawSmall) with
  | some (_, dist) =>
      if dist.maxLen != 5 then
        throw (IO.userError "lz77 dynamic block did not advertise 5-bit distance table")
  | none =>
      throw (IO.userError "lz77 dynamic block tables failed to parse")

-- Decode PNG fixtures that use fixed-Huffman deflate blocks.
private def pngDecodeFixedHuffmanFixtures : IO Unit := do
  let grayBytes <- IO.FS.readBinFile (testFixturePath "test_gray.png")
  match Png.decodeBitmap (px := Gray8) grayBytes with
  | some bmp =>
      if bmp.size.width != 8 || bmp.size.height != 8 then
        throw (IO.userError "fixed-huffman gray fixture has unexpected size")
  | none =>
      throw (IO.userError "fixed-huffman gray fixture failed to decode")
  let rgbaBytes <- IO.FS.readBinFile (testFixturePath "test_rgba.png")
  match Png.decodeBitmap (px := RGBA8) rgbaBytes with
  | some bmp =>
      if bmp.size.width != 4 || bmp.size.height != 4 then
        throw (IO.userError "fixed-huffman RGBA fixture has unexpected size")
  | none =>
      throw (IO.userError "fixed-huffman RGBA fixture failed to decode")

-- All tolerated-chunk fixtures are 4x4 RGB images sharing the same pixel pattern,
-- so decoding any of them must yield this canonical reference bitmap.
-- Generated by `Bitmap/Tests/generate-anc-fixtures.py`; keep this matrix in sync.
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

private def grayAlphaFixture : Bitmap.GrayAlpha8 :=
  Bitmap.ofFn 2 2 (fun idx : Fin (2 * 2) =>
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

private def u16be (n : Nat) : ByteArray :=
  ByteArray.mk #[Png.u8 (n / 256), Png.u8 n]

private def rgb16DownsampleFixture : Bitmap.RGB16 :=
  Bitmap.ofFn 2 1 (fun idx : Fin (2 * 1) =>
    match idx.val with
    | 0 => { r := u16 0x12ab, g := u16 0x3456, b := u16 0xfedc }
    | _ => { r := u16 0x0102, g := u16 0x8001, b := u16 0x00ff })

private def rgba16DownsampleFixture : Bitmap.RGBA16 :=
  Bitmap.ofFn 2 1 (fun idx : Fin (2 * 1) =>
    match idx.val with
    | 0 => { r := u16 0x12ab, g := u16 0x3456, b := u16 0xfedc, a := u16 0x7788 }
    | _ => { r := u16 0x0102, g := u16 0x8001, b := u16 0x00ff, a := u16 0xffff })

private def gray16DownsampleFixture : Bitmap.Gray16 :=
  Bitmap.ofFn 3 1 (fun idx : Fin (3 * 1) =>
    match idx.val with
    | 0 => { v := u16 0x12ab }
    | 1 => { v := u16 0x8001 }
    | _ => { v := u16 0x00ff })

private def grayAlpha16DownsampleFixture : Bitmap.GrayAlpha16 :=
  Bitmap.ofFn 2 1 (fun idx : Fin (2 * 1) =>
    match idx.val with
    | 0 => { v := u16 0x12ab, a := u16 0x3456 }
    | _ => { v := u16 0x8001, a := u16 0x00ff })

private def pngWithAncillary {px : Type} [PixelFormat px] [Png.PixelFormat px]
    (bmp : Bitmap px) (ancillary : ByteArray) : ByteArray :=
  let raw := Png.encodeRawFast bmp
  let idat := Png.zlibCompressFixed raw
  let ihdr :=
    Png.u32be bmp.size.width ++
    Png.u32be bmp.size.height ++
    ByteArray.mk
      #[Png.PixelFormat.bitDepth (α := px), Png.PixelFormat.colorType (α := px),
        Png.u8 0, Png.u8 0, Png.u8 0]
  Png.pngSignature ++
    Png.mkChunkBytes Png.ihdrTypeBytes ihdr ++
    ancillary ++
    Png.mkChunkBytes Png.idatTypeBytes idat ++
    Png.mkChunkBytes Png.iendTypeBytes ByteArray.empty

private def pngWithPostIdatAncillary {px : Type} [PixelFormat px] [Png.PixelFormat px]
    (bmp : Bitmap px) (postIdat : ByteArray) : ByteArray :=
  let raw := Png.encodeRawFast bmp
  let idat := Png.zlibCompressFixed raw
  let ihdr :=
    Png.u32be bmp.size.width ++
    Png.u32be bmp.size.height ++
    ByteArray.mk
      #[Png.PixelFormat.bitDepth (α := px), Png.PixelFormat.colorType (α := px),
        Png.u8 0, Png.u8 0, Png.u8 0]
  Png.pngSignature ++
    Png.mkChunkBytes Png.ihdrTypeBytes ihdr ++
    Png.mkChunkBytes Png.idatTypeBytes idat ++
    postIdat ++
    Png.mkChunkBytes Png.iendTypeBytes ByteArray.empty

private def gamaChunk (gammaScaled : Nat) : ByteArray :=
  Png.mkChunkBytes Png.gamaTypeBytes (Png.u32be gammaScaled)

private def srgbChunk (intent : Png.PngSrgbIntent) : ByteArray :=
  Png.mkChunkBytes Png.srgbTypeBytes (ByteArray.mk #[intent.toByte])

private def chrmChunk (chromaticities : Png.PngChromaticities) : ByteArray :=
  match Png.encodeChrmData? chromaticities with
  | some data => Png.mkChunkBytes Png.chrmTypeBytes data
  | none => Png.mkChunkBytes Png.chrmTypeBytes ByteArray.empty

private def fixedPngTime : Png.PngTime :=
  { year := 2026, month := 5, day := 2, hour := 17, minute := 45, second := 12 }

private def timeChunk (time : Png.PngTime) : ByteArray :=
  match Png.encodeTimeData? time with
  | some data => Png.mkChunkBytes Png.timeTypeBytes data
  | none => Png.mkChunkBytes Png.timeTypeBytes ByteArray.empty

private def physical300Dpi : Png.PngPhysicalPixelDimensions :=
  Png.PngPhysicalPixelDimensions.ofDpiRounded 300 300

private def plteChunk : ByteArray :=
  Png.mkChunkBytes Png.plteTypeBytes
    (ByteArray.mk #[Png.u8 0, Png.u8 0, Png.u8 0])

private def gammaTransformRgb8Data (gammaScaled : Nat) (data : ByteArray) : ByteArray :=
  Id.run do
    let mut out := ByteArray.emptyWithCapacity data.size
    for i in [0:data.size] do
      out := out.push (Png.u8 (Png.gammaSampleToSrgbNat gammaScaled (data.get! i).toNat 255))
    return out

private def gammaTransformRgba8Data (gammaScaled : Nat) (data : ByteArray) : ByteArray :=
  Id.run do
    let mut out := ByteArray.emptyWithCapacity data.size
    let count := data.size / 4
    for i in [0:count] do
      let base := i * 4
      out := out.push (Png.u8 (Png.gammaSampleToSrgbNat gammaScaled (data.get! base).toNat 255))
      out := out.push (Png.u8 (Png.gammaSampleToSrgbNat gammaScaled (data.get! (base + 1)).toNat 255))
      out := out.push (Png.u8 (Png.gammaSampleToSrgbNat gammaScaled (data.get! (base + 2)).toNat 255))
      out := out.push (data.get! (base + 3))
    return out

private def gammaTransformGray16Data (gammaScaled : Nat) (data : ByteArray) : ByteArray :=
  Id.run do
    let mut out := ByteArray.emptyWithCapacity data.size
    let count := data.size / 2
    for i in [0:count] do
      let base := i * 2
      let sample := (data.get! base).toNat * 256 + (data.get! (base + 1)).toNat
      let corrected := Png.gammaSampleToSrgbNat gammaScaled sample 65535
      out := out ++ u16be corrected
    return out

private def wideChromaticities : Png.PngChromaticities :=
  { white := { x := 31270, y := 32900 }
    red := { x := 68000, y := 32000 }
    green := { x := 21000, y := 71000 }
    blue := { x := 15000, y := 6000 } }

private def chrmTransformRgb8Data
    (chromaticities : Png.PngChromaticities) (gamma : Option Nat)
    (data : ByteArray) : ByteArray :=
  match chromaticities.sourceToSrgbMatrix? with
  | none => data
  | some matrix =>
      Id.run do
        let mut out := ByteArray.emptyWithCapacity data.size
        let count := data.size / 3
        for i in [0:count] do
          let base := i * 3
          let (r, g, b) := Png.chrmRgbToSrgbNat matrix gamma
            (data.get! base).toNat (data.get! (base + 1)).toNat
            (data.get! (base + 2)).toNat 255
          out := out.push (Png.u8 r)
          out := out.push (Png.u8 g)
          out := out.push (Png.u8 b)
        return out

private def chrmTransformRgba8Data
    (chromaticities : Png.PngChromaticities) (gamma : Option Nat)
    (data : ByteArray) : ByteArray :=
  match chromaticities.sourceToSrgbMatrix? with
  | none => data
  | some matrix =>
      Id.run do
        let mut out := ByteArray.emptyWithCapacity data.size
        let count := data.size / 4
        for i in [0:count] do
          let base := i * 4
          let (r, g, b) := Png.chrmRgbToSrgbNat matrix gamma
            (data.get! base).toNat (data.get! (base + 1)).toNat
            (data.get! (base + 2)).toNat 255
          out := out.push (Png.u8 r)
          out := out.push (Png.u8 g)
          out := out.push (Png.u8 b)
          out := out.push (data.get! (base + 3))
        return out

private def chrmTransformRgb16Data
    (chromaticities : Png.PngChromaticities) (gamma : Option Nat)
    (data : ByteArray) : ByteArray :=
  match chromaticities.sourceToSrgbMatrix? with
  | none => data
  | some matrix =>
      Id.run do
        let mut out := ByteArray.emptyWithCapacity data.size
        let count := data.size / 6
        for i in [0:count] do
          let base := i * 6
          let r0 := (data.get! base).toNat * 256 + (data.get! (base + 1)).toNat
          let g0 := (data.get! (base + 2)).toNat * 256 + (data.get! (base + 3)).toNat
          let b0 := (data.get! (base + 4)).toNat * 256 + (data.get! (base + 5)).toNat
          let (r, g, b) := Png.chrmRgbToSrgbNat matrix gamma r0 g0 b0 65535
          out := out ++ u16be r ++ u16be g ++ u16be b
        return out

private def chrmTransformGray8Data
    (chromaticities : Png.PngChromaticities) (gamma : Option Nat)
    (data : ByteArray) : ByteArray :=
  match chromaticities.sourceToSrgbMatrix? with
  | none => data
  | some matrix =>
      Id.run do
        let mut out := ByteArray.emptyWithCapacity (data.size / 3)
        let count := data.size / 3
        for i in [0:count] do
          let base := i * 3
          let gray := Png.chrmRgbToGrayNat matrix gamma
            (data.get! base).toNat (data.get! (base + 1)).toNat
            (data.get! (base + 2)).toNat 255
          out := out.push (Png.u8 gray)
        return out

private def chrmTransformGrayAlpha8Data
    (chromaticities : Png.PngChromaticities) (gamma : Option Nat)
    (data : ByteArray) : ByteArray :=
  match chromaticities.sourceToSrgbMatrix? with
  | none => data
  | some matrix =>
      Id.run do
        let mut out := ByteArray.emptyWithCapacity (data.size / 2)
        let count := data.size / 4
        for i in [0:count] do
          let base := i * 4
          let gray := Png.chrmRgbToGrayNat matrix gamma
            (data.get! base).toNat (data.get! (base + 1)).toNat
            (data.get! (base + 2)).toNat 255
          out := out.push (Png.u8 gray)
          out := out.push (data.get! (base + 3))
        return out

private def rgb16MetadataFixture : Bitmap.RGB16 :=
  Bitmap.ofFn 2 1 (fun idx : Fin (2 * 1) =>
    match idx.val with
    | 0 => { r := u16 0x1234, g := u16 0x5678, b := u16 0x9abc }
    | _ => { r := u16 0x2001, g := u16 0x4002, b := u16 0x6003 })

private def rgb16MetadataPng : ByteArray :=
  pngWithAncillary rgb16MetadataFixture
    (Png.mkChunkBytes Png.trnsTypeBytes
        (u16be 0x1234 ++ u16be 0x5678 ++ u16be 0x9abc) ++
      Png.mkChunkBytes Png.bkgdTypeBytes
        (u16be 0x2100 ++ u16be 0x4300 ++ u16be 0x6500))

private def grayAlpha16MetadataFixture : Bitmap.GrayAlpha16 :=
  Bitmap.ofFn 2 1 (fun idx : Fin (2 * 1) =>
    match idx.val with
    | 0 => { v := u16 0x1234, a := u16 0x0000 }
    | _ => { v := u16 0x8001, a := u16 0xffff })

private def grayAlpha16MetadataPng : ByteArray :=
  pngWithAncillary grayAlpha16MetadataFixture
    (Png.mkChunkBytes Png.bkgdTypeBytes (u16be 0x3000))

private def rgba16MetadataFixture : Bitmap.RGBA16 :=
  Bitmap.ofFn 2 1 (fun idx : Fin (2 * 1) =>
    match idx.val with
    | 0 => { r := u16 0x1234, g := u16 0x5678, b := u16 0x9abc, a := u16 0x0000 }
    | _ => { r := u16 0x2001, g := u16 0x4002, b := u16 0x6003, a := u16 0xffff })

private def rgba16MetadataPng : ByteArray :=
  pngWithAncillary rgba16MetadataFixture
    (Png.mkChunkBytes Png.bkgdTypeBytes
      (u16be 0x2100 ++ u16be 0x4300 ++ u16be 0x6500))

private def encodeFixturePng {px : Type} [PixelFormat px] [Png.PixelFormat px]
    (bmp : Bitmap px) : IO ByteArray := do
  match Png.encodeBitmapChecked (px := px) bmp .fixed with
  | Except.ok bytes => pure bytes
  | Except.error err => throw (IO.userError err)

private def adam7Sample8 (x y salt : Nat) : UInt8 :=
  Png.u8 (x * 17 + y * 31 + salt)

private def adam7Sample16 (x y salt : Nat) : Nat :=
  (x * 4099 + y * 257 + salt) % 65536

private def pushU16BE (out : ByteArray) (n : Nat) : ByteArray :=
  (out.push (Png.u8 (n / 256))).push (Png.u8 n)

private def adam7RGB8ExpectedData (w h : Nat) : ByteArray :=
  Id.run do
    let mut out := ByteArray.emptyWithCapacity (w * h * RGB8.bytesPerPixel)
    for y in [0:h] do
      for x in [0:w] do
        out := out.push (adam7Sample8 x y 5)
        out := out.push (adam7Sample8 x y 17)
        out := out.push (adam7Sample8 x y 29)
    return out

private def adam7RGB8ExpectedRGBAData (w h : Nat) : ByteArray :=
  Id.run do
    let mut out := ByteArray.emptyWithCapacity (w * h * RGBA8.bytesPerPixel)
    for y in [0:h] do
      for x in [0:w] do
        out := out.push (adam7Sample8 x y 5)
        out := out.push (adam7Sample8 x y 17)
        out := out.push (adam7Sample8 x y 29)
        out := out.push (if x == 0 && y == 0 then Png.u8 0 else Png.u8 255)
    return out

private def adam7RGB8ExpectedOverBackgroundData (w h : Nat) : ByteArray :=
  Id.run do
    let mut out := ByteArray.emptyWithCapacity (w * h * RGB8.bytesPerPixel)
    for y in [0:h] do
      for x in [0:w] do
        if x == 0 && y == 0 then
          out := out.push (Png.u8 10)
          out := out.push (Png.u8 20)
          out := out.push (Png.u8 30)
        else
          out := out.push (adam7Sample8 x y 5)
          out := out.push (adam7Sample8 x y 17)
          out := out.push (adam7Sample8 x y 29)
    return out

private def adam7Gray8ExpectedData (w h : Nat) : ByteArray :=
  Id.run do
    let mut out := ByteArray.emptyWithCapacity (w * h * Gray8.bytesPerPixel)
    for y in [0:h] do
      for x in [0:w] do
        out := out.push (adam7Sample8 x y 3)
    return out

private def adam7GrayAlpha8ExpectedData (w h : Nat) : ByteArray :=
  Id.run do
    let mut out := ByteArray.emptyWithCapacity (w * h * GrayAlpha8.bytesPerPixel)
    for y in [0:h] do
      for x in [0:w] do
        out := out.push (adam7Sample8 x y 7)
        out := out.push (adam7Sample8 x y 113)
    return out

private def adam7RGBA8ExpectedData (w h : Nat) : ByteArray :=
  Id.run do
    let mut out := ByteArray.emptyWithCapacity (w * h * RGBA8.bytesPerPixel)
    for y in [0:h] do
      for x in [0:w] do
        out := out.push (adam7Sample8 x y 11)
        out := out.push (adam7Sample8 x y 23)
        out := out.push (adam7Sample8 x y 37)
        out := out.push (adam7Sample8 x y 151)
    return out

private def adam7RGB16ExpectedData (w h : Nat) : ByteArray :=
  Id.run do
    let mut out := ByteArray.emptyWithCapacity (w * h * RGB16.bytesPerPixel)
    for y in [0:h] do
      for x in [0:w] do
        out := pushU16BE out (adam7Sample16 x y 0x1001)
        out := pushU16BE out (adam7Sample16 x y 0x3003)
        out := pushU16BE out (adam7Sample16 x y 0x5005)
    return out

private def adam7RGB16DownsampleExpectedData (w h : Nat) : ByteArray :=
  Id.run do
    let mut out := ByteArray.emptyWithCapacity (w * h * RGB8.bytesPerPixel)
    for y in [0:h] do
      for x in [0:w] do
        out := out.push (Png.u8 (adam7Sample16 x y 0x1001 / 256))
        out := out.push (Png.u8 (adam7Sample16 x y 0x3003 / 256))
        out := out.push (Png.u8 (adam7Sample16 x y 0x5005 / 256))
    return out

private def adam7Gray16ExpectedData (w h : Nat) : ByteArray :=
  Id.run do
    let mut out := ByteArray.emptyWithCapacity (w * h * Gray16.bytesPerPixel)
    for y in [0:h] do
      for x in [0:w] do
        out := pushU16BE out (adam7Sample16 x y 0x1234)
    return out

private def adam7Gray16DownsampleExpectedData (w h : Nat) : ByteArray :=
  Id.run do
    let mut out := ByteArray.emptyWithCapacity (w * h * Gray8.bytesPerPixel)
    for y in [0:h] do
      for x in [0:w] do
        out := out.push (Png.u8 (adam7Sample16 x y 0x1234 / 256))
    return out

private def expectAdam7Fixtures : IO Unit := do
  let rgb8Bytes ← IO.FS.readBinFile (testFixturePath "test_adam7_rgb8_9x9_filters.png")
  match Png.decodeBitmap (px := RGB8) rgb8Bytes with
  | some bmp =>
      if bmp.size.width != 9 || bmp.size.height != 9 ||
          bmp.data != adam7RGB8ExpectedData 9 9 then
        throw (IO.userError "Adam7 RGB8 varied-filter fixture mismatch")
  | none =>
      throw (IO.userError "Adam7 RGB8 varied-filter fixture failed to decode")
  let gray8Bytes ← IO.FS.readBinFile (testFixturePath "test_adam7_gray8_2x3.png")
  match Png.decodeBitmap (px := Gray8) gray8Bytes with
  | some bmp =>
      if bmp.size.width != 2 || bmp.size.height != 3 ||
          bmp.data != adam7Gray8ExpectedData 2 3 then
        throw (IO.userError "Adam7 Gray8 small fixture mismatch")
  | none =>
      throw (IO.userError "Adam7 Gray8 small fixture failed to decode")
  let grayAlpha8Bytes ← IO.FS.readBinFile (testFixturePath "test_adam7_grayalpha8_9x9.png")
  match Png.decodeBitmap (px := GrayAlpha8) grayAlpha8Bytes with
  | some bmp =>
      if bmp.size.width != 9 || bmp.size.height != 9 ||
          bmp.data != adam7GrayAlpha8ExpectedData 9 9 then
        throw (IO.userError "Adam7 GrayAlpha8 fixture mismatch")
  | none =>
      throw (IO.userError "Adam7 GrayAlpha8 fixture failed to decode")
  let rgba8Bytes ← IO.FS.readBinFile (testFixturePath "test_adam7_rgba8_1x1.png")
  match Png.decodeBitmap (px := RGBA8) rgba8Bytes with
  | some bmp =>
      if bmp.size.width != 1 || bmp.size.height != 1 ||
          bmp.data != adam7RGBA8ExpectedData 1 1 then
        throw (IO.userError "Adam7 RGBA8 1x1 fixture mismatch")
  | none =>
      throw (IO.userError "Adam7 RGBA8 1x1 fixture failed to decode")
  let rgb16Bytes ← IO.FS.readBinFile (testFixturePath "test_adam7_rgb16_9x9.png")
  match Png.decodeBitmap (px := RGB16) rgb16Bytes with
  | some bmp =>
      if bmp.size.width != 9 || bmp.size.height != 9 ||
          bmp.data != adam7RGB16ExpectedData 9 9 then
        throw (IO.userError "Adam7 RGB16 fixture mismatch")
  | none =>
      throw (IO.userError "Adam7 RGB16 fixture failed to decode")
  match Png.decodeBitmap (px := RGB8) rgb16Bytes with
  | some bmp =>
      if bmp.data != adam7RGB16DownsampleExpectedData 9 9 then
        throw (IO.userError "Adam7 RGB16 -> RGB8 downsample mismatch")
  | none =>
      throw (IO.userError "Adam7 RGB16 -> RGB8 downsample failed")
  let gray16Bytes ← IO.FS.readBinFile (testFixturePath "test_adam7_gray16_2x3.png")
  match Png.decodeBitmap (px := Gray16) gray16Bytes with
  | some bmp =>
      if bmp.size.width != 2 || bmp.size.height != 3 ||
          bmp.data != adam7Gray16ExpectedData 2 3 then
        throw (IO.userError "Adam7 Gray16 fixture mismatch")
  | none =>
      throw (IO.userError "Adam7 Gray16 fixture failed to decode")
  match Png.decodeBitmap (px := Gray8) gray16Bytes with
  | some bmp =>
      if bmp.data != adam7Gray16DownsampleExpectedData 2 3 then
        throw (IO.userError "Adam7 Gray16 -> Gray8 downsample mismatch")
  | none =>
      throw (IO.userError "Adam7 Gray16 -> Gray8 downsample failed")
  let trnsBkgdBytes ← IO.FS.readBinFile (testFixturePath "test_adam7_trns_bkgd_rgb8.png")
  match Png.decodeBitmapWithMetadata (px := RGBA8) trnsBkgdBytes with
  | some decoded =>
      if decoded.bitmap.data != adam7RGB8ExpectedRGBAData 2 3 then
        throw (IO.userError "Adam7 tRNS RGBA alpha mismatch")
  | none =>
      throw (IO.userError "Adam7 tRNS RGBA metadata decode failed")
  match Png.decodeBitmapWithMetadata (px := RGB8) trnsBkgdBytes with
  | some decoded =>
      if decoded.bitmap.data != adam7RGB8ExpectedOverBackgroundData 2 3 then
        throw (IO.userError "Adam7 tRNS+bKGD RGB composition mismatch")
  | none =>
      throw (IO.userError "Adam7 tRNS+bKGD RGB metadata decode failed")
  let interlace2Bytes ← IO.FS.readBinFile (testFixturePath "test_adam7_interlace2.png")
  if (Png.decodeBitmap (px := RGB8) interlace2Bytes).isSome then
    throw (IO.userError "decoder accepted invalid Adam7 interlace method 2")
  let truncatedBytes ← IO.FS.readBinFile (testFixturePath "test_adam7_truncated.png")
  if (Png.decodeBitmap (px := RGB8) truncatedBytes).isSome then
    throw (IO.userError "decoder accepted truncated Adam7 payload")

private def gray1FixtureOn (x y : Nat) : Bool :=
  ((x * 3 + y * 5 + x * y) % 7) < 3

private def gray1FixtureBitmap (w h : Nat) : Bitmap.Gray1 :=
  Bitmap.Gray1.ofFn w h (fun idx =>
    let x := idx.val % w
    let y := idx.val / w
    { v := gray1FixtureOn x y })

private def gray1ExpandedGray8Data (w h : Nat) : ByteArray :=
  Id.run do
    let mut out := ByteArray.emptyWithCapacity (w * h)
    for i in [0:w * h] do
      let x := i % w
      let y := i / w
      out := out.push (if gray1FixtureOn x y then 0xff else 0)
    return out

private def expectGray1ExactFixture (name : String) (w h : Nat) : IO Unit := do
  let bytes ← IO.FS.readBinFile (testFixturePath name)
  match Png.decodeGray1Bitmap bytes with
  | some bmp =>
      if bmp.size.width != w || bmp.size.height != h ||
          bmp.data != (gray1FixtureBitmap w h).data then
        throw (IO.userError s!"{name}: Gray1 exact decode mismatch")
  | none =>
      throw (IO.userError s!"{name}: Gray1 exact decode failed")

private def expectGray1Fixtures : IO Unit := do
  for w in [1, 7, 8, 9, 17] do
    expectGray1ExactFixture s!"test_gray1_w{w}.png" w 3
  expectGray1ExactFixture "test_gray1_filters.png" 17 5
  expectGray1ExactFixture "test_gray1_adam7.png" 9 9

  let expansionSource := gray1FixtureBitmap 9 3
  let expandedGray8 : Bitmap.Gray8 := Bitmap.Gray1.expand expansionSource
  if expandedGray8.data != gray1ExpandedGray8Data 9 3 then
    throw (IO.userError "Gray1 generic expansion to Gray8 mismatch")
  let expandedGray16 : Bitmap.Gray16 := Bitmap.Gray1.expand expansionSource
  if expandedGray16.data.size != 9 * 3 * Gray16.bytesPerPixel then
    throw (IO.userError "Gray1 generic expansion to Gray16 size mismatch")
  let expandedGrayAlpha8 : Bitmap.GrayAlpha8 := Bitmap.Gray1.expand expansionSource
  if expandedGrayAlpha8.data.size != 9 * 3 * GrayAlpha8.bytesPerPixel then
    throw (IO.userError "Gray1 generic expansion to GrayAlpha8 size mismatch")
  let expandedGrayAlpha16 : Bitmap.GrayAlpha16 := Bitmap.Gray1.expand expansionSource
  if expandedGrayAlpha16.data.size != 9 * 3 * GrayAlpha16.bytesPerPixel then
    throw (IO.userError "Gray1 generic expansion to GrayAlpha16 size mismatch")
  let expandedRGB8 : Bitmap.RGB8 := Bitmap.Gray1.expand expansionSource
  if expandedRGB8.data.size != 9 * 3 * RGB8.bytesPerPixel then
    throw (IO.userError "Gray1 generic expansion to RGB8 size mismatch")
  let expandedRGB16 : Bitmap.RGB16 := Bitmap.Gray1.expand expansionSource
  if expandedRGB16.data.size != 9 * 3 * RGB16.bytesPerPixel then
    throw (IO.userError "Gray1 generic expansion to RGB16 size mismatch")
  let expandedRGBA8 : Bitmap.RGBA8 := Bitmap.Gray1.expand expansionSource
  if expandedRGBA8.data.size != 9 * 3 * RGBA8.bytesPerPixel then
    throw (IO.userError "Gray1 generic expansion to RGBA8 size mismatch")
  let expandedRGBA16 : Bitmap.RGBA16 := Bitmap.Gray1.expand expansionSource
  if expandedRGBA16.data.size != 9 * 3 * RGBA16.bytesPerPixel then
    throw (IO.userError "Gray1 generic expansion to RGBA16 size mismatch")

  let filterBytes ← IO.FS.readBinFile (testFixturePath "test_gray1_filters.png")
  match Png.decodeBitmap (px := Gray8) filterBytes with
  | some bmp =>
      if bmp.size.width != 17 || bmp.size.height != 5 ||
          bmp.data != gray1ExpandedGray8Data 17 5 then
        throw (IO.userError "Gray1 -> Gray8 decode mismatch")
  | none =>
      throw (IO.userError "Gray1 -> Gray8 decode failed")
  match Png.decodeBitmap (px := RGB8) filterBytes with
  | some bmp =>
      if bmp.size.width != 17 || bmp.size.height != 5 then
        throw (IO.userError "Gray1 -> RGB8 dimensions mismatch")
  | none =>
      throw (IO.userError "Gray1 -> RGB8 decode failed")
  match Png.decodeBitmap (px := RGBA16) filterBytes with
  | some bmp =>
      if bmp.size.width != 17 || bmp.size.height != 5 then
        throw (IO.userError "Gray1 -> RGBA16 dimensions mismatch")
  | none =>
      throw (IO.userError "Gray1 -> RGBA16 decode failed")

  let metaBytes ← IO.FS.readBinFile (testFixturePath "test_gray1_trns_bkgd.png")
  match Png.decodeGray1BitmapWithMetadata metaBytes with
  | some decoded =>
      if decoded.bitmap.data != (gray1FixtureBitmap 9 3).data then
        throw (IO.userError "Gray1 metadata exact data mismatch")
      match decoded.metadata.transparency, decoded.metadata.background with
      | some (.gray1 true), some (.gray1 false) => pure ()
      | _, _ => throw (IO.userError "Gray1 metadata values mismatch")
  | none =>
      throw (IO.userError "Gray1 metadata decode failed")
  match Png.decodeBitmapWithMetadata (px := RGBA8) metaBytes with
  | some decoded =>
      if decoded.bitmap.size.width != 9 || decoded.bitmap.size.height != 3 then
        throw (IO.userError "Gray1+tRNS -> RGBA8 dimensions mismatch")
  | none =>
      throw (IO.userError "Gray1+tRNS -> RGBA8 decode failed")

  let invalidRgb1 ← IO.FS.readBinFile (testFixturePath "test_gray1_invalid_rgb1.png")
  if (Png.decodeBitmap (px := RGB8) invalidRgb1).isSome then
    throw (IO.userError "invalid RGB bit-depth 1 fixture decoded as RGB8")
  if (Png.decodeGray1Bitmap invalidRgb1).isSome then
    throw (IO.userError "invalid RGB bit-depth 1 fixture decoded as Gray1")
  let truncated ← IO.FS.readBinFile (testFixturePath "test_gray1_truncated.png")
  if (Png.decodeGray1Bitmap truncated).isSome then
    throw (IO.userError "truncated Gray1 fixture unexpectedly decoded")

  let roundTripBmp := gray1FixtureBitmap 17 4
  for mode in [Png.PngEncodeMode.stored, .fixed, .dynamic] do
    match Png.encodeGray1BitmapChecked roundTripBmp mode with
    | Except.error err =>
        throw (IO.userError s!"Gray1 encode failed: {err}")
    | Except.ok bytes =>
        match Png.decodeGray1Bitmap bytes with
        | some decoded =>
            if decoded != roundTripBmp then
              throw (IO.userError "Gray1 encode/decode round-trip mismatch")
        | none =>
            throw (IO.userError "Gray1 encode/decode round-trip failed")

private def indexedPaletteRGB (idx : Nat) : UInt8 × UInt8 × UInt8 :=
  match idx with
  | 0 => (Png.u8 0, Png.u8 0, Png.u8 0)
  | 1 => (Png.u8 220, Png.u8 20, Png.u8 30)
  | 2 => (Png.u8 20, Png.u8 180, Png.u8 70)
  | 3 => (Png.u8 30, Png.u8 60, Png.u8 210)
  | n => (Png.u8 (17 * n + 11), Png.u8 (29 * n + 7), Png.u8 (43 * n + 19))

private def indexedPaletteEntries (count : Nat) : ByteArray :=
  Id.run do
    let mut out := ByteArray.emptyWithCapacity (count * 3)
    for i in [0:count] do
      let (r, g, b) := indexedPaletteRGB i
      out := out.push r
      out := out.push g
      out := out.push b
    return out

private def indexedPalette (count : Nat) : Png.PngPalette :=
  { entries := indexedPaletteEntries count }

private def indexedFixtureIndex (entryCount x y : Nat) : UInt8 :=
  Png.u8 ((x * 3 + y * 5 + x * y) % entryCount)

private def indexedFixtureData (w h entryCount : Nat) : ByteArray :=
  ByteArray.mk <| Array.ofFn (fun i : Fin (w * h) =>
    let x := i.val % w
    let y := i.val / w
    indexedFixtureIndex entryCount x y)

private def indexedFixtureBitmap (w h bitDepth entryCount : Nat)
    (transparency : Option ByteArray := none) (background : Option UInt8 := none) :
    Png.PngIndexedBitmap :=
  let data := indexedFixtureData w h entryCount
  have hvalid : data.size = w * h := by
    simp [data, indexedFixtureData, ByteArray.size]
  { size := { width := w, height := h }
    bitDepth
    palette := indexedPalette entryCount
    data
    transparency
    background
    valid := hvalid }

private def paletteAlphaAtTest (alpha? : Option ByteArray) (idx : Nat) : UInt8 :=
  match alpha? with
  | some alpha =>
      if idx < alpha.size then alpha.get! idx else 0xff
  | none => 0xff

private def indexedExpectedRGB8Data (w h entryCount : Nat)
    (alpha? : Option ByteArray := none) (background? : Option UInt8 := none) :
    ByteArray :=
  Id.run do
    let mut out := ByteArray.emptyWithCapacity (w * h * RGB8.bytesPerPixel)
    let bgRGB :=
      match background? with
      | some bg => indexedPaletteRGB bg.toNat
      | none => (Png.u8 0, Png.u8 0, Png.u8 0)
    for y in [0:h] do
      for x in [0:w] do
        let idx := (indexedFixtureIndex entryCount x y).toNat
        let (r0, g0, b0) := indexedPaletteRGB idx
        let a := paletteAlphaAtTest alpha? idx
        let (r, g, b) :=
          if alpha?.isSome then
            let (br, bg, bb) := bgRGB
            (Png.alphaCompositeByte r0 br a,
              Png.alphaCompositeByte g0 bg a,
              Png.alphaCompositeByte b0 bb a)
          else
            (r0, g0, b0)
        out := out.push r
        out := out.push g
        out := out.push b
    return out

private def indexedExpectedRGBA8Data (w h entryCount : Nat)
    (alpha? : Option ByteArray := none) : ByteArray :=
  Id.run do
    let mut out := ByteArray.emptyWithCapacity (w * h * RGBA8.bytesPerPixel)
    for y in [0:h] do
      for x in [0:w] do
        let idx := (indexedFixtureIndex entryCount x y).toNat
        let (r, g, b) := indexedPaletteRGB idx
        out := out.push r
        out := out.push g
        out := out.push b
        out := out.push (paletteAlphaAtTest alpha? idx)
    return out

private def indexedExpectedGray8Data (w h entryCount : Nat) : ByteArray :=
  Id.run do
    let mut out := ByteArray.emptyWithCapacity (w * h * Gray8.bytesPerPixel)
    for y in [0:h] do
      for x in [0:w] do
        let idx := (indexedFixtureIndex entryCount x y).toNat
        let (r, g, b) := indexedPaletteRGB idx
        out := out.push (Png.grayFromRGB8 r g b)
    return out

private def indexedExpectedGrayAlpha8Data (w h entryCount : Nat)
    (alpha? : Option ByteArray := none) : ByteArray :=
  Id.run do
    let mut out := ByteArray.emptyWithCapacity (w * h * GrayAlpha8.bytesPerPixel)
    for y in [0:h] do
      for x in [0:w] do
        let idx := (indexedFixtureIndex entryCount x y).toNat
        let (r, g, b) := indexedPaletteRGB idx
        out := out.push (Png.grayFromRGB8 r g b)
        out := out.push (paletteAlphaAtTest alpha? idx)
    return out

private def indexedExpectedRGB16Data (w h entryCount : Nat) : ByteArray :=
  Id.run do
    let mut out := ByteArray.emptyWithCapacity (w * h * RGB16.bytesPerPixel)
    for y in [0:h] do
      for x in [0:w] do
        let idx := (indexedFixtureIndex entryCount x y).toNat
        let (r, g, b) := indexedPaletteRGB idx
        out := Png.pushU16Full out r
        out := Png.pushU16Full out g
        out := Png.pushU16Full out b
    return out

private def indexedExpectedRGBA16Data (w h entryCount : Nat)
    (alpha? : Option ByteArray := none) : ByteArray :=
  Id.run do
    let mut out := ByteArray.emptyWithCapacity (w * h * RGBA16.bytesPerPixel)
    for y in [0:h] do
      for x in [0:w] do
        let idx := (indexedFixtureIndex entryCount x y).toNat
        let (r, g, b) := indexedPaletteRGB idx
        out := Png.pushU16Full out r
        out := Png.pushU16Full out g
        out := Png.pushU16Full out b
        out := Png.pushU16Full out (paletteAlphaAtTest alpha? idx)
    return out

private def indexedExpectedGray16Data (w h entryCount : Nat) : ByteArray :=
  Id.run do
    let mut out := ByteArray.emptyWithCapacity (w * h * Gray16.bytesPerPixel)
    for y in [0:h] do
      for x in [0:w] do
        let idx := (indexedFixtureIndex entryCount x y).toNat
        let (r, g, b) := indexedPaletteRGB idx
        out := Png.pushU16Full out (Png.grayFromRGB8 r g b)
    return out

private def indexedExpectedGrayAlpha16Data (w h entryCount : Nat)
    (alpha? : Option ByteArray := none) : ByteArray :=
  Id.run do
    let mut out := ByteArray.emptyWithCapacity (w * h * GrayAlpha16.bytesPerPixel)
    for y in [0:h] do
      for x in [0:w] do
        let idx := (indexedFixtureIndex entryCount x y).toNat
        let (r, g, b) := indexedPaletteRGB idx
        out := Png.pushU16Full out (Png.grayFromRGB8 r g b)
        out := Png.pushU16Full out (paletteAlphaAtTest alpha? idx)
    return out

private def indexedPngWithChunks (w h bitDepth interlace : Nat)
    (preIdat : ByteArray) (raw : ByteArray) : ByteArray :=
  let ihdr := Png.u32be w ++ Png.u32be h ++
    ByteArray.mk #[Png.u8 bitDepth, Png.u8 3, Png.u8 0, Png.u8 0, Png.u8 interlace]
  Png.pngSignature ++ Png.mkChunkBytes Png.ihdrTypeBytes ihdr ++ preIdat ++
    Png.mkChunkBytes Png.idatTypeBytes (Png.zlibCompressFixed raw) ++
    Png.mkChunkBytes Png.iendTypeBytes ByteArray.empty

private def indexedPngWithSplitIdat (w h bitDepth interlace : Nat)
    (preIdat : ByteArray) (raw : ByteArray) : ByteArray :=
  let ihdr := Png.u32be w ++ Png.u32be h ++
    ByteArray.mk #[Png.u8 bitDepth, Png.u8 3, Png.u8 0, Png.u8 0, Png.u8 interlace]
  let idat := Png.zlibCompressFixed raw
  let split := idat.size / 2
  Png.pngSignature ++ Png.mkChunkBytes Png.ihdrTypeBytes ihdr ++ preIdat ++
    Png.mkChunkBytes Png.idatTypeBytes (idat.extract 0 split) ++
    Png.mkChunkBytes Png.idatTypeBytes (idat.extract split idat.size) ++
    Png.mkChunkBytes Png.iendTypeBytes ByteArray.empty

private def packIndexedRowFromFn (width bitDepth : Nat) (f : Nat -> UInt8) :
    ByteArray :=
  Id.run do
    let rowBytes := Png.paletteRowBytes width bitDepth
    let mut row := ByteArray.mk <| Array.replicate rowBytes 0
    for x in [0:width] do
      row := Png.palettePackIndexIntoRow row bitDepth x (f x)
    return row

private def indexedAdam7Raw (w h bitDepth entryCount : Nat) : ByteArray :=
  Id.run do
    let mut raw := ByteArray.empty
    for pass in Png.adam7Passes do
      let passWidth := Png.adam7PassDim w pass.startX pass.stepX
      let passHeight :=
        if passWidth == 0 then
          0
        else
          Png.adam7PassDim h pass.startY pass.stepY
      for passY in [0:passHeight] do
        raw := raw.push 0
        raw := raw ++ packIndexedRowFromFn passWidth bitDepth (fun passX =>
          let x := pass.startX + passX * pass.stepX
          let y := pass.startY + passY * pass.stepY
          indexedFixtureIndex entryCount x y)
    return raw

private def expectPaletteInvalidDecode (bytes : ByteArray) (label : String) : IO Unit := do
  if (Png.decodeIndexedBitmapWithMetadata bytes).isSome then
    throw (IO.userError s!"palette invalid decode accepted: {label}")
  if (Png.decodeBitmapWithMetadata (px := RGB8) bytes).isSome then
    throw (IO.userError s!"palette RGB invalid decode accepted: {label}")

private def expectPaletteRawFilterByte (name : String) (bytes : ByteArray)
    (rowBytes h : Nat) (filter : UInt8) : IO Unit := do
  match inflatedPngRaw? bytes with
  | some raw =>
      if raw.size != h * (rowBytes + 1) then
        throw (IO.userError s!"{name}: filtered raw size mismatch")
      if !allRowsHaveFilter raw rowBytes h filter then
        throw (IO.userError s!"{name}: unexpected filter byte")
  | none =>
      throw (IO.userError s!"{name}: failed to inflate encoded PNG")

private def expectPalettePng : IO Unit := do
  let filters : List Png.PngRowFilter := [.none, .sub, .up, .average, .paeth]
  let modes : List Png.PngEncodeMode := [.stored, .fixed, .dynamic]
  for cfg in [(1, 2), (2, 4), (4, 16), (8, 16)] do
    let bitDepth := cfg.1
    let entryCount := cfg.2
    let bmp := indexedFixtureBitmap 9 5 bitDepth entryCount
    for mode in modes do
      let bytes ←
        match Png.encodeIndexedBitmapChecked bmp mode with
        | Except.ok bytes => pure bytes
        | Except.error err =>
            throw (IO.userError s!"palette encode failed for bit depth {bitDepth}, mode {repr mode}: {err}")
      match Png.decodeIndexedBitmap bytes with
      | some decoded =>
          if decoded.bitDepth != bitDepth || decoded.palette != bmp.palette ||
              decoded.data != bmp.data then
            throw (IO.userError s!"palette compression round-trip mismatch for bit depth {bitDepth}, mode {repr mode}")
      | none =>
          throw (IO.userError s!"palette compression decode failed for bit depth {bitDepth}, mode {repr mode}")
    for filter in filters do
      let strategy := Png.PngFilterStrategy.fixed filter
      let bytes ←
        match Png.encodeIndexedBitmapWithOptionsChecked bmp
            { mode := .fixed, filter := strategy } with
        | Except.ok bytes => pure bytes
        | Except.error err =>
            throw (IO.userError s!"palette encode failed for bit depth {bitDepth}: {err}")
      match Png.decodeIndexedBitmap bytes with
      | some decoded =>
          if decoded.bitDepth != bitDepth || decoded.palette != bmp.palette ||
              decoded.data != bmp.data then
            throw (IO.userError s!"palette exact round-trip mismatch for bit depth {bitDepth}")
      | none =>
          throw (IO.userError s!"palette exact decode failed for bit depth {bitDepth}")
      match Png.decodeBitmap (px := RGB8) bytes with
      | some decoded =>
          if decoded.data != indexedExpectedRGB8Data 9 5 entryCount then
            throw (IO.userError s!"palette RGB8 expansion mismatch for bit depth {bitDepth}")
      | none =>
          throw (IO.userError s!"palette RGB8 expansion failed for bit depth {bitDepth}")
      match Png.decodeBitmap (px := RGBA8) bytes with
      | some decoded =>
          if decoded.data != indexedExpectedRGBA8Data 9 5 entryCount then
            throw (IO.userError s!"palette RGBA8 expansion mismatch for bit depth {bitDepth}")
      | none =>
          throw (IO.userError s!"palette RGBA8 expansion failed for bit depth {bitDepth}")
      match Png.decodeBitmap (px := Gray8) bytes with
      | some decoded =>
          if decoded.data != indexedExpectedGray8Data 9 5 entryCount then
            throw (IO.userError s!"palette Gray8 expansion mismatch for bit depth {bitDepth}")
      | none =>
          throw (IO.userError s!"palette Gray8 expansion failed for bit depth {bitDepth}")
      match Png.decodeBitmap (px := GrayAlpha8) bytes with
      | some decoded =>
          if decoded.data != indexedExpectedGrayAlpha8Data 9 5 entryCount then
            throw (IO.userError s!"palette GrayAlpha8 expansion mismatch for bit depth {bitDepth}")
      | none =>
          throw (IO.userError s!"palette GrayAlpha8 expansion failed for bit depth {bitDepth}")
      expectPaletteRawFilterByte "indexed fixed filter" bytes
        (Png.paletteRowBytes bmp.size.width bitDepth) bmp.size.height filter.toByte
  let bmp16 := indexedFixtureBitmap 7 3 4 16
  let bytes16 ←
    match Png.encodeIndexedBitmapChecked bmp16 .fixed with
    | Except.ok bytes => pure bytes
    | Except.error err => throw (IO.userError s!"palette RGB16 encode failed: {err}")
  match Png.decodeBitmap (px := RGB16) bytes16 with
  | some decoded =>
      if decoded.data != indexedExpectedRGB16Data 7 3 16 then
        throw (IO.userError "palette RGB16 expansion mismatch")
  | none =>
      throw (IO.userError "palette RGB16 expansion failed")
  match Png.decodeBitmap (px := RGBA16) bytes16 with
  | some decoded =>
      if decoded.data != indexedExpectedRGBA16Data 7 3 16 then
        throw (IO.userError "palette RGBA16 expansion mismatch")
  | none =>
      throw (IO.userError "palette RGBA16 expansion failed")
  match Png.decodeBitmap (px := Gray16) bytes16 with
  | some decoded =>
      if decoded.data != indexedExpectedGray16Data 7 3 16 then
        throw (IO.userError "palette Gray16 expansion mismatch")
  | none =>
      throw (IO.userError "palette Gray16 expansion failed")
  match Png.decodeBitmap (px := GrayAlpha16) bytes16 with
  | some decoded =>
      if decoded.data != indexedExpectedGrayAlpha16Data 7 3 16 then
        throw (IO.userError "palette GrayAlpha16 expansion mismatch")
  | none =>
      throw (IO.userError "palette GrayAlpha16 expansion failed")

  let alpha := ByteArray.mk #[Png.u8 0, Png.u8 255, Png.u8 128, Png.u8 255]
  let alphaBmp := indexedFixtureBitmap 5 4 2 4 (some alpha) (some (Png.u8 1))
  let alphaBytes ←
    match Png.encodeIndexedBitmapChecked alphaBmp .fixed with
    | Except.ok bytes => pure bytes
    | Except.error err => throw (IO.userError s!"palette alpha encode failed: {err}")
  if (Png.decodeBitmap (px := RGBA8) alphaBytes).isSome then
    throw (IO.userError "pixel-only palette decode accepted tRNS")
  match Png.decodeBitmapWithMetadata (px := RGBA8) alphaBytes with
  | some decoded =>
      if decoded.bitmap.data != indexedExpectedRGBA8Data 5 4 4 (some alpha) then
        throw (IO.userError "palette tRNS RGBA expansion mismatch")
      match decoded.metadata.transparency, decoded.metadata.background with
      | some (.paletteAlpha a), some (.paletteIndex bg) =>
          if a != alpha || bg != Png.u8 1 then
            throw (IO.userError "palette metadata values mismatch")
      | _, _ =>
          throw (IO.userError "palette metadata missing")
  | none =>
      throw (IO.userError "palette tRNS RGBA metadata decode failed")
  match Png.decodeBitmapWithMetadata (px := RGB8) alphaBytes with
  | some decoded =>
      if decoded.bitmap.data != indexedExpectedRGB8Data 5 4 4 (some alpha) (some (Png.u8 1)) then
        throw (IO.userError "palette tRNS+bKGD RGB composition mismatch")
  | none =>
      throw (IO.userError "palette tRNS+bKGD RGB metadata decode failed")
  match Png.decodeIndexedBitmapWithMetadata alphaBytes with
  | some decoded =>
      if decoded.bitmap.transparency != some alpha || decoded.bitmap.background != some (Png.u8 1) then
        throw (IO.userError "palette exact metadata decode mismatch")
  | none =>
      throw (IO.userError "palette exact metadata decode failed")

  let adam7Pre := Png.mkChunkBytes Png.plteTypeBytes (indexedPaletteEntries 4)
  let adam7Bytes := indexedPngWithChunks 9 7 2 1 adam7Pre (indexedAdam7Raw 9 7 2 4)
  match Png.decodeIndexedBitmap adam7Bytes with
  | some decoded =>
      if decoded.data != indexedFixtureData 9 7 4 then
        throw (IO.userError "palette Adam7 exact decode mismatch")
  | none =>
      throw (IO.userError "palette Adam7 exact decode failed")
  let multiRaw := Png.encodeRawIndexedWithFilter bmp16 .none
  let multiPre := Png.mkChunkBytes Png.plteTypeBytes bmp16.palette.entries
  let multiBytes := indexedPngWithSplitIdat 7 3 4 0 multiPre multiRaw
  match Png.decodeIndexedBitmap multiBytes with
  | some decoded =>
      if decoded.data != bmp16.data || decoded.palette != bmp16.palette then
        throw (IO.userError "palette multi-IDAT exact decode mismatch")
  | none =>
      throw (IO.userError "palette multi-IDAT exact decode failed")

  let colorSpaceBmp := indexedFixtureBitmap 4 2 2 4
  let gamma := 100000
  let gammaBytes ←
    match Png.encodeIndexedBitmapWithOptionsChecked colorSpaceBmp
        { mode := .fixed, colorSpace := some (.gamma gamma) } with
    | Except.ok bytes => pure bytes
    | Except.error err => throw (IO.userError s!"palette gAMA encode failed: {err}")
  match Png.decodeBitmapWithMetadata (px := RGB8) gammaBytes with
  | some decoded =>
      if decoded.bitmap.data != gammaTransformRgb8Data gamma (indexedExpectedRGB8Data 4 2 4) then
        throw (IO.userError "palette gAMA RGB8 decode did not convert samples")
      if decoded.metadata.gamma != some gamma then
        throw (IO.userError "palette gAMA metadata was not preserved")
  | none =>
      throw (IO.userError "palette gAMA RGB8 metadata decode failed")
  let srgbBytes ←
    match Png.encodeIndexedBitmapWithOptionsChecked colorSpaceBmp
        { mode := .fixed, colorSpace := some (.srgb .perceptual true),
          chromaticities := some Png.PngChromaticities.srgb } with
    | Except.ok bytes => pure bytes
    | Except.error err => throw (IO.userError s!"palette sRGB encode failed: {err}")
  match Png.decodeBitmapWithMetadata (px := RGB8) srgbBytes with
  | some decoded =>
      if decoded.bitmap.data != indexedExpectedRGB8Data 4 2 4 then
        throw (IO.userError "palette sRGB decode changed already-sRGB samples")
      if decoded.metadata.srgb != some .perceptual ||
          decoded.metadata.gamma != some 45455 ||
          decoded.metadata.chromaticities != some Png.PngChromaticities.srgb then
        throw (IO.userError "palette sRGB metadata was not preserved")
  | none =>
      throw (IO.userError "palette sRGB metadata decode failed")
  let chrmBytes ←
    match Png.encodeIndexedBitmapWithOptionsChecked colorSpaceBmp
        { mode := .fixed, colorSpace := some (.gamma gamma),
          chromaticities := some wideChromaticities } with
    | Except.ok bytes => pure bytes
    | Except.error err => throw (IO.userError s!"palette cHRM encode failed: {err}")
  match Png.decodeBitmapWithMetadata (px := RGB8) chrmBytes with
  | some decoded =>
      if decoded.bitmap.data !=
          chrmTransformRgb8Data wideChromaticities (some gamma)
            (indexedExpectedRGB8Data 4 2 4) then
        throw (IO.userError "palette cHRM+gAMA RGB8 decode did not convert samples")
      if decoded.metadata.chromaticities != some wideChromaticities ||
          decoded.metadata.gamma != some gamma then
        throw (IO.userError "palette cHRM+gAMA metadata was not preserved")
  | none =>
      throw (IO.userError "palette cHRM+gAMA metadata decode failed")

  let badPaletteSizeBmp := indexedFixtureBitmap 1 1 1 3
  match Png.encodeIndexedBitmapChecked badPaletteSizeBmp .fixed with
  | Except.error _ => pure ()
  | Except.ok _ => throw (IO.userError "palette encoder accepted too many entries for bit depth")
  let badIndexBmp : Png.PngIndexedBitmap :=
    { size := { width := 1, height := 1 }
      bitDepth := 1
      palette := indexedPalette 2
      data := ByteArray.mk #[Png.u8 2]
      transparency := none
      background := none
      valid := by decide }
  match Png.encodeIndexedBitmapChecked badIndexBmp .fixed with
  | Except.error _ => pure ()
  | Except.ok _ => throw (IO.userError "palette encoder accepted out-of-range index")
  let badAlphaBmp := { badIndexBmp with data := ByteArray.mk #[Png.u8 0], transparency := some (ByteArray.mk #[0, 1, 2]) }
  match Png.encodeIndexedBitmapChecked badAlphaBmp .fixed with
  | Except.error _ => pure ()
  | Except.ok _ => throw (IO.userError "palette encoder accepted too-long alpha data")
  let badBackgroundBmp := { badIndexBmp with data := ByteArray.mk #[Png.u8 0], background := some (Png.u8 2) }
  match Png.encodeIndexedBitmapChecked badBackgroundBmp .fixed with
  | Except.error _ => pure ()
  | Except.ok _ => throw (IO.userError "palette encoder accepted out-of-range background")

  let plte2 := Png.mkChunkBytes Png.plteTypeBytes (indexedPaletteEntries 2)
  let plteBadLen := Png.mkChunkBytes Png.plteTypeBytes (ByteArray.mk #[Png.u8 0])
  let plteEmpty := Png.mkChunkBytes Png.plteTypeBytes ByteArray.empty
  let plteOversize := Png.mkChunkBytes Png.plteTypeBytes
    (ByteArray.mk <| Array.replicate (257 * 3) (Png.u8 0))
  let raw1 := ByteArray.mk #[Png.u8 0, Png.u8 0]
  expectPaletteInvalidDecode (indexedPngWithChunks 1 1 1 0 ByteArray.empty raw1) "missing PLTE"
  expectPaletteInvalidDecode (indexedPngWithChunks 1 1 1 0 plteBadLen raw1) "bad PLTE length"
  expectPaletteInvalidDecode (indexedPngWithChunks 1 1 1 0 plteEmpty raw1) "empty PLTE"
  expectPaletteInvalidDecode (indexedPngWithChunks 1 1 8 0 plteOversize raw1) "oversized PLTE"
  expectPaletteInvalidDecode (indexedPngWithChunks 1 1 2 0 plte2 (ByteArray.mk #[0, Png.u8 0xc0]))
    "out-of-range decoded index"
  expectPaletteInvalidDecode (indexedPngWithChunks 1 1 1 0 (plte2 ++ plte2) raw1) "duplicate PLTE"
  expectPaletteInvalidDecode
    (indexedPngWithChunks 1 1 1 0
      (Png.mkChunkBytes Png.trnsTypeBytes (ByteArray.mk #[0]) ++ plte2) raw1)
    "tRNS before PLTE"
  expectPaletteInvalidDecode
    (indexedPngWithChunks 1 1 1 0
      (Png.mkChunkBytes Png.bkgdTypeBytes (ByteArray.mk #[0]) ++ plte2) raw1)
    "bKGD before PLTE"
  expectPaletteInvalidDecode
    (indexedPngWithChunks 1 1 1 0
      (plte2 ++ Png.mkChunkBytes Png.trnsTypeBytes (ByteArray.mk #[0, 1, 2])) raw1)
    "palette tRNS too long"
  expectPaletteInvalidDecode
    (indexedPngWithChunks 1 1 1 0
      (plte2 ++ Png.mkChunkBytes Png.trnsTypeBytes (ByteArray.mk #[0]) ++
        Png.mkChunkBytes Png.trnsTypeBytes (ByteArray.mk #[1])) raw1)
    "duplicate palette tRNS"
  expectPaletteInvalidDecode
    (indexedPngWithChunks 1 1 1 0
      (plte2 ++ Png.mkChunkBytes Png.bkgdTypeBytes (ByteArray.mk #[2])) raw1)
    "palette bKGD out of range"
  expectPaletteInvalidDecode
    (indexedPngWithChunks 1 1 1 0
      (plte2 ++ Png.mkChunkBytes Png.bkgdTypeBytes (ByteArray.mk #[0]) ++
        Png.mkChunkBytes Png.bkgdTypeBytes (ByteArray.mk #[1])) raw1)
    "duplicate palette bKGD"
  expectPaletteInvalidDecode
    (indexedPngWithChunks 1 1 1 0
      (plte2 ++ Png.mkChunkBytes Png.idatTypeBytes raw1 ++
        Png.mkChunkBytes Png.trnsTypeBytes (ByteArray.mk #[0]))
      ByteArray.empty)
    "palette tRNS after IDAT"
  expectPaletteInvalidDecode
    (indexedPngWithChunks 1 1 1 0
      (plte2 ++ Png.mkChunkBytes Png.idatTypeBytes raw1 ++
        Png.mkChunkBytes Png.bkgdTypeBytes (ByteArray.mk #[0]))
      ByteArray.empty)
    "palette bKGD after IDAT"

private def filterRGB8Fixture : Bitmap.RGB8 :=
  Bitmap.ofFn 6 4 (fun idx : Fin (6 * 4) =>
    let x := idx.val % 6
    let y := idx.val / 6
    { r := Png.u8 (30 + x * 17 + y * 9)
      g := Png.u8 (20 + x * 11 + y * 23)
      b := Png.u8 (200 - x * 13 + y * 5) })

private def filterRGBA8Fixture : Bitmap.RGBA8 :=
  Bitmap.ofFn 5 3 (fun idx : Fin (5 * 3) =>
    let x := idx.val % 5
    let y := idx.val / 5
    { r := Png.u8 (x * 40 + y * 7)
      g := Png.u8 (180 - x * 12 + y * 9)
      b := Png.u8 (50 + x * 21 + y * 15)
      a := Png.u8 (90 + x * 19 + y * 17) })

private def filterGray8Fixture : Bitmap.Gray8 :=
  Bitmap.ofFn 7 3 (fun idx : Fin (7 * 3) =>
    let x := idx.val % 7
    let y := idx.val / 7
    { v := Png.u8 (x * 31 + y * 37) })

private def filterGray16Fixture : Bitmap.Gray16 :=
  Bitmap.ofFn 4 3 (fun idx : Fin (4 * 3) =>
    let x := idx.val % 4
    let y := idx.val / 4
    { v := u16 (0x1200 + x * 0x101 + y * 0x1111) })

private def adaptiveNonzeroFixture : Bitmap.RGB8 :=
  Bitmap.ofFn 8 4 (fun _idx : Fin (8 * 4) =>
    { r := Png.u8 80, g := Png.u8 80, b := Png.u8 80 })

private def expectFilteredBitmapRoundTrip {px : Type} [PixelFormat px] [Png.PixelFormat px]
    (name : String) (bmp : Bitmap px) (strategy : Png.PngFilterStrategy) : IO ByteArray := do
  match Png.encodeBitmapWithOptionsChecked (px := px) bmp
      { mode := .fixed, filter := strategy } with
  | Except.error err =>
      throw (IO.userError s!"{name}: filtered encode failed: {err}")
  | Except.ok bytes =>
      match Png.decodeBitmap (px := px) bytes with
      | some decoded =>
          if decoded.size.width != bmp.size.width ||
              decoded.size.height != bmp.size.height ||
              decoded.data != bmp.data then
            throw (IO.userError s!"{name}: filtered round-trip mismatch")
          pure bytes
      | none =>
          throw (IO.userError s!"{name}: filtered decode failed")

private def expectFilteredGray1RoundTrip
    (name : String) (bmp : Bitmap.Gray1) (strategy : Png.PngFilterStrategy) :
    IO ByteArray := do
  match Png.encodeGray1BitmapWithOptionsChecked bmp { mode := .fixed, filter := strategy } with
  | Except.error err =>
      throw (IO.userError s!"{name}: filtered Gray1 encode failed: {err}")
  | Except.ok bytes =>
      match Png.decodeGray1Bitmap bytes with
      | some decoded =>
          if decoded != bmp then
            throw (IO.userError s!"{name}: filtered Gray1 round-trip mismatch")
          pure bytes
      | none =>
          throw (IO.userError s!"{name}: filtered Gray1 decode failed")

private def expectRawFilterByte (name : String) (bytes : ByteArray)
    (rowBytes h : Nat) (filter : UInt8) : IO Unit := do
  match inflatedPngRaw? bytes with
  | some raw =>
      if raw.size != h * (rowBytes + 1) then
        throw (IO.userError s!"{name}: filtered raw size mismatch")
      if !allRowsHaveFilter raw rowBytes h filter then
        throw (IO.userError s!"{name}: unexpected filter byte")
  | none =>
      throw (IO.userError s!"{name}: failed to inflate encoded PNG")

private def expectPngEncodeFilters : IO Unit := do
  let filters : List Png.PngRowFilter := [.none, .sub, .up, .average, .paeth]
  for filter in filters do
    let strategy := Png.PngFilterStrategy.fixed filter
    let rgbBytes ← expectFilteredBitmapRoundTrip "RGB8 fixed filter" filterRGB8Fixture strategy
    expectRawFilterByte "RGB8 fixed filter" rgbBytes
      (filterRGB8Fixture.size.width * RGB8.bytesPerPixel) filterRGB8Fixture.size.height filter.toByte
    let rgbaBytes ← expectFilteredBitmapRoundTrip "RGBA8 fixed filter" filterRGBA8Fixture strategy
    expectRawFilterByte "RGBA8 fixed filter" rgbaBytes
      (filterRGBA8Fixture.size.width * RGBA8.bytesPerPixel) filterRGBA8Fixture.size.height filter.toByte
    let grayBytes ← expectFilteredBitmapRoundTrip "Gray8 fixed filter" filterGray8Fixture strategy
    expectRawFilterByte "Gray8 fixed filter" grayBytes
      (filterGray8Fixture.size.width * Gray8.bytesPerPixel) filterGray8Fixture.size.height filter.toByte
    let grayAlphaBytes ← expectFilteredBitmapRoundTrip "GrayAlpha8 fixed filter" grayAlphaFixture strategy
    expectRawFilterByte "GrayAlpha8 fixed filter" grayAlphaBytes
      (grayAlphaFixture.size.width * GrayAlpha8.bytesPerPixel) grayAlphaFixture.size.height filter.toByte
    let rgb16Bytes ← expectFilteredBitmapRoundTrip "RGB16 fixed filter" rgb16DownsampleFixture strategy
    expectRawFilterByte "RGB16 fixed filter" rgb16Bytes
      (rgb16DownsampleFixture.size.width * RGB16.bytesPerPixel) rgb16DownsampleFixture.size.height filter.toByte
    let gray16Bytes ← expectFilteredBitmapRoundTrip "Gray16 fixed filter" filterGray16Fixture strategy
    expectRawFilterByte "Gray16 fixed filter" gray16Bytes
      (filterGray16Fixture.size.width * Gray16.bytesPerPixel) filterGray16Fixture.size.height filter.toByte
    for w in [1, 7, 8, 9, 17] do
      let bmp := gray1FixtureBitmap w 4
      let bytes ← expectFilteredGray1RoundTrip "Gray1 fixed filter" bmp strategy
      expectRawFilterByte "Gray1 fixed filter" bytes
        (gray1RowBytes bmp.size.width) bmp.size.height filter.toByte

  let defaultBytes ←
    match Png.encodeBitmapChecked (px := RGB8) filterRGB8Fixture .fixed with
    | Except.ok bytes => pure bytes
    | Except.error err => throw (IO.userError err)
  let optionDefaultBytes ←
    match Png.encodeBitmapWithOptionsChecked (px := RGB8) filterRGB8Fixture
        { mode := .fixed, filter := .none } with
    | Except.ok bytes => pure bytes
    | Except.error err => throw (IO.userError err)
  if defaultBytes != optionDefaultBytes then
    throw (IO.userError "default encoder output changed when filter options were omitted")

  let adaptiveBytes ←
    expectFilteredBitmapRoundTrip "RGB8 adaptive filter" adaptiveNonzeroFixture .adaptive
  match inflatedPngRaw? adaptiveBytes with
  | some raw =>
      if !rawHasNonzeroFilter raw
          (adaptiveNonzeroFixture.size.width * RGB8.bytesPerPixel)
          adaptiveNonzeroFixture.size.height then
        throw (IO.userError "adaptive filter failed to choose any nonzero row filter")
  | none =>
      throw (IO.userError "adaptive filter PNG failed to inflate")
  let gray1Adaptive ←
    expectFilteredGray1RoundTrip "Gray1 adaptive filter" (gray1FixtureBitmap 17 4) .adaptive
  if (inflatedPngRaw? gray1Adaptive).isNone then
    throw (IO.userError "Gray1 adaptive filter PNG failed to inflate")
  let zeroBmp := Bitmap.fill (px := RGB8) 5 3 { r := Png.u8 0, g := Png.u8 0, b := Png.u8 0 }
  let zeroBytes ← expectFilteredBitmapRoundTrip "adaptive zero tie" zeroBmp .adaptive
  match inflatedPngRaw? zeroBytes with
  | some raw =>
      if !allRowsHaveFilter raw (zeroBmp.size.width * RGB8.bytesPerPixel) zeroBmp.size.height 0 then
        throw (IO.userError "adaptive all-zero tie did not choose filter 0")
  | none =>
      throw (IO.userError "adaptive zero PNG failed to inflate")

private def expect16To8Downsample : IO Unit := do
  let rgbBytes ← encodeFixturePng rgb16DownsampleFixture
  match Png.decodeBitmap (px := RGB8) rgbBytes with
  | some bmp =>
      if bmp.data != ByteArray.mk #[0x12, 0x34, 0xfe, 0x01, 0x80, 0x00] then
        throw (IO.userError "RGB16 -> RGB8 downsample used unexpected bytes")
  | none =>
      throw (IO.userError "RGB16 -> RGB8 downsample failed")
  let rgbaBytes ← encodeFixturePng rgba16DownsampleFixture
  match Png.decodeBitmap (px := RGBA8) rgbaBytes with
  | some bmp =>
      if bmp.data != ByteArray.mk #[0x12, 0x34, 0xfe, 0x77, 0x01, 0x80, 0x00, 0xff] then
        throw (IO.userError "RGBA16 -> RGBA8 downsample used unexpected bytes")
  | none =>
      throw (IO.userError "RGBA16 -> RGBA8 downsample failed")
  let grayBytes ← encodeFixturePng gray16DownsampleFixture
  match Png.decodeBitmap (px := Gray8) grayBytes with
  | some bmp =>
      if bmp.data != ByteArray.mk #[0x12, 0x80, 0x00] then
        throw (IO.userError "Gray16 -> Gray8 downsample used unexpected bytes")
  | none =>
      throw (IO.userError "Gray16 -> Gray8 downsample failed")
  let grayAlphaBytes ← encodeFixturePng grayAlpha16DownsampleFixture
  match Png.decodeBitmap (px := GrayAlpha8) grayAlphaBytes with
  | some bmp =>
      if bmp.data != ByteArray.mk #[0x12, 0x34, 0x80, 0x00] then
        throw (IO.userError "GrayAlpha16 -> GrayAlpha8 downsample used unexpected bytes")
  | none =>
      throw (IO.userError "GrayAlpha16 -> GrayAlpha8 downsample failed")

private def expect16BitMetadata : IO Unit := do
  match Png.decodeBitmapWithMetadata (px := RGBA8) rgb16MetadataPng with
  | some decoded =>
      if decoded.bitmap.data != ByteArray.mk
          #[0x12, 0x56, 0x9a, 0x00, 0x20, 0x40, 0x60, 0xff] then
        throw (IO.userError "RGB16+tRNS -> RGBA8 metadata decode mismatch")
      match decoded.metadata.transparency with
      | some (Png.PngTransparency.rgb16 r g b) =>
          if r != u16 0x1234 || g != u16 0x5678 || b != u16 0x9abc then
            throw (IO.userError "RGB16 tRNS metadata had wrong value")
      | _ =>
          throw (IO.userError "RGB16 tRNS metadata was missing")
  | none =>
      throw (IO.userError "RGB16+tRNS -> RGBA8 metadata decode failed")
  match Png.decodeBitmapWithMetadata (px := RGB8) rgb16MetadataPng with
  | some decoded =>
      if decoded.bitmap.data != ByteArray.mk #[0x21, 0x43, 0x65, 0x20, 0x40, 0x60] then
        throw (IO.userError "RGB16+tRNS+bKGD -> RGB8 composition mismatch")
      match decoded.metadata.background with
      | some (Png.PngBackground.rgb16 r g b) =>
          if r != u16 0x2100 || g != u16 0x4300 || b != u16 0x6500 then
            throw (IO.userError "RGB16 bKGD metadata had wrong value")
      | _ =>
          throw (IO.userError "RGB16 bKGD metadata was missing")
  | none =>
      throw (IO.userError "RGB16+tRNS+bKGD -> RGB8 metadata decode failed")
  match Png.decodeBitmapWithMetadata (px := RGB16) rgb16MetadataPng with
  | some decoded =>
      if decoded.bitmap.data != ByteArray.mk
          #[0x21, 0x00, 0x43, 0x00, 0x65, 0x00, 0x20, 0x01, 0x40, 0x02, 0x60, 0x03] then
        throw (IO.userError "RGB16+tRNS+bKGD -> RGB16 composition mismatch")
  | none =>
      throw (IO.userError "RGB16+tRNS+bKGD -> RGB16 metadata decode failed")
  match Png.decodeBitmapWithMetadata (px := RGBA16) rgb16MetadataPng with
  | some decoded =>
      if decoded.bitmap.data != ByteArray.mk
          #[0x12, 0x34, 0x56, 0x78, 0x9a, 0xbc, 0x00, 0x00,
            0x20, 0x01, 0x40, 0x02, 0x60, 0x03, 0xff, 0xff] then
        throw (IO.userError "RGB16+tRNS -> RGBA16 alpha mismatch")
  | none =>
      throw (IO.userError "RGB16+tRNS -> RGBA16 metadata decode failed")
  match Png.decodeBitmapWithMetadata (px := Gray8) grayAlpha16MetadataPng with
  | some decoded =>
      if decoded.bitmap.data != ByteArray.mk #[0x30, 0x80] then
        throw (IO.userError "GrayAlpha16+bKGD -> Gray8 composition mismatch")
      match decoded.metadata.background with
      | some (Png.PngBackground.gray16 gray) =>
          if gray != u16 0x3000 then
            throw (IO.userError "GrayAlpha16 bKGD metadata had wrong value")
      | _ =>
          throw (IO.userError "GrayAlpha16 bKGD metadata was missing")
  | none =>
      throw (IO.userError "GrayAlpha16+bKGD -> Gray8 metadata decode failed")
  match Png.decodeBitmapWithMetadata (px := Gray16) grayAlpha16MetadataPng with
  | some decoded =>
      if decoded.bitmap.data != ByteArray.mk #[0x30, 0x00, 0x80, 0x01] then
        throw (IO.userError "GrayAlpha16+bKGD -> Gray16 composition mismatch")
  | none =>
      throw (IO.userError "GrayAlpha16+bKGD -> Gray16 metadata decode failed")
  match Png.decodeBitmapWithMetadata (px := RGB8) rgba16MetadataPng with
  | some decoded =>
      if decoded.bitmap.data != ByteArray.mk #[0x21, 0x43, 0x65, 0x20, 0x40, 0x60] then
        throw (IO.userError "RGBA16+bKGD -> RGB8 composition mismatch")
  | none =>
      throw (IO.userError "RGBA16+bKGD -> RGB8 metadata decode failed")

private def expectGrayAlphaFixtures : IO Unit := do
  match Png.decodeBitmap (px := GrayAlpha8) grayAlphaPng with
  | some bmp =>
      if bmp != grayAlphaFixture then
        throw (IO.userError "gray+alpha PNG did not decode exactly")
  | none =>
      throw (IO.userError "gray+alpha PNG failed to decode")
  match Png.decodeBitmap (px := RGBA8) grayAlphaPng with
  | some bmp =>
      if bmp.size.width != 2 || bmp.size.height != 2 ||
          bmp.data != grayAlphaFixtureExpectedRGBAData then
        throw (IO.userError "gray+alpha PNG did not expand to RGBA")
  | none =>
      throw (IO.userError "gray+alpha PNG failed to decode as RGBA")
  if (Png.decodeBitmap (px := RGB8) grayAlphaPng).isSome then
    throw (IO.userError "pixel-only RGB decode accepted gray+alpha without bKGD")
  if (Png.decodeBitmap (px := Gray8) grayAlphaPng).isSome then
    throw (IO.userError "pixel-only Gray decode accepted gray+alpha without bKGD")
  match Png.decodeBitmapWithMetadata (px := GrayAlpha8) grayAlphaPngWithBkgd with
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
  match Png.decodeBitmapWithMetadata (px := RGB8) grayAlphaPngWithBkgd with
  | some decoded =>
      if decoded.bitmap.data != grayAlphaOverBackgroundRGBData (Png.u8 100) then
        throw (IO.userError "gray+alpha bKGD RGB composition mismatch")
  | none =>
      throw (IO.userError "gray+alpha bKGD RGB decode failed")
  match Png.decodeBitmapWithMetadata (px := Gray8) grayAlphaPngWithBkgd with
  | some decoded =>
      if decoded.bitmap.data != grayAlphaOverBackgroundGrayData (Png.u8 100) then
        throw (IO.userError "gray+alpha bKGD Gray composition mismatch")
  | none =>
      throw (IO.userError "gray+alpha bKGD Gray decode failed")
  if (Png.decodeBitmapWithMetadata (px := RGBA8) grayAlphaPngWithTrns).isSome then
    throw (IO.userError "metadata-aware decoder accepted tRNS for gray+alpha")

private def expectAncDecodeOk (path : System.FilePath) : IO Unit := do
  let bytes <- IO.FS.readBinFile path
  match Png.decodeBitmap (px := RGB8) bytes with
  | some bmp =>
      if bmp.size.width != 4 || bmp.size.height != 4 then
        throw (IO.userError s!"{path}: unexpected dimensions {bmp.size.width}x{bmp.size.height}")
      if bmp.data != ancFixtureReferenceData then
        throw (IO.userError s!"{path}: pixel data mismatch against reference pattern")
  | none =>
      throw (IO.userError s!"{path}: tolerated-chunk fixture failed to decode")

private def expectAncTrnsRgbaOk (path : System.FilePath) : IO Unit := do
  let bytes <- IO.FS.readBinFile path
  match Png.decodeBitmapWithMetadata (px := RGBA8) bytes with
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
  match Png.decodeBitmapWithMetadata (px := RGB8) bytes with
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
  match Png.decodeBitmapWithMetadata (px := RGB8) bytes with
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
  match Png.decodeBitmapWithMetadata (px := RGB8) bytes with
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
  match Png.decodeBitmapWithMetadata (px := Gray8) bytes with
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
  match Png.decodeBitmap (px := RGB8) bytes with
  | some _ =>
      throw (IO.userError s!"{path}: decoder accepted a {label} fixture that should be rejected")
  | none =>
      pure ()

private def expectAncMetadataDecodeNone (path : System.FilePath) (label : String) : IO Unit := do
  let bytes <- IO.FS.readBinFile path
  match Png.decodeBitmapWithMetadata (px := RGBA8) bytes with
  | some _ =>
      throw (IO.userError s!"{path}: metadata-aware decoder accepted a {label} fixture that should be rejected")
  | none =>
      pure ()

private def expectMetadataDecodeNoneBytes (bytes : ByteArray) (label : String) : IO Unit := do
  match Png.decodeBitmapWithMetadata (px := RGBA8) bytes with
  | some _ =>
      throw (IO.userError s!"metadata-aware decoder accepted invalid metadata chunk: {label}")
  | none =>
      pure ()

private def expectColorSpaceChunks : IO Unit := do
  let rgbFixture : Bitmap.RGB8 :=
    Bitmap.ofFn 3 1 (fun idx : Fin (3 * 1) =>
      match idx.val with
      | 0 => { r := Png.u8 32, g := Png.u8 96, b := Png.u8 160 }
      | 1 => { r := Png.u8 64, g := Png.u8 128, b := Png.u8 192 }
      | _ => { r := Png.u8 16, g := Png.u8 48, b := Png.u8 240 })
  for intent in
      #[Png.PngSrgbIntent.perceptual, .relativeColorimetric, .saturation, .absoluteColorimetric] do
    let bytes := pngWithAncillary rgbFixture (srgbChunk intent)
    match Png.decodeBitmapWithMetadata (px := RGB8) bytes with
    | some decoded =>
        if decoded.bitmap.data != rgbFixture.data then
          throw (IO.userError "sRGB changed already-sRGB RGB samples")
        if decoded.metadata.srgb != some intent then
          throw (IO.userError "sRGB rendering intent was not preserved")
    | none =>
        throw (IO.userError "sRGB fixture failed to decode")
  let gamma := 100000
  let gammaBytes := pngWithAncillary rgbFixture (gamaChunk gamma)
  match Png.decodeBitmap (px := RGB8) gammaBytes with
  | some bmp =>
      if bmp.data != gammaTransformRgb8Data gamma rgbFixture.data then
        throw (IO.userError "gAMA RGB8 decode did not convert samples to sRGB")
  | none =>
      throw (IO.userError "gAMA RGB8 fixture failed to decode")
  match Png.decodeBitmapWithMetadata (px := RGB8) gammaBytes with
  | some decoded =>
      if decoded.metadata.gamma != some gamma then
        throw (IO.userError "gAMA metadata was not preserved")
  | none =>
      throw (IO.userError "gAMA metadata decode failed")
  let rgbaFixture : Bitmap.RGBA8 :=
    Bitmap.ofFn 1 1 (fun _ =>
      { r := Png.u8 64, g := Png.u8 128, b := Png.u8 192, a := Png.u8 77 })
  match Png.decodeBitmap (px := RGBA8) (pngWithAncillary rgbaFixture (gamaChunk gamma)) with
  | some bmp =>
      if bmp.data != gammaTransformRgba8Data gamma rgbaFixture.data then
        throw (IO.userError "gAMA RGBA8 decode changed alpha or missed color conversion")
  | none =>
      throw (IO.userError "gAMA RGBA8 fixture failed to decode")
  let gray16Fixture : Bitmap.Gray16 :=
    Bitmap.ofFn 2 1 (fun idx : Fin (2 * 1) =>
      match idx.val with
      | 0 => { v := u16 0x4000 }
      | _ => { v := u16 0x9000 })
  match Png.decodeBitmap (px := Gray16) (pngWithAncillary gray16Fixture (gamaChunk gamma)) with
  | some bmp =>
      if bmp.data != gammaTransformGray16Data gamma gray16Fixture.data then
        throw (IO.userError "gAMA Gray16 decode did not convert samples to sRGB")
  | none =>
      throw (IO.userError "gAMA Gray16 fixture failed to decode")
  let compatBytes := pngWithAncillary rgbFixture (gamaChunk 45455 ++ srgbChunk .perceptual)
  match Png.decodeBitmapWithMetadata (px := RGB8) compatBytes with
  | some decoded =>
      if decoded.bitmap.data != rgbFixture.data then
        throw (IO.userError "sRGB precedence failed for compatible gAMA+sRGB")
      if decoded.metadata.gamma != some 45455 || decoded.metadata.srgb != some .perceptual then
        throw (IO.userError "compatible gAMA+sRGB metadata was not preserved")
  | none =>
      throw (IO.userError "compatible gAMA+sRGB fixture failed to decode")
  let chrmGammaBytes := pngWithAncillary rgbFixture (chrmChunk wideChromaticities ++ gamaChunk gamma)
  match Png.decodeBitmap (px := RGB8) chrmGammaBytes with
  | some bmp =>
      if bmp.data != chrmTransformRgb8Data wideChromaticities (some gamma) rgbFixture.data then
        throw (IO.userError "cHRM+gAMA RGB8 decode did not convert samples to sRGB")
  | none =>
      throw (IO.userError "cHRM+gAMA RGB8 fixture failed to decode")
  match Png.decodeBitmapWithMetadata (px := RGB8) chrmGammaBytes with
  | some decoded =>
      if decoded.metadata.chromaticities != some wideChromaticities ||
          decoded.metadata.gamma != some gamma then
        throw (IO.userError "cHRM+gAMA metadata was not preserved")
  | none =>
      throw (IO.userError "cHRM+gAMA metadata decode failed")
  match Png.decodeBitmap (px := RGBA8)
      (pngWithAncillary rgbaFixture (chrmChunk wideChromaticities ++ gamaChunk gamma)) with
  | some bmp =>
      if bmp.data != chrmTransformRgba8Data wideChromaticities (some gamma) rgbaFixture.data then
        throw (IO.userError "cHRM+gAMA RGBA8 decode changed alpha or missed conversion")
  | none =>
      throw (IO.userError "cHRM+gAMA RGBA8 fixture failed to decode")
  let chrmLinearBytes := pngWithAncillary rgbFixture (chrmChunk wideChromaticities)
  match Png.decodeBitmap (px := RGB8) chrmLinearBytes with
  | some bmp =>
      if bmp.data != chrmTransformRgb8Data wideChromaticities none rgbFixture.data then
        throw (IO.userError "cHRM without gAMA did not use linear-source conversion")
  | none =>
      throw (IO.userError "linear cHRM RGB8 fixture failed to decode")
  match Png.decodeBitmap (px := Gray8) chrmGammaBytes with
  | some bmp =>
      if bmp.data != chrmTransformGray8Data wideChromaticities (some gamma) rgbFixture.data then
        throw (IO.userError "cHRM RGB-to-gray decode did not use sRGB luminance")
  | none =>
      throw (IO.userError "cHRM RGB-to-gray fixture failed to decode")
  match Png.decodeBitmap (px := GrayAlpha8)
      (pngWithAncillary rgbaFixture (chrmChunk wideChromaticities ++ gamaChunk gamma)) with
  | some bmp =>
      if bmp.data != chrmTransformGrayAlpha8Data wideChromaticities (some gamma) rgbaFixture.data then
        throw (IO.userError "cHRM RGBA-to-gray-alpha decode missed luma or alpha")
  | none =>
      throw (IO.userError "cHRM RGBA-to-gray-alpha fixture failed to decode")
  match Png.decodeBitmap (px := RGB16)
      (pngWithAncillary rgb16MetadataFixture (chrmChunk wideChromaticities ++ gamaChunk gamma)) with
  | some bmp =>
      if bmp.data != chrmTransformRgb16Data wideChromaticities (some gamma)
          rgb16MetadataFixture.data then
        throw (IO.userError "cHRM+gAMA RGB16 decode did not convert samples to sRGB")
  | none =>
      throw (IO.userError "cHRM+gAMA RGB16 fixture failed to decode")
  let compatChrmBytes :=
    pngWithAncillary rgbFixture
      (gamaChunk 45455 ++ chrmChunk Png.PngChromaticities.srgb ++ srgbChunk .perceptual)
  match Png.decodeBitmapWithMetadata (px := RGB8) compatChrmBytes with
  | some decoded =>
      if decoded.bitmap.data != rgbFixture.data then
        throw (IO.userError "sRGB precedence failed for compatible gAMA+cHRM+sRGB")
      if decoded.metadata.gamma != some 45455 ||
          decoded.metadata.chromaticities != some Png.PngChromaticities.srgb ||
          decoded.metadata.srgb != some .perceptual then
        throw (IO.userError "compatible gAMA+cHRM+sRGB metadata was not preserved")
  | none =>
      throw (IO.userError "compatible gAMA+cHRM+sRGB fixture failed to decode")
  match Png.encodeBitmapWithOptionsChecked (px := RGB8) rgbFixture
      { mode := .fixed, chromaticities := some wideChromaticities } with
  | Except.ok bytes =>
      match Png.decodeBitmapWithMetadata (px := RGB8) bytes with
      | some decoded =>
          if decoded.metadata.chromaticities != some wideChromaticities then
            throw (IO.userError "encoded cHRM metadata failed to parse")
      | none =>
          throw (IO.userError "encoded cHRM PNG failed to decode")
  | Except.error err =>
      throw (IO.userError err)
  expectMetadataDecodeNoneBytes
    (pngWithAncillary rgbFixture (Png.mkChunkBytes Png.gamaTypeBytes (ByteArray.mk #[Png.u8 1])))
    "bad gAMA length"
  expectMetadataDecodeNoneBytes
    (pngWithAncillary rgbFixture (Png.mkChunkBytes Png.gamaTypeBytes (Png.u32be 0)))
    "zero gAMA"
  expectMetadataDecodeNoneBytes
    (pngWithAncillary rgbFixture (gamaChunk gamma ++ gamaChunk gamma))
    "duplicate gAMA"
  expectMetadataDecodeNoneBytes
    (pngWithAncillary rgbFixture (srgbChunk .perceptual ++ srgbChunk .saturation))
    "duplicate sRGB"
  expectMetadataDecodeNoneBytes
    (pngWithAncillary rgbFixture (Png.mkChunkBytes Png.srgbTypeBytes (ByteArray.mk #[Png.u8 4])))
    "bad sRGB intent"
  expectMetadataDecodeNoneBytes
    (pngWithAncillary rgbFixture (gamaChunk gamma ++ srgbChunk .perceptual))
    "incompatible gAMA+sRGB"
  expectMetadataDecodeNoneBytes
    (pngWithAncillary rgbFixture (plteChunk ++ gamaChunk gamma))
    "gAMA after PLTE"
  expectMetadataDecodeNoneBytes
    (pngWithAncillary rgbFixture (plteChunk ++ srgbChunk .perceptual))
    "sRGB after PLTE"
  expectMetadataDecodeNoneBytes
    (pngWithPostIdatAncillary rgbFixture (gamaChunk gamma))
    "gAMA after IDAT"
  match Png.encodeBitmapWithOptionsChecked (px := RGB8) rgbFixture
      { mode := .fixed, colorSpace := some (.srgb .perceptual true) } with
  | Except.ok bytes =>
      if bytes.extract 37 41 != Png.gamaTypeBytes then
        throw (IO.userError "encoder did not emit compatibility gAMA before sRGB")
      if bytes.extract 53 57 != Png.srgbTypeBytes then
        throw (IO.userError "encoder did not emit sRGB after compatibility gAMA")
      match Png.decodeBitmapWithMetadata (px := RGB8) bytes with
      | some decoded =>
          if decoded.metadata.gamma != some 45455 || decoded.metadata.srgb != some .perceptual then
            throw (IO.userError "encoded sRGB metadata failed to parse")
      | none =>
          throw (IO.userError "encoded sRGB PNG failed to decode")
  | Except.error err =>
      throw (IO.userError err)
  match Png.encodeBitmapWithOptionsChecked (px := RGB8) rgbFixture
      { mode := .fixed, colorSpace := some (.gamma 0) } with
  | Except.ok _ =>
      throw (IO.userError "encoder accepted zero gAMA option")
  | Except.error _ =>
      pure ()

private def expectTimeChunks : IO Unit := do
  let rgbFixture : Bitmap.RGB8 :=
    Bitmap.ofFn 2 1 (fun idx : Fin (2 * 1) =>
      match idx.val with
      | 0 => { r := Png.u8 12, g := Png.u8 34, b := Png.u8 56 }
      | _ => { r := Png.u8 78, g := Png.u8 90, b := Png.u8 123 })
  match Png.encodeBitmapWithOptionsChecked (px := RGB8) rgbFixture
      { mode := .fixed, modificationTime := some fixedPngTime } with
  | Except.ok bytes =>
      match Png.decodeBitmapWithMetadata (px := RGB8) bytes with
      | some decoded =>
          if decoded.bitmap.data != rgbFixture.data then
            throw (IO.userError "tIME encode changed RGB samples")
          if decoded.metadata.modificationTime != some fixedPngTime then
            throw (IO.userError "encoded tIME metadata failed to parse")
      | none =>
          throw (IO.userError "encoded tIME PNG failed to decode")
  | Except.error err =>
      throw (IO.userError err)
  match Png.encodeBitmapWithOptionsChecked (px := RGB8) rgbFixture
      { mode := .fixed, modificationTime := some { fixedPngTime with month := 13 } } with
  | Except.ok _ =>
      throw (IO.userError "encoder accepted invalid tIME option")
  | Except.error _ =>
      pure ()
  for bytes in #[pngWithAncillary rgbFixture (timeChunk fixedPngTime),
      pngWithPostIdatAncillary rgbFixture (timeChunk fixedPngTime)] do
    match Png.decodeBitmapWithMetadata (px := RGB8) bytes with
    | some decoded =>
        if decoded.metadata.modificationTime != some fixedPngTime then
          throw (IO.userError "tIME metadata was not preserved")
    | none =>
        throw (IO.userError "valid tIME fixture failed to decode")
  expectMetadataDecodeNoneBytes
    (pngWithAncillary rgbFixture (Png.mkChunkBytes Png.timeTypeBytes (ByteArray.mk #[Png.u8 1])))
    "bad tIME length"
  expectMetadataDecodeNoneBytes
    (pngWithAncillary rgbFixture
      (Png.mkChunkBytes Png.timeTypeBytes
        (ByteArray.mk #[Png.u8 0x07, Png.u8 0xea, Png.u8 13, Png.u8 1,
          Png.u8 0, Png.u8 0, Png.u8 0])))
    "bad tIME month"
  expectMetadataDecodeNoneBytes
    (pngWithAncillary rgbFixture
      (Png.mkChunkBytes Png.timeTypeBytes
        (ByteArray.mk #[Png.u8 0x07, Png.u8 0xea, Png.u8 2, Png.u8 30,
          Png.u8 0, Png.u8 0, Png.u8 0])))
    "bad tIME day"
  expectMetadataDecodeNoneBytes
    (pngWithAncillary rgbFixture
      (Png.mkChunkBytes Png.timeTypeBytes
        (ByteArray.mk #[Png.u8 0x07, Png.u8 0xea, Png.u8 5, Png.u8 2,
          Png.u8 24, Png.u8 0, Png.u8 0])))
    "bad tIME hour"
  expectMetadataDecodeNoneBytes
    (pngWithAncillary rgbFixture
      (Png.mkChunkBytes Png.timeTypeBytes
        (ByteArray.mk #[Png.u8 0x07, Png.u8 0xea, Png.u8 5, Png.u8 2,
          Png.u8 0, Png.u8 60, Png.u8 0])))
    "bad tIME minute"
  expectMetadataDecodeNoneBytes
    (pngWithAncillary rgbFixture
      (Png.mkChunkBytes Png.timeTypeBytes
        (ByteArray.mk #[Png.u8 0x07, Png.u8 0xea, Png.u8 5, Png.u8 2,
          Png.u8 0, Png.u8 0, Png.u8 61])))
    "bad tIME second"
  expectMetadataDecodeNoneBytes
    (pngWithAncillary rgbFixture (timeChunk fixedPngTime ++ timeChunk fixedPngTime))
    "duplicate tIME"
  expectMetadataDecodeNoneBytes
    (pngWithPostIdatAncillary rgbFixture
      (timeChunk fixedPngTime ++ Png.mkChunkBytes Png.idatTypeBytes ByteArray.empty))
    "IDAT after post-IDAT tIME"
  let defaultPath := System.FilePath.mk "/tmp/bitmap_time_write_default.png"
  match ← Png.Bitmap.RGB8.writePng defaultPath rgbFixture .fixed with
  | Except.error err =>
      throw (IO.userError err)
  | Except.ok _ =>
      let bytes ← IO.FS.readBinFile defaultPath
      match Png.decodeBitmapWithMetadata (px := RGB8) bytes with
      | some decoded =>
          if decoded.metadata.modificationTime.isNone then
            throw (IO.userError "file write did not emit default tIME metadata")
      | none =>
          throw (IO.userError "default tIME file write failed to decode")
  let noTimePath := System.FilePath.mk "/tmp/bitmap_time_write_without_time.png"
  match ← Png.Bitmap.writePngWithoutTime (px := RGB8) noTimePath rgbFixture .fixed with
  | Except.error err =>
      throw (IO.userError err)
  | Except.ok _ =>
      let bytes ← IO.FS.readBinFile noTimePath
      match Png.decodeBitmapWithMetadata (px := RGB8) bytes with
      | some decoded =>
          if decoded.metadata.modificationTime.isSome then
            throw (IO.userError "deterministic file write unexpectedly emitted tIME metadata")
      | none =>
          throw (IO.userError "deterministic no-time file write failed to decode")
  try
    IO.FS.removeFile defaultPath
  catch _ =>
    pure ()
  try
    IO.FS.removeFile noTimePath
  catch _ =>
    pure ()

private def expectPhysicalMetadata : IO Unit := do
  let rgbFixture : Bitmap.RGB8 :=
    Bitmap.ofFn 2 1 (fun idx : Fin (2 * 1) =>
      match idx.val with
      | 0 => { r := Png.u8 22, g := Png.u8 44, b := Png.u8 66 }
      | _ => { r := Png.u8 88, g := Png.u8 110, b := Png.u8 132 })
  match Png.encodeBitmapWithOptionsChecked (px := RGB8) rgbFixture
      { mode := .fixed
        colorSpace := some (.srgb .perceptual true)
        physical := some physical300Dpi
        modificationTime := some fixedPngTime } with
  | Except.ok bytes =>
      if bytes.extract 37 41 != Png.gamaTypeBytes then
        throw (IO.userError "encoder did not emit compatibility gAMA before sRGB")
      if bytes.extract 53 57 != Png.srgbTypeBytes then
        throw (IO.userError "encoder did not emit sRGB before pHYs")
      if bytes.extract 66 70 != Png.physTypeBytes then
        throw (IO.userError "encoder did not emit pHYs after color-space metadata")
      if bytes.extract 87 91 != Png.timeTypeBytes then
        throw (IO.userError "encoder did not emit tIME after pHYs")
      match Png.decodeBitmapWithMetadata (px := RGB8) bytes with
      | some decoded =>
          if decoded.bitmap.data != rgbFixture.data then
            throw (IO.userError "pHYs encode changed RGB samples")
          if decoded.metadata.physical != some physical300Dpi then
            throw (IO.userError "encoded pHYs metadata failed to parse")
      | none =>
          throw (IO.userError "encoded pHYs PNG failed to decode")
  | Except.error err =>
      throw (IO.userError err)
  let path := System.FilePath.mk "/tmp/bitmap_phys_write.png"
  match ← Png.Bitmap.writePngWithOptions (px := RGB8) path rgbFixture
      { mode := .fixed, physical := some physical300Dpi, modificationTime := some fixedPngTime } with
  | Except.error err =>
      throw (IO.userError err)
  | Except.ok _ =>
      let bytes ← IO.FS.readBinFile path
      match Png.decodeBitmapWithMetadata (px := RGB8) bytes with
      | some decoded =>
          if decoded.metadata.physical != some physical300Dpi then
            throw (IO.userError "file write did not preserve pHYs metadata")
      | none =>
          throw (IO.userError "pHYs file write failed to decode")
  try
    IO.FS.removeFile path
  catch _ =>
    pure ()
  let props :=
    (Bitmaps.Widget.Bitmap.RGB8.widgetProps rgbFixture).withPngMetadata
      { Png.PngMetadata.empty with physical := some physical300Dpi }
  if props.physicalXPixelsPerUnit != some physical300Dpi.xPixelsPerUnit ||
      props.physicalYPixelsPerUnit != some physical300Dpi.yPixelsPerUnit ||
      props.physicalUnitIsMeter != true then
    throw (IO.userError "widget props did not preserve meter pHYs metadata")
  let aspectOnly : Png.PngPhysicalPixelDimensions :=
    { xPixelsPerUnit := 2, yPixelsPerUnit := 1, unit := .unknown }
  let aspectProps :=
    (Bitmaps.Widget.Bitmap.RGB8.widgetProps rgbFixture).withPngMetadata
      { Png.PngMetadata.empty with physical := some aspectOnly }
  if aspectProps.physicalXPixelsPerUnit != some 2 ||
      aspectProps.physicalYPixelsPerUnit != some 1 ||
      aspectProps.physicalUnitIsMeter != false then
    throw (IO.userError "widget props did not preserve aspect-only pHYs metadata")

-- Verify the tolerate-and-skip behavior for ancillary chunks plus the
-- rejection guarantees for pixel-affecting chunks, unknown critical chunks,
-- and CRC mismatches. All fixtures live under Bitmap/Tests/.
private def pngAncillaryChunkFixtures : IO Unit := do
  -- Tolerated: tEXt comment, multiple consecutive IDATs, and an unknown ancillary
  -- chunk type ("myCh") all decode to the reference pattern.
  expectAncDecodeOk (testFixturePath "test_anc_text.png")
  expectAncDecodeOk (testFixturePath "test_anc_multi_idat.png")
  expectAncDecodeOk (testFixturePath "test_anc_unknown_anc.png")
  expectAncTrnsRgbaOk (testFixturePath "test_anc_trns.png")
  expectAncDecodeNone (testFixturePath "test_anc_trns.png") "tRNS dropped into RGB"
  expectAncBkgdRgbOk (testFixturePath "test_anc_bkgd_rgb.png")
  expectAncTrnsBkgdRgbOk (testFixturePath "test_anc_trns_bkgd.png")
  expectAncRgbaBkgdRgbOk (testFixturePath "test_anc_rgba_bkgd.png")
  expectAncBkgdGrayOk (testFixturePath "test_anc_bkgd_gray.png")
  -- Rejected: malformed or out-of-order metadata chunks, pixel-affecting chunks
  -- the decoder doesn't honor, an unknown critical chunk type ("MyCh"), and bad CRCs.
  expectAncDecodeNone (testFixturePath "test_anc_unknown_critical.png") "unknown-critical"
  expectAncMetadataDecodeNone (testFixturePath "test_anc_trns_bad_len.png") "bad tRNS length"
  expectAncMetadataDecodeNone (testFixturePath "test_anc_trns_after_idat.png") "tRNS after IDAT"
  expectAncMetadataDecodeNone (testFixturePath "test_anc_trns_duplicate.png") "duplicate tRNS"
  expectAncMetadataDecodeNone (testFixturePath "test_anc_plte_after_trns.png") "PLTE after tRNS"
  expectAncMetadataDecodeNone (testFixturePath "test_anc_trns_rgba.png") "tRNS in RGBA"
  expectAncMetadataDecodeNone (testFixturePath "test_anc_bkgd_bad_len.png") "bad bKGD length"
  expectAncMetadataDecodeNone (testFixturePath "test_anc_bkgd_after_idat.png") "bKGD after IDAT"
  expectAncMetadataDecodeNone (testFixturePath "test_anc_bkgd_duplicate.png") "duplicate bKGD"
  expectAncMetadataDecodeNone (testFixturePath "test_anc_plte_after_bkgd.png") "PLTE after bKGD"
  expectAncDecodeNone (testFixturePath "test_anc_sbit.png") "sBIT"
  expectAncDecodeNone (testFixturePath "test_anc_bad_crc.png") "bad-CRC"

-- Fill a bitmap with deterministic pixels using Bitmap.setPixel, then read all pixels back.
-- Returns elapsed time in nanoseconds and a checksum to prevent dead-code elimination.
private def perfFillRead (w h : Nat) : IO (Nat × Nat) := do
  let t0 <- IO.monoNanosNow
  let xs : Array (Fin w) := Array.finRange w
  let ys : Array (Fin h) := Array.finRange h
  let img0 := Bitmap.fill (px := RGB8) w h { r := 0, g := 0, b := 0 }
  let acc0 :
      { img : Bitmap.RGB8 // img.size.width = w ∧ img.size.height = h } :=
    ⟨img0, by rfl, by rfl⟩
  let accFilled :=
    ys.foldl (init := acc0)
      (fun (acc : { img : Bitmap.RGB8 // img.size.width = w ∧ img.size.height = h }) (y : Fin h) =>
        xs.foldl (init := acc)
          (fun (acc : { img : Bitmap.RGB8 // img.size.width = w ∧ img.size.height = h }) (x : Fin w) =>
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
            let img' := Bitmap.setPixel img x.val y.val { r := r, g := g, b := b } hx hy
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
      let px := Bitmap.getPixel img x.val y.val hx hy
      checksum := checksum + px.r.toNat + px.g.toNat + px.b.toNat
  let t1 <- IO.monoNanosNow
  return (t1 - t0, checksum)

private def perfContentByte (x y channel : Nat) : UInt8 :=
  let tileX := x / 16
  let tileY := y / 8
  let blockValue := (tileX * 37 + tileY * 19 + (x / 256) * 11 + (y / 128) * 7) % 256
  if x % 64 < 48 then
    Png.u8 blockValue
  else
    Png.u8 <|
      match channel with
      | 0 => (x * 17 + y * 5 + blockValue) % 256
      | 1 => (x * 3 + y * 29 + blockValue * 2) % 256
      | _ => (x * 11 + y * 13 + blockValue * 3) % 256

private def perfContentBitmap (w h : Nat) : Bitmap.RGB8 :=
  let bpp := RGB8.bytesPerPixel
  let data := ByteArray.mk <| Array.ofFn (fun i : Fin (w * h * bpp) =>
    let pixel := i.val / bpp
    let channel := i.val % bpp
    let x := pixel % w
    let y := pixel / w
    perfContentByte x y channel)
  have hvalid : data.size = w * h * PixelFormat.bytesPerPixel (α := RGB8) := by
    have hsize : data.size = w * h * bpp := by
      simp [data, ByteArray.size]
    have hbpp : PixelFormat.bytesPerPixel (α := RGB8) = bpp := by
      change RGB8.bytesPerPixel = bpp
      rfl
    rw [hbpp]
    exact hsize
  { size := { width := w, height := h }, data, valid := hvalid }

private def expectParallelScheduling : IO Unit := do
  let options : Png.PngParallelOptions :=
    { maxShards := 8, minRowsPerShard := 2, targetBytesPerShard := 100 }
  if options.shardCountForWork 16 1600 != 8 then
    throw (IO.userError "parallel scheduler did not cap at maxShards")
  if options.shardCountForWork 1 1 != 1 then
    throw (IO.userError "parallel scheduler did not keep tiny work sequential")
  let ranges := Png.rowShardRanges options 16 9
  if ranges.length != 8 then
    throw (IO.userError "parallel scheduler row shard count mismatch")
  let covered := ranges.foldl (fun acc shard => acc + shard.size) 0
  if covered != 16 then
    throw (IO.userError "parallel scheduler row shard coverage mismatch")
  let shardSizes := Png.mapShardsParallel ranges (fun shard => shard.size)
  if shardSizes.foldl (· + ·) 0 != 16 then
    throw (IO.userError "parallel shard task result ordering/coverage mismatch")

private def expectParallelApiEquality : IO Unit := do
  let parallel : Png.PngParallelOptions :=
    { maxShards := 32, minRowsPerShard := 1, targetBytesPerShard := 1 }
  let storedRaw := Png.PixelFormat.encodeRaw (α := RGB8) (perfContentBitmap 257 257)
  let manyBlockStoredRaw :=
    repeatByteArray (Png.uint16MaxValue * 130 + 123) (Png.u8 77)
  for maxShards in [1, 2, 4, 8, 16] do
    let storedParallel : Png.PngParallelOptions :=
      { maxShards := maxShards, minRowsPerShard := 1, targetBytesPerShard := 1 }
    if Png.deflateStoredParallel storedRaw storedParallel != Png.deflateStored storedRaw then
      throw (IO.userError s!"parallel stored deflate block mismatch for maxShards {maxShards}")
    if Png.deflateStoredGroupedParallel manyBlockStoredRaw storedParallel !=
        Png.deflateStored manyBlockStoredRaw then
      throw (IO.userError s!"grouped stored deflate block mismatch for maxShards {maxShards}")
    if Png.zlibCompressStoredParallel storedRaw storedParallel != Png.zlibCompressStored storedRaw then
      throw (IO.userError s!"parallel stored zlib block mismatch for maxShards {maxShards}")
    if Png.zlibCompressStoredGroupedParallel manyBlockStoredRaw storedParallel !=
        Png.zlibCompressStored manyBlockStoredRaw then
      throw (IO.userError s!"grouped stored zlib block mismatch for maxShards {maxShards}")
    let storedZlib := Png.zlibCompressStored storedRaw
    let storedSeqDecoded :=
      if hsize : 2 <= storedZlib.size then
        Png.zlibDecompressStored storedZlib hsize
      else
        none
    let storedParDecoded :=
      if hsize : 2 <= storedZlib.size then
        Png.zlibDecompressStoredParallel storedZlib hsize storedParallel
      else
        none
    if storedParDecoded != storedSeqDecoded then
      throw (IO.userError s!"parallel stored zlib decode mismatch for maxShards {maxShards}")
    if storedParDecoded != some storedRaw then
      throw (IO.userError s!"parallel stored zlib decode payload mismatch for maxShards {maxShards}")
    let manyBlockStoredZlib := Png.zlibCompressStored manyBlockStoredRaw
    let manyBlockSeqDecoded :=
      if hsize : 2 <= manyBlockStoredZlib.size then
        Png.zlibDecompressStored manyBlockStoredZlib hsize
      else
        none
    let manyBlockScannedDecoded :=
      if hsize : 2 <= manyBlockStoredZlib.size then
        Png.zlibDecompressStoredScannedParallel manyBlockStoredZlib hsize storedParallel
      else
        none
    if manyBlockScannedDecoded != manyBlockSeqDecoded then
      throw (IO.userError s!"scanned stored zlib decode mismatch for maxShards {maxShards}")
    if manyBlockScannedDecoded != some manyBlockStoredRaw then
      throw (IO.userError s!"scanned stored zlib decode payload mismatch for maxShards {maxShards}")
    let segmentedFixed := Png.zlibCompressFixedSegmentedParallel storedRaw storedParallel
    if maxShards == 1 && segmentedFixed != Png.zlibCompressFixed storedRaw then
      throw (IO.userError "segmented fixed one-shard zlib did not match sequential fixed zlib")
    match zlibDecompressFixture segmentedFixed with
    | some raw' =>
        if raw' != storedRaw then
          throw (IO.userError s!"segmented fixed zlib decompressed to the wrong raw payload for maxShards {maxShards}")
    | none =>
        throw (IO.userError s!"segmented fixed zlib failed to decompress for maxShards {maxShards}")

  let rgbBmp := filterRGB8Fixture
  for mode in [Png.PngEncodeMode.stored, .fixed, .dynamic] do
    match Png.encodeBitmapChecked (px := RGB8) rgbBmp mode,
        Png.encodeBitmapCheckedParallel (px := RGB8) rgbBmp mode parallel with
    | Except.ok seq, Except.ok par =>
        if seq != par then
          throw (IO.userError "parallel RGB checked encode mismatch")
        match Png.decodeBitmap (px := RGB8) seq,
            Png.decodeBitmapParallel (px := RGB8) seq parallel with
        | some seqBmp, some parBmp =>
            if seqBmp != parBmp then
              throw (IO.userError "parallel RGB decode mismatch")
        | _, _ =>
            throw (IO.userError "parallel RGB decode success mismatch")
    | Except.error seqErr, Except.error parErr =>
        if seqErr != parErr then
          throw (IO.userError "parallel RGB checked encode error mismatch")
    | _, _ =>
        throw (IO.userError "parallel RGB checked encode shape mismatch")

  for maxShards in [1, 2, 4, 8, 16, 32, 64, 128] do
    let segmentedParallel : Png.PngParallelOptions :=
      { maxShards := maxShards, minRowsPerShard := 1, targetBytesPerShard := 1 }
    match Png.encodeBitmapFixedSegmentedCheckedParallel (px := RGB8) rgbBmp segmentedParallel with
    | Except.ok bytes =>
        match Png.decodeBitmapParallel (px := RGB8) bytes segmentedParallel with
        | some decoded =>
            if decoded != rgbBmp then
              throw (IO.userError s!"segmented fixed parallel RGB round-trip mismatch for maxShards {maxShards}")
        | none =>
            throw (IO.userError s!"segmented fixed parallel RGB decode failed for maxShards {maxShards}")
    | Except.error err =>
        throw (IO.userError s!"segmented fixed parallel RGB encode failed: {err}")

  let optionConfig : Png.PngEncodeOptions :=
    { mode := .fixed, filter := .adaptive, colorSpace := some (.srgb .perceptual false) }
  match Png.encodeBitmapWithOptionsChecked (px := RGB8) adaptiveNonzeroFixture optionConfig,
      Png.encodeBitmapWithOptionsCheckedParallel (px := RGB8) adaptiveNonzeroFixture
        optionConfig parallel with
  | Except.ok seq, Except.ok par =>
      if seq != par then
        throw (IO.userError "parallel RGB option encode mismatch")
      match Png.decodeBitmapWithMetadata (px := RGB8) seq,
          Png.decodeBitmapWithMetadataParallel (px := RGB8) seq parallel with
      | some seqDecoded, some parDecoded =>
          if seqDecoded.bitmap != parDecoded.bitmap ||
              seqDecoded.metadata.srgb != parDecoded.metadata.srgb then
            throw (IO.userError "parallel RGB metadata decode mismatch")
      | _, _ =>
          throw (IO.userError "parallel RGB metadata decode success mismatch")
  | Except.error seqErr, Except.error parErr =>
      if seqErr != parErr then
        throw (IO.userError "parallel RGB option encode error mismatch")
  | _, _ =>
      throw (IO.userError "parallel RGB option encode shape mismatch")

  let gray1Bmp := gray1FixtureBitmap 17 4
  match Png.encodeGray1BitmapChecked gray1Bmp .fixed,
      Png.encodeGray1BitmapCheckedParallel gray1Bmp .fixed parallel with
  | Except.ok seq, Except.ok par =>
      if seq != par then
        throw (IO.userError "parallel Gray1 checked encode mismatch")
      match Png.decodeGray1Bitmap seq, Png.decodeGray1BitmapParallel seq parallel with
      | some seqBmp, some parBmp =>
          if seqBmp != parBmp then
            throw (IO.userError "parallel Gray1 decode mismatch")
      | _, _ =>
          throw (IO.userError "parallel Gray1 decode success mismatch")
  | Except.error seqErr, Except.error parErr =>
      if seqErr != parErr then
        throw (IO.userError "parallel Gray1 checked encode error mismatch")
  | _, _ =>
      throw (IO.userError "parallel Gray1 checked encode shape mismatch")

  let indexedBmp := indexedFixtureBitmap 9 5 4 12
  match Png.encodeIndexedBitmapChecked indexedBmp .fixed,
      Png.encodeIndexedBitmapCheckedParallel indexedBmp .fixed parallel with
  | Except.ok seq, Except.ok par =>
      if seq != par then
        throw (IO.userError "parallel indexed checked encode mismatch")
      match Png.decodeIndexedBitmap seq, Png.decodeIndexedBitmapParallel seq parallel with
      | some seqBmp, some parBmp =>
          if seqBmp.data != parBmp.data || seqBmp.palette != parBmp.palette then
            throw (IO.userError "parallel indexed decode mismatch")
      | _, _ =>
          throw (IO.userError "parallel indexed decode success mismatch")
      match Png.decodeIndexedBitmapWithMetadata seq,
          Png.decodeIndexedBitmapWithMetadataParallel seq parallel with
      | some seqDecoded, some parDecoded =>
          if seqDecoded.bitmap.data != parDecoded.bitmap.data ||
              seqDecoded.metadata.palette != parDecoded.metadata.palette then
            throw (IO.userError "parallel indexed metadata decode mismatch")
      | _, _ =>
          throw (IO.userError "parallel indexed metadata decode success mismatch")
  | Except.error seqErr, Except.error parErr =>
      if seqErr != parErr then
        throw (IO.userError "parallel indexed checked encode error mismatch")
  | _, _ =>
      throw (IO.userError "parallel indexed checked encode shape mismatch")

private def measurePngStage (label : String) (iters : Nat) (act : IO Nat) : IO Nat := do
  let hb0 <- IO.getNumHeartbeats
  let mut totalNs : Nat := 0
  let mut checksum : Nat := 0
  for _ in [0:iters] do
    let t0 <- IO.monoNanosNow
    let value <- act
    let t1 <- IO.monoNanosNow
    totalNs := totalNs + (t1 - t0)
    checksum := checksum + value
  let hb1 <- IO.getNumHeartbeats
  let avgNs := totalNs / iters
  IO.println s!"perf png stage {label}: avg {avgNs} ns ({avgNs / 1_000} us) over {iters} runs, checksum {checksum}, heartbeats {hb1 - hb0}"
  return avgNs

private structure PngStageInput where
  bmp : Bitmap.RGB8
  rawNone : ByteArray
  rawAdaptive : ByteArray
  gray1Bmp : Bitmap.Gray1
  indexedBmp : Png.PngIndexedBitmap
  stored : ByteArray
  fixed : ByteArray
  dynamic : ByteArray
  fixedBytes : ByteArray
  colorBytes : ByteArray

private def makePngStageInput (w h salt : Nat) : IO PngStageInput := do
  let bmp := perfContentBitmap w h
  let rawNone := Png.PixelFormat.encodeRaw (α := RGB8) bmp
  let rawAdaptive := Png.encodeRawWithFilter bmp .adaptive
  let gray1Bmp := gray1FixtureBitmap (193 + salt) (17 + (salt % 3))
  let indexedBmp := indexedFixtureBitmap (65 + salt) (17 + (salt % 2)) 4 12
  let stored := Png.zlibCompressStored rawNone
  let fixed := Png.zlibCompressFixed rawNone
  let dynamic := Png.zlibCompressDynamic rawNone
  let fixedBytes ←
    match Png.encodeBitmapChecked (px := RGB8) bmp .fixed with
    | Except.ok bytes => pure bytes
    | Except.error err => throw (IO.userError s!"png stage fixed encode failed: {err}")
  let colorBytes ←
    match Png.encodeBitmapWithOptionsChecked (px := RGB8) bmp
        { mode := .fixed, colorSpace := some (.srgb .perceptual false) } with
    | Except.ok bytes => pure bytes
    | Except.error err => throw (IO.userError s!"png stage color encode failed: {err}")
  pure
    { bmp
      rawNone
      rawAdaptive
      gray1Bmp
      indexedBmp
      stored
      fixed
      dynamic
      fixedBytes
      colorBytes }

private def measurePngStageInputs (label : String) (iters : Nat)
    (inputs : Array PngStageInput) (act : PngStageInput → IO Nat) : IO Nat := do
  if hsize : inputs.size = 0 then
    throw (IO.userError "png stage perf input set is empty")
  else
    let hpos : 0 < inputs.size := Nat.pos_of_ne_zero hsize
    let iterRef ← IO.mkRef 0
    measurePngStage label iters <| do
      let i ← iterRef.get
      iterRef.set (i + 1)
      let hidx : i % inputs.size < inputs.size := Nat.mod_lt i hpos
      act inputs[i % inputs.size]

private def byteArrayChecksum (bytes : ByteArray) : Nat :=
  Id.run do
    let mut checksum := bytes.size
    for i in [0:bytes.size] do
      checksum := checksum + (bytes.get! i).toNat
    return checksum

private def formatRatioTimes100 (ratioTimes100 : Nat) : String :=
  let whole := ratioTimes100 / 100
  let frac := ratioTimes100 % 100
  let fracStr := if frac < 10 then s!"0{frac}" else s!"{frac}"
  s!"{whole}.{fracStr}"

private def perfPngStageResolution : Nat := 192

private def perfPngStageIters : Nat := 5

private def runPngStagePerfTest : IO Unit := do
  let w := perfPngStageResolution
  let h := perfPngStageResolution
  let iters := perfPngStageIters
  let storedParallelOptions : Png.PngParallelOptions :=
    { maxShards := 16, minRowsPerShard := 1, targetBytesPerShard := 1 }
  let input0 ← makePngStageInput w h 0
  let input1 ← makePngStageInput (w + 1) h 1
  let input2 ← makePngStageInput w (h + 1) 2
  let input3 ← makePngStageInput (w + 2) (h - 1) 3
  let input4 ← makePngStageInput (w - 1) (h + 2) 4
  let inputs := #[input0, input1, input2, input3, input4]
  let _ ← measurePngStageInputs "row encode filter none" iters inputs <| fun input => do
    pure (byteArrayChecksum (Png.PixelFormat.encodeRaw (α := RGB8) input.bmp))
  let _ ← measurePngStageInputs "row encode adaptive" iters inputs <| fun input => do
    pure (byteArrayChecksum (Png.encodeRawWithFilter input.bmp .adaptive))
  let _ ← measurePngStageInputs "Gray1 row packing adaptive" iters inputs <| fun input => do
    pure (byteArrayChecksum (Png.encodeRawGray1WithFilter input.gray1Bmp .adaptive))
  let _ ← measurePngStageInputs "indexed row packing adaptive" iters inputs <| fun input => do
    pure (byteArrayChecksum (Png.encodeRawIndexedWithFilter input.indexedBmp .adaptive))
  let _ ← measurePngStageInputs "zlib compress stored" iters inputs <| fun input => do
    pure (byteArrayChecksum (Png.zlibCompressStored input.rawNone))
  let _ ← measurePngStageInputs "zlib compress stored parallel blocks" iters inputs <| fun input => do
    pure (byteArrayChecksum (Png.zlibCompressStoredParallel input.rawNone storedParallelOptions))
  let _ ← measurePngStageInputs "zlib compress stored grouped parallel" iters inputs <| fun input => do
    pure (byteArrayChecksum
      (Png.zlibCompressStoredGroupedParallel input.rawNone storedParallelOptions))
  let _ ← measurePngStageInputs "zlib compress fixed" iters inputs <| fun input => do
    pure (byteArrayChecksum (Png.zlibCompressFixed input.rawNone))
  let _ ← measurePngStageInputs "zlib compress fixed segmented parallel" iters inputs <| fun input => do
    pure (byteArrayChecksum
      (Png.zlibCompressFixedSegmentedParallel input.rawNone storedParallelOptions))
  let _ ← measurePngStageInputs "zlib compress dynamic" iters inputs <| fun input => do
    pure (byteArrayChecksum (Png.zlibCompressDynamic input.rawNone))
  let _ ← measurePngStageInputs "zlib decompress stored" iters inputs <| fun input => do
    match if hsize : 2 <= input.stored.size then Png.zlibDecompressStored input.stored hsize else none with
    | some raw => pure (byteArrayChecksum raw)
    | none => throw (IO.userError "stored zlib stage failed")
  let _ ← measurePngStageInputs "zlib decompress stored parallel" iters inputs <| fun input => do
    match if hsize : 2 <= input.stored.size then
        Png.zlibDecompressStoredParallel input.stored hsize storedParallelOptions
      else none with
    | some raw => pure (byteArrayChecksum raw)
    | none => throw (IO.userError "stored parallel zlib stage failed")
  let _ ← measurePngStageInputs "zlib decompress stored scanned parallel" iters inputs <| fun input => do
    match if hsize : 2 <= input.stored.size then
        Png.zlibDecompressStoredScannedParallel input.stored hsize storedParallelOptions
      else none with
    | some raw => pure (byteArrayChecksum raw)
    | none => throw (IO.userError "stored scanned parallel zlib stage failed")
  let _ ← measurePngStageInputs "zlib decompress fixed" iters inputs <| fun input => do
    match if hsize : 2 <= input.fixed.size then Png.zlibDecompress input.fixed hsize else none with
    | some raw => pure (byteArrayChecksum raw)
    | none => throw (IO.userError "fixed zlib stage failed")
  let _ ← measurePngStageInputs "zlib decompress dynamic" iters inputs <| fun input => do
    match if hsize : 2 <= input.dynamic.size then Png.zlibDecompress input.dynamic hsize else none with
    | some raw => pure (byteArrayChecksum raw)
    | none => throw (IO.userError "dynamic zlib stage failed")
  let _ ← measurePngStageInputs "chunk CRC construction" iters inputs <| fun input => do
    pure (byteArrayChecksum (Png.mkChunkBytes Png.idatTypeBytes input.fixed))
  let _ ← measurePngStageInputs "PNG parse" iters inputs <| fun input => do
    match if hsize : 8 <= input.fixedBytes.size then Png.parsePngForDecode input.fixedBytes hsize else none with
    | some parsed => pure (byteArrayChecksum parsed.idat)
    | none => throw (IO.userError "PNG parse stage failed")
  let _ ← measurePngStageInputs "unfilter and pixel decode" iters inputs <| fun input => do
    match Png.decodeBitmap (px := RGB8) input.fixedBytes with
    | some decoded => pure (byteArrayChecksum decoded.data)
    | none => throw (IO.userError "PNG decode stage failed")
  let _ ← measurePngStageInputs "metadata color-space decode" iters inputs <| fun input => do
    match Png.decodeBitmapWithMetadata (px := RGB8) input.colorBytes with
    | some decoded => pure (byteArrayChecksum decoded.bitmap.data)
    | none => throw (IO.userError "PNG color-space decode stage failed")
  if input0.rawAdaptive.size == 0 then
    throw (IO.userError "adaptive raw stage unexpectedly empty")

-- Keep this large enough that the shard sweep measures real round-trip work.
-- The sweep below requires at least 20 seconds total so shard settings are
-- measured on a workload large enough to show meaningful timing differences.
private def perfPngParallelResolution : Nat := 512

private def perfPngParallelIters : Nat := 5

private def perfPngParallelMinTotalNs : Nat := 20_000_000_000

private def perfPngRoundTripParallel (w h : Nat) (maxShards : Nat) : IO (Nat × Bool) := do
  let parallel : Png.PngParallelOptions :=
    { maxShards := maxShards, minRowsPerShard := 1, targetBytesPerShard := 1 }
  let t0 <- IO.monoNanosNow
  let bmp := perfContentBitmap w h
  let bytes ←
    match Png.encodeBitmapCheckedParallel (px := RGB8) bmp .fixed parallel with
    | Except.ok bytes => pure bytes
    | Except.error err => throw (IO.userError s!"png parallel perf encode failed: {err}")
  match Png.decodeBitmapParallel (px := RGB8) bytes parallel with
  | some bmp' =>
      if bmp' != bmp then
        throw (IO.userError "png parallel perf exact bitmap mismatch")
  | none =>
      throw (IO.userError "png parallel perf decode failed")
  let t1 <- IO.monoNanosNow
  return (t1 - t0, true)

private def perfPngRoundTripFixedSegmentedParallel
    (w h : Nat) (maxShards : Nat) : IO (Nat × Bool) := do
  let parallel : Png.PngParallelOptions :=
    { maxShards := maxShards, minRowsPerShard := 1, targetBytesPerShard := 1 }
  let t0 <- IO.monoNanosNow
  let bmp := perfContentBitmap w h
  let bytes ←
    match Png.encodeBitmapFixedSegmentedCheckedParallel (px := RGB8) bmp parallel with
    | Except.ok bytes => pure bytes
    | Except.error err =>
        throw (IO.userError s!"png segmented fixed parallel perf encode failed: {err}")
  match Png.decodeBitmapParallel (px := RGB8) bytes parallel with
  | some bmp' =>
      if bmp' != bmp then
        throw (IO.userError "png segmented fixed parallel perf exact bitmap mismatch")
  | none =>
      throw (IO.userError "png segmented fixed parallel perf decode failed")
  let t1 <- IO.monoNanosNow
  return (t1 - t0, true)

private def runPngParallelPerfTest : IO Unit := do
  let w := perfPngParallelResolution
  let h := perfPngParallelResolution
  let iters := perfPngParallelIters
  let mut sweepTotalNs : Nat := 0
  for maxShards in [1, 2, 4, 8, 16, 32, 64, 128] do
    let hb0 <- IO.getNumHeartbeats
    let mut totalNs : Nat := 0
    for _ in [0:iters] do
      let (elapsedNs, ok) <- perfPngRoundTripParallel w h maxShards
      if !ok then
        throw (IO.userError "png parallel perf round-trip failed")
      totalNs := totalNs + elapsedNs
    let hb1 <- IO.getNumHeartbeats
    let avgNs := totalNs / iters
    sweepTotalNs := sweepTotalNs + totalNs
    IO.println s!"perf png parallel round-trip: {w}x{h}, maxShards {maxShards}, avg {avgNs / 1_000_000} ms over {iters} runs, heartbeats {hb1 - hb0}"
  IO.println s!"perf png parallel round-trip sweep total: {sweepTotalNs / 1_000_000} ms"
  if sweepTotalNs < perfPngParallelMinTotalNs then
    throw (IO.userError
      s!"png parallel round-trip sweep too small: total {sweepTotalNs / 1_000_000} ms is below 20000 ms")
  for maxShards in [1, 2, 4, 8, 16, 32, 64, 128] do
    let hb0 <- IO.getNumHeartbeats
    let mut totalNs : Nat := 0
    for _ in [0:iters] do
      let (elapsedNs, ok) <- perfPngRoundTripFixedSegmentedParallel w h maxShards
      if !ok then
        throw (IO.userError "png segmented fixed parallel perf round-trip failed")
      totalNs := totalNs + elapsedNs
    let hb1 <- IO.getNumHeartbeats
    let avgNs := totalNs / iters
    IO.println s!"perf png segmented fixed parallel round-trip: {w}x{h}, maxShards {maxShards}, avg {avgNs / 1_000_000} ms over {iters} runs, heartbeats {hb1 - hb0}"

-- Encode a deterministic content bitmap to PNG and decode it back.
-- Returns elapsed time in nanoseconds and whether the round-trip was exact.
private def perfPngRoundTrip (w h : Nat) : IO (Nat × Bool) := do
  let t0 <- IO.monoNanosNow
  let bmp := perfContentBitmap w h
  let bytes ←
    match Png.encodeBitmapChecked (px := RGB8) bmp .fixed with
    | Except.ok bytes => pure bytes
    | Except.error err => throw (IO.userError s!"png perf round-trip encode failed: {err}")
  match Png.decodeBitmap (px := RGB8) bytes with
  | some bmp' =>
      if bmp' != bmp then
        throw (IO.userError "png perf round-trip exact bitmap mismatch")
  | none =>
      throw (IO.userError "png perf round-trip decode failed")
  let t1 <- IO.monoNanosNow
  return (t1 - t0, true)

-- Encode a deterministic content bitmap using dynamic deflate blocks and decode it back.
-- Returns elapsed time in nanoseconds and whether the round-trip was exact.
private def perfPngRoundTripDynamic (w h : Nat) : IO (Nat × Bool) := do
  let t0 <- IO.monoNanosNow
  let bmp := perfContentBitmap w h
  let bytes ←
    match Png.encodeBitmapChecked (px := RGB8) bmp .dynamic with
    | Except.ok bytes => pure bytes
    | Except.error err => throw (IO.userError s!"png perf dynamic round-trip encode failed: {err}")
  match Png.decodeBitmap (px := RGB8) bytes with
  | some bmp' =>
      if bmp' != bmp then
        throw (IO.userError "png perf dynamic round-trip exact bitmap mismatch")
  | none =>
      throw (IO.userError "png perf dynamic round-trip decode failed")
  let t1 <- IO.monoNanosNow
  return (t1 - t0, true)

-- Encode a deterministic content bitmap using stored deflate blocks and decode it back.
-- Returns elapsed time in nanoseconds and whether the round-trip was exact.
private def perfPngRoundTripStored (w h : Nat) : IO (Nat × Bool) := do
  let t0 <- IO.monoNanosNow
  let bmp := perfContentBitmap w h
  let bytes ←
    match Png.encodeBitmapChecked (px := RGB8) bmp .stored with
    | Except.ok bytes => pure bytes
    | Except.error err => throw (IO.userError s!"png perf stored round-trip encode failed: {err}")
  match Png.decodeBitmap (px := RGB8) bytes with
  | some bmp' =>
      if bmp' != bmp then
        throw (IO.userError "png perf stored round-trip exact bitmap mismatch")
  | none =>
      throw (IO.userError "png perf stored round-trip decode failed")
  let t1 <- IO.monoNanosNow
  return (t1 - t0, true)

-- Encode using the public stored-mode parallel path and decode it back.
-- Returns elapsed time in nanoseconds and whether the round-trip was exact.
private def perfPngRoundTripStoredParallel
    (w h maxShards : Nat) : IO (Nat × Bool) := do
  let parallel : Png.PngParallelOptions :=
    { maxShards := maxShards, minRowsPerShard := 1, targetBytesPerShard := 1 }
  let t0 <- IO.monoNanosNow
  let bmp := perfContentBitmap w h
  let bytes ←
    match Png.encodeBitmapCheckedParallel (px := RGB8) bmp .stored parallel with
    | Except.ok bytes => pure bytes
    | Except.error err =>
        throw (IO.userError s!"png perf stored parallel round-trip encode failed: {err}")
  match Png.decodeBitmapParallel (px := RGB8) bytes parallel with
  | some bmp' =>
      if bmp' != bmp then
        throw (IO.userError "png perf stored parallel round-trip exact bitmap mismatch")
  | none =>
      throw (IO.userError "png perf stored parallel round-trip decode failed")
  let t1 <- IO.monoNanosNow
  return (t1 - t0, true)

-- Fixed-size performance test for Bitmap.setPixel/Bitmap.getPixel on this machine.
private def perfResolution : Nat := 3200

private def perfIters : Nat := 10

-- PNG round-trips run the full public encode/decode path. Keep the input
-- large enough that stored deflate emits more than one block, but small enough
-- that generic dynamic-Huffman decoding does not dominate the whole test suite.
private def perfPngResolution : Nat := 512

-- Stored-mode parallel round-trips are much faster than fixed/dynamic
-- compression, so use a larger fixture to keep each shard-setting sample stable.
private def perfPngStoredParallelResolution : Nat := 1664

private def perfPngStoredParallelMinTotalNs : Nat := 1_000_000_000

private def perfPngIters : Nat := 5

private def perfStoredZlibLargeBlocks : Nat := 1024

private def perfDynamicRatioLimit : Nat := 8

-- Fixed-size performance test for Bitmap.setPixel/Bitmap.getPixel on this machine.
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
private def runPngPerfTest : IO Nat := do
  let w : Nat := perfPngResolution
  let h : Nat := perfPngResolution
  let iters : Nat := perfPngIters
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
  return avgNs

-- Fixed-size performance test for PNG encode/decode via dynamic blocks.
private def runPngPerfTestDynamic (fixedAvgNs : Nat) : IO Nat := do
  let w : Nat := perfPngResolution
  let h : Nat := perfPngResolution
  let iters : Nat := perfPngIters
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
  let ratioTimes100 := if fixedAvgNs == 0 then 0 else (avgNs * 100) / fixedAvgNs
  IO.println s!"perf png dynamic round-trip: {w}x{h} pixels, avg {avgMs} ms over {iters} runs, ratio {formatRatioTimes100 ratioTimes100}x fixed, heartbeats {hb1 - hb0}"
  if avgNs > fixedAvgNs * perfDynamicRatioLimit then
    throw (IO.userError
      s!"png perf dynamic round-trip too slow: avg {avgMs} ms exceeds {perfDynamicRatioLimit}x fixed")
  return avgNs

-- Fixed-size performance test for PNG encode/decode via stored blocks.
private def runPngPerfTestStored : IO Unit := do
  let w : Nat := perfPngResolution
  let h : Nat := perfPngResolution
  let iters : Nat := perfPngIters
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

-- Fixed-size performance test for PNG encode/decode via stored parallel blocks.
private def runPngPerfTestStoredParallel : IO Unit := do
  let w : Nat := perfPngStoredParallelResolution
  let h : Nat := perfPngStoredParallelResolution
  let iters : Nat := perfPngIters
  for maxShards in [1, 16, 128] do
    let hb0 <- IO.getNumHeartbeats
    let mut totalNs : Nat := 0
    for _ in [0:iters] do
      let (elapsedNs, ok) <- perfPngRoundTripStoredParallel w h maxShards
      if !ok then
        throw (IO.userError "png perf stored parallel round-trip failed")
      totalNs := totalNs + elapsedNs
    let hb1 <- IO.getNumHeartbeats
    let avgNs := totalNs / iters
    let avgMs := avgNs / 1_000_000
    let totalMs := totalNs / 1_000_000
    IO.println s!"perf png stored parallel round-trip: {w}x{h}, maxShards {maxShards}, avg {avgMs} ms over {iters} runs, total {totalMs} ms, heartbeats {hb1 - hb0}"
    if totalNs < perfPngStoredParallelMinTotalNs then
      throw (IO.userError
        s!"png perf stored parallel round-trip sample too small for maxShards {maxShards}: total {totalMs} ms is below 1000 ms")

private def measureStoredZlibLarge
    (label : String) (iters : Nat) (act : Unit → IO ByteArray) : IO Nat := do
  let hb0 <- IO.getNumHeartbeats
  let mut totalNs : Nat := 0
  let mut checksum : Nat := 0
  for _ in [0:iters] do
    let t0 <- IO.monoNanosNow
    let bytes ← act ()
    let t1 <- IO.monoNanosNow
    totalNs := totalNs + (t1 - t0)
    checksum := checksum + byteArrayChecksum bytes
  let hb1 <- IO.getNumHeartbeats
  let avgNs := totalNs / iters
  IO.println s!"perf png stored zlib large {label}: avg {avgNs / 1_000_000} ms ({avgNs / 1_000} us) over {iters} runs, total {totalNs / 1_000_000} ms, checksum {checksum}, heartbeats {hb1 - hb0}"
  return avgNs

-- Large stored-zlib performance test for the grouped block encoder and scanned
-- payload decoder. The payload intentionally exceeds 128 stored blocks, which
-- is where the proof-backed public stored encoder keeps its conservative
-- fallback and this explicit grouped API continues to shard work.
private def runStoredZlibLargeParallelPerfTest : IO Unit := do
  let iters : Nat := perfPngIters
  let rawSize := Png.uint16MaxValue * perfStoredZlibLargeBlocks + 123
  let raw := repeatByteArray rawSize (Png.u8 91)
  let parallel : Png.PngParallelOptions :=
    { maxShards := 128, minRowsPerShard := 1, targetBytesPerShard := 1 }
  let seqAvg ← measureStoredZlibLarge "compress sequential" iters <| fun _ => do
    pure (Png.zlibCompressStored raw)
  let groupedAvg ← measureStoredZlibLarge "compress grouped parallel" iters <| fun _ => do
    pure (Png.zlibCompressStoredGroupedParallel raw parallel)
  let stored := Png.zlibCompressStored raw
  let decSeqAvg ← measureStoredZlibLarge "decode sequential" iters <| fun _ => do
    match if hsize : 2 <= stored.size then Png.zlibDecompressStored stored hsize else none with
    | some decoded => pure decoded
    | none => throw (IO.userError "large stored zlib sequential decode failed")
  let decScannedAvg ← measureStoredZlibLarge "decode scanned parallel" iters <| fun _ => do
    match if hsize : 2 <= stored.size then
        Png.zlibDecompressStoredScannedParallel stored hsize parallel
      else none with
    | some decoded => pure decoded
    | none => throw (IO.userError "large stored zlib scanned decode failed")
  let grouped := Png.zlibCompressStoredGroupedParallel raw parallel
  if grouped != stored then
    throw (IO.userError "large grouped stored zlib bytes changed")
  match if hsize : 2 <= stored.size then
      Png.zlibDecompressStoredScannedParallel stored hsize parallel
    else none with
  | some decoded =>
      if decoded != raw then
        throw (IO.userError "large scanned stored zlib decoded bytes changed")
  | none => throw (IO.userError "large scanned stored zlib final decode failed")
  let compressRatioTimes100 := if seqAvg == 0 then 0 else (groupedAvg * 100) / seqAvg
  let decodeRatioTimes100 := if decSeqAvg == 0 then 0 else (decScannedAvg * 100) / decSeqAvg
  IO.println s!"perf png stored zlib large ratios: grouped/sequential compress {formatRatioTimes100 compressRatioTimes100}x, scanned/sequential decode {formatRatioTimes100 decodeRatioTimes100}x"

def run : IO Unit := do
  pngDecodeFixedHuffmanFixtures
  expectGrayAlphaFixtures
  IO.println "png gray+alpha fixtures: ok"
  expect16To8Downsample
  IO.println "png 16-to-8 downsample fixtures: ok"
  expect16BitMetadata
  IO.println "png 16-bit metadata fixtures: ok"
  expectAdam7Fixtures
  IO.println "png Adam7 fixtures: ok"
  expectGray1Fixtures
  IO.println "png Gray1 fixtures: ok"
  expectPalettePng
  IO.println "png palette fixtures: ok"
  expectPngEncodeFilters
  IO.println "png encoder filter fixtures: ok"
  expectParallelScheduling
  IO.println "png parallel scheduler: ok"
  expectParallelApiEquality
  IO.println "png parallel API equality: ok"
  expectColorSpaceChunks
  IO.println "png sRGB/gAMA/cHRM fixtures: ok"
  expectTimeChunks
  IO.println "png tIME fixtures: ok"
  expectPhysicalMetadata
  IO.println "png pHYs fixtures: ok"
  pngAncillaryChunkFixtures
  IO.println "png ancillary-chunk fixtures: ok"
  validateDynamicTableValidationBoundary
  validateGeneratedDynamicEncoder
  validateDeflateDistanceInfo
  validateLz77Tokenizer
  validateLz77PublicRoundTrips
  validateDynamicZlibFixtures
  validateMalformedDynamicFixtures
  validateCopyDistanceFast
  runPerfTest
  runPngStagePerfTest
  let fixedAvgNs <- runPngPerfTest
  let _dynamicAvgNs <- runPngPerfTestDynamic fixedAvgNs
  runPngPerfTestStored
  runPngPerfTestStoredParallel
  runStoredZlibLargeParallelPerfTest
  runPngParallelPerfTest

end Bitmap.Tests

def main : IO Unit :=
  Bitmap.Tests.run
