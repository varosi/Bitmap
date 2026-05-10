import Bitmap.Png

namespace Bitmaps

namespace Lemmas

open Png

/-- `readChunk` cannot accept a chunk whose stored CRC differs from the
computed CRC over the parsed type and payload bytes. -/
lemma readChunk_rejects_crc_mismatch (bytes : ByteArray) (pos : Nat)
    (hLen : pos + 3 < bytes.size)
    (hBound : pos + 8 + readU32BE bytes pos hLen + 4 ≤ bytes.size)
    (hBad :
      readU32BE bytes (pos + 8 + readU32BE bytes pos hLen) (by omega) ≠
        (crc32Chunk
          (bytes.extract (pos + 4) (pos + 4 + 4))
          (bytes.extract (pos + 8) (pos + 8 + readU32BE bytes pos hLen))).toNat) :
    readChunk bytes pos hLen = none := by
  unfold readChunk
  simp [hBound, hBad]

/-- Every successful `readChunk` result passed the CRC equality checked by the
runtime parser. This is the soundness direction for chunk CRC validation. -/
lemma readChunk_success_crc_matches (bytes : ByteArray) (pos : Nat)
    (hLen : pos + 3 < bytes.size)
    (hread : (readChunk bytes pos hLen).isSome) :
    ∃ hBound : pos + 8 + readU32BE bytes pos hLen + 4 ≤ bytes.size,
      readU32BE bytes (pos + 8 + readU32BE bytes pos hLen) (by omega) =
        (crc32Chunk
          (bytes.extract (pos + 4) (pos + 4 + 4))
          (bytes.extract (pos + 8) (pos + 8 + readU32BE bytes pos hLen))).toNat := by
  unfold readChunk at hread
  by_cases hBound : pos + 8 + readU32BE bytes pos hLen + 4 ≤ bytes.size
  · simp [hBound] at hread
    refine ⟨hBound, ?_⟩
    simpa using hread
  · simp [hBound] at hread

/-- Before `IHDR`, the block-stream parser rejects every non-`IHDR` chunk. -/
lemma parsePngLoopFuel_rejects_non_ihdr_before_header (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngParseState)
    (typBytes chunkData : ByteArray) (posNext : Nat)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = none)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false) :
    parsePngLoopFuel (fuel + 1) bytes pos state = none := by
  unfold parsePngLoopFuel
  simp [hpos, hLen, hread, hheader, hnotIHDR]

/-- Once an `IHDR` has been accepted, any later `IHDR` is rejected. -/
lemma parsePngLoopFuel_rejects_duplicate_ihdr (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hIHDR : (typBytes == ihdrTypeBytes) = true) :
    parsePngLoopFuel (fuel + 1) bytes pos state = none := by
  unfold parsePngLoopFuel
  simp [hpos, hLen, hread, hheader, hIHDR]

/-- `PLTE` is rejected after another `PLTE` or after any `IDAT`. -/
lemma parsePngLoopFuel_rejects_plte_after_plte_or_idat (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hPLTE : (typBytes == plteTypeBytes) = true)
    (hseen : (state.seenPLTE || state.seenIDAT) = true) :
    parsePngLoopFuel (fuel + 1) bytes pos state = none := by
  unfold parsePngLoopFuel
  simp [hpos, hLen, hread, hheader, hnotIHDR, hPLTE, hseen]

/-- After an ancillary chunk closes the `IDAT` run, another `IDAT` is rejected. -/
lemma parsePngLoopFuel_rejects_idat_after_closed_idat (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hnotPLTE : (typBytes == plteTypeBytes) = false)
    (hIDAT : (typBytes == idatTypeBytes) = true)
    (hclosed : state.closedIDAT = true) :
    parsePngLoopFuel (fuel + 1) bytes pos state = none := by
  unfold parsePngLoopFuel
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hIDAT, hclosed]

/-- An `IEND` chunk with payload bytes is rejected. -/
lemma parsePngLoopFuel_rejects_nonempty_iend (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hnotPLTE : (typBytes == plteTypeBytes) = false)
    (hnotIDAT : (typBytes == idatTypeBytes) = false)
    (hIEND : (typBytes == iendTypeBytes) = true)
    (hdata : (chunkData.size != 0) = true) :
    parsePngLoopFuel (fuel + 1) bytes pos state = none := by
  unfold parsePngLoopFuel
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hnotIDAT, hIEND, hdata]

/-- `IEND` is rejected until at least one `IDAT` has been seen. -/
lemma parsePngLoopFuel_rejects_iend_before_idat (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hnotPLTE : (typBytes == plteTypeBytes) = false)
    (hnotIDAT : (typBytes == idatTypeBytes) = false)
    (hIEND : (typBytes == iendTypeBytes) = true)
    (hdata : (chunkData.size != 0) = false)
    (hseen : state.seenIDAT = false) :
    parsePngLoopFuel (fuel + 1) bytes pos state = none := by
  unfold parsePngLoopFuel
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hnotIDAT, hIEND, hdata, hseen]

/-- `IEND` must consume the final bytes of the PNG stream. -/
lemma parsePngLoopFuel_rejects_trailing_after_iend (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hnotPLTE : (typBytes == plteTypeBytes) = false)
    (hnotIDAT : (typBytes == idatTypeBytes) = false)
    (hIEND : (typBytes == iendTypeBytes) = true)
    (hdata : (chunkData.size != 0) = false)
    (hseen : state.seenIDAT = true)
    (htrail : (posNext != bytes.size) = true) :
    parsePngLoopFuel (fuel + 1) bytes pos state = none := by
  unfold parsePngLoopFuel
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hnotIDAT, hIEND,
    hdata, hseen, htrail]

/-- A `tRNS` chunk is rejected. tRNS attaches transparency to color types 0/2/3 that
the decoder does not honor; silently skipping it would change pixel semantics. -/
lemma parsePngLoopFuel_rejects_tRNS (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hnotPLTE : (typBytes == plteTypeBytes) = false)
    (hnotIDAT : (typBytes == idatTypeBytes) = false)
    (hnotIEND : (typBytes == iendTypeBytes) = false)
    (hTRNS : (typBytes == trnsTypeBytes) = true) :
    parsePngLoopFuel (fuel + 1) bytes pos state = none := by
  unfold parsePngLoopFuel
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hnotIDAT, hnotIEND, hTRNS]

/-- Color type 4 carries alpha in the image samples, so `tRNS` is invalid.
This guards the gray+alpha metadata path from duplicate transparency sources. -/
lemma parseTrnsData_rejects_grayAlpha8 (data : ByteArray) :
    parseTrnsData
      { width := 1, height := 1, colorType := 4, bitDepth := 8 } data = none := by
  unfold parseTrnsData
  simp

/-- Color type 4 still rejects `tRNS` at 16-bit depth.
This keeps alpha-in-sample images from also carrying transparent-color metadata. -/
lemma parseTrnsData_rejects_grayAlpha16 (data : ByteArray) :
    parseTrnsData
      { width := 1, height := 1, colorType := 4, bitDepth := 16 } data = none := by
  unfold parseTrnsData
  simp

/-- A 16-bit grayscale `tRNS` payload is preserved as a `UInt16` sample.
This pins transparent-color parsing for high-precision grayscale PNGs. -/
lemma parseTrnsData_accepts_gray16 :
    parseTrnsData
      { width := 1, height := 1, colorType := 0, bitDepth := 16 }
      (ByteArray.mk #[u8 0x12, u8 0x34]) =
        some (.gray16 (UInt16.ofNat 0x1234)) := by
  native_decide

/-- A 16-bit truecolor `tRNS` payload is preserved as three `UInt16` samples.
This prevents the metadata parser from accidentally truncating RGB transparency. -/
lemma parseTrnsData_accepts_rgb16 :
    parseTrnsData
      { width := 1, height := 1, colorType := 2, bitDepth := 16 }
      (ByteArray.mk #[u8 0x12, u8 0x34, u8 0x56, u8 0x78, u8 0x9a, u8 0xbc]) =
        some (.rgb16 (UInt16.ofNat 0x1234) (UInt16.ofNat 0x5678)
          (UInt16.ofNat 0x9abc)) := by
  native_decide

/-- The metadata-aware parser records a valid `tRNS` chunk and continues.
This is the branch-level correctness fact for supported transparency metadata. -/
lemma parsePngLoopFuelWithMetadata_accepts_tRNS (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngMetadataParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (trns : PngTransparency)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hnotPLTE : (typBytes == plteTypeBytes) = false)
    (hnotIDAT : (typBytes == idatTypeBytes) = false)
    (hnotIEND : (typBytes == iendTypeBytes) = false)
    (hTRNS : (typBytes == trnsTypeBytes) = true)
    (hseen : state.seenIDAT = false)
    (hdup : state.metadata.transparency.isSome = false)
    (hparse : parseTrnsData hdr chunkData = some trns) :
    parsePngLoopFuelWithMetadata (fuel + 1) bytes pos state =
      parsePngLoopFuelWithMetadata fuel bytes posNext
        { state with metadata := { state.metadata with transparency := some trns } } := by
  conv =>
    lhs
    unfold parsePngLoopFuelWithMetadata
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hnotIDAT, hnotIEND,
    hTRNS, hseen, hdup, hparse]

/-- `tRNS` must appear before the first `IDAT` chunk in the metadata-aware parser. -/
lemma parsePngLoopFuelWithMetadata_rejects_tRNS_after_idat (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngMetadataParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hnotPLTE : (typBytes == plteTypeBytes) = false)
    (hnotIDAT : (typBytes == idatTypeBytes) = false)
    (hnotIEND : (typBytes == iendTypeBytes) = false)
    (hTRNS : (typBytes == trnsTypeBytes) = true)
    (hseen : state.seenIDAT = true) :
    parsePngLoopFuelWithMetadata (fuel + 1) bytes pos state = none := by
  unfold parsePngLoopFuelWithMetadata
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hnotIDAT, hnotIEND,
    hTRNS, hseen]

/-- A second `tRNS` chunk is rejected rather than replacing earlier metadata. -/
lemma parsePngLoopFuelWithMetadata_rejects_duplicate_tRNS (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngMetadataParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hnotPLTE : (typBytes == plteTypeBytes) = false)
    (hnotIDAT : (typBytes == idatTypeBytes) = false)
    (hnotIEND : (typBytes == iendTypeBytes) = false)
    (hTRNS : (typBytes == trnsTypeBytes) = true)
    (hseen : state.seenIDAT = false)
    (hdup : state.metadata.transparency.isSome = true) :
    parsePngLoopFuelWithMetadata (fuel + 1) bytes pos state = none := by
  unfold parsePngLoopFuelWithMetadata
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hnotIDAT, hnotIEND,
    hTRNS, hseen, hdup]

/-- The metadata-aware parser records a valid `bKGD` chunk and continues.
This proves background metadata is preserved at the container layer. -/
lemma parsePngLoopFuelWithMetadata_accepts_bKGD (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngMetadataParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (bkgd : PngBackground)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hnotPLTE : (typBytes == plteTypeBytes) = false)
    (hnotIDAT : (typBytes == idatTypeBytes) = false)
    (hnotIEND : (typBytes == iendTypeBytes) = false)
    (hnotTRNS : (typBytes == trnsTypeBytes) = false)
    (hBKGD : (typBytes == bkgdTypeBytes) = true)
    (hseen : state.seenIDAT = false)
    (hdup : state.metadata.background.isSome = false)
    (hparse : parseBkgdData hdr chunkData = some bkgd) :
    parsePngLoopFuelWithMetadata (fuel + 1) bytes pos state =
      parsePngLoopFuelWithMetadata fuel bytes posNext
        { state with metadata := { state.metadata with background := some bkgd } } := by
  conv =>
    lhs
    unfold parsePngLoopFuelWithMetadata
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hnotIDAT, hnotIEND,
    hnotTRNS, hBKGD, hseen, hdup, hparse]

/-- A grayscale `bKGD` payload is valid for color type 4.
This is the payload-level fact used by gray+alpha background composition. -/
lemma parseBkgdData_accepts_grayAlpha8 :
    parseBkgdData
      { width := 1, height := 1, colorType := 4, bitDepth := 8 }
      (ByteArray.mk #[u8 0, u8 100]) = some (.gray8 (u8 100)) := by
  native_decide

/-- A grayscale `bKGD` payload is valid for 16-bit color type 4.
This is the payload fact used by high-precision gray+alpha compositing. -/
lemma parseBkgdData_accepts_grayAlpha16 :
    parseBkgdData
      { width := 1, height := 1, colorType := 4, bitDepth := 16 }
      (ByteArray.mk #[u8 0x12, u8 0x34]) =
        some (.gray16 (UInt16.ofNat 0x1234)) := by
  native_decide

/-- A 16-bit grayscale `bKGD` payload is preserved as a `UInt16` sample.
This covers background metadata for high-precision grayscale PNGs. -/
lemma parseBkgdData_accepts_gray16 :
    parseBkgdData
      { width := 1, height := 1, colorType := 0, bitDepth := 16 }
      (ByteArray.mk #[u8 0x12, u8 0x34]) =
        some (.gray16 (UInt16.ofNat 0x1234)) := by
  native_decide

/-- A 16-bit truecolor `bKGD` payload is preserved as three `UInt16` samples.
This keeps background metadata exact before any requested downsampling. -/
lemma parseBkgdData_accepts_rgb16 :
    parseBkgdData
      { width := 1, height := 1, colorType := 2, bitDepth := 16 }
      (ByteArray.mk #[u8 0x20, u8 0x01, u8 0x40, u8 0x02, u8 0x60, u8 0x03]) =
        some (.rgb16 (UInt16.ofNat 0x2001) (UInt16.ofNat 0x4002)
          (UInt16.ofNat 0x6003)) := by
  native_decide

/-- A 16-bit RGBA `bKGD` payload is parsed as a truecolor background.
This is the payload fact used when compositing high-precision RGBA over bKGD. -/
lemma parseBkgdData_accepts_rgba16 :
    parseBkgdData
      { width := 1, height := 1, colorType := 6, bitDepth := 16 }
      (ByteArray.mk #[u8 0x20, u8 0x01, u8 0x40, u8 0x02, u8 0x60, u8 0x03]) =
        some (.rgb16 (UInt16.ofNat 0x2001) (UInt16.ofNat 0x4002)
          (UInt16.ofNat 0x6003)) := by
  native_decide

/-- `bKGD` must appear before the first `IDAT` chunk in the metadata-aware parser. -/
lemma parsePngLoopFuelWithMetadata_rejects_bKGD_after_idat (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngMetadataParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hnotPLTE : (typBytes == plteTypeBytes) = false)
    (hnotIDAT : (typBytes == idatTypeBytes) = false)
    (hnotIEND : (typBytes == iendTypeBytes) = false)
    (hnotTRNS : (typBytes == trnsTypeBytes) = false)
    (hBKGD : (typBytes == bkgdTypeBytes) = true)
    (hseen : state.seenIDAT = true) :
    parsePngLoopFuelWithMetadata (fuel + 1) bytes pos state = none := by
  unfold parsePngLoopFuelWithMetadata
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hnotIDAT, hnotIEND,
    hnotTRNS, hBKGD, hseen]

/-- A second `bKGD` chunk is rejected rather than replacing earlier metadata. -/
lemma parsePngLoopFuelWithMetadata_rejects_duplicate_bKGD (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngMetadataParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hnotPLTE : (typBytes == plteTypeBytes) = false)
    (hnotIDAT : (typBytes == idatTypeBytes) = false)
    (hnotIEND : (typBytes == iendTypeBytes) = false)
    (hnotTRNS : (typBytes == trnsTypeBytes) = false)
    (hBKGD : (typBytes == bkgdTypeBytes) = true)
    (hseen : state.seenIDAT = false)
    (hdup : state.metadata.background.isSome = true) :
    parsePngLoopFuelWithMetadata (fuel + 1) bytes pos state = none := by
  unfold parsePngLoopFuelWithMetadata
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hnotIDAT, hnotIEND,
    hnotTRNS, hBKGD, hseen, hdup]

/-- A four-byte nonzero `gAMA` payload is parsed as its scaled gamma integer.
This pins the payload-level metadata read used by the color-space parser branch. -/
lemma parseGammaData_accepts_45455 :
    parseGammaData (ByteArray.mk #[u8 0x00, u8 0x00, u8 0xb1, u8 0x8f]) =
      some 45455 := by
  native_decide

/-- A zero `gAMA` value is invalid, so the payload parser rejects it.
This prevents later color transforms from dividing by an invalid gamma. -/
lemma parseGammaData_rejects_zero :
    parseGammaData (ByteArray.mk #[u8 0, u8 0, u8 0, u8 0]) = none := by
  native_decide

/-- `gAMA` has an exact four-byte payload shape.
This lemma exposes the length check used before reading the scaled integer. -/
lemma parseGammaData_rejects_bad_length (data : ByteArray)
    (hlen : data.size ≠ 4) :
    parseGammaData data = none := by
  unfold parseGammaData
  simp [hlen]

/-- The four valid `sRGB` rendering intents are decoded from bytes `0..3`.
This pins all accepted payload values for metadata-aware decode. -/
lemma parseSrgbData_accepts_intents :
    (parseSrgbData (ByteArray.mk #[u8 0]) = some .perceptual) ∧
    (parseSrgbData (ByteArray.mk #[u8 1]) = some .relativeColorimetric) ∧
    (parseSrgbData (ByteArray.mk #[u8 2]) = some .saturation) ∧
    (parseSrgbData (ByteArray.mk #[u8 3]) = some .absoluteColorimetric) := by
  native_decide

/-- An out-of-range `sRGB` intent byte is rejected.
This guards the one-byte rendering-intent parser from accepting reserved values. -/
lemma parseSrgbData_rejects_bad_intent :
    parseSrgbData (ByteArray.mk #[u8 4]) = none := by
  native_decide

/-- A well-formed seven-byte `tIME` payload is decoded exactly.
This witnesses the metadata parser's calendar-field layout. -/
lemma parseTimeData_accepts_valid_time :
    parseTimeData (ByteArray.mk #[u8 0x07, u8 0xea, u8 5, u8 2, u8 17, u8 45, u8 12]) =
      some { year := 2026, month := 5, day := 2, hour := 17, minute := 45, second := 12 } := by
  native_decide

/-- `tIME` has an exact seven-byte payload shape.
This exposes the length check before the calendar fields are read. -/
lemma parseTimeData_rejects_bad_length (data : ByteArray)
    (hlen : data.size ≠ 7) :
    parseTimeData data = none := by
  unfold parseTimeData
  simp [hlen]

/-- Invalid calendar fields in `tIME` are rejected.
This prevents nonsensical modification timestamps from entering metadata. -/
lemma parseTimeData_rejects_bad_month :
    parseTimeData (ByteArray.mk #[u8 0x07, u8 0xea, u8 13, u8 1, u8 0, u8 0, u8 0]) =
      none := by
  native_decide

/-- Invalid calendar days in `tIME` are rejected.
This covers the month-specific day limit used by the validator. -/
lemma parseTimeData_rejects_bad_day :
    parseTimeData (ByteArray.mk #[u8 0x07, u8 0xea, u8 2, u8 30, u8 0, u8 0, u8 0]) =
      none := by
  native_decide

/-- Encoder-side `tIME` payloads use exactly the seven bytes required by PNG.
This keeps the ancillary writer aligned with the parser shape. -/
lemma encodeTimeData?_valid_size :
    (encodeTimeData?
      { year := 2026, month := 5, day := 2, hour := 17, minute := 45, second := 12 }).map
        ByteArray.size = some 7 := by
  native_decide

/-- A valid `pHYs` payload decodes to its physical pixel dimensions.
This pins the field layout used to preserve density metadata. -/
lemma parsePhysData_accepts_meter_300dpi :
    parsePhysData
      (ByteArray.mk #[u8 0, u8 0, u8 46, u8 35, u8 0, u8 0, u8 46, u8 35, u8 1]) =
        some
          { xPixelsPerUnit := 11811
            yPixelsPerUnit := 11811
            unit := .meter } := by
  native_decide

/-- `pHYs` has an exact nine-byte payload shape.
This exposes the length check before the density fields are read. -/
lemma parsePhysData_rejects_bad_length (data : ByteArray)
    (hlen : data.size ≠ 9) :
    parsePhysData data = none := by
  unfold parsePhysData
  simp [hlen]

/-- Invalid `pHYs` unit specifiers are rejected.
This prevents reserved unit bytes from entering preserved metadata. -/
lemma parsePhysData_rejects_bad_unit :
    parsePhysData
      (ByteArray.mk #[u8 0, u8 0, u8 11, u8 19, u8 0, u8 0, u8 11, u8 19, u8 2]) =
        none := by
  native_decide

/-- Encoder-side `pHYs` payloads use exactly the nine bytes required by PNG.
This keeps the ancillary writer aligned with the parser shape. -/
lemma encodePhysData?_valid_size :
    (encodePhysData? (PngPhysicalPixelDimensions.ofDpiRounded 300 300)).map
      ByteArray.size = some 9 := by
  native_decide

/-- Rounded DPI conversion maps 300 DPI to the standard 11811 pixels/metre.
This fixes the user-facing DPI helper at a common print density. -/
lemma dpiToPixelsPerMeterRounded_300 :
    dpiToPixelsPerMeterRounded 300 = 11811 := by
  native_decide

/-- Rounded pixels/metre conversion maps 11811 back to 300 DPI.
This gives the inverse display fact for the common 300 DPI case. -/
lemma pixelsPerMeterToDpiRounded_11811 :
    pixelsPerMeterToDpiRounded 11811 = 300 := by
  native_decide

/-- The metadata-aware parser records a valid `tIME` chunk and continues.
This is the branch-level preservation fact for modification-time metadata. -/
lemma parsePngLoopFuelWithMetadata_accepts_tIME (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngMetadataParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (time : PngTime)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hnotPLTE : (typBytes == plteTypeBytes) = false)
    (hnotIDAT : (typBytes == idatTypeBytes) = false)
    (hnotIEND : (typBytes == iendTypeBytes) = false)
    (hnotTRNS : (typBytes == trnsTypeBytes) = false)
    (hnotBKGD : (typBytes == bkgdTypeBytes) = false)
    (hnotGAMA : (typBytes == gamaTypeBytes) = false)
    (hnotSRGB : (typBytes == srgbTypeBytes) = false)
    (hTIME : (typBytes == timeTypeBytes) = true)
    (hdup : state.metadata.modificationTime.isSome = false)
    (hparse : parseTimeData chunkData = some time) :
    parsePngLoopFuelWithMetadata (fuel + 1) bytes pos state =
      parsePngLoopFuelWithMetadata fuel bytes posNext
        { state with
            closedIDAT := if state.seenIDAT then true else state.closedIDAT
            metadata := { state.metadata with modificationTime := some time } } := by
  conv =>
    lhs
    unfold parsePngLoopFuelWithMetadata
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hnotIDAT, hnotIEND,
    hnotTRNS, hnotBKGD, hnotGAMA, hnotSRGB, hTIME, hdup, hparse]

/-- A second `tIME` chunk is rejected rather than replacing the original value.
This makes modification-time metadata deterministic. -/
lemma parsePngLoopFuelWithMetadata_rejects_duplicate_tIME (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngMetadataParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hnotPLTE : (typBytes == plteTypeBytes) = false)
    (hnotIDAT : (typBytes == idatTypeBytes) = false)
    (hnotIEND : (typBytes == iendTypeBytes) = false)
    (hnotTRNS : (typBytes == trnsTypeBytes) = false)
    (hnotBKGD : (typBytes == bkgdTypeBytes) = false)
    (hnotGAMA : (typBytes == gamaTypeBytes) = false)
    (hnotSRGB : (typBytes == srgbTypeBytes) = false)
    (hTIME : (typBytes == timeTypeBytes) = true)
    (hdup : state.metadata.modificationTime.isSome = true) :
    parsePngLoopFuelWithMetadata (fuel + 1) bytes pos state = none := by
  unfold parsePngLoopFuelWithMetadata
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hnotIDAT, hnotIEND,
    hnotTRNS, hnotBKGD, hnotGAMA, hnotSRGB, hTIME, hdup]

/-- The metadata-aware parser records a valid `pHYs` chunk and continues.
This is the branch-level preservation fact for density metadata. -/
lemma parsePngLoopFuelWithMetadata_accepts_pHYs (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngMetadataParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (physical : PngPhysicalPixelDimensions)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hnotPLTE : (typBytes == plteTypeBytes) = false)
    (hnotIDAT : (typBytes == idatTypeBytes) = false)
    (hnotIEND : (typBytes == iendTypeBytes) = false)
    (hnotTRNS : (typBytes == trnsTypeBytes) = false)
    (hnotBKGD : (typBytes == bkgdTypeBytes) = false)
    (hnotGAMA : (typBytes == gamaTypeBytes) = false)
    (hnotSRGB : (typBytes == srgbTypeBytes) = false)
    (hnotTIME : (typBytes == timeTypeBytes) = false)
    (hPHYS : (typBytes == physTypeBytes) = true)
    (hseen : state.seenIDAT = false)
    (hdup : state.metadata.physical.isSome = false)
    (hparse : parsePhysData chunkData = some physical) :
    parsePngLoopFuelWithMetadata (fuel + 1) bytes pos state =
      parsePngLoopFuelWithMetadata fuel bytes posNext
        { state with metadata := { state.metadata with physical := some physical } } := by
  conv =>
    lhs
    unfold parsePngLoopFuelWithMetadata
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hnotIDAT, hnotIEND,
    hnotTRNS, hnotBKGD, hnotGAMA, hnotSRGB, hnotTIME, hPHYS, hseen, hdup, hparse]

/-- `pHYs` must appear before the first `IDAT` chunk.
This proves the metadata parser rejects late density metadata. -/
lemma parsePngLoopFuelWithMetadata_rejects_pHYs_after_idat (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngMetadataParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hnotPLTE : (typBytes == plteTypeBytes) = false)
    (hnotIDAT : (typBytes == idatTypeBytes) = false)
    (hnotIEND : (typBytes == iendTypeBytes) = false)
    (hnotTRNS : (typBytes == trnsTypeBytes) = false)
    (hnotBKGD : (typBytes == bkgdTypeBytes) = false)
    (hnotGAMA : (typBytes == gamaTypeBytes) = false)
    (hnotSRGB : (typBytes == srgbTypeBytes) = false)
    (hnotTIME : (typBytes == timeTypeBytes) = false)
    (hPHYS : (typBytes == physTypeBytes) = true)
    (hseen : state.seenIDAT = true) :
    parsePngLoopFuelWithMetadata (fuel + 1) bytes pos state = none := by
  unfold parsePngLoopFuelWithMetadata
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hnotIDAT, hnotIEND,
    hnotTRNS, hnotBKGD, hnotGAMA, hnotSRGB, hnotTIME, hPHYS, hseen]

/-- A second `pHYs` chunk is rejected rather than replacing the original value.
This makes physical pixel metadata deterministic. -/
lemma parsePngLoopFuelWithMetadata_rejects_duplicate_pHYs (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngMetadataParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hnotPLTE : (typBytes == plteTypeBytes) = false)
    (hnotIDAT : (typBytes == idatTypeBytes) = false)
    (hnotIEND : (typBytes == iendTypeBytes) = false)
    (hnotTRNS : (typBytes == trnsTypeBytes) = false)
    (hnotBKGD : (typBytes == bkgdTypeBytes) = false)
    (hnotGAMA : (typBytes == gamaTypeBytes) = false)
    (hnotSRGB : (typBytes == srgbTypeBytes) = false)
    (hnotTIME : (typBytes == timeTypeBytes) = false)
    (hPHYS : (typBytes == physTypeBytes) = true)
    (hseen : state.seenIDAT = false)
    (hdup : state.metadata.physical.isSome = true) :
    parsePngLoopFuelWithMetadata (fuel + 1) bytes pos state = none := by
  unfold parsePngLoopFuelWithMetadata
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hnotIDAT, hnotIEND,
    hnotTRNS, hnotBKGD, hnotGAMA, hnotSRGB, hnotTIME, hPHYS, hseen, hdup]

/-- The metadata-aware parser records a valid `gAMA` chunk and continues.
This is the branch-level preservation fact for image gamma metadata. -/
lemma parsePngLoopFuelWithMetadata_accepts_gAMA (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngMetadataParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (gamma : Nat)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hnotPLTE : (typBytes == plteTypeBytes) = false)
    (hnotIDAT : (typBytes == idatTypeBytes) = false)
    (hnotIEND : (typBytes == iendTypeBytes) = false)
    (hnotTRNS : (typBytes == trnsTypeBytes) = false)
    (hnotBKGD : (typBytes == bkgdTypeBytes) = false)
    (hGAMA : (typBytes == gamaTypeBytes) = true)
    (horder : (state.seenPLTE || state.seenIDAT) = false)
    (hdup : state.metadata.gamma.isSome = false)
    (hsrgb : state.metadata.srgb = none)
    (hparse : parseGammaData chunkData = some gamma) :
    parsePngLoopFuelWithMetadata (fuel + 1) bytes pos state =
      parsePngLoopFuelWithMetadata fuel bytes posNext
        { state with metadata := { state.metadata with gamma := some gamma } } := by
  conv =>
    lhs
    unfold parsePngLoopFuelWithMetadata
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hnotIDAT, hnotIEND,
    hnotTRNS, hnotBKGD, hGAMA, horder, hdup, hparse, hsrgb]

/-- `gAMA` must precede both `PLTE` and `IDAT`.
This is the ordering-rejection branch for gamma metadata. -/
lemma parsePngLoopFuelWithMetadata_rejects_gAMA_after_plte_or_idat (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngMetadataParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hnotPLTE : (typBytes == plteTypeBytes) = false)
    (hnotIDAT : (typBytes == idatTypeBytes) = false)
    (hnotIEND : (typBytes == iendTypeBytes) = false)
    (hnotTRNS : (typBytes == trnsTypeBytes) = false)
    (hnotBKGD : (typBytes == bkgdTypeBytes) = false)
    (hGAMA : (typBytes == gamaTypeBytes) = true)
    (horder : (state.seenPLTE || state.seenIDAT) = true) :
    parsePngLoopFuelWithMetadata (fuel + 1) bytes pos state = none := by
  unfold parsePngLoopFuelWithMetadata
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hnotIDAT, hnotIEND,
    hnotTRNS, hnotBKGD, hGAMA, horder]

/-- A second `gAMA` chunk is rejected rather than replacing earlier metadata.
This makes gamma parsing deterministic. -/
lemma parsePngLoopFuelWithMetadata_rejects_duplicate_gAMA (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngMetadataParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hnotPLTE : (typBytes == plteTypeBytes) = false)
    (hnotIDAT : (typBytes == idatTypeBytes) = false)
    (hnotIEND : (typBytes == iendTypeBytes) = false)
    (hnotTRNS : (typBytes == trnsTypeBytes) = false)
    (hnotBKGD : (typBytes == bkgdTypeBytes) = false)
    (hGAMA : (typBytes == gamaTypeBytes) = true)
    (horder : (state.seenPLTE || state.seenIDAT) = false)
    (hdup : state.metadata.gamma.isSome = true) :
    parsePngLoopFuelWithMetadata (fuel + 1) bytes pos state = none := by
  unfold parsePngLoopFuelWithMetadata
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hnotIDAT, hnotIEND,
    hnotTRNS, hnotBKGD, hGAMA, horder, hdup]

/-- The metadata-aware parser records a valid `sRGB` chunk and continues.
This is the branch-level preservation fact for rendering-intent metadata. -/
lemma parsePngLoopFuelWithMetadata_accepts_sRGB (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngMetadataParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (intent : PngSrgbIntent)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hnotPLTE : (typBytes == plteTypeBytes) = false)
    (hnotIDAT : (typBytes == idatTypeBytes) = false)
    (hnotIEND : (typBytes == iendTypeBytes) = false)
    (hnotTRNS : (typBytes == trnsTypeBytes) = false)
    (hnotBKGD : (typBytes == bkgdTypeBytes) = false)
    (hnotGAMA : (typBytes == gamaTypeBytes) = false)
    (hSRGB : (typBytes == srgbTypeBytes) = true)
    (horder : (state.seenPLTE || state.seenIDAT) = false)
    (hdup : state.metadata.srgb.isSome = false)
    (hgamma : state.metadata.gamma = none)
    (hparse : parseSrgbData chunkData = some intent) :
    parsePngLoopFuelWithMetadata (fuel + 1) bytes pos state =
      parsePngLoopFuelWithMetadata fuel bytes posNext
        { state with metadata := { state.metadata with srgb := some intent } } := by
  conv =>
    lhs
    unfold parsePngLoopFuelWithMetadata
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hnotIDAT, hnotIEND,
    hnotTRNS, hnotBKGD, hnotGAMA, hSRGB, horder, hdup, hparse, hgamma]

/-- `sRGB` must precede both `PLTE` and `IDAT`.
This is the ordering-rejection branch for sRGB metadata. -/
lemma parsePngLoopFuelWithMetadata_rejects_sRGB_after_plte_or_idat (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngMetadataParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hnotPLTE : (typBytes == plteTypeBytes) = false)
    (hnotIDAT : (typBytes == idatTypeBytes) = false)
    (hnotIEND : (typBytes == iendTypeBytes) = false)
    (hnotTRNS : (typBytes == trnsTypeBytes) = false)
    (hnotBKGD : (typBytes == bkgdTypeBytes) = false)
    (hnotGAMA : (typBytes == gamaTypeBytes) = false)
    (hSRGB : (typBytes == srgbTypeBytes) = true)
    (horder : (state.seenPLTE || state.seenIDAT) = true) :
    parsePngLoopFuelWithMetadata (fuel + 1) bytes pos state = none := by
  unfold parsePngLoopFuelWithMetadata
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hnotIDAT, hnotIEND,
    hnotTRNS, hnotBKGD, hnotGAMA, hSRGB, horder]

/-- A second `sRGB` chunk is rejected rather than replacing the original intent.
This makes color-space metadata deterministic. -/
lemma parsePngLoopFuelWithMetadata_rejects_duplicate_sRGB (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngMetadataParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hnotPLTE : (typBytes == plteTypeBytes) = false)
    (hnotIDAT : (typBytes == idatTypeBytes) = false)
    (hnotIEND : (typBytes == iendTypeBytes) = false)
    (hnotTRNS : (typBytes == trnsTypeBytes) = false)
    (hnotBKGD : (typBytes == bkgdTypeBytes) = false)
    (hnotGAMA : (typBytes == gamaTypeBytes) = false)
    (hSRGB : (typBytes == srgbTypeBytes) = true)
    (horder : (state.seenPLTE || state.seenIDAT) = false)
    (hdup : state.metadata.srgb.isSome = true) :
    parsePngLoopFuelWithMetadata (fuel + 1) bytes pos state = none := by
  unfold parsePngLoopFuelWithMetadata
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hnotIDAT, hnotIEND,
    hnotTRNS, hnotBKGD, hnotGAMA, hSRGB, horder, hdup]

/-- An `sRGB` chunk is incompatible with non-sRGB-compatible existing `gAMA`.
This proves the parser rejects conflicting color-space metadata. -/
lemma parsePngLoopFuelWithMetadata_rejects_sRGB_after_incompatible_gAMA (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngMetadataParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (intent : PngSrgbIntent) (gamma : Nat)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hnotPLTE : (typBytes == plteTypeBytes) = false)
    (hnotIDAT : (typBytes == idatTypeBytes) = false)
    (hnotIEND : (typBytes == iendTypeBytes) = false)
    (hnotTRNS : (typBytes == trnsTypeBytes) = false)
    (hnotBKGD : (typBytes == bkgdTypeBytes) = false)
    (hnotGAMA : (typBytes == gamaTypeBytes) = false)
    (hSRGB : (typBytes == srgbTypeBytes) = true)
    (horder : (state.seenPLTE || state.seenIDAT) = false)
    (hdup : state.metadata.srgb.isSome = false)
    (hgamma : state.metadata.gamma = some gamma)
    (hbad : gamma ≠ 45455)
    (hparse : parseSrgbData chunkData = some intent) :
    parsePngLoopFuelWithMetadata (fuel + 1) bytes pos state = none := by
  unfold parsePngLoopFuelWithMetadata
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hnotIDAT, hnotIEND,
    hnotTRNS, hnotBKGD, hnotGAMA, hSRGB, horder, hdup, hparse, hgamma, hbad]

/-- With no color-space metadata, the final color transform is a no-op.
This keeps existing encoder round-trip clients on the unchanged pixel path. -/
lemma applyPngColorSpaceTransform_no_metadata (targetColorType targetBitDepth : UInt8)
    (pixels : ByteArray) :
    applyPngColorSpaceTransform PngMetadata.empty targetColorType targetBitDepth pixels =
      some pixels := by
  rfl

/-- `sRGB` metadata has precedence and does not rewrite already-sRGB samples.
This exposes the no-op transform branch for all rendering intents. -/
lemma applyPngColorSpaceTransform_sRGB_noop (metadata : PngMetadata)
    (intent : PngSrgbIntent) (targetColorType targetBitDepth : UInt8)
    (pixels : ByteArray) :
    applyPngColorSpaceTransform { metadata with srgb := some intent }
      targetColorType targetBitDepth pixels = some pixels := by
  cases intent <;> rfl

/-- The 8-bit RGBA gamma transform leaves the alpha byte untouched.
This concrete witness guards the non-alpha-channel traversal used by the LUT pass. -/
lemma applyGamma8ToPixels_preserves_rgba_alpha_sample :
    (applyGamma8ToPixels 100000 (u8 6)
      (ByteArray.mk #[u8 64, u8 128, u8 192, u8 77])).map (fun out => out.get! 3) =
        some (u8 77) := by
  native_decide

/-- The 16-bit grayscale+alpha gamma transform leaves the alpha sample untouched.
This witness covers the two-byte alpha-preservation path. -/
lemma applyGamma16ToPixels_preserves_grayAlpha_alpha_sample :
    (applyGamma16ToPixels 100000 (u8 4)
      (ByteArray.mk #[u8 0x12, u8 0x34, u8 0xab, u8 0xcd])).map
        (fun out => (out.get! 2, out.get! 3)) = some (u8 0xab, u8 0xcd) := by
  native_decide

/-- Once transparency or background metadata has appeared, a later `PLTE` is
rejected so the parser enforces the required relative chunk order. -/
lemma parsePngLoopFuelWithMetadata_rejects_plte_after_metadata (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngMetadataParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hPLTE : (typBytes == plteTypeBytes) = true)
    (hseen : (state.seenPLTE || state.seenIDAT) = false)
    (hmetadata : (state.metadata.transparency.isSome || state.metadata.background.isSome) = true) :
    parsePngLoopFuelWithMetadata (fuel + 1) bytes pos state = none := by
  unfold parsePngLoopFuelWithMetadata
  simp [hpos, hLen, hread, hheader, hnotIHDR, hPLTE, hseen, hmetadata]

/-- An `sBIT` chunk is rejected. sBIT records the original significant bit count per
channel; silently skipping it would misrepresent pixel precision. -/
lemma parsePngLoopFuel_rejects_sBIT (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hnotPLTE : (typBytes == plteTypeBytes) = false)
    (hnotIDAT : (typBytes == idatTypeBytes) = false)
    (hnotIEND : (typBytes == iendTypeBytes) = false)
    (hnotTRNS : (typBytes == trnsTypeBytes) = false)
    (hnotGAMA : (typBytes == gamaTypeBytes) = false)
    (hnotSRGB : (typBytes == srgbTypeBytes) = false)
    (hnotTIME : (typBytes == timeTypeBytes) = false)
    (hnotPHYS : (typBytes == physTypeBytes) = false)
    (hSBIT : (typBytes == sbitTypeBytes) = true) :
    parsePngLoopFuel (fuel + 1) bytes pos state = none := by
  unfold parsePngLoopFuel
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hnotIDAT, hnotIEND,
    hnotTRNS, hnotGAMA, hnotSRGB, hnotTIME, hnotPHYS, hSBIT]

/-- Unknown critical chunk types are rejected after the header. -/
lemma parsePngLoopFuel_rejects_unknown_critical (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hnotPLTE : (typBytes == plteTypeBytes) = false)
    (hnotIDAT : (typBytes == idatTypeBytes) = false)
    (hnotIEND : (typBytes == iendTypeBytes) = false)
    (hnotTRNS : (typBytes == trnsTypeBytes) = false)
    (hnotGAMA : (typBytes == gamaTypeBytes) = false)
    (hnotSRGB : (typBytes == srgbTypeBytes) = false)
    (hnotTIME : (typBytes == timeTypeBytes) = false)
    (hnotPHYS : (typBytes == physTypeBytes) = false)
    (hnotSBIT : (typBytes == sbitTypeBytes) = false)
    (hcritical : isCriticalChunkType typBytes = true) :
    parsePngLoopFuel (fuel + 1) bytes pos state = none := by
  unfold parsePngLoopFuel
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hnotIDAT, hnotIEND,
    hnotTRNS, hnotGAMA, hnotSRGB, hnotTIME, hnotPHYS, hnotSBIT, hcritical]

/-- Ancillary chunks (other than the explicitly handled color/precision metadata)
before the `IDAT` run do not change parser state. -/
lemma parsePngLoopFuel_ignores_ancillary_before_idat (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hnotPLTE : (typBytes == plteTypeBytes) = false)
    (hnotIDAT : (typBytes == idatTypeBytes) = false)
    (hnotIEND : (typBytes == iendTypeBytes) = false)
    (hnotTRNS : (typBytes == trnsTypeBytes) = false)
    (hnotGAMA : (typBytes == gamaTypeBytes) = false)
    (hnotSRGB : (typBytes == srgbTypeBytes) = false)
    (hnotTIME : (typBytes == timeTypeBytes) = false)
    (hnotPHYS : (typBytes == physTypeBytes) = false)
    (hnotSBIT : (typBytes == sbitTypeBytes) = false)
    (hcritical : isCriticalChunkType typBytes = false)
    (hseen : state.seenIDAT = false) :
    parsePngLoopFuel (fuel + 1) bytes pos state =
      parsePngLoopFuel fuel bytes posNext state := by
  conv =>
    lhs
    unfold parsePngLoopFuel
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hnotIDAT, hnotIEND,
    hnotTRNS, hnotGAMA, hnotSRGB, hnotTIME, hnotPHYS, hnotSBIT, hcritical, hseen]

/-- An `IDAT` chunk in an open `IDAT` run appends its payload and continues. -/
lemma parsePngLoopFuel_idat_appends_when_open (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hnotPLTE : (typBytes == plteTypeBytes) = false)
    (hIDAT : (typBytes == idatTypeBytes) = true)
    (hclosed : state.closedIDAT = false)
    (hpalette : (hdr.colorType == 3 && !state.seenPLTE) = false) :
    parsePngLoopFuel (fuel + 1) bytes pos state =
      parsePngLoopFuel fuel bytes posNext
        { header := some hdr
          idat := state.idat ++ chunkData
          seenPLTE := state.seenPLTE
          seenIDAT := true
          closedIDAT := false
          metadata := state.metadata } := by
  conv =>
    lhs
    unfold parsePngLoopFuel
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hIDAT, hclosed, hpalette]

end Lemmas

end Bitmaps
